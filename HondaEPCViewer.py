
def format_price(price_raw):
    if price_raw is None:
        return ""
    txt = str(price_raw).replace("\x00", "").strip()
    # PLMST stores this literal in Shift-JIS; the cache decodes it before
    # the value reaches the viewer. Keep the original label unchanged.
    if txt == "ｵｰﾌﾟﾝ":
        return txt
    # Numeric prices are displayed with thousands separators.
    if txt.isdigit():
        return f"{int(txt):,}"
    return txt

import re
import unicodedata
from pathlib import Path
import sqlite3, re, tempfile, os, sys, struct, json, threading, queue
import tkinter as tk
from tkinter import ttk, messagebox
from PIL import Image, ImageTk, ImageOps

try:
    from epc_cache import build_cache, cache_is_current, parse_ksrb
except Exception as e:
    build_cache = cache_is_current = None
    _CACHE_IMPORT_ERROR = e

APP_DIR = Path(__file__).resolve().parent
DATA_DIR = APP_DIR / 'Data'
CACHE_DIR = APP_DIR / 'Cache'
IMAGE_CACHE = APP_DIR / 'image_cache'
CACHE_DIR.mkdir(exist_ok=True)
IMAGE_CACHE.mkdir(exist_ok=True)


def frame_number(value):
    m = re.findall(r'\d+', value.upper().replace(',', ''))
    return int(m[-1]) if m else None


def format_part_number(value):
    """Format Honda part numbers for display without changing the stored value.

    10 chars:  5-5   (9411110800 -> 94111-10800)
    11 chars:  5-3-3 (90113SA0025 -> 90113-SA0-025)
    12 chars:  5-5-2 (93600060140H -> 93600-06014-0H)
    13 chars:  5-3-5 (43471SS1010ZA -> 43471-SS1-010ZA)
    Other lengths are returned unchanged.
    """
    v = str(value or '').strip()
    if len(v) == 10:
        return f'{v[:5]}-{v[5:]}'
    if len(v) == 11:
        return f'{v[:5]}-{v[5:8]}-{v[8:]}'
    if len(v) == 12:
        return f'{v[:5]}-{v[5:10]}-{v[10:]}'
    if len(v) == 13:
        return f'{v[:5]}-{v[5:8]}-{v[8:]}'
    return v


def format_block_number(value):
    """Format the 7-byte Honda block number for display.

    Source layout is 3-byte symbol + 2-byte parent + 2-byte child.
    Examples: B1910 -> B-19-10, E0200 -> E-02-00, ATM1210 -> ATM-12-10.
    Empty/space-filled child fields are omitted. The stored value is unchanged.
    """
    v = str(value or '').strip()
    # The source field is exactly 7 bytes: symbol(3) + parent(2) + child(2).
    # Keep the field-based split rather than guessing from the number of letters.
    raw = str(value or '')
    if len(raw) >= 7:
        symbol = raw[:3].strip()
        parent = raw[3:5].strip()
        child = raw[5:7].strip()
        parts = [x for x in (symbol, parent, child) if x]
        return '-'.join(parts) if parts else v
    # Be tolerant of already-trimmed/short values.
    m = re.match(r'^(.{1,3})(.{2})(.{0,2})$', v)
    if m:
        parts = [x.strip() for x in m.groups() if x.strip()]
        return '-'.join(parts)
    return v


def make_vertical_splitter_v39(parent, upper, lower):
    """User-adjustable vertical splitter: drag the sash to resize upper/lower panes."""
    pane = tk.PanedWindow(parent, orient=tk.VERTICAL, sashwidth=7,
                          sashrelief=tk.RAISED, bd=0)
    pane.add(upper, stretch="always")
    pane.add(lower, stretch="always")
    return pane

class EPC:
    def __init__(self, db_path, data_base=None):
        self.db_path = Path(db_path)
        self.base = Path(data_base) if data_base is not None else self.db_path.parent
        self.con = sqlite3.connect(self.db_path)
        self.image_map = {p.name.upper(): p for p in self.base.rglob('*') if p.is_file() and p.suffix.upper() not in {'.CD', '.SQLITE'} and p.name.lower() != self.db_path.name.lower()}

    def close(self):
        try: self.con.close()
        except Exception: pass

    def q(self, sql, args=()):
        return self.con.execute(sql, args).fetchall()

    def models(self):
        return [r[0] for r in self.q('select distinct model from ksrb where trim(model)<>? order by model', ('',))]

    @staticmethod
    def _display_spec(raw):
        """Return only the specification text actually stored in KSRB.

        No model-specific labels (e.g. Version C/F/Z) are manufactured here.
        parse_ksrb already extracts the specification field from the source data.
        """
        v=str(raw or '').strip()
        return v if v else '－'

    def _ksrb_rows(self, model, typ='すべて'):
        clauses=['model=?']; args=[model]
        if typ and typ not in ('すべて','－'): clauses.append('type=?'); args.append(typ)
        return self.q('select offset,record_length,ident,model,type,frame_from,frame_to,grade,dbid,condition_id,condition_family,condition_e,condition_ids,option_codes,option_names,doors,transmission,engine from ksrb where '+' and '.join(clauses)+' order by offset',tuple(args))

    def types(self, model):
        vals=[]
        # KSRB is already filtered to folders present on this CD.  Build the
        # format list from those surviving records, not the shared TSMIR catalog.
        for r in self.q('select distinct type from ksrb where model=? and trim(type)<>? order by type',(model,'')):
            v=str(r[0] or '').strip()
            if v and v not in vals: vals.append(v)
        return vals

    def type_choices(self, model):
        return self.types(model)

    def grade_choices(self, model, typ, range_key=None):
        rows=self._ksrb_rows(model,typ)
        if range_key:
            lo,hi=range_key
            rows=[r for r in rows if r[5].strip()==lo and r[6].strip()==hi]
        vals=[]; seen=set()
        for r in rows:
            v=self._display_grade(r[7])
            detail=' / '.join(x for x in (r[15],r[16],r[17]) if x)
            label=f'{v} [ {detail} ]' if detail else v
            if v and label not in seen:
                seen.add(label); vals.append(label)
        return vals

    def option_choices(self, model, typ, grade, range_key=None):
        """Return option combinations for the selected type, hiding options
        fitted to every type in the same form/frame range.

        The common-option test uses the union of option codes within each
        distinct type, then intersects those sets.  It is intentionally scoped
        to the selected model/form/frame; other frames and forms do not affect it.
        """
        all_rows=self._ksrb_rows(model,typ)
        if range_key:
            lo,hi=range_key
            all_rows=[r for r in all_rows if r[5].strip()==lo and r[6].strip()==hi]

        def type_label(r):
            base=self._display_grade(r[7])
            detail=' / '.join(x for x in (r[15],r[16],r[17]) if x)
            return f'{base} [ {detail} ]' if detail else base

        # Keep every option recorded for the selected KSRBHMH combination.
        # Common-option suppression hid legitimate names (and could turn
        # several distinct combinations into repeated "標準" entries).
        common=set()

        rows=[r for r in all_rows if self._grade_matches(r[7],grade) and type_label(r)==grade]
        # Explicitly enforce the selected transmission.  The grade label also
        # carries this detail, but this guard prevents AT/MT rows from being
        # mixed if source records share the same visible grade text.
        selected_trans=next((str(r[16] or '').strip().upper() for r in rows if str(r[16] or '').strip()), '')
        if selected_trans in ('AT','MT'):
            rows=[r for r in rows if str(r[16] or '').strip().upper() in ('',selected_trans)]

        out=[]; seen=set()
        for r in rows:
            try:
                codes=[int(x) for x in json.loads(r[13] or '[]')]
                names=json.loads(r[14] or '[]')
            except Exception:
                codes=[]; names=[]
            # Show the source option names without suppressing common codes.
            # Keep the original record/ident for condition matching.
            visible=[str(n).strip() for code,n in zip(codes,names) if code not in common and str(n).strip()]
            label=' / '.join(visible) or 'なし'
            ident=str(r[2] or '').strip()
            if ident and (label,ident) not in seen:
                seen.add((label,ident)); out.append((label,ident))
        return out

    def grades(self, model, typ, range_key=None):
        return [label for label,_ident in self.grade_choices(model,typ,range_key)]

    def serial_ranges(self, model, typ):
        """Return distinct frame/production ranges present in KSRBHMH.

        The UI uses these exact source ranges; no labels such as 前期/後期 are added.
        """
        rows=self._ksrb_rows(model,typ)
        seen=set(); out=[]
        for r in rows:
            lo=str(r[5] or '').strip(); hi=str(r[6] or '').strip()
            if not lo and not hi: continue
            key=(lo,hi)
            if key in seen: continue
            seen.add(key)
            out.append(key)
        def num(x):
            m=re.search(r'\d+',x or '')
            return int(m.group()) if m else 10**30
        out.sort(key=lambda x:(num(x[0]),num(x[1]),x[0],x[1]))
        return out

    def range_label(self, pair):
        lo,hi=pair
        lo=lo.strip(); hi=hi.strip()
        if lo and hi: return f'{lo} ～ {hi}'
        if lo: return f'{lo} ～'
        if hi: return f'～ {hi}'
        return '－'

    def _range_matches(self, row, range_key):
        if not range_key: return True
        return row[5].strip()==range_key[0] and row[6].strip()==range_key[1]

    def _display_grade(self, raw):
        """Convert the source specification to the UI label without inventing names.

        The first two characters in the KSRBHMH specification field are a
        numeric catalog prefix (for example 00BEAT).  They are not part of
        the human-readable specification name.  Keep the raw value in the
        database/cache and normalize only for display/matching.
        """
        v=str(raw or '').strip()
        if re.match(r'^\d{2}[^0-9]', v):
            return v[2:].strip()
        return v

    def _grade_matches(self, raw, label):
        if not label or label=='すべて': return True
        shown=str(label).strip().split(' [',1)[0].strip()
        return self._display_grade(raw)==shown

    @staticmethod
    def _grade_ident(label):
        m=re.search(r'\[([^\]]+)\]\s*$',str(label or ''))
        return m.group(1).strip() if m else ''

    def _frame_matches(self, lo0, hi0, frame):
        if not frame: return True
        fn=frame_number(frame)
        if fn is None: return False
        lo,hi=frame_number(lo0),frame_number(hi0)
        return lo is not None and fn>=lo and (hi is None or fn<=hi)

    def variant_rows(self, model, typ='すべて', grade='すべて', frame='', range_key=None, grade_ident=None):
        ident=str(grade_ident or self._grade_ident(grade)).strip()
        rows=self._ksrb_rows(model,typ)
        out=[]
        for r in rows:
            if not self._range_matches(r,range_key): continue
            if ident:
                if str(r[2] or '').strip()!=ident: continue
            elif not self._grade_matches(r[7],grade):
                continue
            if not self._frame_matches(r[5],r[6],frame): continue
            out.append(r)
        return out

    def selected_condition_ids(self, model, typ, grade, frame, range_key=None, grade_ident=None):
        rows=self.variant_rows(model,typ,grade,frame,range_key,grade_ident)
        if not rows:
            return None

        # The frame-range selection is already the vehicle applicability
        # filter. Multiple KSRB rows represent the specification variants in
        # that range. Use only the first two KSRB condition IDs; option codes
        # are not part of PLMST/block condition matching. Keep the UNION of
        # those two-ID condition pairs because the UI selects one specification
        # record at a time and the part filter consumes the active IDs:
        # this means "show every part valid somewhere in this selected frame
        # range", while an option condition belonging only to a different
        # frame range cannot leak in.
        selected=[]
        seen=set()
        for r in rows:
            try:
                # condition_ids is deliberately limited to KSRB WORD 1 and WORD 2.
                vals=json.loads(r[12] or '[]')
            except Exception:
                vals=[v for v in (r[10],r[11]) if v is not None]
            for v in vals[:2]:
                if v is None: continue
                v=int(v)
                if v>0 and v not in seen:
                    seen.add(v); selected.append(v)
        return selected

    def conditions(self, model, typ, grade, frame):
        return [(r[9],r[2],r[4],r[5],r[6],r[7]) for r in self.variant_rows(model,typ,grade,frame)]

    def condition_family(self, model, typ, grade, frame):
        return sorted({r[10] for r in self.variant_rows(model,typ,grade,frame) if r[10] is not None})

    def groups(self):
        return self.q('select rowid,code,name,kind,offset,length from groups order by rowid')

    def blocks(self, group_rowid, conditions=None, model=None, grade=None):
        # Keep the complete diagram list at the data level, then hide only
        # diagrams for which *no part* is applicable to the currently selected
        # frame/specification.  This is deliberately different from v14's
        # block-level condition intersection: common diagrams remain visible,
        # while option-only diagrams (such as the three late-frame BEAT
        # drawings) disappear when their parts have no applicable condition.
        rows=self.q("""select id,section,image,description from blocks
                       where group_code=(select code from groups where rowid=?)
                         and kind=(select kind from groups where rowid=?)
                       order by record_offset""",(group_rowid,group_rowid))
        if conditions is None:
            return rows
        selected=set(int(x) for x in conditions if x is not None)
        visible=[]
        for r in rows:
            # BLKTYTBL's own block-level condition list is authoritative for
            # deciding whether the drawing itself belongs to the selected KSRB
            # variant.  A block with no BLKTYTBL condition IDs is common here
            # and remains visible (including engine/common drawings).
            bconds={int(x[0]) for x in self.q('select condition_id from block_conditions where block_id=?',(r[0],))}
            if bconds and not (bconds & selected):
                continue
            # Do not use part records to decide whether the drawing exists.
            # Once the block survives this test, parts() performs the second
            # stage of filtering inside that drawing.
            visible.append(r)
        return visible

    def parts(self,bid,conds=None,family_conds=None,model=None,grade=None):
        rows=self.q("""select p.id,p.part_number,p.description,p.price,p.annotation,group_concat(distinct pc.condition_id)
                       from parts p left join part_conditions pc on pc.part_id=p.id
                       where p.block_id=? group by p.id order by p.seq""",(bid,))
        if conds is None:
            # No matching KSRB row: do not impose a vehicle-condition filter.
            return [(part,desc,price,ann,condtxt) for _pid,part,desc,price,ann,condtxt in rows]
        selected=set(conds); out=[]
        for _pid,part,desc,price,ann,condtxt in rows:
            ids={int(x) for x in condtxt.split(',') if x} if condtxt else set()
            # Parts with no condition IDs are common parts and must remain
            # visible regardless of which conditional parts are active.
            if not ids or (ids & selected):
                out.append((part,desc,price,ann,condtxt))
        return out

    def image(self,name):
        key=name.upper().strip()
        if not key: return None
        if key in self.image_map: return self.image_map[key]
        # BLKTYTBL の10バイト名は、実ファイル名では先頭8文字の後に
        # ピリオドを補って格納されている場合がある。
        # 例: SS11E0100A -> SS11E010.0A
        if len(key) == 10:
            dotted = key[:8] + '.' + key[8:]
            if dotted in self.image_map: return self.image_map[dotted]
        # BLKTYTBL の9文字キーと、実ファイル側の拡張子相当の
        # 「.0B」「.2A」等が一致しないケースを許容する。
        # 例: SS11B311 -> SS11B311.0B
        pref=sorted((n for n in self.image_map if n.startswith(key+'.')), key=lambda n:(len(n),n))
        if pref: return self.image_map[pref[0]]
        m=re.match(r'^(.*?)(\d)$',key)
        if m:
            base,d=m.groups()
            for candidate in (f'{base}.{d}', f'{base}.{d}A', f'{base}.{d}B', f'{base}.{d}C', f'{base}.{d}D', f'{base}.{d}E', f'{base}.{d}F'):
                if candidate in self.image_map: return self.image_map[candidate]
        return None


class App(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("Honda EPC Viewer v78")
        self.geometry('1550x920'); self.minsize(1150,720)
        self.epc=None; self.photo=None; self.orig=None; self.current_conditions=[]; self.current_family_conditions=[]; self._groups=[]; self._blocks=[]; self._vehicle_entries=[]; self.current_dataset=None
        self._build(); self._discover_databases()

    def _build(self):
        # 上段：カタログと車種。内部データセット名はUIには出さない。
        top=ttk.Frame(self,padding=(8,8,8,4)); top.pack(fill='x')
        ttk.Label(top,text='カタログ').grid(row=0,column=0,sticky='w')
        self.dbvar=tk.StringVar(); self.cmb_db=ttk.Combobox(top,textvariable=self.dbvar,state='readonly',width=18); self.cmb_db.grid(row=0,column=1,padx=(4,18)); self.cmb_db.bind('<<ComboboxSelected>>',self._db_changed)
        ttk.Label(top,text='車名').grid(row=0,column=2,sticky='w')
        self.vehicle=tk.StringVar(); self.model=tk.StringVar(); self.cmb_vehicle=ttk.Combobox(top,textvariable=self.vehicle,state='readonly',width=20); self.cmb_vehicle.grid(row=0,column=3,padx=4); self.cmb_vehicle.bind('<<ComboboxSelected>>',self._vehicle_changed)
        self.status=tk.StringVar(value='')
        ttk.Button(top,text='逆引き検索',command=self._open_reverse_search).grid(row=0,column=4,padx=(18,4))

        # 車種→形式→号機→仕様。号機候補はKSRBHMHの実データから生成する。
        filt=ttk.LabelFrame(self,text='車両条件',padding=(8,6)); filt.pack(fill='x',padx=8,pady=(2,8))
        ttk.Label(filt,text='形式').grid(row=0,column=0,sticky='w')
        self.typ=tk.StringVar(value='－'); self.cmb_type=ttk.Combobox(filt,textvariable=self.typ,state='readonly',width=8); self.cmb_type.grid(row=0,column=1,padx=(4,18)); self.cmb_type.bind('<<ComboboxSelected>>',self._type_changed)
        ttk.Label(filt,text='フレームNo.').grid(row=0,column=2,sticky='w')
        self.serial=tk.StringVar(value='－'); self.cmb_serial=ttk.Combobox(filt,textvariable=self.serial,state='readonly',width=18); self.cmb_serial.grid(row=0,column=3,padx=(4,18)); self.cmb_serial.bind('<<ComboboxSelected>>',self._serial_changed)
        ttk.Label(filt,text='タイプ').grid(row=0,column=4,sticky='w')
        self.grade=tk.StringVar(value='－'); self.cmb_grade=ttk.Combobox(filt,textvariable=self.grade,state='readonly',width=34); self.cmb_grade.grid(row=0,column=5,padx=(4,8)); self.cmb_grade.bind('<<ComboboxSelected>>',self._grade_changed)
        ttk.Label(filt,text='オプション').grid(row=0,column=6,sticky='w')
        self.option=tk.StringVar(value='－'); self.cmb_option=ttk.Combobox(filt,textvariable=self.option,state='readonly',width=60); self.cmb_option.grid(row=0,column=7,padx=(4,4)); self.cmb_option.bind('<<ComboboxSelected>>',self._option_changed)
        self._option_tip_window=None; self._option_tip_text=None; self._option_hover_list=None
        self.cmb_option.bind('<Destroy>',self._hide_option_tip,add='+')
        self.after_idle(self._install_option_hover)

        pan=ttk.PanedWindow(self,orient='horizontal'); pan.pack(fill='both',expand=True,padx=8,pady=(0,8))
        left=ttk.Frame(pan,width=340); right=ttk.Frame(pan); pan.add(left,weight=0); pan.add(right,weight=1)
        ttk.Label(left,text='グループ').pack(anchor='w'); self.group=tk.StringVar(); self.cmb_group=ttk.Combobox(left,textvariable=self.group,state='readonly',width=42); self.cmb_group.pack(fill='x',pady=4); self.cmb_group.bind('<<ComboboxSelected>>',self._group_changed)
        ttk.Label(left,text='ブロック').pack(anchor='w',pady=(8,0)); self.block_list=tk.Listbox(left,exportselection=False,width=52,font=('TkFixedFont',),activestyle='none'); self.block_list.pack(fill='both',expand=True); self.block_list.bind('<<ListboxSelect>>',self._block_changed)

        # 図面と部品一覧を上下のPanedWindowにして、境界をドラッグして表示領域を変更可能にする。
        vertical=ttk.PanedWindow(right,orient='vertical'); vertical.pack(fill='both',expand=True)
        imgframe=ttk.LabelFrame(vertical,text='イラスト')
        partsframe=ttk.LabelFrame(vertical,text='部品一覧')
        vertical.add(imgframe,weight=3)
        vertical.add(partsframe,weight=1)
        self._vertical_pane=vertical

        imgframe.rowconfigure(0,weight=1); imgframe.columnconfigure(0,weight=1)
        self.canvas=tk.Canvas(imgframe,bg='white',highlightthickness=0)
        self.hscroll=ttk.Scrollbar(imgframe,orient='horizontal',command=self.canvas.xview)
        self.vscroll=ttk.Scrollbar(imgframe,orient='vertical',command=self.canvas.yview)
        self.canvas.configure(xscrollcommand=self.hscroll.set,yscrollcommand=self.vscroll.set)
        self.canvas.grid(row=0,column=0,sticky='nsew')
        # スクロールバーは常時配置してキャンバス寸法を固定し、
        # ホイール操作中の表示/非表示によるConfigure再帰を防ぐ。
        self.hscroll.grid(row=1,column=0,sticky='ew'); self.vscroll.grid(row=0,column=1,sticky='ns')
        self.canvas.bind('<Configure>',self._canvas_configure)
        self.canvas.bind('<Double-1>',self._image_double_click)
        self.canvas.bind('<MouseWheel>',self._mousewheel_zoom)
        self.canvas.bind('<Button-4>',lambda e:self._mousewheel_zoom(e,1))
        self.canvas.bind('<Button-5>',lambda e:self._mousewheel_zoom(e,-1))
        self.canvas.bind('<ButtonPress-1>',self._pan_start)
        self.canvas.bind('<B1-Motion>',self._pan_move)
        self.zoom_factor=1.0; self._fit_scale=1.0; self._pan_last=None
        self.annotation_boxes=[]
        self.selected_annotation=''
        self._tree_hit_items=[]
        # 部品一覧は等幅フォントにして、部品番号・価格の桁位置を確実にそろえる。
        tree_style=ttk.Style(self)
        tree_style.configure('EPC.Treeview',font='TkFixedFont')
        tree_style.configure('EPC.Treeview.Heading',font='TkFixedFont')
        cols=('ann','part','desc','price'); self.tree=ttk.Treeview(partsframe,columns=cols,show='headings',height=12,style='EPC.Treeview')
        self.tree.tag_configure('epc_hit',background='#fff59d',foreground='black')
        heads={'ann':'見出し','part':'部品番号','desc':'部品名','price':'希望小売価格'}
        widths={'ann':90,'part':162,'desc':420,'price':110}
        anchors={'ann':'center','part':'center','desc':'w','price':'w'}
        for c in cols:
            self.tree.heading(c,text=heads[c],anchor=anchors[c])
            # 固定幅の列はウインドウを横に広げても伸ばさない。
            # 余った幅は最後の「希望小売価格」列だけが受け取る。
            self.tree.column(c,width=widths[c],anchor=anchors[c],stretch=(c=='price'))
        ys=ttk.Scrollbar(partsframe,orient='vertical',command=self.tree.yview); self.tree.configure(yscrollcommand=ys.set); self.tree.pack(side='left',fill='both',expand=True); ys.pack(side='right',fill='y')
        self.tree.bind('<Double-1>',self._tree_double_click)
        # 部品番号・部品名のセルを右クリックすると、その文字列を指定して逆引き検索を開く。
        self.tree.bind('<Button-3>',self._tree_right_click)

    def _tree_right_click(self,event):
        iid=self.tree.identify_row(event.y)
        column=self.tree.identify_column(event.x)
        field={'#2':'part','#3':'desc'}.get(column)
        if not iid or field is None:
            return 'break'
        query=str(self.tree.set(iid,field) or '').strip()
        if not query:
            return 'break'
        self.tree.selection_set(iid)
        self.tree.focus(iid)
        menu=tk.Menu(self,tearoff=0)
        menu.add_command(label='逆引き検索',command=lambda q=query:self._open_reverse_search(q))
        try:
            menu.tk_popup(event.x_root,event.y_root)
        finally:
            menu.grab_release()
        return 'break'

    def _open_reverse_search(self,initial_query=None):
        win=getattr(self,'_reverse_window',None)
        if win is not None and win.winfo_exists():
            if initial_query is not None:
                win.set_query(initial_query)
            win.lift(); win.focus_force(); return
        self._reverse_window=ReverseSearchWindow(self,initial_query=initial_query)

    def apply_reverse_result(self, result):
        """逆引き検索で選択された車両条件・図面・部品をメイン画面へ反映する。"""
        db_name=result['dbdir'].name
        db_values=list(self.cmb_db['values'])
        if db_name not in db_values:
            messagebox.showerror('Honda EPC','検索結果のカタログがメイン画面にありません。')
            return
        self.cmb_db.current(db_values.index(db_name))
        self._db_changed()

        model=str(result.get('model') or '').strip()
        vehicle_values=list(self.cmb_vehicle['values'])
        if model not in vehicle_values:
            messagebox.showerror('Honda EPC',f'車名「{model}」をメイン画面で選択できません。')
            return
        self.cmb_vehicle.current(vehicle_values.index(model))
        self._vehicle_changed()

        typ=str(result.get('form') or '').strip()
        type_values=list(getattr(self,'_type_values',[]))
        if typ not in type_values:
            messagebox.showerror('Honda EPC',f'形式「{typ}」を選択できません。')
            return
        self.cmb_type.current(type_values.index(typ))
        self._type_changed()

        range_key=(str(result.get('frame_from') or '').strip(),
                   str(result.get('frame_to') or '').strip())
        ranges=list(getattr(self,'_serial_ranges',[]))
        if range_key not in ranges:
            messagebox.showerror('Honda EPC','検索結果のフレーム範囲を選択できません。')
            return
        self.cmb_serial.current(ranges.index(range_key))
        self._serial_changed()

        # 検索結果に含まれるKSRBの詳細項目から、メイン画面と同じ仕様ラベルを組み立てる。
        grade_base=self.epc._display_grade(result.get('grade'))
        detail=' / '.join(x for x in (str(result.get('doors') or '').strip(),
                                      str(result.get('transmission') or '').strip(),
                                      str(result.get('engine') or '').strip()) if x)
        grade_label=f'{grade_base} [ {detail} ]' if detail else grade_base
        grade_values=list(self.cmb_grade['values'])
        if grade_label not in grade_values:
            # 空白や表記揺れがあるCDに備え、表示名の基部でも照合する。
            matches=[i for i,value in enumerate(grade_values)
                     if str(value).split(' [',1)[0].strip()==grade_base]
            if not matches:
                messagebox.showerror('Honda EPC',f'タイプ「{grade_label}」を選択できません。')
                return
            grade_index=matches[0]
        else:
            grade_index=grade_values.index(grade_label)
        self.cmb_grade.current(grade_index)
        self._grade_changed()

        option_ident=str(result.get('option_ident') or '').strip()
        option_ids=list(getattr(self,'_option_choice_idents',[]))
        if option_ident in option_ids:
            self.cmb_option.current(option_ids.index(option_ident))
            self._option_changed()

        # グループ・ブロックを特定して、メイン画面の図面と部品一覧を表示する。
        # グループ名ではなくGRPTBL由来のコード＋種別で特定する。
        # 同名グループや表示名の空白差があっても誤選択しない。
        group_code=str(result.get('group_code') or '').strip()
        group_kind=str(result.get('group_kind') or '').strip()
        group_index=next((i for i,row in enumerate(self._groups)
                          if str(row[1] or '').strip()==group_code
                          and str(row[3] or '').strip()==group_kind),None)
        if group_index is None:
            messagebox.showerror('Honda EPC',
                f'グループを選択できません。（コード={group_code!r}, 種別={group_kind!r}）')
            return
        self.cmb_group.current(group_index)
        self._group_changed()

        image_name=str(result.get('image') or '').strip()
        block_index=next((i for i,row in enumerate(self._blocks)
                          if str(row[2] or '').strip().casefold()==image_name.casefold()),None)
        if block_index is None:
            messagebox.showerror('Honda EPC',f'図面「{image_name}」を選択できません。')
            return
        self.block_list.selection_clear(0,'end')
        self.block_list.selection_set(block_index)
        self.block_list.activate(block_index)
        self.block_list.see(block_index)
        self._block_changed()

        # 該当部品行も選択し、図面上の見出し番号を赤枠表示する。
        target_part=self._norm_part_for_handoff(result.get('part_number'))
        target_ann=str(result.get('annotation') or '').strip()
        for iid in self.tree.get_children():
            part=self._norm_part_for_handoff(self.tree.set(iid,'part'))
            ann=str(self.tree.set(iid,'ann') or '').strip()
            if part==target_part and (not target_ann or ann==target_ann):
                self.tree.selection_set(iid)
                self.tree.see(iid)
                if ann:
                    self._select_annotation(ann)
                break

        self.deiconify()
        self.lift()
        self.focus_force()
        self.status.set(f'逆引き検索結果を反映しました：{model} / {typ} / {image_name}')

    @staticmethod
    def _norm_part_for_handoff(value):
        return re.sub(r'[\s\-‐‑‒–—―]+','',str(value or '')).upper()

    def _dataset_candidates(self, dbdir):
        out=[]
        if not dbdir.exists(): return out
        direct=[p for p in dbdir.iterdir() if p.is_dir() and (p/'PLMST.CD').is_file()]
        if direct: return sorted(direct)
        if (dbdir/'PLMST.CD').is_file(): return [dbdir]
        # tolerate one extra folder level in a copied CD
        for p in dbdir.iterdir():
            if p.is_dir() and (p/'PLMST.CD').is_file(): out.append(p)
        return sorted(out)

    def _discover_databases(self):
        self.db_paths={}
        if DATA_DIR.exists():
            for dbdir in sorted([p for p in DATA_DIR.iterdir() if p.is_dir()]):
                ds=self._dataset_candidates(dbdir)
                # Compatibility: if a dataset only has the old v3 SQLite, expose it too.
                if not ds:
                    ds=sorted([p for p in dbdir.iterdir() if p.is_dir() and list(p.glob('*.sqlite'))])
                if ds: self.db_paths[dbdir.name]=ds
        self.cmb_db['values']=list(self.db_paths)
        if self.db_paths:
            self.cmb_db.current(0); self._db_changed()
        else:
            messagebox.showerror('Honda EPC','Data フォルダー内にHonda EPCデータが見つかりません。\n\nData\\カタログ\\車種データ\\PLMST.CD のように配置してください。')

    def _cache_path(self, dbdir, dataset):
        return CACHE_DIR / dbdir.name / (dataset.name + '.sqlite')

    def _prepare_cache(self, dbdir, dataset):
        legacy=list(dataset.glob('*.sqlite'))
        raw=(dataset/'PLMST.CD').is_file()
        if raw and build_cache and cache_is_current:
            cache=self._cache_path(dbdir,dataset)
            if not cache_is_current(cache,dbdir,dataset):
                self.status.set('初回解析：CDデータから検索用キャッシュを作成しています…'); self.update_idletasks()
                build_cache(dbdir,dataset,cache)
            return cache
        if legacy:
            return legacy[0]
        if not raw:
            raise FileNotFoundError('PLMST.CD が見つかりません。')
        if build_cache:
            cache=self._cache_path(dbdir,dataset)
            self.status.set('CDデータを解析しています…'); self.update_idletasks(); build_cache(dbdir,dataset,cache); return cache
        raise RuntimeError(f'CDデータ解析モジュールを読み込めません: {_CACHE_IMPORT_ERROR}')

    def _vehicle_candidates(self, dbdir):
        """このカタログに実際に存在するデータセットだけから車種を作る。

        KSRBHMH の +0x61..+0x68 はフォルダID（例: 11SA511）。
        実在するデータフォルダに対応するレコードだけを候補にする。共有TSMIR全体の車種は候補にしない。
        """
        datasets=self._dataset_candidates(dbdir)
        if not datasets:
            datasets=sorted([p for p in dbdir.iterdir() if p.is_dir() and list(p.glob('*.sqlite'))]) if dbdir.exists() else []
        raw_ksrb=None
        if dbdir.exists():
            p=dbdir/'KSRBHMH.CD'
            if p.is_file(): raw_ksrb=p
            else:
                hits=list(dbdir.rglob('KSRBHMH.CD'))
                if hits: raw_ksrb=hits[0]
        by_source={}
        if raw_ksrb:
            try:
                for r in parse_ksrb(raw_ksrb):
                    source=r[8].strip().upper()
                    if source:
                        by_source.setdefault(source,set()).add(r[3].strip())
            except Exception:
                by_source={}
        # 同じ車名が複数のフォルダ（データセット）に現れても、
        # プルダウンでは車名ごとに1項目へまとめる。フォルダ名は表示しない。
        by_model={}
        for ds in datasets:
            names=set(by_source.get(ds.name.strip().upper(),()))
            # 旧SQLiteしかない場合も、修正済みdbid/sourceで絞る。
            if not names:
                legacy=list(ds.glob('*.sqlite'))
                if legacy:
                    try:
                        con=sqlite3.connect(legacy[0])
                        names={r[0].strip() for r in con.execute('select distinct model from ksrb where upper(trim(dbid))=? order by model',(ds.name.strip().upper(),)) if r[0]}
                        con.close()
                    except Exception:
                        names=set()
            for name in (n for n in names if n):
                by_model.setdefault(name,[]).append(ds)
        # 現段階では車名を一項目に統合し、同一車名の先頭データセットを
        # 選択先として使う。フォルダ別の切替は仕様・フレーム選択の検証後に扱う。
        return [(name,name,sorted(dslist,key=lambda p:p.name.casefold()))
                for name,dslist in sorted(by_model.items(),key=lambda x:x[0].casefold())]

    def _db_changed(self,*_):
        name=self.dbvar.get(); dbdir=DATA_DIR / name
        self._vehicle_entries=self._vehicle_candidates(dbdir)
        self.cmb_vehicle['values']=[r[0] for r in self._vehicle_entries]
        if self._vehicle_entries:
            self.cmb_vehicle.current(0); self._vehicle_changed()
        else:
            self.vehicle.set(''); self.status.set('このカタログに利用可能な車種データがありません。')

    def _vehicle_changed(self,*_):
        idx=self.cmb_vehicle.current()
        if idx<0 or idx>=len(self._vehicle_entries): return
        _label,model,datasets=self._vehicle_entries[idx]
        dataset=datasets[0]
        dbdir=DATA_DIR / self.dbvar.get()
        try:
            if self.epc:self.epc.close()
            dbpath=self._prepare_cache(dbdir,dataset)
            self.epc=EPC(dbpath,dataset)
        except Exception as e:
            messagebox.showerror('Honda EPC','カタログの準備に失敗しました。\n\n'+str(e)); return
        self.current_dataset=dataset
        self.model.set(model)
        types=self.epc.type_choices(model)
        # Even when there is only one format, display the actual format name
        # stored in the source data.  Never manufacture a Version/grade label.
        if len(types)==1:
            self.typ.set(types[0]); self.cmb_type['values']=types; self._type_values=types; self.cmb_type.current(0)
        elif len(types)>1:
            self.cmb_type['values']=types; self._type_values=types; self.typ.set(types[0]); self.cmb_type.current(0)
        else:
            self.typ.set('－'); self.cmb_type['values']=['－']; self._type_values=[]
        # 車種切替直後も、初期選択された形式に対応するデータフォルダへ
        # 同期してからフレーム・仕様候補を作る。Comboboxの選択イベントは
        # set()/current()では発火しないため、ここで明示的に呼び出す。
        self._select_dataset_for_type()
        self._refresh_serials()
        self._select_dataset_for_type(self._selected_serial_range(), self._selected_grade_ident())
        self._refresh_serials(self.serial.get()); self._refresh_grades(); self.apply_filter()
        self._refresh_groups()
        self.status.set(f'車種 {model}：元CDデータを使用中（検索キャッシュはCacheに自動生成）')

    def _refresh_groups(self, preserve=None):
        """Show the AT/MT mission record selected by the current specification.

        GRPTBL.CD is parsed in source-record order.  Its second record is the
        AT mission and its third record is the MT mission; do not infer this
        from the translated group name.  Transmission is taken from the
        selected specification label (the bracketed detail shown in the UI).
        """
        if not self.epc:
            self._groups=[]; self.cmb_group['values']=[]; self.cmb_group.set(''); return

        import re, unicodedata
        detail=unicodedata.normalize('NFKC', str(self.grade.get() or '')).upper()
        # The displayed spec is e.g. "grade [ 2ドア / MT / E07A ]".
        # Use the same transmission value the user can see, not the first
        # KSRB row for the whole type (which may belong to another spec).
        match=re.search(r'\[([^\]]*)\]', detail)
        spec_detail=match.group(1) if match else detail
        tokens=[x.strip() for x in re.split(r'[/|、,\s]+', spec_detail) if x.strip()]
        trans=next((x for x in tokens if x in ('AT','MT')), '')

        all_groups=self.epc.groups()
        kept=[]
        for i,row in enumerate(all_groups):
            # Identify mission records by their actual GRPBRTBL labels. Some
            # CDs (e.g. BEAT) contain MT but no AT record, so index-only
            # filtering would incorrectly remove the MT entry.
            normalized=unicodedata.normalize('NFKC', str(row[2] or '')).upper()
            normalized=re.sub(r'\s+', '', normalized)
            is_at=('ミッション' in normalized and 'AT' in normalized)
            is_mt=('ミッション' in normalized and 'MT' in normalized)
            if trans=='AT' and is_mt:
                continue
            if trans=='MT' and is_at:
                continue
            # Positional fallback only for unlabeled records when both slots exist.
            if not (is_at or is_mt) and len(all_groups)>=3:
                if trans=='MT' and i==1: continue
                if trans=='AT' and i==2: continue
            kept.append(row)
        self._groups=kept
        labels=[str(r[2]).strip() for r in kept]
        self.cmb_group['values']=labels
        if preserve in labels:
            self.cmb_group.current(labels.index(preserve))
        elif labels:
            self.cmb_group.current(0)
        else:
            self.cmb_group.set('')

    def _selected_type(self):
        i=self.cmb_type.current(); vals=getattr(self,'_type_values',[])
        return vals[i] if 0 <= i < len(vals) else (self.typ.get().split(' [',1)[0].strip())
    def _refresh_serials(self, preserve=None):
        if not self.epc or not self.model.get(): return
        ranges=self.epc.serial_ranges(self.model.get(), self._selected_type())
        labels=[self.epc.range_label(x) for x in ranges]
        self._serial_ranges=ranges
        self.cmb_serial['values']=labels
        if preserve in labels:
            self.serial.set(preserve)
        elif labels:
            self.cmb_serial.current(0)
        else:
            self.serial.set('－')
    def _refresh_grades(self, preserve=None):
        if not self.epc or not self.model.get(): return
        pair=self._selected_serial_range()
        choices=self.epc.grade_choices(self.model.get(),self._selected_type(),pair)
        labels=choices if choices else ['－']
        self.cmb_grade['values']=labels
        if preserve in labels: self.grade.set(preserve)
        elif choices: self.cmb_grade.current(0)
        else: self.grade.set('－')
        self._refresh_options()
    def _refresh_options(self, preserve=None):
        if not self.epc or not self.model.get() or self.grade.get()=='－':
            self.cmb_option['values']=['－']; self.option.set('－'); self._option_choice_idents=[]; return
        choices=self.epc.option_choices(self.model.get(),self._selected_type(),self.grade.get(),self._selected_serial_range())
        self._option_choice_idents=[ident for _label,ident in choices]
        labels=[label for label,_ident in choices] or ['－']
        self.cmb_option['values']=labels
        if preserve in labels: self.option.set(preserve)
        elif choices: self.cmb_option.current(0)
        else: self.option.set('－')

    def _install_option_hover(self):
        """Attach a tooltip to individual rows in the ttk Combobox popdown.

        Tk does not expose popdown rows as Python widgets, so use the standard
        ttk popdown listbox path and forward its mouse-motion event.
        """
        try:
            cb=str(self.cmb_option)
            pop=self.tk.call('ttk::combobox::PopdownWindow', cb)
            lb=str(pop)+'.f.l'
            if not self.tk.call('winfo','exists',lb):
                return
            self._option_hover_list=lb
            script=f'event generate {cb} <<OptionListMotion>> -y %y'
            self.tk.call('bind',lb,'<Motion>',script)
            self.cmb_option.bind('<<OptionListMotion>>',self._option_list_motion,add='+')
            self.tk.call('bind',lb,'<Leave>',f'event generate {cb} <<OptionListLeave>>')
            self.cmb_option.bind('<<OptionListLeave>>',self._hide_option_tip,add='+')
        except Exception:
            # The normal combobox remains fully usable on Tk builds whose
            # popdown implementation differs; only the optional tooltip is lost.
            self._option_hover_list=None

    def _option_list_motion(self,event):
        try:
            idx=int(self.tk.call(self._option_hover_list,'nearest',event.y))
            values=list(self.cmb_option['values'])
            if idx<0 or idx>=len(values):
                self._hide_option_tip(); return
            full=str(values[idx])
            # Compare rendered text width with the actual popdown list width;
            # Japanese characters can occupy more pixels than their character count suggests.
            font_name=self.tk.call(self._option_hover_list,'cget','-font')
            text_width=int(self.tk.call('font','measure',font_name,full))
            list_width=int(self.tk.call('winfo','width',self._option_hover_list))
            if text_width <= max(1,list_width-12):
                self._hide_option_tip(); return
            if self._option_tip_text==full and self._option_tip_window:
                return
            self._hide_option_tip()
            tip=tk.Toplevel(self)
            tip.wm_overrideredirect(True)
            label=ttk.Label(tip,text=full,relief='solid',padding=(6,3))
            label.pack()
            # Keep the tooltip above the native ttk popdown (which is a
            # separate toplevel on Windows) so the text is not obscured.
            tip.wm_attributes('-topmost', True)
            tip.update_idletasks()
            x=self.winfo_pointerx()+14; y=self.winfo_pointery()+18
            tip.wm_geometry(f'+{x}+{y}')
            tip.lift()
            self._option_tip_window=tip; self._option_tip_text=full
        except Exception:
            self._hide_option_tip()

    def _hide_option_tip(self,*_):
        tip=getattr(self,'_option_tip_window',None)
        if tip is not None:
            try: tip.destroy()
            except Exception: pass
        self._option_tip_window=None; self._option_tip_text=None

    def _selected_option_ident(self):
        i=self.cmb_option.current(); ids=getattr(self,'_option_choice_idents',[])
        return ids[i] if 0 <= i < len(ids) else None

    def _selected_serial_range(self):
        label=self.serial.get()
        for pair in getattr(self,'_serial_ranges',[]):
            if self.epc.range_label(pair)==label:
                return pair
        return None

    def _type_changed(self,*_):
        # A vehicle can have different format records on different data folders.
        # Select the folder referenced by the KSRBHMH records for this format,
        # rather than keeping the alphabetically first folder for the vehicle.
        self._select_dataset_for_type()
        old_serial=self.serial.get(); old_grade=self.grade.get()
        self._refresh_serials(old_serial)
        self._select_dataset_for_type(self._selected_serial_range(), self._selected_grade_ident())
        self._refresh_serials(self.serial.get())
        self._refresh_grades(old_grade)
        self.apply_filter()
        self._refresh_groups()

    def _select_dataset_for_type(self, range_key=None, grade_ident=None):
        """Resolve the CD folder from the currently selected KSRB variant.

        Current discs do not appear to split folders by specification, but
        retain the condition/variant match so future KSRB data can do so.
        """
        if not self.epc or not self.model.get() or not self._selected_type():
            return
        idx=self.cmb_vehicle.current()
        if idx<0 or idx>=len(self._vehicle_entries): return
        _label,model,datasets=self._vehicle_entries[idx]
        rows=self.epc._ksrb_rows(model,self._selected_type())
        if range_key:
            rows=[r for r in rows if (str(r[5] or '').strip(),str(r[6] or '').strip())==tuple(range_key)]
        if grade_ident:
            matched=[r for r in rows if str(r[2] or '').strip()==str(grade_ident).strip()]
            if matched:
                rows=matched
        folder_ids=[]
        for row in rows:
            folder=str(row[8] or '').strip().upper()
            if folder and folder not in folder_ids:
                folder_ids.append(folder)
        # Match the selected frame/specification's KSRB folder id to a real directory.
        by_name={p.name.strip().upper():p for p in datasets}
        target=next((by_name[x] for x in folder_ids if x in by_name),None)
        if target is None or target==self.current_dataset:
            return
        dbdir=DATA_DIR / self.dbvar.get()
        try:
            new_path=self._prepare_cache(dbdir,target)
            new_epc=EPC(new_path,target)
        except Exception as e:
            messagebox.showerror('Honda EPC','形式に対応するフォルダの読み込みに失敗しました。\n\n'+str(e)); return
        if self.epc: self.epc.close()
        self.epc=new_epc
        self.current_dataset=target
        self._refresh_groups()


    def _serial_changed(self,*_):
        old_grade=self.grade.get()
        self._select_dataset_for_type(self._selected_serial_range(), self._selected_grade_ident())
        self._refresh_serials(self.serial.get())
        self._refresh_grades(old_grade)
        self.apply_filter()

    def _frame_changed(self,*_):
        self._serial_changed()

    def _selected_grade_ident(self):
        return self._selected_option_ident()

    def _grade_changed(self,*_):
        self._refresh_options()
        self._refresh_groups()
        self._option_changed()

    def _option_changed(self,*_):
        self._select_dataset_for_type(self._selected_serial_range(), self._selected_option_ident())
        self.apply_filter()

    def apply_filter(self):
        if not self.epc or not self.model.get(): return
        frame=''
        pair=self._selected_serial_range()
        grade=self.grade.get() if self.grade.get()!='－' else 'すべて'
        grade_ident=self._selected_option_ident()
        self.current_conditions=self.epc.selected_condition_ids(self.model.get(),self._selected_type(),grade,frame,pair,grade_ident)
        self.current_family_conditions=[]
        if self.current_conditions is None:
            self.status.set('選択条件に対応するKSRBデータがありません（部品条件は適用しません）')
        elif not self.current_conditions:
            self.status.set('共通部品のみ表示（選択範囲に適用条件がありません）')
        else:
            self.status.set('選択した仕様の適用条件で部品を表示中')
        if self.cmb_group.current()>=0: self._group_changed()

    def _group_changed(self,*_):
        idx=self.cmb_group.current(); self.block_list.delete(0,'end')
        if idx<0 or not self.epc:return
        # ブロック一覧は条件IDで削らず、図面として存在するものを表示する。
        # 部品側で条件IDを適用することで、隠し条件/オプション違いの図面も確認できる。
        g=self._groups[idx]; self._blocks=self.epc.blocks(g[0],self.current_conditions,self.model.get(),self.grade.get())
        for r in self._blocks:self.block_list.insert('end',f'{format_block_number(r[1]):<10} {r[3]}')
        if self._blocks:self.block_list.selection_set(0); self._block_changed()
        else:
            self.canvas.delete('all'); self.canvas.create_text(100,50,text='選択条件に該当するブロックがありません',fill='black',anchor='nw')
            for x in self.tree.get_children():self.tree.delete(x)

    def _block_changed(self,*_):
        sel=self.block_list.curselection()
        if not sel:return
        bid=self._blocks[sel[0]][0]; rows=self.epc.parts(bid,self.current_conditions,self.current_family_conditions,self.model.get(),self.grade.get())
        for x in self.tree.get_children():self.tree.delete(x)
        self._tree_hit_items=[]
        for part,desc,price,ann,conds in rows:
            part_display=format_part_number(part)
            # 部品番号は表示長を15文字にそろえてから列の中央へ配置する。
            # これにより桁数の異なる部品番号でも先頭位置がそろう。
            part_field=part_display.ljust(15)
            # 価格は左寄せのまま、上位桁を空白で埋めて下位桁をそろえる。
            price_display=(format_price(price) or '')[:9].rjust(9)
            iid=self.tree.insert('','end',values=(ann or '',part_field,desc,price_display))
            self._tree_hit_items.append((iid,str(ann or '').strip()))
        self.selected_annotation=''
        self._show_image(self._blocks[sel[0]][2])

    def _show_image(self,name):
        path=self.epc.image(name)
        if not path:
            self.orig=None; self.canvas.delete('all'); self.canvas.create_text(20,20,text=f'画像 {name} が見つかりません',fill='black',anchor='nw'); return
        try:
            png=IMAGE_CACHE/(self.dbvar.get()+'_'+(self.current_dataset.name if self.current_dataset else 'dataset')+'_'+path.name+'.png')
            if not png.exists() or png.stat().st_mtime < path.stat().st_mtime:self._convert(path,png)
            self.orig=Image.open(png).convert('RGB')
            self.zoom_factor=1.0
            self.annotation_boxes=self._parse_image_annotations(path)
            self.selected_annotation=''
            self._redraw()
        except Exception as e:
            self.orig=None; self.canvas.delete('all'); self.canvas.create_text(20,20,text=str(e),fill='black',anchor='nw')

    def _convert(self,path,png):
        b=path.read_bytes()
        if len(b)<21: raise ValueError('Honda image header too short')
        w=int.from_bytes(b[11:13],'big'); h=int.from_bytes(b[13:15],'big'); comp=b[21:]
        entries=[(256,4,1,w),(257,4,1,h),(258,3,1,1),(259,3,1,4),(262,3,1,1),(273,4,1,0),(278,4,1,h),(279,4,1,len(comp)),(277,3,1,1),(266,3,1,1)]
        entries.sort(key=lambda x:x[0]); strip=8+2+12*len(entries)+4; entries=[(t,y,c,(strip if t==273 else v)) for t,y,c,v in entries]
        raw=bytearray(b'II*\x00'+struct.pack('<I',8)+struct.pack('<H',len(entries)))
        for t,y,c,v in entries:
            raw+=struct.pack('<HHI',t,y,c)
            if y==3 and c==1: raw+=struct.pack('<H',v)+b'\0\0'
            else: raw+=struct.pack('<I',v)
        raw+=struct.pack('<I',0)+comp
        with tempfile.NamedTemporaryFile(suffix='.tif',delete=False) as f:f.write(raw); tmp=f.name
        try:
            im=Image.open(tmp).convert('L'); im=ImageOps.invert(im); im.save(png,'PNG')
        finally:
            try: os.unlink(tmp)
            except OSError: pass

    def _parse_image_annotations(self,path):
        """Read Honda image annotation records as (図番, x1,y1,x2,y2).

        The annotation section begins after the 21-byte image header and the
        compressed-image payload.  The section itself starts with a 3-byte
        big-endian length.

        A normal annotation record is 11 bytes and is laid out as:
            +0x00..+0x07  X1,Y1,X2,Y2 (four big-endian uint16 values)
            +0x08..+0x0A  3-byte ASCII figure number

        Some images have a leading 0x43 byte before the first bbox.  In that
        form the record is 12 bytes:
            +0x00        0x43 (record attribute/type byte)
            +0x01..+0x08 X1,Y1,X2,Y2
            +0x09..+0x0B 3-byte ASCII figure number

        The figure number is therefore always taken from the LAST three bytes
        of the bbox record.  No +1/sequence correction is applied.  This is
        important because the same displayed figure number can occur more than
        once in one drawing (e.g. two separate figure-46 callouts).
        """
        try:
            b=path.read_bytes()
            if len(b)<21:
                return []
            comp_len=int.from_bytes(b[17:19],'big')
            ann_off=21+comp_len
            if ann_off+3>len(b):
                return []
            sec_len=int.from_bytes(b[ann_off:ann_off+3],'big')
            start=ann_off+3
            # Section length includes the 3-byte length field itself.
            end=min(len(b),ann_off+sec_len)

            out=[]
            pos=start
            while pos<end:
                # 0x43 is an attribute/type byte belonging to the record;
                # it is NOT the figure number.  Its record has one extra byte.
                if b[pos] == 0x43:
                    rec_len=12
                    if pos+rec_len>end:
                        break
                    coord_off=pos+1
                else:
                    rec_len=11
                    if pos+rec_len>end:
                        break
                    coord_off=pos

                x1=int.from_bytes(b[coord_off:coord_off+2],'big')
                y1=int.from_bytes(b[coord_off+2:coord_off+4],'big')
                x2=int.from_bytes(b[coord_off+4:coord_off+6],'big')
                y2=int.from_bytes(b[coord_off+6:coord_off+8],'big')
                raw=b[pos+rec_len-3:pos+rec_len]
                try:
                    raw_ann=raw.decode('ascii').strip()
                except UnicodeDecodeError:
                    raw_ann=''
                if raw_ann and re.fullmatch(r'\d{1,3}',raw_ann):
                    out.append((raw_ann,x1,y1,x2,y2))
                pos += rec_len
            return out
        except Exception:
            return []

    def _clear_tree_hit(self):
        for iid,_ann in self._tree_hit_items:
            self.tree.item(iid,tags=())

    def _select_annotation(self,ann):
        """Select/toggle one figure number across both drawing and parts list."""
        ann=str(ann).strip()
        if not ann:
            return
        # Double-clicking the already highlighted number toggles it off.
        if self.selected_annotation==ann:
            self.selected_annotation=''
            self._clear_tree_hit()
            self.tree.selection_remove(self.tree.selection())
            self._redraw()
            return

        # Selecting another number replaces the previous highlight.
        self.selected_annotation=ann
        self._clear_tree_hit()
        hits=[]
        for iid,row_ann in self._tree_hit_items:
            if row_ann==ann:
                self.tree.item(iid,tags=('epc_hit',))
                hits.append(iid)
        if hits:
            self.tree.selection_set(hits[0])
            self.tree.see(hits[0])
        else:
            self.tree.selection_remove(self.tree.selection())
        self._redraw()

    def _tree_double_click(self,event):
        """Double-click a parts-list row to highlight its figure number on the drawing."""
        iid=self.tree.identify_row(event.y)
        if not iid:
            return
        ann=str(self.tree.set(iid,'ann') or '').strip()
        if ann:
            self._select_annotation(ann)

    def _canvas_configure(self,event):
        # 枠サイズ変更時は、現在の倍率を維持しつつ基準フィット倍率を更新する。
        self._redraw()

    def _mousewheel_zoom(self,event,direction=None):
        if self.orig is None: return 'break'
        if direction is None:
            direction = 1 if event.delta > 0 else -1
        factor = 1.15 if direction > 0 else (1/1.15)
        new_zoom=max(1.0,min(3.0,self.zoom_factor*factor))
        if abs(new_zoom-self.zoom_factor)<1e-9: return 'break'
        # ポインタ直下の画像上の点が、拡大縮小後も同じ画面位置に残るようにする。
        sx,sy=event.x,event.y
        cx,cy=self.canvas.canvasx(sx),self.canvas.canvasy(sy)
        old_scale=self._fit_scale*self.zoom_factor
        old_left,old_top=self._image_origin
        ix=(cx-old_left)/old_scale; iy=(cy-old_top)/old_scale
        self.zoom_factor=new_zoom
        self._redraw(anchor=(sx,sy,ix,iy))
        return 'break'

    def _pan_start(self,event):
        if self.orig is not None and self.zoom_factor>1.0001:
            self.canvas.scan_mark(event.x,event.y); self._pan_last=(event.x,event.y)

    def _pan_move(self,event):
        if self._pan_last is not None:
            self.canvas.scan_dragto(event.x,event.y,gain=1)

    def _image_double_click(self,event):
        if self.orig is None or not self.annotation_boxes:
            return
        scale=self._fit_scale*self.zoom_factor
        left,top=self._image_origin
        iw,ih=self.orig.size
        ox=(self.canvas.canvasx(event.x)-left)/scale; oy=(self.canvas.canvasy(event.y)-top)/scale
        if ox<0 or oy<0 or ox>iw or oy>ih:
            return
        # Prefer the smallest bbox containing the click if records overlap.
        hits=[]
        for box in self.annotation_boxes:
            ann,x1,y1,x2,y2=box
            if x1<=ox<=x2 and y1<=oy<=y2:
                hits.append((max(1,(x2-x1)*(y2-y1)),ann))
        if hits:
            hits.sort(key=lambda x:x[0])
            self._select_annotation(hits[0][1])

    def _redraw(self,anchor=None):
        if self.orig is None:return
        w=max(100,self.canvas.winfo_width()); h=max(100,self.canvas.winfo_height())
        iw,ih=self.orig.size
        self._fit_scale=min((w-10)/iw,(h-10)/ih)
        if self._fit_scale<=0:return
        scale=self._fit_scale*self.zoom_factor
        dw,dh=iw*scale,ih*scale
        # 拡大時は左上を原点にし、縮小（フィット）時は枠内中央に配置する。
        left=max(0,(w-dw)/2); top=max(0,(h-dh)/2)
        self._image_origin=(left,top)
        im=self.orig.resize((max(1,round(dw)),max(1,round(dh))),Image.Resampling.LANCZOS)
        self.photo=ImageTk.PhotoImage(im)
        self.canvas.delete('all')
        self.canvas.create_image(left,top,image=self.photo,anchor='nw')
        if self.selected_annotation:
            for ann,x1,y1,x2,y2 in self.annotation_boxes:
                if ann!=self.selected_annotation: continue
                sx1=left+x1*scale; sy1=top+y1*scale
                sx2=left+x2*scale; sy2=top+y2*scale
                self.canvas.create_rectangle(sx1,sy1,sx2,sy2,outline='red',width=3,fill='yellow',stipple='gray25')
        total_w=max(w,round(left+dw)); total_h=max(h,round(top+dh))
        self.canvas.configure(scrollregion=(0,0,total_w,total_h))
        # バーの表示切替は行わない。表示領域の変化に伴う
        # Configure→再描画→バー切替の振動を避ける。
        if anchor is not None:
            sx,sy,ix,iy=anchor
            target_x=max(0,left+ix*scale-sx); target_y=max(0,top+iy*scale-sy)
            self.update_idletasks()
            sw=max(1,self.canvas.winfo_width(),total_w); sh=max(1,self.canvas.winfo_height(),total_h)
            self.canvas.xview_moveto(min(1,target_x/max(1,total_w)))
            self.canvas.yview_moveto(min(1,target_y/max(1,total_h)))
        elif self.zoom_factor<=1.0001:
            self.canvas.xview_moveto(0); self.canvas.yview_moveto(0)


class ReverseSearchWindow(tk.Toplevel):
    """PLMST横断検索。検索結果を選ぶと対応図面と見出し枠を表示する。"""
    def __init__(self, app, initial_query=None):
        super().__init__(app)
        self.app=app
        self.title('Honda EPC Viewer - 逆引き検索')
        self.geometry('1420x900')
        self.minsize(980,650)
        self.protocol('WM_DELETE_WINDOW',self._close)

        self._epcs={}
        self._results=[]
        self._image=None
        self._photo=None
        self._boxes=[]
        self._selected_ann=''
        self._orig_size=(0,0)
        self._img_origin=(0,0)
        self._scale=1.0

        top=ttk.Frame(self,padding=8)
        top.pack(fill='x')
        ttk.Label(top,text='部品番号／部品名').pack(side='left')
        self.query=tk.StringVar(value=str(initial_query or ''))
        self.entry=ttk.Entry(top,textvariable=self.query,width=48)
        self.entry.pack(side='left',padx=(8,6))
        self.entry.bind('<Return>',lambda e:self.search())
        self.search_button=ttk.Button(top,text='検索',command=self.search)
        self.search_button.pack(side='left')
        self._searching=False
        self._search_queue=queue.Queue()
        self._cancel_event=None
        self._progress_window=None
        self._progress_text=None
        self._cancel_button=None
        self.status=tk.StringVar(value='部品番号または部品名を入力してください。')
        ttk.Label(self,textvariable=self.status,anchor='w',padding=(9,2)).pack(fill='x')

        split=ttk.PanedWindow(self,orient='vertical')
        split.pack(fill='both',expand=True,padx=8,pady=(2,8))
        table_frame=ttk.Frame(split)
        image_frame=ttk.LabelFrame(split,text='該当図面')
        split.add(table_frame,weight=2)
        split.add(image_frame,weight=3)
        self._split=split

        cols=('unique_id','model','form','frame','grade','group','block')
        self.table=ttk.Treeview(table_frame,columns=cols,show='headings',selectmode='browse')
        heads={'unique_id':'Unique ID','model':'車名','form':'形式','frame':'フレームナンバー','grade':'タイプ','group':'グループ名','block':'ブロック名'}
        widths={'unique_id':150,'model':150,'form':130,'frame':170,'grade':190,'group':220,'block':330}
        for c in cols:
            self.table.heading(c,text=heads[c])
            self.table.column(c,width=widths[c],minwidth=70,anchor='w',stretch=(c in ('group','block')))
        y=ttk.Scrollbar(table_frame,orient='vertical',command=self.table.yview)
        x=ttk.Scrollbar(table_frame,orient='horizontal',command=self.table.xview)
        self.table.configure(yscrollcommand=y.set,xscrollcommand=x.set)
        self.table.grid(row=0,column=0,sticky='nsew')
        y.grid(row=0,column=1,sticky='ns')
        x.grid(row=1,column=0,sticky='ew')
        table_frame.rowconfigure(0,weight=1); table_frame.columnconfigure(0,weight=1)
        self.table.bind('<<TreeviewSelect>>',self._result_selected)
        self.table.bind('<Double-1>',self._apply_selected_to_main)
        self.table.bind('<Return>',self._apply_selected_to_main)

        image_frame.rowconfigure(0,weight=1); image_frame.columnconfigure(0,weight=1)
        self.canvas=tk.Canvas(image_frame,bg='white',highlightthickness=0)
        self.canvas.grid(row=0,column=0,sticky='nsew')
        sy=ttk.Scrollbar(image_frame,orient='vertical',command=self.canvas.yview)
        sx=ttk.Scrollbar(image_frame,orient='horizontal',command=self.canvas.xview)
        self.canvas.configure(yscrollcommand=sy.set,xscrollcommand=sx.set)
        sy.grid(row=0,column=1,sticky='ns'); sx.grid(row=1,column=0,sticky='ew')
        self.canvas.bind('<Configure>',self._redraw)
        self.canvas.bind('<MouseWheel>',self._zoom)
        self.canvas.bind('<Button-4>',lambda e:self._zoom(e,1))
        self.canvas.bind('<Button-5>',lambda e:self._zoom(e,-1))
        self.entry.focus_set()
        if initial_query:
            self.entry.selection_range(0,'end')

    def set_query(self,value):
        """メイン画面から渡された部品番号／部品名を検索窓へ設定する。"""
        self.query.set(str(value or ''))
        self.entry.focus_set()
        self.entry.selection_range(0,'end')

    @staticmethod
    def _norm_part(value):
        return re.sub(r'[\s\-‐‑‒–—―]+','',str(value or '')).upper()

    @staticmethod
    def _norm_text(value):
        return re.sub(r'\s+','',str(value or '')).casefold()

    def _all_datasets(self, dbdir):
        """現在選択中のカタログに属するデータセットだけを返す。"""
        found=[]
        if not dbdir.exists():
            return found
        for ds in self.app._dataset_candidates(dbdir):
            if (ds/'PLMST.CD').is_file() or list(ds.glob('*.sqlite')):
                found.append((dbdir,ds))
        return found

    def search(self):
        if self._searching:
            return
        term=self.query.get().strip()
        if not term:
            self.status.set('検索語を入力してください。')
            self.entry.focus_set()
            return

        # 検索対象は、メイン画面で現在選択されているDBに限定する。
        db_name=self.app.dbvar.get().strip()
        dbdir=DATA_DIR/db_name
        datasets=self._all_datasets(dbdir)
        if not datasets:
            self.status.set(f'カタログ「{db_name}」内に検索可能なPLMST.CDが見つかりません。')
            return

        for iid in self.table.get_children():
            self.table.delete(iid)
        self._results=[]
        self._clear_image()
        self._searching=True
        self.search_button.configure(state='disabled')
        self._cancel_event=threading.Event()
        self._search_queue=queue.Queue()

        # 検索状況と中断操作は独立したダイアログに表示する。
        dlg=tk.Toplevel(self)
        self._progress_window=dlg
        dlg.title('逆引き検索')
        dlg.transient(self)
        dlg.resizable(False,False)
        dlg.protocol('WM_DELETE_WINDOW',self._cancel_search)
        body=ttk.Frame(dlg,padding=14)
        body.pack(fill='both',expand=True)
        self._progress_text=tk.StringVar(value='検索を準備しています…')
        ttk.Label(body,textvariable=self._progress_text,width=62,anchor='w').pack(fill='x',pady=(0,8))
        self._progress_bar=ttk.Progressbar(body,mode='determinate',maximum=len(datasets),length=420)
        self._progress_bar.pack(fill='x',pady=(0,10))
        self._cancel_button=ttk.Button(body,text='検索を中断',command=self._cancel_search)
        self._cancel_button.pack(anchor='e')
        dlg.update_idletasks()
        dlg.geometry(f'+{self.winfo_rootx()+max(20,(self.winfo_width()-dlg.winfo_width())//2)}+{self.winfo_rooty()+max(20,(self.winfo_height()-dlg.winfo_height())//2)}')
        dlg.grab_set()

        norm_part=self._norm_part(term)
        norm_text=self._norm_text(term)
        cancel_event=self._cancel_event
        result_queue=self._search_queue

        def worker():
            results=[]; errors=[]
            total=len(datasets)
            for index,(target_db,ds) in enumerate(datasets,1):
                if cancel_event.is_set():
                    break
                result_queue.put(('progress',index-1,total,f'{index}/{total}  {target_db.name} / {ds.name}'))
                con=None
                try:
                    cache=self.app._cache_path(target_db,ds)
                    if (ds/'PLMST.CD').is_file():
                        if not cache_is_current(cache,target_db,ds):
                            if not build_cache:
                                raise RuntimeError('CDデータ解析モジュールを読み込めません')
                            build_cache(target_db,ds,cache)
                    else:
                        legacy=list(ds.glob('*.sqlite'))
                        if legacy:
                            cache=legacy[0]
                        else:
                            raise FileNotFoundError('PLMST.CD / SQLiteが見つかりません')
                    if cancel_event.is_set():
                        break
                    con=sqlite3.connect(cache)
                    con.row_factory=None
                    part_rows=con.execute("""select p.id,p.part_number,p.description,p.annotation,p.block_id,
                                                    b.image,b.description,b.group_code,b.kind
                                             from parts p
                                             join blocks b on b.id=p.block_id
                                             order by p.id""").fetchall()
                    hits=[]
                    for row in part_rows:
                        if cancel_event.is_set():
                            break
                        pnum,pname=row[1],row[2]
                        number_hit=bool(norm_part and norm_part in self._norm_part(pnum))
                        name_hit=bool(norm_text and norm_text in self._norm_text(pname))
                        if number_hit or name_hit:
                            hits.append(row)
                    if cancel_event.is_set():
                        break
                    if hits:
                        ksrb_rows=con.execute("""select model,type,frame_from,frame_to,grade,dbid,
                                                        condition_ids,ident,form_id,doors,transmission,engine
                                                 from ksrb where upper(trim(dbid))=? order by offset""",
                                              (ds.name.strip().upper(),)).fetchall()
                        for part in hits:
                            if cancel_event.is_set():
                                break
                            pid,partno,partname,ann,bid,image,block_name,group_code,group_kind=part
                            part_conds={int(r[0]) for r in con.execute(
                                'select condition_id from part_conditions where part_id=?',(pid,)).fetchall()}
                            block_conds={int(r[0]) for r in con.execute(
                                'select condition_id from block_conditions where block_id=?',(bid,)).fetchall()}
                            for vehicle in ksrb_rows:
                                if cancel_event.is_set():
                                    break
                                model,form,lo,hi,grade,dbid,cond_json,ident,form_id,doors,transmission,engine=vehicle
                                try:
                                    selected={int(x) for x in json.loads(cond_json or '[]')[:2]
                                              if x is not None and int(x)>0}
                                except Exception:
                                    selected=set()
                                if part_conds and not (part_conds & selected):
                                    continue
                                if block_conds and not (block_conds & selected):
                                    continue
                                frame=(str(lo or '').strip()+' ～ '+str(hi or '').strip()).strip(' ～') or '－'
                                grade_label=self._display_grade(grade) or '－'
                                unique_id=re.sub(r'\s+','',str(form_id or '')+str(ident or ''))
                                group_row=con.execute(
                                    'select name from groups where trim(code)=trim(?) and trim(kind)=trim(?) order by rowid limit 1',
                                    (group_code,group_kind)).fetchone()
                                group_name=group_row[0] if group_row else ''
                                display=(unique_id,str(model or '').strip(),str(form or '').strip(),frame,grade_label,
                                         str(group_name or '').strip(),str(block_name or '').strip())
                                results.append({
                                    'display':display,'dbdir':target_db,'dataset':ds,'cache':cache,
                                    'image':image,'annotation':str(ann or '').strip(),
                                    'part_number':partno,'part_name':partname,'block_id':bid,
                                    'part_id':pid,'ident':ident,'unique_id':unique_id,
                                    'group_code':group_code,'group_kind':group_kind,
                                    'model':model,'form':form,'frame_from':lo,'frame_to':hi,
                                    'grade':grade,'doors':doors,'transmission':transmission,'engine':engine,
                                    'option_ident':ident
                                })
                except Exception as exc:
                    errors.append(f'{target_db.name}/{ds.name}: {exc}')
                finally:
                    if con is not None:
                        try: con.close()
                        except Exception: pass
                result_queue.put(('progress',index,total,f'{index}/{total}  {target_db.name} / {ds.name}'))
            result_queue.put(('done',results,errors,cancel_event.is_set()))

        threading.Thread(target=worker,daemon=True).start()
        self.after(100,self._poll_search)

    @staticmethod
    def _display_grade(raw):
        value=str(raw or '').strip()
        if re.match(r'^\d{2}[^0-9]',value):
            return value[2:].strip()
        return value

    def _cancel_search(self):
        if not self._searching or self._cancel_event is None:
            return
        self._cancel_event.set()
        if self._progress_text:
            self._progress_text.set('中断しています…（処理中のデータセットが終わるまでお待ちください）')
        if self._cancel_button:
            self._cancel_button.configure(state='disabled')

    def _poll_search(self):
        if not self._searching:
            return
        finished=False
        while True:
            try:
                item=self._search_queue.get_nowait()
            except queue.Empty:
                break
            if item[0]=='progress':
                _kind,done,total,label=item
                if self._progress_window is not None and self._progress_window.winfo_exists():
                    self._progress_bar.configure(maximum=max(1,total),value=done)
                    self._progress_text.set(f'検索中… {label}')
            elif item[0]=='done':
                _kind,results,errors,cancelled=item
                self._finish_search(results,errors,cancelled)
                finished=True
        if not finished and self._searching:
            self.after(100,self._poll_search)

    def _finish_search(self,results,errors,cancelled):
        self._searching=False
        self.search_button.configure(state='normal')
        if self._progress_window is not None:
            try:
                self._progress_window.grab_release()
                self._progress_window.destroy()
            except Exception:
                pass
        self._progress_window=None

        # 同じ部品/ブロック/車両条件の重複を除去する。
        unique=[]; seen=set()
        for result in results:
            key=(str(result['cache']),result['part_id'],result['ident'],result['display'])
            if key in seen:
                continue
            seen.add(key); unique.append(result)
        self._results=unique

        # 図面表示用のEPC接続はTk側で生成する（ワーカースレッドとの共有を避ける）。
        for result in self._results:
            key=(str(result['cache']),str(result['dataset']))
            if key not in self._epcs:
                try:
                    self._epcs[key]=EPC(result['cache'],result['dataset'])
                except Exception as exc:
                    errors.append(f"{result['dataset'].name}: {exc}")

        for i,result in enumerate(self._results):
            self.table.insert('','end',iid=str(i),values=result['display'])

        if cancelled:
            self.status.set(f'検索を中断しました。中断までに {len(self._results):,} 件見つかりました。')
        elif self._results:
            self.status.set(f'{len(self._results):,} 件見つかりました。結果を選択すると図面を表示します。')
        elif errors:
            self.status.set('検索結果はありません。一部のデータで読み込みエラーが発生しました。')
        else:
            self.status.set('該当する部品は見つかりませんでした。')

        if self._results:
            first=self.table.get_children()[0]
            self.table.selection_set(first); self.table.focus(first); self.table.see(first)
            self._result_selected()
        if errors and not cancelled:
            messagebox.showwarning('逆引き検索','一部の車両データを検索できませんでした。\n\n'+'\n'.join(errors[:8]),parent=self)

    def _apply_selected_to_main(self,event=None):
        selection=self.table.selection()
        if not selection:
            return 'break'
        try:
            result=self._results[int(selection[0])]
        except (ValueError,IndexError):
            return 'break'
        try:
            self.app.apply_reverse_result(result)
        except Exception as exc:
            messagebox.showerror('Honda EPC','メイン画面への反映中にエラーが発生しました。\n\n'+str(exc),parent=self)
        return 'break'

    def _result_selected(self,event=None):
        selection=self.table.selection()
        if not selection: return
        try: result=self._results[int(selection[0])]
        except Exception: return
        epc=self._epcs.get((str(result['cache']),str(result['dataset'])))
        if epc is None:
            self._clear_image(); return
        path=epc.image(result['image'])
        if path is None:
            self._clear_image(f'図面ファイルが見つかりません: {result["image"]}')
            return
        try:
            png=IMAGE_CACHE/(result['dbdir'].name+'_'+result['dataset'].name+'_'+path.name+'.png')
            if not png.exists() or png.stat().st_mtime<path.stat().st_mtime:
                self.app._convert(path,png)
            self._image=Image.open(png).convert('RGB')
            self._orig_size=self._image.size
            self._boxes=self.app._parse_image_annotations(path)
            self._selected_ann=result['annotation']
            self._redraw()
        except Exception as exc:
            self._clear_image(str(exc))

    def _clear_image(self,message='検索結果を選択すると図面を表示します。'):
        self._image=None; self._boxes=[]; self._selected_ann=''
        self.canvas.delete('all')
        self.canvas.configure(scrollregion=(0,0,1,1))
        self.canvas.create_text(14,14,text=message,fill='black',anchor='nw')

    def _redraw(self,event=None):
        if self._image is None: return
        w=max(100,self.canvas.winfo_width()); h=max(100,self.canvas.winfo_height())
        iw,ih=self._image.size
        scale=min((w-12)/iw,(h-12)/ih)
        if scale<=0: return
        self._scale=scale
        dw,dh=max(1,round(iw*scale)),max(1,round(ih*scale))
        left=max(0,(w-dw)/2); top=max(0,(h-dh)/2)
        self._img_origin=(left,top)
        resized=self._image.resize((dw,dh),Image.Resampling.LANCZOS)
        self._photo=ImageTk.PhotoImage(resized)
        self.canvas.delete('all')
        self.canvas.create_image(left,top,image=self._photo,anchor='nw')
        if self._selected_ann:
            for ann,x1,y1,x2,y2 in self._boxes:
                if str(ann).strip()==self._selected_ann:
                    self.canvas.create_rectangle(left+x1*scale,top+y1*scale,
                                                 left+x2*scale,top+y2*scale,
                                                 outline='red',width=3)
        self.canvas.configure(scrollregion=(0,0,max(w,round(left+dw)),max(h,round(top+dh))))
        self.canvas.xview_moveto(0); self.canvas.yview_moveto(0)

    def _zoom(self,event,direction=None):
        # 初版は読みやすさ優先で、ホイールによる倍率変更を行わず、
        # ウインドウサイズに合わせて図面全体をフィット表示する。
        return 'break'

    def _close(self):
        for epc in self._epcs.values():
            try: epc.close()
            except Exception: pass
        self._epcs.clear()
        self.destroy()

if __name__=='__main__':
    try: App().mainloop()
    except Exception as e:
        messagebox.showerror('Honda EPC',str(e)); raise
