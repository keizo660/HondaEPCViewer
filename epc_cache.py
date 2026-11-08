from pathlib import Path
import sqlite3, re, struct, json, hashlib

CACHE_FORMAT_VERSION = 'HondaEPC cache v24.0 mission-option-fix'

# PLMST reference field is 14 bytes: optional leading padding + variable-length
# figure number + fixed 11-character Honda part number.  The figure number
# must be taken from the whole prefix; removing the first byte would turn
# ' 46' into '4'.

def normalize_option_name(v):
    # SYSBMST.CD stores option names in fixed 18-byte fields.  Spaces can be
    # inserted to accommodate the original viewer's line wrapping (e.g.
    # "ｴｱｰ   ﾊﾞｯｸﾞ").  The specification selector is a single horizontal line,
    # so remove those padding spaces rather than preserving the wrap.
    return str(v or '').replace('\x00', '').replace(' ', '').strip()


def txt(b, enc='cp932'):
    return b.decode(enc, 'replace').replace('\x00', '').strip()

def u32(b, o):
    return int.from_bytes(b[o:o+4], 'little')

def find_shared_file(dbdir, name):
    p = dbdir / name
    if p.is_file():
        return p
    # tolerate a CD copied with an extra top-level folder
    hits = list(dbdir.rglob(name))
    return hits[0] if hits else None

def signature_files(dbdir, dataset):
    files = []
    for p in [find_shared_file(dbdir, 'TSMIR.CD'), find_shared_file(dbdir, 'KRHHKI.CD'), find_shared_file(dbdir, 'KSRBHMH.CD'), find_shared_file(dbdir, 'SYSBMST.CD')]:
        if p and p.is_file(): files.append(p)
    for p in dataset.rglob('*.CD'):
        if p.is_file(): files.append(p)
    rows=[]
    for p in sorted(set(files), key=lambda x: str(x).upper()):
        st=p.stat(); rows.append(f'{p.relative_to(dbdir)}|{st.st_size}|{st.st_mtime_ns}')
    # Folder inventory affects which KSRBHMH records are usable on this CD.
    rows.extend(f'__FOLDER__|{p.relative_to(dbdir)}' for p in sorted(dbdir.rglob('*'), key=lambda x: str(x).upper()) if p.is_dir())
    rows.append(f'__FORMAT__|{CACHE_FORMAT_VERSION}')
    return hashlib.sha256('\n'.join(rows).encode('utf-8')).hexdigest()

def parse_tsmir(path, form_ids=None):
    form_ids=form_ids or {}
    data=path.read_bytes(); pos=0; rows=[]
    while pos+2<=len(data):
        n=int.from_bytes(data[pos:pos+2],'little')
        if n<23 or pos+n>len(data): break
        r=data[pos:pos+n]; model=txt(r[2:17]); q=17
        while q+21<=n:
            typ=txt(r[q:q+13]); off=u32(r,q+13); ln=u32(r,q+17)
            if not typ: break
            rows.append((model,typ,off,ln,form_ids.get(typ, ""))); q+=21
        pos+=n
    return rows

def parse_krhhki(path):
    """形式名から5バイト形式IDへの対応表。先頭26バイトはヘッダー。"""
    data=path.read_bytes(); out={}
    pos=26
    while pos+26 <= len(data):
        r=data[pos:pos+26]
        name=txt(r[:13]); form_id=txt(r[13:18])
        if name and form_id:
            out.setdefault(name, form_id)
        pos += 26
    return out

def parse_sysbmst(path):
    """Read SYSBMST.CD option definitions.

    The file starts with an 18-byte blank/header area.  Thereafter each
    record is exactly 20 bytes: WORD option code followed by an 18-byte
    fixed-width option name.  The first two bytes of each record are used
    only as the option-code key; they are not part of the displayed name.
    """
    out={}
    if not path or not path.is_file():
        return out
    data=path.read_bytes()
    pos=18
    # The first two bytes of each record are NOT the KSRB option code.
    # KSRB option code 0x01 means the first 20-byte record after the
    # 18-byte header, 0x02 means the second record, etc.  The two-byte
    # value stored at the head of each SYSBMST record is unrelated here.
    rec_index=1
    while pos+20<=len(data):
        rec=data[pos:pos+20]
        name=normalize_option_name(rec[2:20].decode('cp932','replace'))
        if name:
            out[rec_index]=name
        rec_index += 1
        pos += 20
    return out


def parse_ksrb(path, option_map=None):
    data=path.read_bytes(); rows=[]; pos=0
    option_map=option_map or {}
    while pos+2<=len(data):
        n=int.from_bytes(data[pos:pos+2],'little')
        if n<2 or pos+n>len(data): break
        r=data[pos:pos+n]
        if n>=0x45:
            form_id=txt(r[2:7]); ident=txt(r[7:13]); model=txt(r[13:28]); typ=txt(r[28:41])
            frame_from=txt(r[0x34:0x3c]) if n>=0x3c else ''
            frame_to=txt(r[0x3c:0x44]) if n>=0x44 else ''
            spec_text=txt(r[0x42:0x53]) if n>=0x53 else ''
            grade=spec_text.strip()
            dbid=txt(r[0x61:0x69]) if n>=0x69 else ''

            # KSRBHMH condition area: first two WORDs are the condition IDs
            # used to match PLMST/block conditions.  Everything after those
            # WORDs is option-code data used by the specification selector.
            # From this point KSRBHMH stores a variable number of WORDs.
            # The first two WORDs are the condition IDs used by PLMST/block
            # matching.  WORD 3 and later are SYSBMST option codes only; they
            # must never enter the part-condition filter.
            # KSRBHMH condition/option area begins at +0x69.
            # Working rule established from the repeated KSRB records:
            #   WORD #1 and WORD #2 = condition IDs
            #   WORD #3 onward    = SYSBMST option codes
            # Do not compress the sequence by removing zero WORDs: the field
            # positions themselves are significant.  This keeps the parser
            # faithful to the record layout even when an unused WORD occurs.
            words=[]
            if n>0x69:
                for off in range(0x69, n-1, 2):
                    words.append(int.from_bytes(r[off:off+2], 'little'))
            cond_ids=words[:2]
            option_codes=[v for v in words[2:] if v]
            cond_ids=[v for v in cond_ids if v]

            cond_family=cond_ids[0] if len(cond_ids)>0 else None
            cond_e=cond_ids[1] if len(cond_ids)>1 else None
            condition=cond_family if cond_family is not None else None
            option_names=[option_map.get(v, f'コード{v:02X}') for v in option_codes]
            # KSRBHMH +0x56..+0x60: transmission(2), door count(1), engine(remaining).
            detail = txt(r[0x56:0x61]) if n >= 0x61 else ''
            transmission = detail[:2].strip()
            door_raw = detail[2:3].strip()
            doors = (door_raw + 'ドア') if door_raw.isdigit() else ''
            engine = detail[3:].strip()
            rows.append((pos,n,ident,model,typ,frame_from,frame_to,grade,dbid,condition,cond_family,cond_e,
                         json.dumps(cond_ids),json.dumps(option_codes),json.dumps(option_names,ensure_ascii=False),form_id,doors,transmission,engine))
        pos+=n
    return rows

def parse_groups(path):
    data=path.read_bytes(); out=[]
    for pos in range(0,len(data),54):
        r=data[pos:pos+54]
        if len(r)<54: break
        code=txt(r[2:4]); name=txt(r[4:42]); kind=txt(r[42:46]); start=u32(r,46); ln=u32(r,50)
        out.append((code,name,kind,start,ln))
    return out

def parse_blocks(path, groups, plm_size):
    data=path.read_bytes(); out=[]; pdat=path.parent/'PLMST.CD'; pdat=pdat.read_bytes()
    for gcode,gname,kind,start,ln in groups:
        end=min(start+ln,len(data)); pos=start
        while pos+2<=end:
            n=int.from_bytes(data[pos:pos+2],'little')
            if n<18 or pos+n>end: break
            r=data[pos:pos+n]
            section=txt(r[2:9]); image=txt(r[0x09:0x13]); desc1=txt(r[0x13:0x2c]); desc2=txt(r[0x2c:0x45]); desc=desc1.rstrip()+desc2.rstrip()
            cand=[]
            for base in range(0x45,min(0x59,n-7)+1,4):
                off=u32(r,base); ln2=u32(r,base+4)
                for delta in (0,-2,2,-4,4):
                    oo=off+delta
                    if 0<=oo<plm_size-2 and 0<ln2<=plm_size-oo:
                        cand.append((base,delta,oo,ln2))
            chosen=None
            for base,delta,oo,ln2 in cand:
                if oo+2>len(pdat): continue
                rl=int.from_bytes(pdat[oo:oo+2],'little')
                if 20<=rl<=ln2 and oo+rl<=len(pdat) and 32<=pdat[oo+2]<=90:
                    chosen=(oo,ln2,base,delta); break
            if chosen is None:
                for base,delta,oo,ln2 in cand:
                    if oo+ln2<=plm_size: chosen=(oo,ln2,base,delta); break
            po,pl,fb,delta=chosen if chosen else (None,None,None,None)
            out.append((gcode,gname,kind,section,image,desc,pos,n,po,pl,fb,delta))
            pos+=n
    return out

def parse_annotation_conditions(r):
    """Extract the currently usable PLMST condition IDs.

    Confirmed layout used here:
      +0x00 .. +0x51  fixed portion
      +0x52 .. +0x58  7-byte common area
      +0x59 onward   repeated [WORD subrecord_length][payload]

    The purpose/selection relationship of multiple PLMST subrecords is not
    yet established from the binary alone.  Therefore this routine only
    walks the subrecord boundaries exactly and preserves the existing,
    provisional condition extraction inside each payload.  No new semantic
    interpretation of the subrecords is introduced here.
    """
    if len(r) <= 0x5B:
        return '', []
    tail=r[0x52:]
    q=9  # 7-byte header + 2-byte field
    all_vals=[]
    annotations=[]
    while q+2 <= len(tail):
        n=int.from_bytes(tail[q:q+2], 'little')
        if n < 2 or q+n > len(tail):
            break
        block=tail[q:q+n]
        payload=block[2:]
        candidates=list(re.finditer(rb'\(\d{1,3}\)?|\x20{1,3}\d{1,3}', payload))
        if candidates:
            m=candidates[-1]
            rawq=m.group(0)
            try:
                textq=rawq.decode('ascii')
            except Exception:
                textq=''
            if textq.startswith('('):
                ann=textq[1:-1] if textq.endswith(')') else textq[1:]
            else:
                ann=textq.strip()
            if ann:
                annotations.append(ann)
            pos=m.end()
            while pos+2 <= len(payload):
                v=int.from_bytes(payload[pos:pos+2], 'little')
                if 1 <= v <= 1024:
                    all_vals.append(v)
                pos += 2
        q += n
    seen=set(); vals=[]
    for v in all_vals:
        if v not in seen:
            seen.add(v); vals.append(v)
    return ' / '.join(annotations), vals

def parse_parts(plm,start,length,block_id):
    end=min(start+length,len(plm)); pos=start; rows=[]; seq=0
    while pos+2<=end:
        n=int.from_bytes(plm[pos:pos+2],'little')
        if n<24 or pos+n>end: break
        r=plm[pos:pos+n]; typ=chr(r[2]) if len(r)>2 else ''
        if typ in 'ABEM':
            # PLMST B/part records use the fixed layout established from the
            # binary records:
            #   +0x0A..0x0B : 2-byte ASCII drawing/heading number
            #   +0x0C..0x18 : 13-byte part-number field (space padded)
            #   +0x19..0x31 : 25-byte part name, left-aligned
            #   +0x32..0x4A : 25-byte note, right-aligned
            # Actual part numbers can be 10, 11, 12, or 13 characters.
            ann=txt(r[0x0a:0x0c], 'ascii')
            part=txt(r[0x0c:0x19], 'ascii')
            part_name=txt(r[0x19:0x32]).rstrip()
            note=txt(r[0x32:0x4b]).strip()
            desc=part_name + note
            # PLMST fixed fields: 25-byte part name + 25-byte note, followed
            # by the Price field: 6 bytes at record offset +0x4B.
            # (The following byte is not part of the displayed price field.)
            price=txt(r[0x4b:0x52], 'cp932')
            _ann2,conds=parse_annotation_conditions(r)
            rows.append((block_id,seq,part,desc,price,ann,json.dumps(conds),pos,n,typ))
            seq+=1
        pos+=n
    return rows

def available_folder_ids(dbdir):
    """Return directory names present on this CD, case-insensitively.

    KSRBHMH +0x61..+0x68 is an 8-byte folder identifier.  The ISO inventory
    confirms exact matches for folders such as 11SA511; scan recursively so
    both a copied CD root and an extra wrapper directory are supported.
    """
    return {p.name.strip().upper() for p in dbdir.rglob('*') if p.is_dir() and p.name.strip()}


def build_cache(dbdir, dataset, cache_db):
    tsmir=find_shared_file(dbdir,'TSMIR.CD')
    krhhki=find_shared_file(dbdir,'KRHHKI.CD')
    ksrb=find_shared_file(dbdir,'KSRBHMH.CD')
    required=['GRPTBL.CD','BLKTYTBL.CD','PLMST.CD']
    missing=[x for x in required if not (dataset/x).is_file()]
    if not tsmir or not krhhki or not ksrb or missing:
        raise FileNotFoundError('必要なCDデータがありません: '+', '.join(missing or [x for x,p in [('TSMIR.CD',tsmir),('KRHHKI.CD',krhhki),('KSRBHMH.CD',ksrb)] if not p]))
    dataset=dataset.resolve(); dbdir=dbdir.resolve(); cache_db=cache_db.resolve()
    cache_db.parent.mkdir(parents=True,exist_ok=True)
    sig=signature_files(dbdir,dataset)
    tmp=cache_db.with_suffix('.tmp.sqlite')
    if tmp.exists(): tmp.unlink()
    con=sqlite3.connect(tmp); c=con.cursor()
    c.executescript('''
    CREATE TABLE meta(key TEXT PRIMARY KEY,value TEXT);
    CREATE TABLE tsmir(model TEXT,type TEXT,ksrb_offset INTEGER,ksrb_length INTEGER,form_id TEXT);
    CREATE TABLE ksrb(offset INTEGER,record_length INTEGER,ident TEXT,model TEXT,type TEXT,frame_from TEXT,frame_to TEXT,grade TEXT,dbid TEXT,condition_id INTEGER,condition_family INTEGER,condition_e INTEGER,condition_ids TEXT,option_codes TEXT,option_names TEXT,form_id TEXT,doors TEXT,transmission TEXT,engine TEXT);
    CREATE TABLE groups(code TEXT,name TEXT,kind TEXT,offset INTEGER,length INTEGER);
    CREATE TABLE blocks(id INTEGER PRIMARY KEY,group_code TEXT,group_name TEXT,kind TEXT,section TEXT,image TEXT,description TEXT,record_offset INTEGER,record_length INTEGER,plmst_offset INTEGER,plmst_length INTEGER,field_base INTEGER,field_delta INTEGER);
    CREATE TABLE block_conditions(block_id INTEGER,condition_id INTEGER);
    CREATE TABLE parts(id INTEGER PRIMARY KEY,block_id INTEGER,seq INTEGER,part_number TEXT,description TEXT,price TEXT,annotation TEXT,record_offset INTEGER,record_length INTEGER,record_type TEXT);
    CREATE TABLE part_conditions(part_id INTEGER,condition_id INTEGER);
    CREATE INDEX idx_parts_block ON parts(block_id); CREATE INDEX idx_parts_ann ON parts(block_id,annotation); CREATE INDEX idx_pc_part ON part_conditions(part_id); CREATE INDEX idx_pc_cond ON part_conditions(condition_id);
    ''')
    c.execute('insert into meta values (?,?)',('signature',sig)); c.execute('insert into meta values (?,?)',('dataset',str(dataset))); c.execute('insert into meta values (?,?)',('format',CACHE_FORMAT_VERSION))
    form_ids=parse_krhhki(krhhki)
    for r in parse_tsmir(tsmir, form_ids): c.execute('insert into tsmir values (?,?,?,?,?)',r)
    sysbmst=find_shared_file(dbdir,'SYSBMST.CD')
    option_map=parse_sysbmst(sysbmst)
    # Cache only records whose referenced data folder actually exists on this CD.
    # The source KSRBHMH.CD is never modified.
    folder_ids=available_folder_ids(dbdir)
    ksrb_rows=parse_ksrb(ksrb, option_map)
    for r in ksrb_rows:
        if r[8].strip().upper() in folder_ids:
            c.execute('insert into ksrb values (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)',r)
    c.execute('insert into meta values (?,?)',('ksrb_total_records',str(len(ksrb_rows))))
    c.execute('insert into meta values (?,?)',('ksrb_available_records',str(sum(1 for r in ksrb_rows if r[8].strip().upper() in folder_ids))))
    c.execute('insert into meta values (?,?)',('available_folder_count',str(len(folder_ids))))
    groups=parse_groups(dataset/'GRPTBL.CD')
    for r in groups: c.execute('insert into groups values (?,?,?,?,?)',r)
    plm=(dataset/'PLMST.CD').read_bytes()
    blkdata=(dataset/'BLKTYTBL.CD').read_bytes()
    blocks=parse_blocks(dataset/'BLKTYTBL.CD',groups,len(plm))
    for i,r in enumerate(blocks):
        c.execute('insert into blocks values (?,?,?,?,?,?,?,?,?,?,?,?,?)',(i,)+r)
        # BLKTYTBL verified variable tail:
        #   +0x55  WORD: first subrecord length
        #   ...     first subrecord (length includes its own WORD)
        #   next    WORD: second subrecord length, if present
        #   ...     second subrecord payload = block-condition WORD list
        # The first subrecord is not interpreted here.  The second subrecord
        # is the block-condition list established in the current analysis.
        boff=r[6]; blen=r[7]
        rec=blkdata[boff:boff+blen]
        q=0x55
        subrecords=[]
        while q+2 <= len(rec):
            sublen=int.from_bytes(rec[q:q+2], 'little')
            if sublen < 2 or q+sublen > len(rec):
                break
            subrecords.append(rec[q:q+sublen])
            q += sublen
        if len(subrecords) >= 2:
            payload=subrecords[1][2:]
            for q in range(0,len(payload)-1,2):
                cond=int.from_bytes(payload[q:q+2],'little')
                if cond:
                    c.execute('insert into block_conditions values (?,?)',(i,cond))
    pid=0
    for bid,b in enumerate(blocks):
        po,pl=b[8],b[9]
        if po is None: continue
        for row in parse_parts(plm,po,pl,bid):
            block_id,seq,part,desc,price,ann,condj,ro,rl,typ=row
            c.execute('insert into parts values (?,?,?,?,?,?,?,?,?,?)',(pid,block_id,seq,part,desc,price,ann,ro,rl,typ))
            for cond in json.loads(condj): c.execute('insert into part_conditions values (?,?)',(pid,cond))
            pid+=1
    con.commit(); con.close();
    if cache_db.exists(): cache_db.unlink()
    tmp.replace(cache_db)
    return cache_db

def cache_is_current(cache_db, dbdir, dataset):
    if not cache_db.is_file(): return False
    try:
        con=sqlite3.connect(cache_db); row=con.execute("select value from meta where key='signature'").fetchone(); con.close()
        return bool(row and row[0]==signature_files(dbdir,dataset))
    except Exception:
        return False
