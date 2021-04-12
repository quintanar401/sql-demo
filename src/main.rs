extern crate rand;
extern crate rayon;
extern crate fnv;

use rayon::prelude::*;
use std::collections::HashMap;
// use std::collections::BTreeMap;
use std::rc::Rc;
use fnv::FnvHashMap;

#[derive(Debug)]
struct Token<'a> {
    str: &'a str,
    kind:&'static str,
}

fn lexer() -> impl Fn(&str) -> Vec<Token> {
    // map: char -> group
    let mut c2grp: Vec<usize>= vec![0;128];
    let cgrp: [&[u8];10] = [b"\t \r\n",b"0123456789",b"abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ",b"\\",b"\"",b"=",b"<",b">",b".",b"'"];
    cgrp.iter().enumerate().for_each(|(i,&s)| s.iter().for_each(|&s| c2grp[s as usize] = i + 1));

    // automata: (state,grp) -> state
    let rules: [&[u8];21] = [b"aA A a0.",b"0I I 0",b"0I F .",b"F F 0",
                        b"= E =",b"> E =",b"< E =",b"< E >",
                        b"\" S *",b"S S *",b"S R \"",b"S T \\",b"\" R \"",b"\" T \\",b"T S *",
                        b"' U *",b"U U *",b"U V '",b"V U '",b"' V '",b"\tW W \t"];
    let rules: Vec<Vec<&[u8]>> = rules.iter().map(|&s| s.split(|&s| s == b' ').collect()).collect(); // " " vs/: rules
    let states = { // distinct " ",(first each cgrp),raze rules[;1]
        let mut st = vec![b' '];
        for v in &cgrp { st.push(v[0])};
        for v in &rules { st.extend_from_slice(v[1]) };
        distinct(&st)
    };
    let fsa = {
        let len = 1+cgrp.len();
        let mut fsa: Vec<Vec<usize>> = (0..states.len()).into_iter().map(|_| til(len)).collect(); // (count states;len)#til len
        for r in rules {
            let st:Vec<Vec<usize>> = r.iter().map(|v| findn(states.as_ref(),v)).collect(); // st:states?y
            let i2 = if r[2].len() > find1(r[2],&b'*') {til(len)} else {st[2].clone()}; // i2:(st 2;til 1+count cgrp)"*" in y 2
            for &i in &st[0] { sidxn1(&mut fsa[i],&i2,&st[1][0]) } // x[st 0;i2] = st[1;0]
        }
        fsa
    };
    let sta = find1(&states,&b'A');
    let stn = findn(&states,b"a0\"'\t");
    let s2n = move |v| ["ID","NUM","STR","STR","WS","OTHER"][find1(&stn,&v)].clone();
    // Lexer itself
    move |s| {
        if s.len()==0 {return Vec::<Token>::new()};
        let mut sti = 0usize;
        let st: Vec<usize> = s.as_bytes().iter().map(|b| { // st:fsa\[0;c2grp x]
            sti = fsa[sti][c2grp[*b as usize]];
            sti}).collect();
        let mut ix = wh(&lt1(&st, sta)); // where st<sta
        ix.push(st.len());
        (0..ix.len()-1).into_iter()
            .filter_map(|i|
                match s2n(st[ix[i]]) { 
                    "WS" => None,  
                    kind => Some(Token{ str:&s[ix[i]..ix[i+1]], kind}) 
                }).collect()
    }
}

type RRVal=Result<Rc<Val>,String>;
type RVal=Rc<Val>;

#[derive(Debug,Clone)]
enum Val {   
    I(i64),
    D(f64),
    II(Vec<i64>),
    DD(Vec<f64>),
    S(String),
    SS(Vec<String>),
    TBL(Dict<RVal>),
    ERR(String),
}

impl Val {
    fn as_i(&self) -> i64 { if let Val::I(i) = self {return *i} else {panic!("unexpected {:?}",self)} }
    // Unlike count return -1 for atoms, -2 for all other
    fn len(&self) -> i64 { match self {
        Val::II(i) => i.len() as i64,
        Val::DD(i) => i.len() as i64,
        Val::SS(i) => i.len() as i64,
        Val::I(_) => -1,
        Val::D(_) => -1,
        Val::S(_) => -1,
        _ => -2}}
    fn take(&self, i: usize) -> RVal { match self {
        Val::I(j) => Val::II(vec![*j;i]).into(),
        Val::D(j) => Val::DD(vec![*j;i]).into(),
        Val::S(j) => Val::SS((0..i).into_iter().map(|_| j.clone()).collect()).into(),
        _ => panic!("unexpected {:?}",self)}
    }
    fn filter(&self, i: &Vec<usize>) -> RRVal { match self {
        Val::II(j) => Ok(Val::II(i.iter().map(|v| j[*v]).collect()).into()),
        Val::DD(j) => Ok(Val::DD(i.iter().map(|v| j[*v]).collect()).into()),
        Val::SS(j) => Ok(Val::SS(i.iter().map(|v| j[*v].clone()).collect()).into()),
        _ => Err("type".into())}
    }
    fn get_vec(&self, l: usize) -> RRVal { match self {
        Val::I(_) => Ok(Val::II(Vec::with_capacity(l)).into()),
        Val::D(_) => Ok(Val::DD(Vec::with_capacity(l)).into()),
        Val::S(_) => Ok(Val::SS(Vec::with_capacity(l)).into()),
        Val::II(_) => Ok(Val::II(Vec::with_capacity(l)).into()),
        Val::DD(_) => Ok(Val::DD(Vec::with_capacity(l)).into()),
        Val::SS(_) => Ok(Val::SS(Vec::with_capacity(l)).into()),
        _ => Err("type".into())
    }}
    fn join(&mut self, v:RVal) -> Result<(),String> { match (self,&*v) {
        (Val::II(v),Val::I(i)) => Ok(v.push(*i)),
        (Val::II(v),Val::II(i)) => Ok(v.push(i[0])),
        (Val::DD(v),Val::D(i)) => Ok(v.push(*i)),
        (Val::DD(v),Val::DD(i)) => Ok(v.push(i[0])),
        (Val::SS(v),Val::S(i)) => Ok(v.push(i.clone())),
        (Val::SS(v),Val::SS(i)) => Ok(v.push(i[0].clone())),
        _ => Err("type".into())
    }}
}

impl std::fmt::Display for Val {   
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        fn prv<T: std::fmt::Display>(v: &Vec<T>, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(f, "[{};", v.len())?;
            for i in 0..usize::min(20,v.len()) { write!(f, " {}", v[i])?;};
            write!(f,"{}",if v.len()<=20 {"]"} else {" ..]"})
        }
        fn adj_col(v:Vec<String>) -> Vec<String> {
            let mx = v.iter().map(|v| v.len()).max().unwrap();
            v.into_iter().map(|v| format!("{:<1$}",v,mx)).collect()
        }
        match self {
            Val::I(i) => write!(f, "{}", i),
            Val::D(i) => write!(f, "{}", i),
            Val::S(i) => write!(f, "{}", i),
            Val::II(i) => prv(i,f),
            Val::DD(i) => prv(i,f),
            Val::SS(i) => prv(i,f),
            Val::ERR(i) => write!(f, "Error: {}", i),
            Val::TBL(d) => {
                let l = fn_count(d.v[0].clone()).unwrap().as_i() as usize;
                let cnt = usize::min(l,20);
                let mut s: Vec<String> = (0..1+cnt).map(|_| String::new()).collect();
                for (i,c) in d.k.iter().enumerate() {
                    s[0] = format!("{} {}",s[0],c);
                    for j in 0..cnt { s[j+1] = format!("{} {}",s[j+1],fn_idx(d.v[i].clone(),j).unwrap()) }
                    s = adj_col(s)
                }
                writeln!(f,"{}",s[0])?;
                writeln!(f,"{:-<1$}","",s[0].len())?;
                for i in 0..cnt { writeln!(f,"{}",s[i+1])?;};
                if cnt < l {writeln!(f,"...")?}
                Result::Ok(())
            }
        }
    }
}

#[derive(Debug,Clone)]
enum Expr {
    Empty,
    F1(fn (RVal) -> RRVal, Box<Expr>),
    F2(fn (RVal,RVal) -> RRVal, Box<Expr>, Box<Expr>),
    ELst(Vec<Expr>),
    ID(String),
    Val(Val),
    Set(String,Box<Expr>),
    Sel(Sel),
    Tbl(Vec<String>,Vec<Expr>),
}

#[derive(Debug,Clone)]
struct Sel {
    s:Option<(Vec<String>,Vec<Expr>)>,
    d:bool,
    into: Option<String>,
    w: Option<Box<Expr>>,
    g: Option<Vec<Expr>>,
    j:(Box<(String,Expr)>,(Vec<(String,Expr)>,Vec<(Vec<String>,Vec<String>)>)), // (Str,Expr) -> name: table; (Str*,Str*) -> join conditions
}

impl Expr {
    fn as_id(self) -> String { if let Self::ID(s) = self {s} else {panic!("ID expected: {:?}",self)}}
    fn as_elst(self) -> Vec<Expr> { if let Self::ELst(e) = self {e} else {panic!("ELst expected: {:?}",self)}}
    fn as_option(self) -> Option<Expr> { if let Self::Empty = self {None} else {Some(self)} }
}

#[derive(Debug,Clone)]
struct Dict<T> {
    k: Vec<String>,
    v: Vec<T>,
}

impl<T> Dict<T> {
    fn from_parts(k: Vec<String>, v: Vec<T>) -> Self { Self {k, v} }
    fn set(&mut self, k: String, v: T) {
        let i = find1(&self.k, &k);
        if i == self.k.len() {
            self.k.push(k); self.v.push(v)
        } else { self.v[i] = v }
    }
    fn get_unchecked(&self, k:&String) -> &T { &self.v[find1(&self.k, k)] }
    fn get(&self, k:&String) -> Option<&T> { let i = find1(&self.k, k); if i<self.k.len() {Some(&self.v[i])} else {None} }
    fn extend(&mut self, d:Dict<T>) { d.k.into_iter().zip(d.v.into_iter()).for_each(|(k,v)| self.set(k,v)) }
}

impl<T> From<(Vec<String>,Vec<T>)> for Dict<T> {
    fn from(v: (Vec<String>,Vec<T>)) -> Dict<T> { Dict::from_parts(v.0,v.1)}
}

impl<T> IntoIterator for Dict<T> {
    type Item = (String,T);
    type IntoIter = std::iter::Zip<std::vec::IntoIter<String>,std::vec::IntoIter<T>>;

    fn into_iter(self) -> Self::IntoIter {
        self.k.into_iter().zip(self.v.into_iter())
    }
}

struct Table {
    cmap: Dict<String>,
    tbl: Dict<RVal>,
}


struct ECtx {
    ctx: HashMap<String,Rc<Val>>,   // variables
    tbl: Option<Table>,             // within select
    idx: Option<Vec<usize>>,        // idx into tbl
}

impl ECtx {
    fn new() -> Self {ECtx {ctx:HashMap::new(), tbl:None, idx: None}}

    fn eval_table(&mut self, n: Vec<String>, e: Vec<Expr>) -> RRVal {
        if distinct(&n).len() != n.len() { return Result::Err("duplicate name".into())}
        let v = self.eval_table_inner(e)?;
        Ok(Val::TBL(Dict::from_parts(n,v)).into())
    }

    fn eval_table_inner(&mut self, e: Vec<Expr>) -> Result<Vec<RVal>,String> {
        let r = e.into_iter().map(|v| Ok(self.eval(v)?)).collect::<Result<Vec<RVal>,String>>()?;
        let mut sz = -1;
        for i in r.iter() { // all columns must be vecs of the same size, convert atoms by dup
            let rsz = i.len();
            if rsz > -1 && sz > -1 && sz != rsz {return Result::Err("length".into())}; // length control
            if rsz == -2 {return Result::Err("type".into())}; // only atoms and vecs
            if rsz > -1 {sz = rsz}
        }
        if sz == -1 {sz = 1}
        Ok(r.into_iter().map(|v| if v.len() == -1 {v.take(sz as usize)} else {v}).collect())
    }

    fn eval(&mut self, e: Expr) -> RRVal {
        match e {
            Expr::ID(id) => self.resolve_name(&id),
            Expr::Set(id,e) => {let v = self.eval(*e)?; self.ctx.insert(id,v.clone()); Ok(v)}
            Expr::Val(v) => Ok(v.into()),
            Expr::F1(f,e) => Ok(f(self.eval(*e)?)?),
            Expr::F2(f,e1,e2) => Ok(f(self.eval(*e1)?,self.eval(*e2)?)?),
            Expr::Tbl(n,e) => { self.eval_table(n, e) }
            Expr::Sel(s) => self.do_sel(s),
            e => Result::Err(format!("unexpected expr {:?}",e))
        }
    }
    // search tbl, then vars
    fn resolve_name(&self, n:&String) -> RRVal {
        if let Some(ref tbl) = self.tbl {
            if let Some(n2) = tbl.cmap.get(&n) {
                let mut v = tbl.tbl.get_unchecked(&n2).clone();
                if let Some(ref idx) = self.idx { v = v.filter(idx)? }
                return Ok(v)
            } else if n == "_i" {
                // we must return idx really but we would need to clone it, it is used only in count(*) atm so it is ok
                let mut v = tbl.tbl.v[0].clone();
                if let Some(ref idx) = self.idx { v = v.filter(idx)? }
                return Ok(v)
            }
        }
        if let Some(v) = self.ctx.get(n) {Ok(v.clone())} else {Result::Err(n.into())}
    }

    fn do_sel(&mut self, mut s:Sel) -> RRVal {
        let (tbl,idx) = (std::mem::take(&mut self.tbl),std::mem::take(&mut self.idx));
        let into = std::mem::take(&mut s.into); let d = s.d;
        let r = self.do_sel_core(s);
        self.tbl = tbl; self.idx = idx;
        let mut r = r?;
        if d { // if let will always succeed
            if let Some(Val::TBL(ref mut d)) = Rc::get_mut(&mut r) {
                let v = std::mem::take(&mut d.v);
                d.v = Self::do_dist(v)?
            }
        }
        if let Some(n) = into { self.ctx.insert(n,r.clone()); }
        Ok(r)
    }

    fn do_sel_core(&mut self, s:Sel) -> RRVal {
        self.tbl = Some(self.do_join(s.j)?);
        self.do_where(s.w)?;
        let se = if let Some(s) = s.s {Dict::from(s)}
            else {
                let t = self.tbl.as_ref().unwrap();
                let rmap: Dict<String> = Dict { k:t.cmap.v.clone(), v:t.cmap.k.clone()};
                let k: (Vec<String>,Vec<Expr>) = t.tbl.k.iter().map(|v| {
                    let k = rmap.get_unchecked(v).clone();
                    (k.replace(".","_"),Expr::ID(k))}).unzip();
                Dict::from(k)
            };
        if let Some(g) = s.g {
            let r = self.eval_table_inner(g)?;
            let l = r[0].len() as usize;
            let mut h:FnvHashMap<HashedKey,Vec<usize>> = FnvHashMap::default();
            for i in 0..l as usize {
                let e = h.entry(HashedKey{src:&r,idx:i}).or_insert(Vec::new());
                e.push(i);
            }
            let idx: Vec<Vec<usize>> = h.into_iter().map(|(_,v)| if let Some(ref i) = self.idx {v.into_iter().map(|v| i[v]).collect()} else {v}).collect();
            let r = idx.into_iter().map(|i| {self.idx = Some(i); se.v.clone().into_iter().map(|v| self.eval(v)).collect::<Result<Vec<RVal>,String>>()}).collect::<Result<Vec<Vec<RVal>>,String>>()?;
            let res = r[0].iter().map(|v| v.get_vec(r[0].len())).collect::<Result<Vec<RVal>,String>>()?;
            let res = r.into_iter().try_fold(res,|res,v| res.into_iter().zip(v.into_iter())
                .map(|(mut res,v)| {Rc::get_mut(&mut res).unwrap().join(v)?; Ok(res)}).collect::<Result<Vec<RVal>,String>>())?;
            return Ok(Val::TBL(Dict::from_parts(se.k,res)).into());
        }
        self.eval_table(se.k, se.v)
    }

    fn do_dist(v: Vec<RVal>) -> Result<Vec<RVal>,String> {
        let l = v[0].len() as usize;
        let mut h:FnvHashMap<HashedKey,usize> = FnvHashMap::default();
        for i in 0..l as usize { h.entry(HashedKey{src:&v,idx:i}).or_insert(i); }
        if h.len() == v.len() {return Ok(v)}
        let idx = h.into_iter().map(|(_,v)| v).collect();
        v.into_iter().map(|v| v.filter(&idx)).collect::<Result<Vec<RVal>,String>>()
    }

    fn do_where(&mut self, w:Option<Box<Expr>>) -> Result<(),String> {
        if let Some(e) = w {
            return match &*self.eval(*e)? {
                Val::II(i) => Ok(self.idx = Some(i.into_iter().enumerate().filter_map(|(i,v)| if *v == 0 {None} else {Some(i)}).collect())),
                _ => Err("where: type".into())
            }
        };
        Ok(())
    }

    fn do_join(&mut self, j:(Box<(String,Expr)>,(Vec<(String,Expr)>,Vec<(Vec<String>,Vec<String>)>))) -> Result<Table,String> {
        let mut tbl = self.ren(*j.0,"@".into())?;
        if j.1.0.len() == 0 { return Ok(tbl) }; // no joins
        for ((i,t),cnd) in j.1.0.into_iter().enumerate().zip(j.1.1.into_iter()) {
            let mut tbl2 = self.ren(t,i.to_string())?;
            if let Some(name) = cnd.0.iter().find(|s| tbl.cmap.get(*s).is_none()) { return Err(format!("Invalid column {}",name))}
            tbl2.cmap.extend(tbl.cmap); // old columns have priority
            let tbl1 = tbl.tbl; // destroy tbl completely to satisfy bchecker
            if let Some(name) = cnd.1.iter().find(|s| {let n = tbl2.cmap.get(*s); n.is_none() || tbl2.tbl.get(&n.unwrap()).is_none()}) { return Err(format!("Invalid column {}",name))}
            let c0: Vec<String> = cnd.0.iter().map(|s| tbl2.cmap.get_unchecked(s).clone()).collect(); // rename conditions
            let c1: Vec<String> = cnd.1.iter().map(|s| tbl2.cmap.get_unchecked(s).clone()).collect();
            tbl2.cmap.extend(Dict::from_parts(cnd.1.clone(),c0.clone())); // right hand columns must be replaced with the left hand cols
            let j1: Vec<RVal> = c0.iter().map(|c| tbl1.get_unchecked(c).clone()).collect(); // cond -> values
            let j2: Vec<RVal> = c1.iter().map(|c| tbl2.tbl.get_unchecked(c).clone()).collect();
            let (i1,i2) = ECtx::do_sij(j1,j2)?;
            tbl.tbl = tbl1.into_iter().map(|(k,v)| Ok((k,fn_idxn(v,&i1)?))).collect::<Result<Vec<(String,RVal)>,String>>()?.into_iter().unzip().into();
            for v in tbl2.tbl { if c1.len() == find1(&c1,&v.0) {tbl.tbl.set(v.0,fn_idxn(v.1,&i2)?);} }
            tbl.cmap = tbl2.cmap;
        }
        Ok(tbl)
    }

    // find join idxs into t1 and t2
    fn do_sij(t1:Vec<RVal>, t2:Vec<RVal>) -> Result<(Vec<usize>,Vec<usize>),String> {
        let ylen = t2[0].len() as usize;
        let i:Vec<usize> =  { 
            let h:FnvHashMap<HashedKey,usize> = (0..t2[0].len()as usize).into_iter().map(|i| (HashedKey{src:&t2,idx:i},i)).collect();
            (0..t1[0].len()as usize).into_iter().map(|i| if let Some(j) = h.get(&HashedKey{src:&t1,idx:i}) {*j} else {ylen}).collect()
        };
        let j: Vec<usize> = i.iter().enumerate().filter_map(|(i,v)| if *v<ylen {Some(i)} else {None}).collect();
        let i = j.iter().map(|v| i[*v]).collect();
        Ok((j,i))
    }

    // rename columns
    fn ren(&mut self, tbl: (String,Expr), prfx: String) -> Result<Table,String> {
        let r = self.eval(tbl.1)?;
        let t = match &*r {
            Val::TBL(d) => d,
            _  => return Result::Err("select: not a table".into())
        };
        let tbl0 = tbl.0;
        let orig_full: Vec<String> = t.k.iter().map(|v| format!("{}.{}",tbl0,v)).collect(); // tname.cname
        let unique: Vec<String> = orig_full.iter().map(|v| format!("{}{}",prfx,v)).collect(); // @tname.cname
        let mut cmap = Dict::from_parts(t.k.clone(),unique.clone());
        cmap.extend(Dict::from_parts(orig_full,unique.clone()));
        let tbl = Dict::from_parts(unique,t.v.clone());
        Ok(Table { cmap, tbl })
    }
}

struct HashedKey<'a> {
    src:&'a Vec<RVal>,
    idx: usize,
}

impl std::hash::Hash for HashedKey<'_> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.src.iter().for_each(|v| match &**v {
            Val::II(v) => v[self.idx].hash(state),
            Val::DD(v) => v[self.idx].to_be_bytes().hash(state),
            Val::SS(v) => v[self.idx].hash(state),
            _ => ()
        })
    }
}

impl PartialEq for HashedKey<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.src.iter().zip(other.src.iter()).all(|(v1,v2)| match (&**v1,&**v2) {
            (Val::II(v1),Val::II(v2)) => v1[self.idx] == v2[other.idx],
            (Val::DD(v1),Val::DD(v2)) => v1[self.idx] == v2[other.idx],
            (Val::SS(v1),Val::SS(v2)) => v1[self.idx] == v2[other.idx],
            _ => false
        })
    }
}

impl Eq for HashedKey<'_> {}

impl Ord for HashedKey<'_> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        let mut o = std::cmp::Ordering::Equal;
        for i in 0..self.src.len() {
            o = match (&*self.src[i],&*other.src[i]) {
                (Val::II(v1),Val::II(v2)) => v1[self.idx].cmp(&v2[other.idx]),
                (Val::DD(v1),Val::DD(v2)) => if let Some(o) = v1[self.idx].partial_cmp(&v2[other.idx]) {o} else
                    {match (v1[self.idx].is_nan(),v2[other.idx].is_nan()) {
                        (true,true) => std::cmp::Ordering::Equal,
                        (true,false) => std::cmp::Ordering::Less,
                        _ => std::cmp::Ordering::Greater
                    }}
                (Val::SS(v1),Val::SS(v2)) => v1[self.idx].cmp(&v2[other.idx]),
                _ => panic!("unexpected type in HashKey::Ord")
            };
            if o != std::cmp::Ordering::Equal {break}
        }
        return o
    }
}

impl PartialOrd for HashedKey<'_> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl From<Val> for Expr {
    fn from(v:Val) -> Self {Expr::Val(v)}
}

type ParseFn = Box<dyn Fn(&PCtx,&[Token],usize) -> Option<(Expr,usize)>>;
type PPFn = Box<fn(Vec<Expr>) -> Expr>;

struct PCtx {
    rules: HashMap<String,ParseFn>,
    ppfns: HashMap<String,PPFn>,
}

impl PCtx {
    fn parse(&self, t:&[Token]) -> Expr {
        if let Some((e,i)) = self.rules["top"](&self,t,0) {
            if i == t.len() {e} else {Val::ERR("parse error: input is not consumed".into()).into()}
        } else {Val::ERR("parse error".into()).into()}
    }
}

fn parser(l: &dyn Fn(&str) -> Vec<Token>) -> PCtx {
    let parse = |str| {
        let t = l(str);  // add ({}) depth map
        let mut lvl = 0; // internal lexer -> errors are not expected
        pp_or(&t.into_iter().map(|v| {match v.str.as_bytes()[0] {b'(' | b'{' => lvl+=1, b')' | b'}' => lvl-=1, _ => ()}; (v,std::cmp::max(0,lvl))} ).collect::<Vec<(Token,i32)>>(), 0)
    };
    let mut map = HashMap::new();
    let kws = ["select","distinct","into","where","group","by","from","as","join","on","or","and","not","set","count","rand","avg","sum","min","max"];
    // rules
    [("top",  "sel | set | expr"),
     ("set","'set' ID expr {set}"),
     ("sel",  "'select' 'distinct'? sexpr ('into' ID)? 'from' join ('where' expr)? ('group' 'by' elst)? {sel}"),
     ("sexpr","'*' | nexpr (',' nexpr)* {conc}"),
     ("nexpr","expr ('as'? ID)? {nexpr}"),
     ("join", "tbl ('join' tbl 'on' jelst {24})* {lst}"),
     ("jexpr","ID '=' ID {13}"),
     ("jelst","jexpr (',' jexpr)* {conc}"),
     ("tbl",  "ID ('as' ID)? {tbl}| '(' sel ')' ('as' ID)? {tsel}"),
     ("expr", "expr1 ('or' expr {lst})? {f2}"),
     ("expr1","'not' expr1 {f1} | expr2 ('and' expr1 {lst})? {f2}"),
     ("expr2","expr3 (('='|'<>'|'<='|'>='|'>'|'<') expr2 {lst})? {f2}"),
     ("expr3","expr4 (('+'|'-') expr3 {lst})? {f2}"),
     ("expr4","vexpr (('*'|'/') expr4 {lst})? {f2}"),
     ("vexpr","'(' expr ')' {2} | '-' expr {f1} | call | ID | STR | NUM | '[' (telst (',' telst)* {conc}) ']' {tblv}"),
     ("call", "('sum'|'avg'|'count'|'min'|'max') '(' expr ')' {call} | 'count' '(' '*' ')' {cnt} | 'rand' '(' STR ',' NUM ')' {rand}"),
     ("telst","ID expr {lst}"),
     ("elst", "expr (',' expr)* {conc}")].iter().for_each(|(n,v)| {map.insert(n.to_string(),parse(v));});

     // token parsers
    map.insert("STR".to_string(),Box::new(|_,toks,i| Some((Val::S(toks[i].str[1..toks[i].str.len()-1].to_string()).into(),i+1))));
    map.insert("NUM".to_string(),Box::new(|_,toks,i| {
        let s = toks[i].str;
        if s.contains('.') {
            s.parse::<f64>().ok().map(|v| (Val::D(v).into(),i+1))
        } else {
            s.parse::<i64>().ok().map(|v| (Val::I(v).into(),i+1))}}));
    map.insert("ID".to_string(),Box::new(move |_,toks,i|{
        if kws.iter().any(|v| &toks[i].str == v) {return None};
        Some((Expr::ID(toks[i].str.to_string()),i+1)) }));

    // parse helpers
    let mut pfn: HashMap<String,PPFn> = HashMap::new();
    pfn.insert("default".to_string(),Box::new(|mut e| e.pop().unwrap())); // return the last val, in many cases it is ok
    pfn.insert("lst".to_string(),Box::new(|e| Expr::ELst(e)));  // wrap into ELst
    pfn.insert("sel".to_string(),Box::new(|mut e| { // select distinct? sexprs into? from join where? group?
        let g = e.pop().unwrap().as_option().map(|v| v.as_elst());
        let w = e.pop().unwrap().as_option().map(|v| Box::new(v));
        let mut j = e.pop().unwrap().as_elst(); e.pop();
        let into = e.pop().unwrap().as_option().map(|v| v.as_id());
        let s = e.pop().unwrap();
        let d = e.pop().unwrap().as_option().is_some();
        let mut i = 0;
        let s: Option<(Vec<String>,Vec<Expr>)> = match s { Expr::ID(_) => None, _ => Some(s.as_elst().into_iter()
            .map(|v|{ let mut v = v.as_elst();
                    let id = v.pop().unwrap().as_id();
                    (if id.len()==0 || id.contains('.') {i+=1; format!("x{}",i)} else {id},v.pop().unwrap())}).unzip())}; // -> names!exprs
        // j0 = ((name,expr),(name,name)*)*
        fn get_tbl(mut v: Vec<Expr>) -> (String,Expr) { let e = v.pop().unwrap(); (v.pop().unwrap().as_id(),e)}
        let j0: (Vec<(String,Expr)>,Vec<(Vec<String>,Vec<String>)>) = j.pop().unwrap().as_elst().into_iter().map(|v| {
            let mut v = v.as_elst(); let cnd = v.pop().unwrap().as_elst(); let v = v.pop().unwrap().as_elst();
            let cnd = cnd.into_iter().map(|v| {let mut v = v.as_elst(); let n = v.pop().unwrap().as_id(); (v.pop().unwrap().as_id(),n)}).unzip();
            (get_tbl(v),cnd)
        }).unzip();
        
        Expr::Sel(Sel {s, d, into, w, g, j: (get_tbl(j.pop().unwrap().as_elst()).into(),j0)})
    }));
    pfn.insert("f2".to_string(),Box::new(|mut e| { // exp ('fn' exp)?
        let r = e.pop().unwrap(); let l = e.pop().unwrap();
        if let Expr::Empty = r {return l};
        let mut r = r.as_elst(); let r2 = r.pop().unwrap();
        Expr::F2(pp_fn2(r.pop().unwrap().as_id()),l.into(),r2.into())
    }));
    pfn.insert("2".to_string(),Box::new(|mut e| e.swap_remove(1))); // [_, e, _] -> e
    pfn.insert("13".to_string(),Box::new(|mut e| {e.swap_remove(1); Expr::ELst(e)})); // [e, _, e] -> [e,e]
    pfn.insert("24".to_string(),Box::new(|mut e| {e.swap_remove(2); e.remove(0); Expr::ELst(e)})); // [_, e, _, e] -> [e,e]
    pfn.insert("conc".to_string(),Box::new(|mut e| {let mut v = e.pop().unwrap().as_elst(); e.append(&mut v); Expr::ELst(e)} )); // concat  a (b)* -> [a,b..]
    pfn.insert("call".to_string(),Box::new(|mut e| { Expr::F1(pp_fn1(e.swap_remove(0).as_id()),e.swap_remove(2).into()) })); // fn ( exp )
    pfn.insert("f1".to_string(),Box::new(|mut e| { let v = e.pop().unwrap(); Expr::F1(pp_fn1(e.pop().unwrap().as_id()),v.into()) })); // fn expr
    pfn.insert("cnt".to_string(),Box::new(|_| Expr::F1(pp_fn1("count".into()),Box::new(Expr::ID("_i".into()))) )); // count(*)
    pfn.insert("set".to_string(),Box::new(|mut e| Expr::Set(e.swap_remove(1).as_id(),e.pop().unwrap().into()) )); // set name expr
    pfn.insert("rand".to_string(), Box::new(|mut e| { Expr::F2(pp_fn2("rand".into()),e.swap_remove(2).into(),e.swap_remove(4).into())} )); // rand(s,n)
    pfn.insert("tblv".to_string(),Box::new(|mut e| { // [ name expr, ... ]
        let (e,id): (Vec<Expr>,Vec<Expr>) = e.swap_remove(1).as_elst().into_iter()
            .map(|v| {let mut v = v.as_elst(); (v.pop().unwrap(),v.pop().unwrap())}).unzip();
        Expr::Tbl(id.into_iter().map(|v| v.as_id()).collect(),e) }));
    pfn.insert("nexpr".to_string(),Box::new(|mut e| { // expr ('as'? ID)? -> adjust ID
        let mut id = e.pop().unwrap(); let e = e.pop().unwrap(); 
        if let Expr::Empty = id { id = Expr::ID(match &e { Expr::ID(n) => n.clone(), _ => "".into()})}
        Expr::ELst(vec![e,id])
    }));
    pfn.insert("tbl".to_string(),Box::new(|mut e| {
        let id = e.pop().unwrap(); let t = e.pop().unwrap().as_id();
        Expr::ELst(vec![if let Expr::Empty = id {Expr::ID(t.clone())} else {id},Expr::ID(t)]) })); // ID ('as' ID)? -> (name,tbl)
    pfn.insert("tsel".to_string(),Box::new(|mut e| {
        let id = e.pop().unwrap(); e.pop();
        Expr::ELst(vec![if let Expr::Empty = id {Expr::ID("?".into())} else {id},e.pop().unwrap()]) })); // '(' sel ')' ('as' ID)? -> (name,sel)
    PCtx { rules:map, ppfns:pfn}
}

fn pp_fn2(n:String) -> fn(RVal,RVal) -> RRVal {
    match n.as_ref() {
        "+" => fn_add,
        "-" => fn_mins,
        "*" => fn_mul,
        "/" => fn_div,
        ">" => fn_gt,
        "<" => fn_lt,
        ">=" => fn_gte,
        "<=" => fn_lte,
        "<>" => fn_neq,
        "=" => fn_eq,
        "or" => fn_or,
        "and" => fn_and,
        "rand" => fn_rand,
        _ => unreachable!(),
    }
}

fn pp_fn1(n:String) -> fn(RVal) -> RRVal {
    match n.as_ref() {
        "sum" => fn_sum,
        "avg" => fn_avg,
        "count" => fn_count,
        "min" => fn_min,
        "max" => fn_max,
        "not" => fn_not,
        "-" => fn_neg,
        _ => unreachable!(),
    }
}

fn pp_or(t: &[(Token,i32)], lvl:i32) -> ParseFn {
    if t.len() == 0 {return Box::new(|_,_,i| Some((Expr::Empty,i)))};
    let mut r: Vec<ParseFn> = t.split(|(v,i)| *i == lvl && v.str.as_bytes()[0] == b'|' ).map(|v| pp_and(v,lvl)).collect();
    if 1 == r.len() {r.pop().unwrap()} else {Box::new(move |ctx,toks,idx| r.iter().find_map(|f| f(ctx,toks,idx)))}
}

fn pp_and(t: &[(Token,i32)], lvl:i32) -> ParseFn {
    if t.len() == 0 {return Box::new(|_,_,i| Some((Expr::Empty,i)))};
    let (rules,usr) = pp_val(Vec::<ParseFn>::new(),t,lvl); // internal => recursion is ok
    Box::new(move |ctx,toks,i| {
        let mut j = i; let mut v = Vec::<Expr>::with_capacity(rules.len());
        for r0 in &rules { if let Some((v0,j0)) = r0(ctx,toks,j) {j = j0; v.push(v0)} else {return None} };
        Some((ctx.ppfns[&usr](v),j))
    })
}

fn pp_val(mut v:Vec<ParseFn>, t: &[(Token,i32)], lvl:i32) -> (Vec<ParseFn>,String) {
    if t.len() == 0 { return (v,"default".to_string()) };
    let mut nxt = 0;
    // (...) TOK rname 'str' {ppfn}
    let mut rule:ParseFn = if t[0].1 > lvl {
        if t[0].0.str.as_bytes()[0] == b'{' { return (v,t[1].0.str.to_string()) }; // ppfn at the end
        nxt = (0..t.len()).into_iter().find(|&i| t[i].1 <= lvl).unwrap_or(t.len());
        pp_or(&t[1..nxt],lvl+1) // recursive or
    } else {
        let tk = &t[0].0;
        match tk.kind {
            "STR" => {let s = tk.str[1..tk.str.len()-1].to_string(); Box::new(move |_,tok,i| if i<tok.len() && tok[i].str == s {Some((Expr::ID(tok[i].str.to_string()),i+1))} else {None})},
            "ID" => {
                let s = tk.str.to_string();
                if tk.str.chars().all(|c| c.is_ascii_uppercase())
                    {Box::new(move |ctx,tok,i| if i<tok.len() && tok[i].kind == s {ctx.rules[&s](ctx,tok,i)} else {None})} // token
                    else {Box::new(move |ctx,tok,i| ctx.rules[&s](ctx,tok,i))}},  // subrule
            _ => panic!("unexpected token {:?} in SQL grammar",tk)
        }
    };
    // * + ? modifiers
    if nxt+1 < t.len() {
        nxt+=1;
        rule = match t[nxt].0.str.as_bytes()[0] {
            b'?' => Box::new(move |ctx,tok,i| Some(rule(ctx,tok,i).unwrap_or((Expr::Empty,i)))),
            b'*' => Box::new(move |ctx,tok,i| {let (e,i) = plst(&rule,ctx,tok,i); Some((Expr::ELst(e),i))}),
            b'+' => Box::new(move |ctx,tok,i| {let (e,i) = plst(&rule,ctx,tok,i); if 0<e.len() {Some((Expr::ELst(e),i))} else {None}}),
            _ => {nxt-=1; rule}
        }
    };
    v.push(rule);
    pp_val(v,&t[std::cmp::Ord::min(t.len(),nxt+1)..],lvl) // next rule
}

fn plst(rule:&ParseFn, ctx:&PCtx, tok:&[Token], i: usize) -> (Vec<Expr>,usize) {
    let mut j = i; let mut v:Vec<Expr> = Vec::new();
    while let Some((e,i)) = rule(ctx,tok,j) {j=i; v.push(e)};
    (v,j)
}


// v as an iterator is more complicated and not needed
fn distinct<T: std::hash::Hash + Eq + Clone>(v:&[T]) -> Vec<T> {
    use std::collections::HashSet;
    let mut h: HashSet<&T> = HashSet::with_capacity(v.len()/4);
    return v.iter().filter(|itm| h.insert(itm)).map(|itm| itm.clone()).collect();
}
fn find1<T:PartialEq>(v:&[T], a:&T) -> usize { for (i,b) in v.iter().enumerate() {if b == a {return i}}; v.len() }
fn findn<T:PartialEq>(v:&[T], a:&[T]) -> Vec<usize> { a.iter().map(|b| find1(v,b)).collect() }
fn til(a:usize) -> Vec<usize> { (0..a).into_iter().collect() }
fn sidxn1<T:Clone>(v:&mut[T], ix:&[usize], e:&T) { for &i in ix { v[i] = e.clone() }}
fn lt1<T:Ord+Copy>(v:&[T],a:T) -> Vec<bool> { v.iter().map(|b| *b<a).collect() }
fn wh(v:&[bool]) -> Vec<usize> {v.iter().enumerate().filter_map(|(i,&b)| if b {Some(i)} else {None}).collect()}

macro_rules! fn_op2 {
    ($n:ident,$op:path) => {
        fn $n(a:RVal, b:RVal) -> RRVal {
            match (&*a,&*b) {
                (Val::I(i1),Val::I(i2)) => Ok(Val::I($op(*i1,*i2)).into()),
                (Val::I(i1),Val::D(i2)) => Ok(Val::D($op(*i1 as f64,*i2)).into()),
                (Val::D(i1),Val::I(i2)) => Ok(Val::D($op(*i1,*i2 as f64)).into()),
                (Val::D(i1),Val::D(i2)) => Ok(Val::D($op(*i1,*i2)).into()),
                (Val::I(i1),Val::II(i2)) => Ok(Val::II(i2.iter().map(|v| $op(*i1,*v)).collect()).into()),
                (Val::II(i1),Val::I(i2)) => Ok(Val::II(i1.iter().map(|v| $op(*v,*i2)).collect()).into()),
                (Val::D(i1),Val::DD(i2)) => Ok(Val::DD(i2.iter().map(|v| $op(*i1,*v)).collect()).into()),
                (Val::DD(i1),Val::D(i2)) => Ok(Val::DD(i1.iter().map(|v| $op(*v,*i2)).collect()).into()),
                (Val::I(i1),Val::DD(i2)) => Ok(Val::DD(i2.iter().map(|v| $op(*i1 as f64,*v)).collect()).into()),
                (Val::II(i1),Val::D(i2)) => Ok(Val::DD(i1.iter().map(|v| $op(*v as f64,*i2)).collect()).into()),
                (Val::D(i1),Val::II(i2)) => Ok(Val::DD(i2.iter().map(|v| $op(*i1,*v as f64)).collect()).into()),
                (Val::DD(i1),Val::I(i2)) => Ok(Val::DD(i1.iter().map(|v| $op(*v,*i2 as f64)).collect()).into()),
                (Val::II(i1),Val::II(i2)) => Ok(Val::II(i1.iter().zip(i2.iter()).map(|(v1,v2)| $op(*v1,*v2)).collect()).into()),
                (Val::DD(i1),Val::DD(i2)) => Ok(Val::DD(i1.iter().zip(i2.iter()).map(|(v1,v2)| $op(*v1,*v2)).collect()).into()),
                (Val::II(i1),Val::DD(i2)) => Ok(Val::DD(i1.iter().zip(i2.iter()).map(|(v1,v2)| $op(*v1 as f64,*v2)).collect()).into()),
                (Val::DD(i1),Val::II(i2)) => Ok(Val::DD(i1.iter().zip(i2.iter()).map(|(v1,v2)| $op(*v1,*v2 as f64)).collect()).into()),
                _ => Result::Err("type".into())
            }
        }
    };
}

fn_op2!(fn_add,std::ops::Add::add);
fn_op2!(fn_mins,std::ops::Sub::sub);
fn_op2!(fn_mul,std::ops::Mul::mul);
fn_op2!(fn_div2,std::ops::Div::div);
fn fn_div(a:RVal, b:RVal) -> RRVal { 
    match (&*a,&*b) {
        (Val::I(i1),Val::I(i2)) => Ok(Val::D(*i1 as f64 / *i2 as f64).into()),
        (Val::I(i1),Val::II(i2)) => Ok(Val::DD(i2.iter().map(|v| *i1 as f64 / *v as f64).collect()).into()),
        (Val::II(i1),Val::I(i2)) => Ok(Val::DD(i1.iter().map(|v| *v as f64 / *i2 as f64).collect()).into()),
        (Val::II(i1),Val::II(i2)) => Ok(Val::DD(i1.iter().zip(i2.iter()).map(|(v1,v2)| *v1 as f64 / *v2 as f64).collect()).into()),
        _ => fn_div2(a,b)
    }
}
fn fn_min2<T:PartialOrd>(a:T, b:T) -> T { if a>b {b} else {a}}
fn_op2!(fn_and,fn_min2);
fn fn_max2<T:PartialOrd>(a:T, b:T) -> T { if a>b {a} else {b}}
fn_op2!(fn_or,fn_max2);

macro_rules! fn_cop2 {
    ($n:ident,$op:path) => {
        fn $n(a:RVal, b:RVal) -> RRVal {
            match (&*a,&*b) {
                (Val::I(i1),Val::I(i2)) => Ok(Val::I($op(i1,i2)as i64).into()),
                (Val::I(i1),Val::D(i2)) => Ok(Val::I($op(&(*i1 as f64),i2)as i64).into()),
                (Val::D(i1),Val::I(i2)) => Ok(Val::I($op(i1,&(*i2 as f64))as i64).into()),
                (Val::D(i1),Val::D(i2)) => Ok(Val::I($op(i1,i2)as i64).into()),
                (Val::I(i1),Val::II(i2)) => Ok(Val::II(i2.iter().map(|v| $op(i1,v)as i64).collect()).into()),
                (Val::II(i1),Val::I(i2)) => Ok(Val::II(i1.iter().map(|v| $op(v,i2)as i64).collect()).into()),
                (Val::D(i1),Val::DD(i2)) => Ok(Val::II(i2.iter().map(|v| $op(i1,v)as i64).collect()).into()),
                (Val::DD(i1),Val::D(i2)) => Ok(Val::II(i1.iter().map(|v| $op(v,i2)as i64).collect()).into()),
                (Val::I(i1),Val::DD(i2)) => Ok(Val::II(i2.iter().map(|v| $op(&(*i1 as f64),v)as i64).collect()).into()),
                (Val::II(i1),Val::D(i2)) => Ok(Val::II(i1.iter().map(|v| $op(&(*v as f64),i2)as i64).collect()).into()),
                (Val::D(i1),Val::II(i2)) => Ok(Val::II(i2.iter().map(|v| $op(i1,&(*v as f64))as i64).collect()).into()),
                (Val::DD(i1),Val::I(i2)) => Ok(Val::II(i1.iter().map(|v| $op(v,&(*i2 as f64))as i64).collect()).into()),
                (Val::II(i1),Val::II(i2)) => Ok(Val::II(i1.iter().zip(i2.iter()).map(|(v1,v2)| $op(v1,v2)as i64).collect()).into()),
                (Val::DD(i1),Val::DD(i2)) => Ok(Val::II(i1.iter().zip(i2.iter()).map(|(v1,v2)| $op(v1,v2)as i64).collect()).into()),
                (Val::II(i1),Val::DD(i2)) => Ok(Val::II(i1.iter().zip(i2.iter()).map(|(v1,v2)| $op(&(*v1 as f64),v2)as i64).collect()).into()),
                (Val::DD(i1),Val::II(i2)) => Ok(Val::II(i1.iter().zip(i2.iter()).map(|(v1,v2)| $op(v1,&(*v2 as f64))as i64).collect()).into()),
                (Val::S(i1),Val::S(i2)) => Ok(Val::I($op(i1,i2)as i64).into()),
                (Val::S(i1),Val::SS(i2)) => Ok(Val::II(i2.par_iter().map(|v| $op(i1,v)as i64).collect()).into()),
                (Val::SS(i1),Val::S(i2)) => Ok(Val::II(i1.par_iter().map(|v| $op(v,i2)as i64).collect()).into()),
                (Val::SS(i1),Val::SS(i2)) => Ok(Val::II(i1.par_iter().zip(i2.par_iter()).map(|(v1,v2)| $op(v1,v2)as i64).collect()).into()),
                _ => Result::Err("type".into())
            }
        }
    };
}

fn_cop2!(fn_eq,std::cmp::PartialEq::eq);
fn_cop2!(fn_neq,std::cmp::PartialEq::ne);
fn_cop2!(fn_gt,std::cmp::PartialOrd::gt);
fn fn_lt(a:RVal, b:RVal) -> RRVal { fn_gt(b,a) }
fn_cop2!(fn_gte,std::cmp::PartialOrd::ge);
fn fn_lte(a:RVal, b:RVal) -> RRVal { fn_gte(b,a) }

fn fn_rand(s:RVal, num:RVal) -> RRVal {
    if let (Val::S(ty),Val::I(n)) = (&*s,&*num) {
        use rand::Rng;
        let rng = rand::thread_rng();
        if *n<=0 {return Result::Err("domain".into())}
        let ri = |l1:i64,l2:i64| -> RRVal { 
            let rng = rand::thread_rng();
            let s: Vec<i64> = rng.sample_iter(rand::distributions::Uniform::from(l1..l2)).take(*n as usize).collect();
            Ok(Val::II(s).into())
        };
        if ty == "s" {
            let v = ["apple","msft","ibm","bp","gazp","google","fb","abc"];
            let s: Vec<String> = rng.sample_iter(rand::distributions::Uniform::from(0..v.len())).map(|i| v[i].to_string()).take(*n as usize).collect();
            return Ok(Val::SS(s).into());
        } else if ty == "i" { return ri(0,100)
        } else if ty == "i3" { return ri(0,3)
        } else if ty == "i4" { return ri(1,4)
        } else {
            let s: Vec<f64> = rng.sample_iter(rand::distributions::Open01).map(|f:f64| 100.0*f).take(*n as usize).collect();
            return Ok(Val::DD(s).into());
        }
    };
    Result::Err("type".into())
}

fn fn_sum(a:RVal) -> RRVal {
    match &*a {
        Val::I(_) => Ok(a.clone()),
        Val::II(v) => Ok(Val::I(v.into_iter().sum()).into()),
        Val::D(_) => Ok(a.clone()),
        Val::DD(v) => Ok(Val::D(v.into_iter().sum()).into()),
        _ => Result::Err("type".into())
    }
}
fn fn_avg(a:RVal) -> RRVal { 
    match &*a {
        Val::I(_) => Ok(a.clone()),
        Val::II(v) => Ok(Val::D(v.into_iter().sum::<i64>() as f64 / v.len() as f64).into()),
        Val::D(_) => Ok(a.clone()),
        Val::DD(v) => Ok(Val::D(v.into_iter().sum::<f64>() / v.len() as f64).into()),
        _ => Result::Err("type".into())
    }
}
fn fn_count(a:RVal) -> RRVal {
    match &*a {
        Val::I(_) => Ok(Val::I(1).into()),
        Val::II(v) => Ok(Val::I(v.len() as i64).into()),
        Val::D(_) => Ok(Val::I(1).into()),
        Val::DD(v) => Ok(Val::I(v.len() as i64).into()),
        Val::S(_) => Ok(Val::I(1).into()),
        Val::SS(v) => Ok(Val::I(v.len() as i64).into()),
        Val::TBL(v) => Ok(Val::I(v.v[0].len() as i64).into()),
        _ => Result::Err("type".into())
    }
}
fn fn_min(a:RVal) -> RRVal {
    match &*a {
        Val::I(_) => Ok(a.clone()),
        Val::II(v) => Ok(Val::I(if let Some(m) = v.iter().min() {*m} else {i64::MAX}).into()),
        Val::D(_) => Ok(a.clone()),
        Val::DD(v) => Ok(Val::D(if 0<v.len() {v.iter().fold(f64::MAX,|m,i| m.min(*i))} else {f64::NAN}).into()),
        _ => Result::Err("type".into())
    }
}
fn fn_max(a:RVal) -> RRVal { 
    match &*a {
        Val::I(_) => Ok(a.clone()),
        Val::II(v) => Ok(Val::I(if let Some(m) = v.iter().max() {*m} else {i64::MIN}).into()),
        Val::D(_) => Ok(a.clone()),
        Val::DD(v) => Ok(Val::D(if 0<v.len() {v.iter().fold(f64::MIN,|m,i| m.max(*i))} else {f64::NAN}).into()),
        _ => Result::Err("type".into())
    }
}
fn fn_not(a:RVal) -> RRVal {
    match &*a {
        Val::I(i) => Ok(Val::I((*i==0) as i64).into()),
        Val::II(v) => Ok(Val::II(v.iter().map(|i| (*i==0) as i64).collect()).into()),
        _ => Result::Err("type".into())
    }
}
fn fn_neg(a:RVal) -> RRVal { 
    match &*a {
        Val::I(i) => Ok(Val::I(-i).into()),
        Val::II(v) => Ok(Val::II(v.iter().map(|i| -i).collect()).into()),
        Val::D(i) => Ok(Val::D(-i).into()),
        Val::DD(v) => Ok(Val::DD(v.iter().map(|i| -i).collect()).into()),
        _ => Result::Err("type".into())
    }
}
fn fn_idx(a:RVal, idx: usize) -> RRVal { 
    match &*a {
        Val::II(v) => Ok(Val::I(v[idx]).into()),
        Val::DD(v) => Ok(Val::D(v[idx]).into()),
        Val::SS(v) => Ok(Val::S(v[idx].clone()).into()),
        _ => Result::Err("type".into())
    }
}
fn fn_idxn(a:RVal, idx: &Vec<usize>) -> RRVal { 
    match &*a {
        Val::II(v) => Ok(Val::II(idx.iter().map(|i| v[*i]).collect()).into()),
        Val::DD(v) => Ok(Val::DD(idx.iter().map(|i| v[*i]).collect()).into()),
        Val::SS(v) => Ok(Val::SS(idx.iter().map(|i| v[*i].clone()).collect()).into()),
        _ => Result::Err("type".into())
    }
}

fn main() -> std::io::Result<()> {
    let l = lexer();
    let p = parser(&l);
    let mut ectx = ECtx::new();

    ectx.eval(p.parse(&l("set t [ a rand('i', 100), b rand('f',100)]"))).unwrap();
    ectx.eval(p.parse(&l("set t2 [ a rand('i', 100), c rand('f',100)]"))).unwrap();

    ectx.eval(p.parse(&l("set bt [sym rand('s',10000000), size rand('i', 10000000), price rand('f', 10000000)]"))).unwrap();
    ectx.eval(p.parse(&l("set ref [sym rand('s', 100), size rand('i', 100), info rand('f',100)]"))).unwrap();
    ectx.eval(p.parse(&l("select sym,size,max(info) as info into res from ref where size<50 group by sym,size"))).unwrap();
    // select sym,size,count(*),avg(price) into r from bt group by sym,size
    // select * from (select sym,size,count(*),avg(price) into r from bt where price>10.0 group by sym,size) as t1 join ref on t1.sym=ref.sym, t1.size = ref.size
    // select * from (select sym,size,count(*),avg(price) into r from bt where price>10.0 and sym='fb' group by sym,size) as t1 join ref on t1.sym=ref.sym, t1.size = ref.size

    loop {
        use std::io::Write;
        let mut buffer = String::new();
        print!(">"); std::io::stdout().flush()?;
        std::io::stdin().read_line(&mut buffer)?;
        let s = buffer.trim();
        if s == "quit" {break} else if s.len() == 0 {continue};
        let tm = std::time::Instant::now();
        let e = ectx.eval(p.parse(&l(s)));
        println!("Time: {:?}",tm.elapsed());
        match e {
            Err(e) => println!("Error: {}",e),
            Ok(e) => println!("{}",e),
        }
    }
    Ok(())
}
// HashMap BTreeMap FnvHashMap
// 10m  3.35 4.39 3.08
// 100m 44   53.4 40