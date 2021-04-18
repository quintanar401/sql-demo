// Lexer
cgrp:("\t \r\n";.Q.n;.Q.a,.Q.A),"\\\"=<>.'";
c2grp:128#0; c2grp[`long$cgrp]:1+til count cgrp;

fsa: ("aA A a0.";"0I I 0";"0I F .";"F F 0";
    "= E =";"> E =";"< E =";"< E >";
    "\" S *";"S S *";"S R \"";"S T \\";"\" R \"";"\" T \\";"T S *";
    "' U *";"U U *";"U V '";"V U '";"' V '";"\tW W \t");
fsa:" "vs/:fsa;

states:distinct " ",(first each cgrp),raze fsa[;1];
fsa:{yst:states?y; x[yst 0;(yst 2;til 1+count cgrp)"*" in y 2]:first yst 1;x}/[(count states;cnt)#til cnt:1+count cgrp;fsa];
state2name:(states?"a0\"'\t")!("ID";"NUM";"STR";"STR";"WS");
lex:{i:where (st:fsa\[0;c2grp x])<states?"A"; {x[;where not "WS"~/:x 0]} (state2name st i;i cut x)};

// Parser generator
plex:{flip x,enlist {sums(neg x0 in ")}")+(x0:x[;0])in "({"} last x:lex x};
extr:{x:x 1+y+til -1+(y _x[;2])?0; x[;2]-:1; x};
// BNF
pconst:{$[x~lower y[1;z];(z+1;x);()]}; // const like 'select'
ptok:{$[x~y[0;z];(z+1;y[1;z]);()]}; // token like NUM/STR
psub:{sql[x][y;z]}; // subrule like expr
por:{{$[count y;y;z . x]}[(y;z)]/[();x]}; // or like A | B
pand:{v:{$[count y;z[x;y 0];()]}[y]\[(z;());x]; $[()~last v;();(first last v;v[;1])]}; // and like expr '+' expr
popt:{$[count v:x[y;z];v;(z;())]}; // ? like expr?
pmlt:{v:-1_{x[y;z 0]}[x;y]\[count;x[y;z]]; $[count v;(first last v;v[;1]);(z;())]}; // * like expr*
ppls:{v:pmlt[x;y;z]; $[z=v 0;();v]}; // + like expr+
pusr:{[uf;f;t;i] v:f[t;i]; $[count v;(v 0;uf v 1);v]}; // pp func like expr {ppfn}

pptop:{ppor plex x};
ppor:{x:enlist[$[count i;i[0]#x;x]],1_'(i:where (0=x[;2])&x[;1;0]="|")cut x;$[1=count x;ppand x 0;por ppand each x]}; // parse "A | B"
ppand:{v:ppval[x]\[{x>y 0}count x;ppval[x;(0;())]]; $[10=type last v:v[;1];pusr[value last v] pand -1_v;pand v]}; // parse A B C
ppval:{
    if[rec:0<(v:x y:y 0)2; r:extr[x;y]; f:$["("=v[1;0];ppor r;"{",(" "sv r[;1]),"}"]; y+:2+count r];
    if[not rec; f:$["STR"~(v:x y)0;pconst 1_-1_v 1;"ID"~v 0;$[v[1]~upper v 1;ptok v 1;psub `$v 1];'"unexpected"]; y+:1; y];
    if[3>n:"?+*"?x[y][1;0]; f:(popt;ppls;pmlt)[n]f; y+:1];
    (y;f)
 };

// Parser
sql:(`$())!();
sql[`expr]: pptop "expr1 ('or' expr)? {mke1[|;x]}";
sql[`expr1]: pptop "'not' expr1 {(not;x 1)} | expr2 ('and' expr1)? {mke1[&;x]}";
sql[`expr2]: pptop "expr3 (('=' {seq}|'<>' {{not seq x}}|'<=' {<=}|'>=' {>=}|'>' {>}|'<' {<}) expr2)? {mke2 x}";
sql[`expr3]: pptop "expr4 (('+' {+}|'-' {-}) expr3)? {mke2 x}";
sql[`expr4]: pptop "vexpr (('*' {*}|'/' {%}) expr4)? {mke2 x}";
sql[`vexpr] : pptop "'(' expr ')' {x 1} | '-' expr {f1} {(neg;x 1)}| call {x 0}| name {x 0}| STR {({y;x}neg[1]_1_x 0;0)}| NUM {value x 0}";
sql[`name]: pptop "ID {x 0}";
sql[`call]: pptop "('sum'|'avg'|'count'|'min'|'max') '(' expr ')' {(value x[0;0];x 2)} | 'count' '(' '*' ')' {(count;\"_i\")}";
sql[`elst]: pptop "expr (',' expr)* {mke3 x}";

sql[`sel]: pptop "'select' 'distinct'? sexpr ('into' name {x 1})? 'from' join ('where' expr {x 1})? ('group' 'by' elst {x 2})? {mksel x}";
sql[`sexpr]: pptop "'*' {()}| nexpr (',' nexpr)* {mknm x}";
sql[`nexpr]: pptop "expr ('as'? name {x 1})? {($[count x 1;x 1;10=type x 0;x 0;\"\"];x 0)}";
sql[`join]: pptop "tbl ('join' tbl 'on' jelst {x 1 3})* {(x 0;x[1][;0];x[1][;1])}";
sql[`jexpr]: pptop "name '=' name {x 0 2}";
sql[`jelst]: pptop "jexpr (',' jexpr)* {mke3 x}";
sql[`tbl]: pptop "name ('as' name)? {($[count x 1;x[1;1];x 0];x 0)}| '(' sel ')' ('as' name)? {($[count x 3;x[3;1];`];x 1)}";
// helpers
mke1:{$[count y 1;(x;y 0;y[1;1]);y 0]}; // f[x;y] or x
mke2:{$[count x 1;(x[1;0];x 0;x[1;1]);x 0]}; // f[x;y] or x
mke3:{(1#x),$[count x 1;x[1][;1];()]}; // a,b,c -> [a;b;c]
mksel:{`d`s`in`j`w`g!x 1 2 3 5 6 7};
mknm:{x:flip mke3 x;(nfix x 0)!x 1}; // name!expr
nfix:{x[i]:"x",/:string til count i:where ("."in/:x)|""~/:x;x};
seq:{ty:type y; $[10=type x;$[10=ty;x~y;x~/:y];10=ty;x~\:y;0=ty;x~'y;x=y]}; // x=y does not work for strings

// interpreter
kw:("select";"from";"into";"where";"group";"distinct";"by";"join";"on";"as";"or";"and";"not";"sum";"avg";"max";"min";"count");
spar:{x:lex x; if[not count[x 0]~first v:sql[`sel][.[x;(0;where x[1]in kw);{""}];0]; '"error"]; v 1}; // main parse fn
// join
sget:{$[10=type x;get x;sel1 x]}; // get tbl/select
sren:{t:sget x 1; k:(k!v),(n,/:k)!v:(y,n:x[0],"."),/:k:key t; (k;v!value t)}; // rename cols to unique
sjcore:{c:(m:y[0],x 0)z; m[z[;1]]:c[;0]; (m;sidx[sij[x[1]c[;0];y[1]c[;1]];x 1;c[;1]_y 1])}; // join 2 tbls
sjoin:{v:x`j; sjcore/[sren[v 0;"@"];sren'[v 1;string til count v 1];v 2]}; // join all tbls
sij:{j:where count[y 0]>i:$[1=count x;y[0]?x 0;flip[y]?flip x]; (j;i j)}; // get join idx into x and y
sidx:{(y@\:x 0),z@\:x 1}; // concat joined tbls
// select
sel:{sel1 spar x}; // main fn
sel1:{r:sel2 x; if[count x`d; r:(key r)!flip distinct flip value r]; if[count x`in; (`$x`in)set r]; r};
sel2:{[p]
    i:swh[tbl:sjoin p;p`w];
    rmap:v[vi]!key[tbl 0] vi:v?distinct v:value tbl 0;
    if[0=count p`s; p[`s]:{nfix[x]!x} rmap key tbl 1];
    if[count p`g;
        gn:nfix {$[10=type x;x;""]} each p`g;
        :key[p`s]!flip {x[z] each y}[seval[tbl;;gn];value p`s] each sgrp[tbl;i;p`g]];
    (),/:seval[tbl;i;()] each p`s
 };
swh:{[t;w] i:(::); $[count w;where 0<>seval[t;i;();w];i]};
// sgrp:{[t;i;g] i value group flip seval[t;i;()] each g};
sgrp:{[t;i;g] i value group {flip(count[x]#`c)!x} seval[t;i;()] each g};
seval:{[t;i;gn;v] $[10=ty:type v;$[v in key t 0;$[any v~/:gn;first;::] t[1;t[0;v]]i;v~"_i";i;'v];ty in 0 11h;v[0]. .z.s[t;i;gn] each 1_v;v]};

n:10000000; s:("apple";"msft";"ibm";"bp";"gazp";"google";"fb";"abc");
bt:("sym";"size";"price")!(n?s;n?100;n?100.0);
ref:("sym";"size";"price")!(100?s;100?100;100?100.0);
qbt:flip (`$key bt)!value bt;
qref:flip (`$key ref)!value ref;

// select sym,size,count(*),avg(price) into r from bt group by sym,size
// select count i, avg price by sym, size from qbt
// 1.15 vs 1.88
// select * from (select sym,size,count(*),avg(price) into r   from bt where price>10.0 and sym='fb'   group by sym,size)  as t1 join ref on t1.sym=ref.sym, t1.size = ref.size