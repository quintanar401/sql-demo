// Lexer
cgrp:("\t \r\n";.Q.n;.Q.a,.Q.A),"\\\"=<>.'";
c2grp:128#0; c2grp[`long$cgrp]:1+til count cgrp;

fsa: ("aA A a0.";"0I I 0";"0I F .";"F F 0";
    "= E =";"> E =";"< E =";"< E >";
    "\" S *";"S S *";"S R \"";"S T \\";"\" R \"";"\" T \\";"T S *";
    "' U *";"U U *";"U V '";"V U '";"' V '";"\tW W \t");
fsa:" "vs/:fsa;

states:distinct " ",(first each grp),raze fsa[;1];
fsa:{yst:states?y; x[yst 0;(yst 2;til 1+count cgrp)"*" in y 2]:first yst 1;x}/[(count states;cnt)#til cnt:1+count cgrp;fsa];
state2name:(states?"a0\"'\t")!("ID";"NUM";"STR";"STR";"WS");
lex:{i:where (st:fsa\[0;c2grp x])<states?"A"; {x[;where not "WS"~/:x 0]} (state2name st i;i cut x)};

// Parser generator
plex:{f;ip x,enlist {sums(neg x0 in ")}")+(x0:x[;0])in "({"} last x:lex x};
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
sql[`expr2]: pptop "expr3 (('=' {=}|'<>' {<>}|'<=' {<=}|'>=' {>=}|'>' {>}|'<' {<}) expr2)? {mke2 x}";
sql[`expr3]: pptop "expr4 (('+' {+}|'-' {-}) expr3)? {mke2 x}";
sql[`expr4]: pptop "vexpr (('*' {*}|'/' {%}) expr4)? {mke2 x}";
sql[`vexpr: pptop "'(' expr ')' {x 1} | '-' expr {f1} {(neg;x 1)}| call {x 0}| name {x 0}| STR {neg[1]_1_x 0}| NUM {value x 0}";
sql[`name]: pptop "ID {x 0}";
sql[`call]: pptop "('sum'|'avg'|'count'|'min'|'max') '(' expr ')' {(value x[0;0];x 2)} | 'count' '(' '*' ')' {(count;\"_i\")}";
sql[`elst]: pptop "expr (',' expr)* {mke3 x}";

sql[`sel]: pptop "'select' 'distinct'? sexpr ('into' name {x 1})? 'from' join ('where' expr {x 1})? ('group' 'by' elst {x 2})? {mksel x}";
sql[`sexpr]: pptop "'*' {()}| nexpr (',' nexpr)* {mknm x}";
sql[`nexpr]: pptop "expr ('as'? name {x 1})? {($[count x 1;x 1;10=type x 0;x 0;\"\"];x 0)}";
sql[`join]: pptop "tbl ('join' tbl 'on' jelst {x 1 3})* {(x 0;x[1][;0];x[1][;1])}";
sql[`jexpr]: pptop "name '=' name {x 0 2}";
sql[`jelst]: pptop "jexpr (',' jexpr)* {mke3 x}";
sql[`tbl: pptop "name ('as' name)? {($[count x 1;x[1;1];x 0];x 0)}| '(' sel ')' ('as' name)? {($[count x 3;x[3;1];`];x 1)}";
// helpers
mke1:{$[count y 1;(x;y 0;y[1;1]);y 0]}; // f[x;y] or x
mke2:{$[count x 1;(x[1;0];x 0;x[1;1]);x 0]}; // f[x;y] or x
mke3:{(1#x),$[count x 1;x[1][;1];()]}; // a,b,c -> [a;b;c]
mksel:{`d`s`in`j`w`g!x 1 2 3 5 6 7};
mknm:{x:flip mke3 x;(nfix x 0)!x 1}; // name!expr