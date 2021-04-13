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