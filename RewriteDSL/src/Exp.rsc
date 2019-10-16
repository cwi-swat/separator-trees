module Exp

import ParseTree;
import String;

layout WS = [\t-\n\r\ ]*; // <1>
    
lexical IntegerLiteral = [0-9]+;
lexical Ident = [a-z A-Z 0-9 _] !<< [a-z A-Z][a-z A-Z 0-9 _]* !>> [a-z A-Z 0-9 _];

start syntax Exp
  = con: IntegerLiteral lit
  | bracket br: "(" Exp e ")"
  | fcall: Ident fname "(" {Exp ","}* args ")"
  > left mul: Exp l "*" Exp r        
  > left add: Exp l "+" Exp r
  ;

data Expr
  = con(int i, loc origin)
  | br(Expr e, loc origin)
  | call(Id name, list[Expr] args, loc origin)
  | mul(Expr l, Expr r, loc origin)
  | add(Expr l, Expr r, loc origin)
  ;
data Id = id(str name, loc origin);

//Expr implode(c:con(l)) = con(intLit(toInt("<l>")), c@\loc);
Expr implode(c:con(l)) = con(toInt("<l>"), c@\loc);
Expr implode(b:br(e)) = br(implode(e), b@\loc);
Expr implode(m:mul(l, r)) = mul(implode(l), implode(r), m@\loc);
Expr implode(a:add(l, r)) = add(implode(l), implode(r), a@\loc);
Expr implode(f:fcall(name, args)) = call(id("<name>", name@\loc),  [implode(arg) | arg <- args], f@\loc);
