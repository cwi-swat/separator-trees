module Syntax

extend lang::std::Layout;

lexical SId = [a-z A-Z 0-9 _] !<< [a-z A-Z][a-z A-Z 0-9 _]* !>> [a-z A-Z 0-9 _];

start syntax Syntax = SRule* rules;

syntax SRule = "rule" Lhs lhs "=\>" Rhs rhs;

syntax Lhs
   = cons: SId cons "(" {Lhs ","}* args ")"
   | var: SId var
   | intLit: [0-9]+ intLit
   | strLit: StrLit strLit
   | lst: "[" {Lhs ","}* elts "]"
   | hol: "_"
   | lvar: SId var "*"
   ;

lexical StrLit
  = "\"" Txt "\"";

lexical Txt
  = [A-Za-z0-9()\[\],\ \\+-*/] !<< [A-Za-z0-9()\[\],\ \\+-*/]+ txt !>> [A-Za-z0-9()\[\],\ \\+-*/];

lexical TxtOpt
  = [A-Za-z0-9()\[\],\ \\+-*/] !<< [A-Za-z0-9()\[\],\ \\+-*/]* txt !>> [A-Za-z0-9()\[\],\ \\+-*/];

lexical Rhs = "\"" Part* parts "\"";

lexical Part
  = txt: Txt txt
  | marked: "$" TxtOpt txt "$"
  | var: SVar v
  | lvar: LVar v
  ;

syntax SVar = "\<" SId name "\>";

syntax LVar = "\<" SId name "*" "\>";

