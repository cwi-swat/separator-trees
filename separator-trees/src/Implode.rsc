module Implode

import Node;
import ParseTree;
import Type;
import List;
import IO;

bool isSep(lit(_)) = true;
bool isSep(cilit(_)) = true;
bool isSep(layouts(_)) = true;
default bool isSep(_) = false;

str yield(node n) 
  = yieldArgs(getChildren(n), seps)
  when list[str] seps := getKeywordParameters(n)["seps"];

str yield(<list[value] xs, list[str] seps>)
  = yieldArgs(xs, ["", *seps, ""]);
  
default str yield(value v) = "<v>";
 
str yieldArgs(list[value] xs, list[str] seps)
  = ( seps[0] | it + yield(xs[i]) + seps[i+1] | int i <- [0..size(xs)] );


value implodeSep(aa:appl(regular(Symbol sym), list[Tree] args)) {
  // return <list[elts], list[str] seps

  tuple[list[value], list[str]] makeList(list[Symbol] seps, list[Tree] args) {
    elts = [];
    strSeps = [];
    int i = 0;
    while (i < size(args)) {
      elts += [implodeSep(args[i])];
      i += 1;
      curSep = "";
      if (i < size(args) - 1) {
        for (_ <- [0..size(seps)]) {
          curSep += "<args[i]>";
          i += 1;
        }
        strSeps += [curSep];
      }
    } 
    return <elts, strSeps>;
  }
  
  value makeSeqNode(list[Symbol] symbols, list[Tree] args) {
    elts = [];
    strSeps = [];
    int i = 0;
    
    curSep = "";
    for (int i <- [0..size(args)]) {
      if (isSep(symbols[i])) {
        curSep += "<args[i]>";
      } else {
        strSeps += [curSep];
        curSep = "";
        elts += [implodeSep(args[i])];
      }
    }
    strSeps += [curSep];
    return makeNode(printSymbol(aa.prod.def, false), elts, keywordParameters=("seps": strSeps));
  }
  
  switch (sym) {
    case empty(): 
      return <[], []>;
    
    case opt(Symbol s): {
      if (args == []) {
        return <[], []>;
      }
      assert size(args) == 1;
      return implodeSep(args[0]);
      //return <[ implodeSep(a) | a <- args ], []> ;
    }
    
    case iter(Symbol s): 
      return <[ implodeSep(a) | a <- args ], []> ;
    
    case \iter-star(Symbol s): 
      return <[ implodeSep(a) | a <- args ], []> ;
    
    case \iter-seps(Symbol s, list[Symbol] seps): 
      return makeList(seps, args);
    
    case \iter-star-seps(Symbol s, list[Symbol] seps): 
      return makeList(seps, args);
    
    case \seq(list[Symbol] symbols): 
      return makeSeqNode(symbols, args);
      
    default: throw "Unsupported regular: <sym>";
  }
}

str getName(label(str x, _)) = x;
str getName(sort(str x)) = x;
str getName(lex(str x)) = x;

bool isLex(label(_, Symbol s)) = isLex(s);
default bool isLex(Symbol s) = s is lex || s is lit;

value implodeSep(t:appl(prod(Symbol s, list[Symbol] syms, _), list[Tree] args)) {
  if (isLex(s)) {
    return "<t>";
  }

  // return "<x>"(args, seps=[...])
  list[value] kids = [];
  list[str] seps = [];
  
  curSep = "";
  for (int i <- [0..size(syms)]) {
    if (isSep(syms[i])) {
      curSep += "<args[i]>";
    }
    else {
      seps += [curSep];
      curSep = "";
      kids += [implodeSep(args[i])];
    }
  }
  seps += [curSep];
  
  return makeNode(getName(s), kids, keywordParameters=("seps": seps));
}

  
default value implodeSep(Tree t) {
  throw "Unsupported tree: `<t>`";
}