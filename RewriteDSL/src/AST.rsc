module AST

import Exp;
import IO;
import ParseTree;
import String;
import Syntax;
import util::Math;

data Value
  = tree(str cons, list[Value] args, list[str] seps)
  | literal(value val, str src)
  | listval(list[Value] elts, list[str] seps, str sep = "")
  ;
  
data Rewriter = rewriter(list[Rule] rules);

data Rule = rule(Pattern pattern, Str s);

data Pattern
  = cons(str name, list[Pattern] args)
  | pvar(str name)
  | listvar(str name)
  | val(int n)
  | val(str s)
  | lst(list[Pattern] elts)
  | hol()
  ;

data Str = string(list[Elt] elts);

void foo(Value v) {
  visit (v) {
    case "hoi" => "foo"
  }
}

data Elt
  = txt(str lit)
  | var(str name)
  | lvar(str name)
  ;
  
Rewriter implode(Syntax program) = rewriter([implode(rule) | SRule rule <- program.rules]);
Rule implode(SRule r) = rule(implode(r.lhs), implode(r.rhs));
Pattern implode(Lhs lhs) {
  if (lhs is cons)
    return cons("<lhs.cons>", [implode(arg) | arg <- lhs.args]);
  if (lhs is var)
    return pvar("<lhs.var>");
  if (lhs is intLit)
    return val(toInt("<lhs.intLit>"));
  if (lhs is strLit)
    return val("<lhs.strLit>");
  if (lhs is lst)
    return lst([implode(elt) | elt <- lhs.elts]);
  if (lhs is hol)
    return hol();
  if (lhs is lvar)
    return listvar("<lhs.var>");
  throw "Cannot happen";
}
Str implode(Rhs rhs)
  = string({for (part <- rhs.parts) {
    if (part is txt) {
      append txt("<part.txt>");
    } else if (part is var) {
      append var("<part.v.name>");
    } else if (part is lvar) {
      append lvar("<part.v.name>");
    } else {
      throw "Cannot happen";
    }
  }});

//Example rules
public Syntax spec = (Syntax)`rule br(con(Y)) =\> "\<Y\>"
                             'rule add(X, X) =\> "2 *      \<X\>"
                             'rule add(X, con(0)) =\> "\<X\>"
                             'rule add(con(0), X) =\> "\<X\>"
                             'rule mul(con(0), _) =\> "0"
                             'rule mul(_, con(0)) =\> "0"
                             'rule br(br(E)) =\> "(\<E\>)"`;
public Syntax distribute = (Syntax)`rule mul(con(X), br(add(con(A), con(B)))) =\> "\<X\> * \<A\> + \<X\> * \<B\>"`;
public Syntax dedistribute = (Syntax)`rule add(mul(con(X),con(A)),mul(con(X),con(B))) =\> "\<X\> * (\<A\> + \<B\>)"`;
public Syntax listSpec = (Syntax)`rule call(N, [X*, Y*, Z*, B, con(1), A*]) =\> "\<N\>(\<Z*\>, \<Y*\>, \<X*\>, \<B\>, 2, \<A*\>)"`;
public Syntax listSpec2 = (Syntax)`rule call(N, [Pre*, con(1), Post*]) =\> "\<N\>(\<Pre*\>, 2, \<Post*\>)"`;

public loc exampleFile = |project://RewriteDSL/src/example.exp|;

map[loc, str] srcCache = ();//TODO: make not global

void foo() = rewrite(exampleFile, parse(#Syntax, |project://RewriteDSL/src/rules.rewr|));
void rewrite() = rewrite(exampleFile, listSpec2);
void rewrite(Syntax spec) = rewrite(exampleFile, spec);
void rewrite(loc file, Syntax spec, Value (str src, loc file) toValue = toValue) {
  src = readFile(file);
  ast = toValue(src, file);
  oldAst = ast;
  int i = -1;
  rules = implode(spec).rules;
  srcCache = ();//TODO: remove if not global anymore
  main: do {
    i = i + 1;
    println("iteration <i>");
    println(toString(ast));
    oldAst = ast;
    for (rule <- rules) {
      try {
        <subtree, vars> = match(rule.pattern, ast, ());
        
        replacementSrc = substitute(rule.s, vars);
        cacheLoc = |cache://<"<i>">|;
        srcCache += (cacheLoc : replacementSrc);
        replacementAst = toValue(replacementSrc, cacheLoc);
        
        ast = replaceSubtree(ast, subtree, replacementAst);
        continue main;
      } catch Backtrack(): {
        //println("Rule failed, next");
        ;
      } catch NYI(msg): {
        println("NYI: <msg>, continuing");
      } catch value v: {
        println("BOO");
        iprintln(v);
      }
    }
  } while (ast != oldAst);
  println("Done, <i> rewrites");
}

&T <: node replaceSubtree(&T <: node ast, &S <: node toReplace, &S <: node replacement)
  = bottom-up-break visit (ast) {
    case toReplace => replacement
  };

str substitute(Str s, map[str, Value] variables) {
  result = "";
  removeSeparator = "";
  for (i <- [0..size(s.elts)]) {
    e = s.elts[i];
    if (txt(str t) := e) {
      if (startsWith(t, removeSeparator)) {
        result += t[size(removeSeparator)..];
      } else {
        result += t;
      }
      removeSeparator = "";
    } else if (var(str v) := e) {
      boundValue = variables[v];
      result += toString(boundValue);
      removeSeparator = "";
    } else if (lvar(str v) := e) {
      boundValues = variables[v].elts;
      sep = variables[v].sep;
      if (boundValues == []) {
        if (result[-size(sep)..] == sep) {//remove separator before if present
          result = result[..-size(sep)];
          removeSeparator = "";
        } else {
          removeSeparator = sep;
        }
        continue;
      }
      result += toString(variables[v]);
    }
  }
  return result;
}

data MatchException = Backtrack() | Failed() | NYI(str msg);

tuple[Value subtree, map[str, Value] vars] match(Pattern pattern, Value val, map[str, Value] boundVariables) {
  switch (pattern) {
    case cons(name,args): {
      if (val is tree) {
        try {
          if (val.cons == name && size(val.args) == size(args)) {
            //constructor name and arity match, check children
            vars = boundVariables;
            for (i <- [0..size(args)]) {
              vars += match_aux(args[i], val.args[i], vars);
            }
            return <val, vars>;
          }
        } catch Failed(): ;
        //recurse to find pattern in children
        for (i <- [0..size(val.args)]) {
          try {
            return match(pattern, val.args[i], boundVariables);
          } catch Backtrack():;
        }
      } else if (val is listval) {
        for (i <- [0..size(val.elts)]) {
          try {
            return match(pattern, val.elts[i], boundVariables);
          } catch Backtrack():;
        }
      }
    }
  }
  throw Backtrack();
}

map[str, Value] match_aux(Pattern pattern, Value val, map[str, Value] boundVariables) {
  switch (pattern) {
    case cons(name, args): {
      if (!(val is tree) || val.cons != name || size(val.args) != size(args)) {
        throw Failed();
      }
      //constructor name and arity match, check children
      for (i <- [0..size(args)]) {
        boundVariables += match_aux(args[i], val.args[i], boundVariables);
      }
      return boundVariables;
    }
    case hol() : {//always matches
      return boundVariables;
    }
    case pvar(varName) : {
      if (varName notin boundVariables) {//unbound variable, add binding
        return boundVariables + (varName : val);
      }
      boundValue = boundVariables[varName];//bound variable, check values
      if (matchValues(boundValue, val)) {
        return boundVariables;
      }
      throw Failed(); 
    }
    case val(value v): {
      if (literal(v,_) := val) {//compare values
        return boundVariables;
      }
      throw Failed();
    }
    case lst(elts): {
      if (val is listval) {
        try {
          return match_list(pattern, val, boundVariables, sep = val.sep);
        } catch Backtrack():;
      }
      throw Failed();
    }
    default: throw "Missed pattern <pattern>";
  }
}

map[str, Value] match_list(Pattern p, Value v, map[str, Value] boundVariables, str sep = "") {
  assert p is lst;
  assert v is listval;
  list[Pattern] pattern = p.elts;
  list[Value] val = v.elts;
  if (pattern == [] && val == []) {
    return boundVariables;
  }
  if (pattern == [] && val != []) {
    throw Backtrack();
  }
  switch (pattern[0]) {
    case cons(name, args): {
      if (val == [] || val[0].cons != name || size(val[0].args) != size(args)) {
        throw Backtrack();
      }
      try {
        for (i <- [0..size(args)]) {
          boundVariables += match_aux(args[i], val[0].args[i], boundVariables);
        }
        return match_list(lst(tail(pattern)), listval(tail(val), v.seps[1..], sep = v.sep), boundVariables, sep = sep);
      } catch Failed(): ;
      throw Backtrack() ;
    }
    case pvar(varName): {
      if (val == []) {
        throw Backtrack();
      }
      if (varName notin boundVariables) {
        return match_list(lst(tail(pattern)), listval(tail(val), v.seps[1..], sep = v.sep), boundVariables + (varName : val[0]), sep = sep);
      } else if (true) throw NYI("Non-linear matching");
      throw Backtrack();
    }
    case val(value l): {
      if (literal(l,_) := val[0]) {
        return match_list(lst(tail(pattern)), listval(tail(val), v.seps[1..], sep = v.sep), boundVariables, sep = sep);
      }
      throw Backtrack();
    }
    case listvar(varName): {
      if (varName in boundVariables) {
        throw NYI("Non-linear matching");
      }
      for (i <- [0..size(val)+1]) {
        try {
          return match_list(
                   lst(tail(pattern)),
                   listval(val[i..], v.seps[i..], sep = v.sep),
                   boundVariables + (varName : listval(val[..i], v.seps[..max(0,i-1)], sep = v.sep)),
                   sep = sep);
        } catch MatchException _: {
          continue;
        }
      }
      throw Backtrack();
    }
    default: throw "Missed list pattern <pattern>";
  }
}

bool matchValues(Value l, Value r) {
  if (l is tree && r is tree && l.cons == r.cons && size(l.args) == size(r.args)) {
    return (true | it && matchValues(l.args[i],r.args[i]) | i <- [0..size(l.args)]);
  }
  if (literal(ll,_) := l && literal(rr,_) := r) {
    return ll := rr;
  }
  if (listval(lelts, _) := l && listval(relts, _) := r) {
    if (size(lelts) != size(relts)) {
      return false;
    }
    for (i <- [0..size(lelts)]) {
      lelt = lelts[i];
      relt = relts[i];
      return matchValues(lelt, relt);
    }
    return (size(l.elts) == size(r.elts) | it && matchValues(l.elts[i],r.elts[i]) | i <- [0..size(l.elts)]);
  }
  return false;
}


str toString(t:tree(cons,args,seps)) {
  result = seps[0];
  i = 1;
  if (args != []) {
    for (k <- [0..size(args)-1]) {
      result += toString(args[k]);
      result += seps[i];
      i = i + 1;
    }
    result += toString(args[-1]);
  }
  assert i == size(seps) - 1;
  result += seps[i];
  return result;
}
str toString(literal(_,src)) {
  return src;
}
str toString(listval(elts,seps)) {
  if (elts == []) {
    return "";
  }
  return (toString(elts[0]) | it + seps[i] + toString(elts[i+1]) | i <- [0..size(seps)]);
}

str readSrc(loc l) {
  if (l.scheme != "cache") {
    return readFile(l);
  }
  return srcCache[l.top][l.offset..l.offset+l.length];
}

loc makeLoc(loc l, int offset, int length) = l.top[offset=offset][length=length];

Value toValue(str src, loc l) = toValue(implode(parse(#Exp, src, l)));
Value toValue(con(i, origin)) = tree("con", [literal(i, "<i>")], ["",""]);
Value toValue(br(e, origin)) {
  before = readSrc(makeLoc(origin,origin.offset,e.origin.offset-origin.offset));
  after = readSrc(makeLoc(origin,e.origin.offset+e.origin.length,origin.offset+origin.length-e.origin.offset-e.origin.length));
  return tree("br", [toValue(e)], [before, after]);
}
Value toValue(mul(l, r, origin)) {
  before = readSrc(makeLoc(origin,origin.offset,l.origin.offset-l.origin.offset));
  between = readSrc(makeLoc(origin,l.origin.offset+l.origin.length,r.origin.offset-l.origin.offset-l.origin.length));
  after = readSrc(makeLoc(origin,r.origin.offset+r.origin.length,origin.offset+origin.length-r.origin.offset-r.origin.length));
  return tree("mul", [toValue(l), toValue(r)], [before,between,after]);
}
Value toValue(add(l, r, origin)) {
  before = readSrc(makeLoc(origin,origin.offset,l.origin.offset-l.origin.offset));
  between = readSrc(makeLoc(origin,l.origin.offset+l.origin.length,r.origin.offset-l.origin.offset-l.origin.length));
  after = readSrc(makeLoc(origin,r.origin.offset+r.origin.length,origin.offset+origin.length-r.origin.offset-r.origin.length));
  return tree("add", [toValue(l), toValue(r)], [before,between,after]);
}
Value toValue(call(name, args, origin)) {
  before = readSrc(makeLoc(origin,origin.offset,name.origin.offset-name.origin.offset));
  if (args == []) {
    after = readSrc(makeLoc(origin,name.origin.offset+name.origin.length,origin.offset+origin.length-name.origin.offset-name.origin.length));
    return tree("call", [toValue(name), listval([], [], sep = ", ")], [before, after]);
  }
  elts = [toValue(arg) | arg <- args];
  seps = for (i <- [0..max(0,size(args)-1)]) {
    src = args[i].origin;
    src = src[offset=src.offset+src.length];
    src = src[length=args[i+1].origin.offset-src.offset];
    append readSrc(src);
  }
  between = readSrc(makeLoc(origin,name.origin.offset+name.origin.length,args[0].origin.offset-name.origin.offset-name.origin.length));
  after = readSrc(makeLoc(origin,args[-1].origin.offset+args[-1].origin.length,origin.offset+origin.length-args[-1].origin.offset-args[-1].origin.length));
  return tree("call", [toValue(name), listval(elts, seps, sep = ", ")], [before, between, after]);
}
Value toValue(id(n, _)) = literal(n, "<n>");

