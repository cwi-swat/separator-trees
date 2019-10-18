module Paper

import List;

/* 
 * Separator trees
 */

data Term
  = cons(str name, list[Term] args, list[str] seps)
  | lst(list[Term] elts, list[str] seps)
  | lit(str src)
  ;


str yield(cons(_, args, seps)) 
  = yieldL(args, seps);

str yield(lst(xs, seps))
  = yieldL(xs, ["", *seps, ""]);
  
str yield(lit(x)) = x;
 
str yieldL(xs, list[str] seps)
  = ( seps[0] | it + yield(xs[i]) + seps[i+1] | int i <- [0..size(xs)] );


/*
 * Rules, patterns and interpolated strings
 */
 
data Rule = rule(Pattern lhs, Txt rhs);

data Pattern
  = cons(str name, list[Pattern] args)
  | lst(list[Pattern] elts)
  | lit(str src)
  | var(str name)
  | lvar(str name)
  ;
 
alias Txt = list[Elt];

data Elt
  = lit(str src)
  | marked(str src)
  | var(str name)
  | lvar(str name)
  ;

str par() = "§";

/*

«  »


  f(<Args*>) => f(<Args*>§, §Logger log)
  
  {<Stmts*>} => "{
                '  <Stmts*>§;
                '  §println()
                '}";

*/


/*
 * Substitution in right-hand sides
 */

alias Env = map[str, Term];

str subst(txt, env) 
  = ( "" | it + e.src | e <- subst(txt, [], env) );


// post: result only has lit or marked
Txt subst([], hist, _) = hist;

Txt subst([lit(x), *tail], hist, env) 
  = subst(tail, [*hist, lit(x)], env);
  
Txt subst([var(x), *tail], hist, env) 
  = subst(tail, [*hist, lit(yield(env[x]))], env);

Txt subst([marked(x), *tail], hist, env)
  = subst(tail, [*hist, marked(x)], env); 
  
Txt subst([lvar(x), *tail], hist, env) {
  lst = env[x];
  
  // we assume listvars are directly preceded
  // or followed by a marked separator, if any.
  if (lst.elts == []) { 
    if (hist != [], hist[-1] is marked) 
      hist = hist[..-1];
    else if (tail != [], tail[0] is marked)
      tail = tail[1..];
  }
  
  return subst(tail, [*hist,lit(yield(lst))], env);
}




/*
 * Pattern matching
 */

tuple[bool, Env] match(Term t, Pattern p) {
  try 
    return <true, match(t, p, ())>; 
  catch Fail():
    return <false, ()>;
}

Env match(t, var(x), env) = env + (x: t)
  when x notin env;

Env match(t, var(x), env) = env 
  when x in env, equalModSep(env[x], t);
  
Env match(lit(x), lit(x), env) = env;  
  
Env match(cons(x, as, _), cons(x, bs), env)
  = ( env | it + match(as[i], bs[i], it) | i <- [0..size(as)] )
  when size(as) == size(bs);
  
Env match(lst(xs, seps), lst(ys), env)
  = matchL(xs, seps, ys, env);
  
default Env match(_, _, _) = { throw Fail(); };
  
  
/*
 * List matching  
 */

Env matchL([], _, [], env) = env;

Env matchL([], _, [!lvar(_), *_], _) 
  = { throw Fail(); };

Env matchL(ts, seps, [lvar(x), *ps], env) {
  for (i <- [0..size(ts)+1]) 
    try {
      sub = lst(ts[0..i], seps[0..i]);
      if (x in env, !equalModSep(env[x], sub)) 
        continue;
      return matchL(ts[i..], seps[i..], ps, env + (x: sub));
    }
    catch Fail(): ;
  throw Fail();
}

default Env matchL([t, *ts], seps, [p, *ps], env) 
  = matchL(ts, seps[1..], ps, match(t, p, env));
  

/*
 * Rule application
 */
 
//Term parse(str src); 
 
Term apply(rule(lhs, rhs), Term t) = parse(subst(rhs, env))
  when <true, env> := match(t, lhs); 
