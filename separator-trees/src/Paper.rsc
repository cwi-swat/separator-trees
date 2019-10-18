module Paper


/* 
 * Separator trees
 */

data Term
  = cons(str name, list[Term] args, list[str] seps)
  | lst(list[Term] elts, list[str] seps, str sep)
  | lit(str src)
  ;


str yield(cons(_, args, seps)) 
  = yieldL(args, seps);

str yield(lst(xs, seps, _))
  = yieldL(xs, ["", *seps, ""]);
  
str yield(lit(x)) = x;
 
str yieldL(xs, list[str] seps)
  = ( seps[0] | it + yield(xs[i]) + seps[i+1] | int i <- [0..size(xs)] );


/*
 * Rules, patterns and interpolated strings
 */
 
data Rule = rule(Pattern lhs, String rhs);

data Pattern
  = cons(str name, list[Pattern] args)
  | lst(list[Pattern] elts)
  | lit(str src)
  | var(str name)
  | lvar(str name)
  ;
 
alias String = list[Elt];

data Elt
  = lit(str src)
  | var(str name)
  | lvar(str name);



/*
 * Substitution in right-hand sides
 */

alias Env = map[str, Term];

str subst(string, env) = subst(string, "", env);

str subst([], prefix, _) = prefix ;

str subst([lit(x), *tail], prefix, env) = subst(tail, prefix + x, env);
  
str subst([var(x), *tail], prefix, env) = subst(tail, prefix + yield(env[x]), env);
  
str subst([lvar(x), *tail], prefix, env) {
  prefix = prefix + yield(l); 
  suffix = subst(tail, "", env);
  Term l = env[x];
  if (l.elts == []) {
    if (endsWith(sep, prefix)) 
      prefix = prefix[0..size(prefix) - size(sep)];
    if (startsWith(sep, suffix)) 
      suffix = suffix[size(sep)..];
  }
  return prefix + suffix;
}




/*
 * Pattern matching
 */

tuple[bool, Env] match(Term t, Pattern p) {
  try {
    env = match(t, p, ());
    return <true, env>; 
  }
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
  
Env match(lst(xs, seps, sep), lst(ys), env)
  = matchL(xs, seps, sep, ys, env);
  
default Env match(_, _, _) = { throw Fail(); };
  
  
/*
 * List matching  
 */

Env matchL([], _, _, [], env) = env;

Env matchL([], _, _, [!lvar(_), *ps], _) 
  = { throw Fail(); };

Env matchL(ts, seps, sep, [lvar(x), *ps], env) {
  for (i <- [0..size(ts)+1]) {
    try {
      sub = lst(ts[0..i], seps[0..i], sep);
      if (x in env, !equalModSep(env[x], sub)) 
        continue;
      return matchL(ts[i..], seps[i..], ps, env + (x: sub));
    }
    catch Fail(): ;
  }
  throw Fail();
}

default Env matchL([t, *ts], seps, [p, *ps], env) 
  = matchL(ts, seps[1..], ps, match(t, p, env));
  

/*
 * Rule application
 */
 
Term parse(str src); 
 
Term apply(rule(lhs, rhs), Term t)
  = parse(subst(rhs, env))
  when <true, env> := match(t, lhs); 
