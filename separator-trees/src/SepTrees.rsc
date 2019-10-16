module SepTrees

import List;
import Node;

data MyList[&T] = lval(list[&T] elts, list[str] seps = [], str sep = "");

str yield(str s) = s;
str yield(node n) {
  if (lval(elts, seps = seps) := n) {
    if (elts == []) {
      return "";
    }
    if ([elt] := elts) {
      return yield(elt);
    }
    return (yield(elts[0]) | it + seps[i-1] + yield(elts[i]) | i <- [1..size(elts)]);
  }
  seps = getSeps(n);
  children = getChildren(n);
  return (seps[0] | it + yield(children[i]) + seps[i+1] | i <- [0..size(children)]);
}

list[str] getSeps(node n) {
  if (list[str] seps := n.seps) {
    return seps;
  }
  throw "Impossible";
}