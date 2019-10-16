module Plugin

import util::IDE;
import Exp;
import Syntax;
import ParseTree;


void main() {
  registerLanguage("Bla", "rewr", start[Syntax](str src, loc org) {
    return parse(#start[Syntax], src, org);
  });
  registerLanguage("Blaa", "exp", start[Exp](str src, loc org) {
    return parse(#start[Exp], src, org);
  });
}
