import sys
import tree_sitter_tlaplus as tstla
from tree_sitter import Language, Parser

TLAPLUS_LANGUAGE = Language(tstla.language())

if __name__ == "__main__":
    parser = Parser(TLAPLUS_LANGUAGE)

    file_content = None
    with open(sys.argv[1], "rb") as f:
        file_content = f.read()
        
    tree = parser.parse(file_content)

    # https://tree-sitter.github.io/tree-sitter/using-parsers/queries/1-syntax.html
    # query = TLAPLUS_LANGUAGE.query('(def_eq \"≜\") @capture')
    # captures = query.captures(tree.root_node)
    # print(captures['capture'])

    root = tree.root_node
    print(root)