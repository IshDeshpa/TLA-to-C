import tree_sitter_tlaplus as tstla
from tree_sitter import Language, Parser
from abc import ABC, abstractmethod

TLAPLUS_LANGUAGE = Language(tstla.language())

always = []
eventually = []

def convert_to_ast_node(node):
    try:
        ast_class = globals()[node.type]
    except KeyError:
        raise ValueError(f"No AST class found for node type: {node.type}")
    return ast_class(node)

class base(ABC):
    def __init__(self, node):
        self.node = node

    @abstractmethod
    def to_c(self):
        pass

class _expr(ABC):
    def __init__(self, node):
        self.node = node

    @abstractmethod
    def to_c(self):
        pass

class _number(_expr):
    pass

class nat_number(_number):
    def to_c(self):
        return self.node.text.decode("utf-8")

class real_number(_number):
    def to_c(self):
        return self.node.text.decode("utf-8")

class binary_number(_number):
    def to_c(self):
        return self.node.text.decode("utf-8")

class octal_number(_number):
    def to_c(self):
        return self.node.text.decode("utf-8")

class hex_number(_number):
    def to_c(self):
        return self.node.text.decode("utf-8")

class string(_expr):
    def to_c(self):
        return f"{self.node.text.decode("utf-8")}"

class boolean(_expr):
    def to_c(self):
        return "true" if self.node.text == b"TRUE" else "false"

class _primitive_value_set(_expr):
    pass

class string_set(_primitive_value_set):
    def to_c(self):
        return "STRING"

class boolean_set(_primitive_value_set):
    def to_c(self):
        return "BOOLEAN"

class _number_set(_primitive_value_set):
    pass

class nat_number_set(_number_set):
    def to_c(self):
        return "Nat"

class int_number_set(_number_set):
    def to_c(self):
        return "Int"

class real_number_set(_number_set):
    def to_c(self):
        return "Real"

class parentheses(_expr):
    def __init__(self, node):
        super().__init__(node)
        inner_node = node.children[0]
        self.inner_expr = convert_to_ast_node(inner_node)

    def to_c(self):
        return self.inner_expr.to_c()

class identifier(_expr):
    def to_c(self):
        return self.node.text.decode("utf-8")

class identifier_ref(identifier):
    pass

class finite_set_literal(_expr):
    def to_c(self):
        elements = []
        valid_children = [child for child in self.node.children if child.type not in ("{", "}", ",")]
        for child in valid_children:
            elem = convert_to_ast_node(child)
            elements.append(elem.to_c())
        return "{" + ", ".join(elements) + "}"

class tuple_literal(_expr):
    def to_c(self):
        elements = []
        valid_children = [child for child in self.node.children if child.type not in ("langle_bracket", "rangle_bracket", ",")]
        for child in valid_children:
            elem = convert_to_ast_node(child)
            elements.append(elem.to_c())
        return "{" + ", ".join(elements) + "}"

class record_literal(_expr):
    def to_c(self):
        fields = []
        valid_children = [child for child in self.node.children if child.type not in ("[", "]", ",", "comment")]
        for i in range(0, len(valid_children), 3):
            key_node = valid_children[i]
            value_node = valid_children[i + 2]
            value_obj = convert_to_ast_node(value_node)
            fields.append(f".{key_node.text.decode("utf-8")} = {value_obj.to_c()}")
        return "{" + ", ".join(fields) + "}"

class _op(ABC):
    def __init__(self, node):
        self.node = node
    
    @abstractmethod
    def to_c(self):
        pass

class prefix_op_symbol(_op):
    def to_c(self):
        converted_node = convert_to_ast_node(self.node.children[0])
        return converted_node.to_c()

class lnot(_op):
    def to_c(self):
        return "!"

class negative(_op):
    def to_c(self):
        return "-"

class negative_dot(negative):
    pass

class always(_op):
    def __init__(self, node):
        super().__init__(node)
        always.append(node)

    def to_c(self):
        return ""

class eventually(_op):
    def __init__(self, node):
        super().__init__(node)
        eventually.append(node)

    def to_c(self):
        return ""

class infix_op_symbol(_op):
    def to_c(self):
        converted_node = convert_to_ast_node(self.node.children[0])
        return converted_node.to_c()

class equiv(_op):
    def to_c(self):
        return "=="

class iff(_op):
    def to_c(self):
        return "=="

class land(_op):
    def to_c(self):
        return "&&"

class lor(_op):
    def to_c(self):
        return "||"

class assign(_op):
    def to_c(self):
        return "="

class eq(_op):
    def to_c(self):
        return "=="

class neq(_op):
    def to_c(self):
        return "!="

class lt(_op):
    def to_c(self):
        return "<"

class gt(_op):
    def to_c(self):
        return ">"

class leq(_op):
    def to_c(self):
        return "<="

class geq(_op):
    def to_c(self):
        return ">="

class plus(_op):
    def to_c(self):
        return "+"

class plusplus(_op):
    def to_c(self):
        return "++"

class mod(_op):
    def to_c(self):
        return "%"

class vert(_op):
    def to_c(self):
        return "|"

class vertvert(_op):
    def to_c(self):
        return "||"

class minus(_op):
    def to_c(self):
        return "-"

class minusminus(_op):
    def to_c(self):
        return "--"

class amp(_op):
    def to_c(self):
        return "&"

class ampamp(_op):
    def to_c(self):
        return "&&"

class mul(_op):
    def to_c(self):
        return "*"

class slash(_op):
    def to_c(self):
        return "/"

class dots_3(_op):
    def to_c(self):
        return "..."

class hashhash(_op):
    def to_c(self):
        return "##"

class cdot(_op):
    def to_c(self):
        return "*"

class postfix_op_symbol(_op):
    def to_c(self):
        converted_node = convert_to_ast_node(self.node.children[0])
        return converted_node.to_c()

class sup_plus(_op):
    def to_c(self):
        return "^+"

class asterisk(_op):
    def to_c(self):
        return "^*"

class sup_hash(_op):
    def to_c(self):
        return "^#"

class prime(_op):
    def to_c(self):
        return "'"

class tuple_of_identifiers(_expr):
    def to_c(self):
        elements = []
        valid_children = [child for child in self.node.children if child.type not in ("langle_bracket", "rangle_bracket", ",")]
        for child in valid_children:
            elem = convert_to_ast_node(child)
            elements.append(elem.to_c())
        return "{" + ", ".join(elements) + "}"

class def_eq(base):
    def to_c(self):
        return "=="

class set_in(base):
    def to_c(self):
        return "in"

class gets(base):
    def to_c(self):
        return "="

class forall(base):
    def to_c(self):
        return "FORALL"

class exists(base):
    def to_c(self):
        return "EXISTS"

class temporal_forall(base):
    def to_c(self):
        return "TEMP_FORALL"

class temporal_exists(base):
    def to_c(self):
        return "TEMP_EXISTS"

class all_map_to(base):
    def to_c(self):
        return "ALL_MAP_TO"

class maps_to(base):
    def to_c(self):
        return "->"

class langle_bracket(base):
    def to_c(self):
        return "<<"

class rangle_bracket(base):
    def to_c(self):
        return ">>"

class rangle_bracket_sub(base):
    def to_c(self):
        return ">>"

class case_box(base):
    def to_c(self):
        return "[]"

class case_arrow(base):
    def to_c(self):
        return "->"

class colon(base):
    def to_c(self):
        return ":"

class address(base):
    def to_c(self):
        return "@"

class label_as(base):
    def to_c(self):
        return "::"

class placeholder(base):
    def to_c(self):
        return "_"

class bullet_conj(base):
    def to_c(self):
        return "&&"

class bullet_disj(base):
    def to_c(self):
        return "||"

class unit(base):
    pass

class _definition(unit):
    pass

class operator_definition(_definition):
    def to_c(self):
        converted_node = convert_to_ast_node(self.node.children[2])
        return converted_node.to_c()

class source_file(base):
    def to_c(self):
        converted_node = convert_to_ast_node(self.node.children[0])
        return converted_node.to_c()

class module(base):
    def to_c(self):
        result = []
        for child in self.node.children:
            if child.type == "operator_definition":
                converted_node = convert_to_ast_node(child)
                result.append(converted_node.to_c())
        return result

def parse_tla_file(specification, constants, invariants, properties, tla):
    parser = Parser(TLAPLUS_LANGUAGE)
    tree = parser.parse(tla)

    converted_root_node = convert_to_ast_node(tree.root_node)
    print(converted_root_node.to_c())
    quit()

