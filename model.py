import tree_sitter_tlaplus as tstla
from tree_sitter import Language, Parser
from abc import ABC, abstractmethod

TLAPLUS_LANGUAGE = Language(tstla.language())

definitions = {}

# TODO: Use TLC model checker from tlc2tools.jar to evaluate the domain
def eval_domain(domain):
    pass

class func:
    def __init__(self, kind, args, domain, expr):
        self.kind = kind
        self.args = args
        self.domain = domain
        self.expr = expr

prefixes = {
    "lnot":         lambda x: f"!({x})",
    "negative":     lambda x: f"-{x}",
    "negative_dot": lambda x: f"-{x}",
}

infixes = {
    "implies":   lambda a, b: f"!({a}) || ({b})",
    "equiv":     lambda a, b: definitions[a] = b,
    "iff":       lambda a, b: f"({a}) == ({b})",
    "land":      lambda a, b: f"({a}) && ({b})",
    "lor":       lambda a, b: f"({a}) || ({b})",
    "assign":    lambda a, b: f"({a}) = ({b})",
    "bnf_rule":  lambda a, b: definitions[a] = b,
    "eq":        lambda a, b: f"({a}) == ({b})",
    "neq":       lambda a, b: f"({a}) != ({b})",
    "lt":        lambda a, b: f"({a}) < ({b})",
    "gt":        lambda a, b: f"({a}) > ({b})",
    "leq":       lambda a, b: f"({a}) <= ({b})",
    "geq":       lambda a, b: f"({a}) >= ({b})",
    "plus":      lambda a, b: f"({a}) + ({b})",
    "plusplus":  lambda a, b: f"({a}) + ({b})",
    "mod":       lambda a, b: f"({a}) % ({b})",
    "modmod":    lambda a, b: f"({a}) % ({b})",
    "vert":      lambda a, b: f"({a}) | ({b})",
    "vertvert":  lambda a, b: f"({a}) || ({b})",
    "minus":     lambda a, b: f"({a}) - ({b})",
    "minusminus":lambda a, b: f"({a}) - ({b})",
    "amp":       lambda a, b: f"({a}) & ({b})",
    "ampamp":    lambda a, b: f"({a}) && ({b})",
    "mul":       lambda a, b: f"({a}) * ({b})",
    "mulmul":    lambda a, b: f"({a}) * ({b})",
    "times":     lambda a, b: f"({a}) * ({b})",
}

postfixes = {}

def convert_to_ast_node(node):
    try:
        ast_class = globals()[node.type]
    except KeyError:
        raise ValueError(f"No AST class found for node type: {node.type}")
    return ast_class(node)

class ast_node(ABC):
    def __init__(self, node):
        self.node = node

    @abstractmethod
    def to_c(self):
        pass

class _op_or_expr(ast_node):
    pass

class _expr(_op_or_expr):
    pass

class _number(_expr):
    pass

class nat_number(_number):
    def to_c(self):
        return self.node.text.decode("utf-8")

class real_number(_number):
    def to_c(self):
        return self.node.text.decode("utf-8") + "f"

class binary_number(_number):
    def to_c(self):
        return "0b" + self.node.text.decode("utf-8")

class octal_number(_number):
    def to_c(self):
        return "0" + self.node.text.decode("utf-8")

class hex_number(_number):
    def to_c(self):
        return "0x" + self.node.text.decode("utf-8")

class string(_expr):
    def to_c(self):
        return f"{self.node.text.decode("utf-8")}"

class boolean(_expr):
    def to_c(self):
        return "true" if self.node.text == b"TRUE" else "false"

class parentheses(_expr):
    def eval(self):
        inner_expr_node = self.node.children[1]
        self.inner_expr = convert_to_ast_node(inner_expr_node)
        return self.inner_expr.to_c()

class identifier(_expr):
    def to_c(self):
        return self.node.text.decode("utf-8")

class identifier_ref(identifier):
    pass

class word(identifier):
    pass

class bound_op(_expr):
    def to_c(self):
        name_node = self.node.child_by_field_name('name')
        name = name_node.text.decode("utf-8")
        parameter_nodes = self.node.child_by_field_name('parameter')
        valid_parameter_nodes = [
            node for node in parameter_nodes.children
            if node.type not in ('(', ',', ')')
        ]
        parameters = []
        for node in valid_parameter_nodes:
            parameter = convert_to_ast_node(node)
            parameters.append(parameter.to_c))
        parameters_str = ", ".join(str(p) for p in parameters)
        return f"{name}({parameters_str})"

class bound_nonfix_op(_expr):
    def to_c(self):
        symbol_node = self.node.child_by_field_name('symbol')
        symbol = symbol_node.text.decode("utf-8")
        if symbol in prefixes:
            x = self.node.children[2]
            return prefixes[symbol](x)
        if symbol in infixes:
            a = self.node.children[2]
            b = self.node.children[3]
            return infixes[symbol](a, b)
        if symbol in postfixes:
            x = self.node.children[2]
            return postfixes[symbol](x)
        raise NotImplementedError(f"Unexpected operator: {symbol}")

class bound_prefix_op(_expr):
    def to_c(self):
        symbol_node = self.node.child_by_field_name('symbol')
        symbol = symbol_node.text.decode("utf-8")
        rhs_node = self.node.child_by_field_name('rhs')
        rhs = convert_to_ast_node(rhs_node)
        rhs = rhs.to_c()
        try:
            return prefixes[symbol](rhs)
        except KeyError: 
            raise NotImplementedError(f"Unexpected operator: {symbol}")

class bound_infix_op(_expr):
    def to_c(self):
        symbol_node = self.node.child_by_field_name('symbol')
        symbol = symbol_node.text.decode("utf-8")
        rhs_node = self.node.child_by_field_name('rhs')
        rhs = convert_to_ast_node(rhs_node)
        rhs = rhs.to_c()
        try:
            return infixes[symbol](rhs)
        except KeyError: 
            raise NotImplementedError(f"Unexpected operator: {symbol}")

class bound_postfix_op(_expr):
    def to_c(self):
        symbol_node = self.node.child_by_field_name('symbol')
        symbol = symbol_node.text.decode("utf-8")
        rhs_node = self.node.child_by_field_name('rhs')
        rhs = convert_to_ast_node(rhs_node)
        rhs = rhs.to_c()
        try:
            return postfixes[symbol](rhs)
        except KeyError: 
            raise NotImplementedError(f"Unexpected operator: {symbol}")

class bounded_quantification(_expr):
    # TODO
    pass

class unbounded_quantification(_expr):
    # TODO
    pass

class choose(_expr):
    # TODO
    pass

class finite_set_literal(_expr):
    def to_c(self):
        elements = []
        valid_children = [child for child in self.node.children if child.type not in ("{", "}", ",")]
        for child in valid_children:
            elem = convert_to_ast_node(child)
            elements.append(elem.to_c())
        return "{" + ", ".join(elements) + "}"

class set_filter(_expr):
    # TODO
    pass

class set_map(_expr):
    # TODO
    pass

class function_evaluation(_expr):
    # TODO
    pass

class function_literal(_expr):
    # TODO
    pass

class set_of_functions(_expr):
    # TODO
    pass

class record_literal(_expr):
    def to_c(self):
        fields = []
        valid_children = [child for child in self.node.children if child.type not in ("[", "]", ",", "comment")]
        for i in range(0, len(valid_children), 3):
            key_node = valid_children[i]
            value_node = valid_children[i + 2]
            elem = convert_to_ast_node(value_node)
            fields.append(f".{key_node.text.decode("utf-8")} = {elem.to_c()}")
        return "{" + ", ".join(fields) + "}"

class set_of_records(_expr):
    def to_c(self):
        fields = []
        valid_children = [child for child in self.node.children if child.type not in ("[", "]", ",", "comment")]
        for i in range(0, len(valid_children), 3):
            key_node = valid_children[i]
            expr_node = valid_children[i + 2]
            elem = convert_to_ast_node(expr_node)
            fields.append(f".{key_node.text.decode("utf-8")} = {elem.to_c()}")
        return "{" + ", ".join(fields) + "}"

class record_value(_expr):
    def to_c(self):
        r_node = self.node.children[0]
        r = r_node.text.decode("utf-8")
        val_node = self.node.children[2]
        val = val_node.text.decode("utf-8")
        return f"{r}.{val}"

class tuple_literal(_expr):
    def to_c(self):
        elements = []
        valid_children = [child for child in self.node.children if child.type not in ("langle_bracket", "rangle_bracket", ",")]
        for child in valid_children:
            elem = convert_to_ast_node(child)
            elements.append(elem.to_c())
        return "{" + ", ".join(elements) + "}"

class if_then_else(_expr):
    def to_c(self):
        _if_node = self.node.children[1]
        _if = convert_to_ast_node(_if_node)
        _then_node = self.node.children[3]
        _then = convert_to_ast_node(_then_node)
        _else_node = self.node.children[5]
        _else = convert_to_ast_node(_else_node)
        return f"({_if.to_eval()}) ? {then.to_c()} : {_else.to_c()}"

class tuple_of_identifiers(_expr):
    def to_c(self):
        elements = []
        valid_children = [child for child in self.node.children if child.type not in ("langle_bracket", "rangle_bracket", ",")]
        for child in valid_children:
            elem = convert_to_ast_node(child)
            elements.append(elem.to_c())
        return "{" + ", ".join(elements) + "}"

class _unit(ast_node):
    pass

class _definition(_unit):
    pass

class operator_definition(_definition):
    # TODO
    def to_c(self):
        symbol_node = self.node.child_by_field_name('name')
        symbol = symbol_node.text.decode("utf-8")
        definition_node = self.node.child_by_field_name('definition')
        definition = convert_to_ast_node(definition_node)
        if symbol in prefixes:
            parameter_node = self.node.children[1]
            parameter = convert_to_ast_node(parameter_node)
            definitions[f"{symbol}{parameter.to_c()}"] = definition.to_c()
        if symbol in infixes:
            parameter_a_node = self.node.children[0]
            parameter_a = convert_to_ast_node(parameter_a_node)
            parameter_b_node = self.node.children[2]
            parameter_b = convert_to_ast_node(parameter_b_node)
            definitions[f"{parameter_a.to_c()} {symbol} {parameter_b.to_c()}"] = definition.to_c()
        if symbol in postfixes:
            parameter_node = self.node.children[0]
            parameter = convert_to_ast_node(parameter_node)
            definitions[f"{parameter.to_c()}{symbol}"] = definition.to_c()

        raise NotImplementedError(f"Unexpected operator: {symbol}")


class function_definition(_definition):
    # TODO
    pass



def parse_tla_file(specification, constants, invariants, properties, tla):
    parser = Parser(TLAPLUS_LANGUAGE)
    tree = parser.parse(tla)

    converted_root_node = convert_to_ast_node(tree.root_node)
    print(converted_root_node.to_c())
    quit()

