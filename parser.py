import tree_sitter_tlaplus as tstla
from tree_sitter import Language, Parser
from abc import ABC, abstractmethod
import tlc
import pdb

TLAPLUS_LANGUAGE = Language(tstla.language())

func_counter = 0

invariants = []
definitions = {}
variables = []
constants = {}
funcs = {}

class func:
    def __init__(self, kind, bound, expr):
        self.kind = kind
        self.bound = bound
        self.expr = expr

    def to_c(self):
        # TODO: Use class members to complete a template which is of C code
        # if kind is forall, then check expr on everything in the bound and pass if all ture
        # if kind is exists, then check expr on everything in bound and pass if one is true
        # if choice, choose randomly from bound and apply expr
        # if func, run everything in the bound to the expr and return values
        pass

def _record_definition(a, b):
    definitions[a] = b
    return ""

prefixes = {
    "lnot":         lambda x: f"!({x})",
    "negative":     lambda x: f"-{x}",
    "negative_dot": lambda x: f"-{x}",
    "!":         lambda x: f"!({x})",
    "-":     lambda x: f"-{x}",
    "-.":     lambda x: f"-{x}",
}

infixes = {
    "implies":   lambda a, b: f"!({a}) || ({b})",
    "equiv":     lambda a, b: _record_definition(a, b),
    "iff":       lambda a, b: f"({a}) == ({b})",
    "land":      lambda a, b: f"({a}) && ({b})",
    "lor":       lambda a, b: f"({a}) || ({b})",
    "assign":    lambda a, b: f"({a}) = ({b})",
    "bnf_rule":  lambda a, b: _record_definition(a, b),
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
    "*":         lambda a, b: f"({a}) * ({b})",
    "=":         lambda a, b: f"({a}) == ({b})",
    "||":        lambda a, b: f"({a}) || ({b})",
    "&&":        lambda a, b: f"({a}) && ({b})",
    "==":        lambda a, b: f"({a}) == ({b})",
    "!=":        lambda a, b: f"({a}) != ({b})",
    "<":         lambda a, b: f"({a}) < ({b})",
    ">":         lambda a, b: f"({a}) > ({b})",
    "<=":        lambda a, b: f"({a}) <= ({b})",
    ">=":        lambda a, b: f"({a}) >= ({b})",
    "%":         lambda a, b: f"({a}) % ({b})",
    "|":         lambda a, b: f"({a}) | ({b})",
    "&":         lambda a, b: f"({a}) & ({b})",
    "-":         lambda a, b: f"({a}) - ({b})",
    "+":         lambda a, b: f"({a}) + ({b})",
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
    def to_c(self):
        inner_expr_node = self.node.children[1]
        inner_expr = convert_to_ast_node(inner_expr_node)
        inner_expr_val = self.inner_expr.to_c()
        return inner_expr_val

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
        name = convert_to_ast_node(name_node)
        name_val = name.to_c()
        parameter_nodes = self.node.child_by_field_name('parameter')
        valid_parameter_nodes = [
            node for node in parameter_nodes.children
            if node.type not in ('(', ',', ')')
        ]
        parameters = []
        for node in valid_parameter_nodes:
            parameter = convert_to_ast_node(node)
            parameters.append(parameter.to_c)
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
        lhs_node = self.node.child_by_field_name('lhs')
        lhs = convert_to_ast_node(lhs_node)
        lhs = lhs.to_c()
        rhs_node = self.node.child_by_field_name('rhs')
        rhs = convert_to_ast_node(rhs_node)
        rhs = rhs.to_c()
        try:
            return infixes[symbol](lhs, rhs)
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

class forall(ast_node):
    def to_c(self):
        return "forall"

class exists(ast_node):
    def to_c(self):
        return "exists"

class quantifier_bound(ast_node):
    def to_c(self):
        if self.node.children[0].type == "identifier":
            _set_node = self.node.children[2]
            _set = _set_node.text.decode("utf-8")
            result = tlc.evaluate(_set)
            return result

        if self.node.children[0].type == "tuple_of_identifiers":
            raise NotImplementedError("tuple_of_identifiers not supported yet")
        else:
            raise RuntimeError("Incorrect type for quantifier_bound node")

class bounded_quantification(_expr):
    def to_c(self):
        global func_counter
        import pdb; pdb.set_trace()

        quantifier_node = self.node.child_by_field_name('quantifier')
        quantifier = convert_to_ast_node(quantifier_node)
        quantifier = quantifier.to_c()

        bound_node = self.node.child_by_field_name('bound')
        bound = convert_to_ast_node(bound_node)
        bound = bound.to_c()

        expression_node = self.node.child_by_field_name('expression')
        expression = convert_to_ast_node(expression_node)
        expression = expression.to_c()

        function = func(quantifier, bound, expression)
        name_node = self.node.parent.child_by_field_name('name')
        if name_node:
            name = name_node.text.decode("utf-8")
        else:
            name = f"func_{func_counter}"
            func_counter += 1
        funcs[name] = function
        return f"{name}()"

class choose(_expr):
    def to_c(self):
        identifier_node = self.node.child_by_field_name('intro')
        identifier = convert_to_ast_node(identifier_node)
        identifier = identifier.to_c()
        _set_node = self.node.child_by_field_name('set')
        _set = _set_node.text.decode("utf-8")
        bound = {
            "identifier": identifier,
            "set": _set,
        }
        expression_node = self.node.child_by_field_name('expression')
        expression = convert_to_ast_node(expression_node)
        expression = expression.to_c()
        function = func("choose", bound, expression)
        name_node = self.node.parent.child_by_field_name('name')
        if name_node:
            name = name_node.text.decode("utf-8")
        else:
            name = f"func_{func_counter}"
            func_counter += 1
        funcs[name] = function
        return f"{name}()"


class finite_set_literal(_expr):
    def to_c(self):
        elements = []
        valid_children = [child for child in self.node.children if child.type not in ("{", "}", ",")]
        for child in valid_children:
            elem = convert_to_ast_node(child)
            elements.append(elem.to_c())
        return "{" + ", ".join(elements) + "}"

class set_filter(_expr):
    def to_c(self):
        value = self.node.text.decode("utf-8")
        result = tlc.evaluate(value)
        return result

class set_map(_expr):
    def to_c(self):
        value = self.node.text.decode("utf-8")
        result = tlc.evaluate(value)
        return result

class function_evaluation(_expr):
    def to_c(self):
        function_node = self.node.children[0]
        function = convert_to_ast_node(function_node)
        function_val = function.to_c()
        children = self.node.children
        lbr_idx = 1
        rbr_idx = next(
            i for i, ch in enumerate(children[lbr_idx+1:], start=lbr_idx+1)
            if ch.type == ']'
        )
        arg_nodes = [
            ch for ch in children[lbr_idx+1:rbr_idx]
            if not (ch.type == ',' or ch.type == 'comma')
        ]
        args = []
        for arg_node in arg_nodes:
            args.append(convert_to_ast_node(arg_node))
        arg_vals = []
        for arg in args:
            arg_vals.append(arg.to_c())
        if function_node.type == "identifier" or function_node.type == "identifier_ref":
            return f"{function_val}({', '.join(arg_vals)})"
        if function_node.type == "bound_op":
            return f"{function_val}({', '.join(arg_vals)})"
        if function_node.type == "identifier":
            return f"{function_val}({', '.join(arg_vals)})"
        if function_node.type == "identifier":
            return f"{function_val}({', '.join(arg_vals)})"
        raise NotImplementedError(f"Unexpected type: {function_node.type}")

class function_literal(_expr):
    def to_c(self):
        value = self.node.text.decode("utf-8")
        result = tlc.evaluate(value)
        return result

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
        return f"({_if.to_c()}) ? {_then.to_c()} : {_else.to_c()}"

# class tuple_of_identifiers(_expr):
#     def to_c(self):
#         elements = []
#         valid_children = [child for child in self.node.children if child.type not in ("langle_bracket", "rangle_bracket", ",")]
#         for child in valid_children:
#             elem = convert_to_ast_node(child)
#             elements.append(elem.to_c())
#         return "{" + ", ".join(elements) + "}"

class _unit(ast_node):
    pass

class _definition(_unit):
    pass

class variable_declaration(_unit):
    def to_c(self):
        id_nodes = [
            child for child in self.node.children
            if child.type == "identifier"
        ]
        names = [n.text.decode("utf-8") for n in id_nodes]
        for name in names:
            variables.append(name)

class constant_declaration(_unit):
    def to_c(self):
        id_nodes = [
            ch for ch in self.node.children[1:]
            if not (ch.type == ',' or ch.type == 'comma')
        ]
        ids = []
        for id_node in id_nodes:
            ids.append(convert_to_ast_node(id_node))
        id_vals = []
        for _id in ids:
            id_vals.append(_id.to_c())

        for id_val in id_vals:
            if id_val not in constants:
                raise KeyError(f"Undefined constant: {id_val!r}")

class operator_definition(_definition):
    def to_c(self):
        if self.node.children[0].type == "identifier":
            id_node = self.node.children[0]
            identifier = convert_to_ast_node(id_node)
            definition_node = self.node.child_by_field_name('definition')
            definition = convert_to_ast_node(definition_node)
            definitions[identifier.to_c()] = definition.to_c()
        else:
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
    def to_c(self):
        name_node = self.node.child_by_field_name('name')
        name = convert_to_ast_node(name_node).to_c()

        definition_node = self.node.child_by_field_name('definition')
        definition = convert_to_ast_node(definition_node).to_c()

        children = self.node.children
        lbr_idx = 1
        rbr_idx = next(
            i for i, ch in enumerate(children[lbr_idx+1:], start=lbr_idx+1)
            if ch.type == ']'
        )

        qb_nodes = [
            ch for ch in children[lbr_idx+1:rbr_idx]
            if not (ch.type == ',' or ch.type == 'comma')
        ]
        qbs = []
        for qb_node in qb_nodes:
            qbs.append(convert_to_ast_node(qb_node))
        qb_vals = []
        for qb in qbs:
            qb_vals.append(qb.to_c())

        quantifier_str = ", ".join(qb_vals)
        function = func("func", quantifier_str, definition)

        funcs[name] = function
        return f"{name}()"

# PCAL
class pcal_assign(_unit):
    def to_c(self):
        lhs_node = self.node.children[0].children[0]
        lhs = convert_to_ast_node(lhs_node)
        lhs = lhs.to_c()
        rhs_node = self.node.children[2]
        rhs = convert_to_ast_node(rhs_node)
        rhs = rhs.to_c()
        return f"{lhs} = {rhs};"

class pcal_while(_unit):
    def to_c(self):
        return f"while ({convert_to_ast_node(self.node.children[1]).to_c()}) {{ \
            {convert_to_ast_node(self.node.children[3]).to_c()} \
        }}"

class pcal_algorithm_body(_unit):
    def to_c(self):
        statements = []
        # if self.node.child_by_field_name('label'):
        #     print("label found")

        for child in self.node.children:
            if child.type in ["pcal_while"]:
                statement = convert_to_ast_node(child)
                statements.append(statement.to_c())

        return "\n".join(statements)

class pcal_var_decl(variable_declaration):
    pass

class pcal_algorithm(_unit):
    def to_c(self):
        global func_counter
        name_node = self.node.child_by_field_name('name')
        name = convert_to_ast_node(name_node).to_c()
        
        var_decl_node = None
        var_decls = []
        for child in self.node.children:
            if child.type == "pcal_var_decls":
                var_decl_node = child
                break
        
        if var_decl_node:
            var_decl_nodes = [
                child for child in var_decl_node.children
                if child.type == "pcal_var_decl"
            ]
            
            for var_decl in var_decl_nodes:
                var_decl_node = convert_to_ast_node(var_decl)
                var_decls.append(var_decl_node.to_c())

        alg_body_node = None
        for child in self.node.children:
            if child.type == "pcal_algorithm_body":
                alg_body_node = child
                break
        
        if not alg_body_node:
            raise NoValidModuleError(f"No valid algorithm body present")
        
        alg_body_node = convert_to_ast_node(alg_body_node)
        alg_body = alg_body_node.to_c()

        name_node = self.node.parent.child_by_field_name('name')
        if name_node:
            name = name_node.text.decode("utf-8")
        else:
            name = f"func_{func_counter}"
            func_counter += 1
        
        return (f"{name}() {{\n" + 
                alg_body + "\n" + 
                "}\n")

class module(_unit):
    def to_c(self):
        op_def_nodes = [
            child for child in self.node.children
            if child.type == "operator_definition" and
            child.child_by_field_name('name').text.decode("utf-8") in invariants
        ]
        op_defs = []
        for op_def_node in op_def_nodes:
            op_defs.append(convert_to_ast_node(op_def_node))
        for op_def in op_defs:
            op_def.to_c()

        func_def_nodes = [
            child for child in self.node.children
            if child.type == "function_definition" and
            child.child_by_field_name('name').text.decode("utf-8") in invariants
        ]
        func_defs = []
        for func_def_node in func_def_nodes:
            func_defs.append(convert_to_ast_node(func_def_node))
        for func_def in func_defs:
            func_def.to_c()


        var_dec_nodes = [
            child for child in self.node.children
            if child.type == "variable_declaration"
        ]
        var_decs = []
        for var_dec_node in var_dec_nodes:
            var_decs.append(convert_to_ast_node(var_dec_node))
        for var_dec in var_decs:
            var_dec.to_c()
        
        const_dec_nodes = [
            child for child in self.node.children
            if child.type == "constant_declaration"
        ]
        const_decs = []
        for const_dec_node in const_dec_nodes:
            const_decs.append(convert_to_ast_node(const_dec_node))
        for const_dec in const_decs:
            const_dec.to_c()

        pcal_alg_nodes = []
        for child in self.node.children:
            if child.type == "block_comment":
                pcal_alg_nodes.extend([
                    child2 for child2 in child.children
                    if child2.type == "pcal_algorithm"
                ])
        
        pcal_algs = []
        for pcal_alg_node in pcal_alg_nodes:
            pcal_algs.append(convert_to_ast_node(pcal_alg_node))
        for pcal_alg in pcal_algs:
            pcal_alg.to_c()

        # TODO: add pcal alg(s) as functions here

class source_file(ast_node):
    def to_c(self):
        module_nodes = [
            child for child in self.node.children
            if child.type == "module"
        ]
        if not module_nodes:
            raise RuntimeError(f"No valid modules present")
        modules = []
        for module_node in module_nodes:
            modules.append(convert_to_ast_node(module_node))
        for module in modules:
           module.to_c()

def parse(_constants, _invariants, tla_bytes):
    global constants, invariants
    constants = _constants
    invariants = _invariants

    parser = Parser(TLAPLUS_LANGUAGE)
    tree = parser.parse(tla_bytes)

    converted_root_node = convert_to_ast_node(tree.root_node)
    converted_root_node.to_c()

    print(f"Definitions: {definitions}")
    print(f"Variables: {variables}")
    print(f"Constants: {constants}")
    print(f"Functions: {funcs}")

    # TODO: Return everything you have for later
