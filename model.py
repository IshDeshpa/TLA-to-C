import tree_sitter_tlaplus as tstla
from tree_sitter import Language, Parser
from abc import ABC, abstractmethod

TLAPLUS_LANGUAGE = Language(tstla.language())

# --- Basic Classes ---

class expression(ABC):
    """
    Base class for TLA+ expressions.
    Provides a common interface for conversion to C.
    """
    def __init__(self, node):
        self.node = node

    @abstractmethod
    def to_c(self):
        """
        Convert the expression to its C code equivalent.
        """
        pass

class value(expression):
    """
    Base class for TLA+ values.
    """
    pass

# --- Primitive Value Classes ---

class primitive(value):
    """
    Base class for TLA+ primitive values.
    """
    pass

class string(primitive):
    def to_c(self):
        # Returns a C string literal.
        return f"{self.node.text.decode("utf-8")}"

class boolean(primitive):
    def to_c(self):
        # Returns the C boolean literal.
        return "true" if self.node.text == b"TRUE" else "false"

class nat_number(primitive):
    def to_c(self):
        # Returns the numeric literal as-is.
        return self.node.text.decode("utf-8")

# --- Complex Value Classes ---

class complex(value):
    """
    Base class for TLA+ complex values.
    """
    pass

class finite_set_literal(complex):
    def to_c(self):
        """
        Convert a finite set literal to a C array literal.
        Example: TLA+ {1, 2, 3} -> C code: {1, 2, 3}
        """
        elements = []
        valid_children = [child for child in self.node.children if child.type not in ("{", "}", ",")]
        for child in valid_children:
            elem = get_value(child)
            elements.append(elem.to_c())
        return "{" + ", ".join(elements) + "}"

class tuple_literal(complex):
    def to_c(self):
        """
        Convert a tuple literal to a C array literal.
        Example: TLA+ <<1, 2, 3>> -> C code: {1, 2, 3}
        """
        elements = []
        valid_children = [child for child in self.node.children if child.type not in ("langle_bracket", "rangle_bracket", ",")]
        for child in valid_children:
            elem = get_value(child)
            elements.append(elem.to_c())
        return "{" + ", ".join(elements) + "}"

class record_literal(complex):
    def to_c(self):
        """
        Convert a record literal to a C struct initializer.
        Example: TLA+ [a -> "apple", b -> 2] -> C code: {.a = "apple", .b = 2}
        """
        valid_children = [child for child in self.node.children if child.type not in ("[", "]", ",", "comment")]
        fields = []
        # Process every 3 valid children as a record field.
        for i in range(0, len(valid_children), 3):
            key_node = valid_children[i]
            # valid_children[i+1] is the mapping operator and is ignored.
            value_node = valid_children[i + 2]
            value_obj = get_value(value_node)
            fields.append(f".{key_node.text.decode("utf-8")} = {value_obj.to_c()}")
        return "{" + ", ".join(fields) + "}"

class function_literal(complex):
    """
    Base class for TLA+ function literals.
    """
    pass

class function_literal_string(function_literal):
    def to_c(self):
        pass

class function_literal_boolean(function_literal):
    def to_c(self):
        pass

class function_literal_nat_number(function_literal):
    def to_c(self):
        pass

class function_literal_finite_set_literal(function_literal):
    def to_c(self):
        pass

class function_literal_tuple_literal(function_literal):
    def to_c(self):
        pass

class function_literal_record_literal(function_literal):
    def to_c(self):
        pass

class function_literal_function_literal(function_literal):
    def to_c(self):
        pass
class if_then_else(expression):
    def to_c(self):
        if_node = self.node.children[1]
        then_node = self.node.children[3]
        else_node = self.node.children[5]

        if_expr = get_value(if_node)
        then_expr = get_value(then_node)
        else_expr = get_value(else_node)

        return f"(({if_expr.to_c()}) ? ({then_expr.to_c()}) : ({else_expr.to_c()}))"


# --- Infix Operator ---
class bound_infix_op(expression):
    # Big lookup table of lambdas
    # Fill this out with all the TLA+ operators eventually
    ops = {
        "implies": lambda x, y: f"(({x}) && (!({y})))",
        "eq": lambda x, y: f"(({x}) == ({y}))",
    }

    def to_c(self):
        operator = self.node.children[1]
        left_operand = self.node.children[0]
        right_operand = self.node.children[2]

        left_expr = get_value(left_operand)
        right_expr = get_value(right_operand)

        return self.ops[operator.type](left_expr.to_c(), right_expr.to_c())

# --- Misc. Classes ---
class identifier_ref(expression):
    def to_c(self):
        return self.node.text.decode("utf-8") 

class comment(expression):
    def to_c(self):
        return self.node.text.decode("utf-8").replace("\\*", "//") 

# --- Helper Factory Function ---

def get_value(node):
    """
    Factory function to create a value instance from a tree-sitter node.
    Assumes that node.type corresponds to one of the class names (in lowercase).
    """
    type_map = {
        "string": string,
        "boolean": boolean,
        "nat_number": nat_number,
        "finite_set_literal": finite_set_literal,
        "tuple_literal": tuple_literal,
        "record_literal": record_literal,
        "function_literal": function_literal,
        "identifier_ref": identifier_ref,
        "identifier": identifier_ref,
        "comment": comment,
        "if_then_else": if_then_else,
        "bound_infix_op": bound_infix_op,
    }
    cls = type_map.get(node.type)
    if cls:
        return cls(node)
    else:
        raise ValueError(f"Unsupported node type: {node.type}\n\tNode start: {node.start_point}\n\tNode text: {node.text.decode('utf-8')}")

# --- Parsing Function ---

def parse_tla_file(specification, constants, invariants, properties, tla):
    """
    Parses a TLA+ specification using tree-sitter, then traverses the AST.
    Instantiate value objects (using get_value) based on the node types.
    """
    parser = Parser(TLAPLUS_LANGUAGE)
    tree = parser.parse(tla)

    # XXX: Testing code
    def traverse(node):
        if node.type in ("string", "boolean", "nat_number", "finite_set_literal", "tuple_literal", "record_literal"):
            value_obj = get_value(node)
            print(f"C code for {node.type}:", value_obj.to_c())
        # Recursively traverse all children.
        for child in node.children:
            traverse(child)

    traverse(tree.root_node)
