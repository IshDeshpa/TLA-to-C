# parser.py

import ply.lex as lex
import ply.yacc as yacc

# List of token names
tokens = (
    'VAR',
    'AND',
    'OR',
    'NOT',
    'IN'
)

t_VAR = r'[a-zA-Z_][a-zA-Z0-9_]*'
t_AND = r'/\\'
t_OR = r'\\/'
t_NOT = r'~'
t_IN = r'\\in'

