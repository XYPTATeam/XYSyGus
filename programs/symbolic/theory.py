# Author: Garvit Juniwal (garvitjuniwal@eecs.berkeley.edu)

# This file contains the meaning of theory symbols
# Currently supported theories are QF_LIA and QF_BV

from z3 import *  # @UnusedWildImport

def _Equal(a, b):
    return a == b

def _IntAdd(a, b):
    return a + b


def _IntSub(a, b):
    return a - b


def _IntMul(a, b):
    return a * b


def _ITE(a, b, c):
    return If(a, b, c)


def _BoolAnd(a, b):
    return And(a, b)


def _BoolOr(a, b):
    return Or(a, b)


def _BoolNot(a):
    return Not(a)


def _BoolXor(a, b):
    return Xor(a, b)


def _BoolImplies(a, b):
    return Implies(a, b)


def _IntLE(a, b):
    return a <= b


def _IntGE(a, b):
    return a >= b


def _IntLT(a, b):
    return a < b


def _IntGT(a, b):
    return a > b

def _Identity(a):
    return a


def GetFunctionFromSymbol(funcSymbol):
    try:
        return{'=':       _Equal,
               '+':       _IntAdd,
               '-':       _IntSub,
               '*':       _IntMul,
               'ite':     _ITE,
               'and':     _BoolAnd,
               'or':      _BoolOr,
               'not':     _BoolNot,
               'xor':     _BoolXor,
               '<=':      _IntLE,
               '>=':      _IntGE,
               '>':       _IntGT,
               '<':       _IntLT,
               '=>':      _BoolImplies,
               '_ID':     _Identity
               }[funcSymbol]
    except:
        raise Exception('Function %s not recognised by theory' % funcSymbol)
