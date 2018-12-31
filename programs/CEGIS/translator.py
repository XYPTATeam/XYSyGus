from z3 import *

verbose = False


def declare_var(sort, name):
    if sort == "Int":
        return Int(name)
    if sort == 'Bool':
        return Bool(name)


def get_sort(sort):
    if sort == "Int":
        return IntSort()
    if sort == "Bool":
        return BoolSort()


def to_string(Expr, Bracket=True, ForceBracket=False):
    if type(Expr) == str:
        return Expr
    if type(Expr) == tuple:
        return (str(Expr[1]))  # todo: immediate
    subexpr = []
    for expr in Expr:
        if type(expr) == list:
            subexpr.append(to_string(expr, ForceBracket=ForceBracket))
        elif type(expr) == tuple:
            subexpr.append(str(expr[1]))
        else:
            subexpr.append(expr)

    if not Bracket:
        # print subexpr
        return "%s" % (' '.join(subexpr))
    # Avoid Redundant Brackets
    if ForceBracket:
        return "(%s)" % (' '.join(subexpr))
    if len(subexpr) == 1:
        return "%s" % (' '.join(subexpr))
    else:
        return "(%s)" % (' '.join(subexpr))


# Declare Target Function
class SynFunction:
    def __init__(self, SynFunExpr):
        self.name = SynFunExpr[1]
        self.argList = SynFunExpr[2]
        self.retSort = SynFunExpr[3]
        self.Sorts = []
        for expr in self.argList:
            self.Sorts.append(get_sort(expr[1]))
        self.Sorts.append(get_sort(self.retSort))
        self.targetFunction = Function('__TARGET_FUNCTION__', *(self.Sorts))


class CheckST:
    def __init__(self):
        self.SynFunExpr = []
        self.SynFunction = None
        self.VarDecMap = {}
        self.VarDecList = []
        self.Constraints = []
        self.FunDefMap = {}
        self.VarTable = {}


class Checker:
    def __init__(self, synFunction, VarTable, Constraints):

        self.synFunction = synFunction
        self.VarTable = VarTable
        self.Constraints = Constraints
        self.solver = Solver()

    def check(self, funcDefStr):
        self.solver.push()

        spec_smt2 = [funcDefStr]
        for constraint in self.Constraints:
            spec_smt2.append('(assert %s)' % (to_string(constraint[1:])))
        spec_smt2 = '\n'.join(spec_smt2)
        # print spec_smt2
        spec = parse_smt2_string(spec_smt2, decls=dict(self.VarTable))
        spec = And(spec)
        self.solver.add(Not(spec))
        if verbose:
            print("spec:", spec)

        res = self.solver.check()
        if res == unsat:
            self.solver.pop()
            return None
        else:
            model = self.solver.model()
            self.solver.pop()
            return model


def read_query(bmExpr):
    st = CheckST()
    for expr in bmExpr:
        if len(expr) == 0:
            continue
        elif expr[0] == 'synth-fun':
            st.SynFunExpr = expr
        elif expr[0] == 'declare-var':
            st.VarDecMap[expr[1]] = expr
            st.VarDecList.append(expr[1])
        elif expr[0] == 'constraint':
            st.Constraints.append(expr)
        elif expr[0] == 'define-fun':
            st.FunDefMap[expr[1]] = expr

    if verbose:
        print(st.SynFunExpr)
        print(st.VarDecMap)
        print(st.FunDefMap)
        print(st.Constraints)

    # Declare Var
    for var in st.VarDecMap:
        st.VarTable[var] = declare_var(st.VarDecMap[var][2], var)

    st.SynFunction = SynFunction(st.SynFunExpr)

    checker = Checker(st.SynFunction, st.VarTable, st.Constraints)
    return checker, st
