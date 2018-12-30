from z3 import *
import copy

verbose = False

def declareVar(sort, name):
    if sort == "Int":
        return Int(name)
    if sort == 'Bool':
        return Bool(name)


def getSort(sort):
    if sort == "Int":
        return IntSort()
    if sort == "Bool":
        return BoolSort()


def toString(Expr, Bracket=True, ForceBracket=False):
    if type(Expr) == str:
        return Expr
    if type(Expr) == tuple:
        return (str(Expr[1]))  # todo: immediate
    subexpr = []
    for expr in Expr:
        if type(expr) == list:
            subexpr.append(toString(expr, ForceBracket=ForceBracket))
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


def ReadQuery(bmExpr):
    SynFunExpr = []
    VarDecMap = {}
    VarDecList = []
    Constraints = []
    FunDefMap = {}
    for expr in bmExpr:
        if len(expr) == 0:
            continue
        elif expr[0] == 'synth-fun':
            SynFunExpr = expr
        elif expr[0] == 'declare-var':
            VarDecMap[expr[1]] = expr
            VarDecList.append(expr[1])
        elif expr[0] == 'constraint':
            Constraints.append(expr)
        elif expr[0] == 'define-fun':
            FunDefMap[expr[1]] = expr

    if verbose:
        print(SynFunExpr)
        print(VarDecMap)
        print(FunDefMap)
        print(Constraints)

    VarTable = {}
    # Declare Var
    for var in VarDecMap:
        VarTable[var] = declareVar(VarDecMap[var][2], var)

    # Declare Target Function
    class SynFunction:
        def __init__(self, SynFunExpr):
            self.name = SynFunExpr[1]
            # TODO: arg and ret sort
            self.argList = SynFunExpr[2]
            self.retSort = SynFunExpr[3]
            self.Sorts = []
            for expr in self.argList:
                self.Sorts.append(getSort(expr[1]))
            self.Sorts.append(getSort(self.retSort))
            self.targetFunction = Function('__TARGET_FUNCTION__', *(self.Sorts))

    synFunction = SynFunction(SynFunExpr)

    class Checker:
        def __init__(self, VarTable, synFunction, Constraints):

            self.CEGISPositiveList = []
            self.CEGISNegativeList = []

            self.VarTable = VarTable

            self.synFunction = synFunction

            self.Constraints = Constraints

            self.solver = Solver()

        def check(self, funcDefStr):
            self.solver.push()

            spec_smt2 = [funcDefStr]
            for constraint in Constraints:
                spec_smt2.append('(assert %s)' % (toString(constraint[1:])))
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

        def add_positive_CEGIS(self):
            temp_contraints = copy.deepcopy(Constraints)
            func_list = []
            func_list.append(SynFunExpr[1])
            for var in VarDecList:
                func_list.append(var)
            self.check_in_constraint_list(temp_contraints, func_list)

            smt2 = []
            for var in VarDecMap:
                smt2.append('(declare-const {0} {1})'.format(var, VarDecMap[var][2]))
            smt2.append('(declare-const ret Int)')

            for constraint in temp_contraints:
                smt2.append('(assert %s)' % (toString(constraint[1:])))

            self.solver.push()
            str_smt2 = '\n'.join(smt2)
            spec = parse_smt2_string(str_smt2)
            self.solver.add(spec)

            res = self.solver.check()
            if res == sat:
                model = self.solver.model()
                d = {}
                for var in VarDecMap:
                    value = model.eval(VarTable[var])
                    sexpr = value.sexpr()
                    if sexpr.startswith('('):
                        sexpr = sexpr[1:-1]
                    val_str = sexpr.replace(' ','')
                    d[var] = int(val_str)
                ret = Int('ret')
                value = model.eval(ret)
                sexpr = value.sexpr()
                if sexpr.startswith('('):
                    sexpr = sexpr[1:-1]
                val_str = sexpr.replace(' ', '')
                d['ret'] = int(val_str)
                self.CEGISPositiveList.append(d)

            self.solver.pop()

        def check_in_constraint_list(self, l, target_list):
            target_len = len(target_list)
            l_len = len(l)
            flag = True
            for i in range(l_len):
                contex = l[i]
                if isinstance(contex, list):
                    flag = False
                    result = self.check_in_constraint_list(contex, target_list)
                    if result:
                        l[i] = 'ret'

            if not flag:
                return False

            for i in range(target_len):
                if l[i] != target_list[i]:
                    return False
            return True

        def add_negative_CEGIS(self, model, func_str):
            self.solver.push()
            str_list = []
            ret_str = '(declare-const ret Int)'
            str_list.append(ret_str)
            str_list.append(func_str)
            arg_list = []
            d = {}
            for arg in VarDecList:
                var = self.VarTable[arg]
                value = model.eval(var)
                sexpr = value.sexpr()
                if sexpr.startswith('('):
                    sexpr = sexpr[1:-1]
                val_str = sexpr.replace(' ', '')
                d[arg] = int(val_str)
                arg_list.append(str(value))
            func_ret_str = '(assert (= ret ({0} {1})))'.format(SynFunExpr[1], ' '.join(arg_list))
            str_list.append(func_ret_str)

            str_CEGIS = "\n".join(str_list).encode('utf8')

            spec = parse_smt2_string(str_CEGIS)
            res = self.solver.check(spec)
            if res == sat:
                res_model = self.solver.model()
                ret = Int('ret')
                value = res_model.eval(ret)
                sexpr = value.sexpr()
                if sexpr.startswith('('):
                    sexpr = sexpr[1:-1]
                val_str = sexpr.replace(' ', '')
                d['ret'] = int(val_str)

            self.CEGISNegativeList.append(d)
            self.solver.pop()

        def check_CEGIS(self, func_str):
            str_list = []
            ret_str = '(declare-const ret Int)'
            str_list.append(ret_str)
            str_list.append(func_str)

            for d in self.CEGISPositiveList:
                self.solver.push()
                arg_list = []
                for arg in VarDecList:
                    arg_list.append(str(d[arg]))
                func_ret_str = '(assert (= ret ({0} {1})))'.format(SynFunExpr[1], ' '.join(arg_list))
                str_list.append(func_ret_str)
                str_CEGIS = "\n".join(str_list).encode('utf8')
                str_list.pop(-1)
                spec = parse_smt2_string(str_CEGIS)

                res = self.solver.check(spec)
                if res == sat:
                    res_model = self.solver.model()
                    ret = Int('ret')
                    value = res_model.eval(ret)
                    sexpr = value.sexpr()
                    if sexpr.startswith('('):
                        sexpr = sexpr[1:-1]
                    val_str = sexpr.replace(' ', '')

                    if not d['ret'] == int(val_str):
                        return res_model

                self.solver.pop()

            for d in self.CEGISNegativeList:
                self.solver.push()
                arg_list = []
                for arg in VarDecList:
                    arg_list.append(str(d[arg]))
                func_ret_str = '(assert (= ret ({0} {1})))'.format(SynFunExpr[1], ' '.join(arg_list))
                str_list.append(func_ret_str)
                str_CEGIS = "\n".join(str_list).encode('utf8')
                str_list.pop(-1)
                spec = parse_smt2_string(str_CEGIS)

                res = self.solver.check(spec)
                if res == sat:
                    res_model = self.solver.model()
                    ret = Int('ret')
                    value = res_model.eval(ret)
                    sexpr = value.sexpr()
                    if sexpr.startswith('('):
                        sexpr = sexpr[1:-1]
                    val_str = sexpr.replace(' ', '')

                    if d['ret'] == int(val_str):
                        return res_model

                self.solver.pop()

            return None


    checker = Checker(VarTable, synFunction, Constraints)
    return checker
