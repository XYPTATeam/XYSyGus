from z3 import *
import translator
CEGISPositiveList = []
CEGISNegativeList = []


def add_positive_CEGIS(checker, st, target_list):
    temp_contraints = copy.deepcopy(st.Constraints)

    check_in_constraint_list(temp_contraints, target_list)

    smt2 = []
    for var in st.VarDecMap:
        smt2.append('(declare-const {0} {1})'.format(var, st.VarDecMap[var][2]))
    smt2.append('(declare-const ret Int)')

    for constraint in temp_contraints:
        smt2.append('(assert %s)' % (translator.toString(constraint[1:])))

    checker.solver.push()
    str_smt2 = '\n'.join(smt2)
    spec = parse_smt2_string(str_smt2)
    checker.solver.add(spec)

    res = checker.solver.check()
    if res == sat:
        model = checker.solver.model()
        d = {}
        for var in st.VarDecMap:
            value = model.eval(st.VarTable[var])
            sexpr = value.sexpr()
            if sexpr.startswith('('):
                sexpr = sexpr[1:-1]
            val_str = sexpr.replace(' ', '')
            d[var] = int(val_str)
        ret = Int('ret')
        value = model.eval(ret)
        sexpr = value.sexpr()
        if sexpr.startswith('('):
            sexpr = sexpr[1:-1]
        val_str = sexpr.replace(' ', '')
        d['ret'] = int(val_str)
        CEGISPositiveList.append(d)

    checker.solver.pop()


def check_in_constraint_list(l, target_list):
    target_len = len(target_list)
    l_len = len(l)
    flag = True
    for i in range(l_len):
        contex = l[i]
        if isinstance(contex, list):
            flag = False
            result = check_in_constraint_list(contex, target_list)
            if result:
                l[i] = 'ret'

    if not flag:
        return False

    for i in range(target_len):
        if l[i] != target_list[i]:
            return False
    return True


def add_negative_CEGIS(checker, st, model, func_str):
    checker.solver.push()
    str_list = []
    ret_str = '(declare-const ret Int)'
    str_list.append(ret_str)
    str_list.append(func_str)
    arg_list = []
    d = {}
    for arg in st.VarDecList:
        var = st.VarTable[arg]
        value = model.eval(var)
        if not isinstance(value, IntNumRef):
            return
        sexpr = value.sexpr()
        if sexpr.startswith('('):
            sexpr = sexpr[1:-1]
        val_str = sexpr.replace(' ', '')
        d[arg] = int(val_str)
        arg_list.append(str(value))
    func_ret_str = '(assert (= ret ({0} {1})))'.format(st.SynFunExpr[1], ' '.join(arg_list))
    str_list.append(func_ret_str)

    str_CEGIS = "\n".join(str_list).encode('utf8')

    spec = parse_smt2_string(str_CEGIS)
    res = checker.solver.check(spec)
    if res == sat:
        res_model = checker.solver.model()
        ret = Int('ret')
        value = res_model.eval(ret)
        sexpr = value.sexpr()
        if sexpr.startswith('('):
            sexpr = sexpr[1:-1]
        val_str = sexpr.replace(' ', '')
        d['ret'] = int(val_str)

    CEGISNegativeList.append(d)
    checker.solver.pop()


def check_CEGIS(checker, st, func_str):
    str_list = []
    ret_str = '(declare-const ret Int)'
    str_list.append(ret_str)
    str_list.append(func_str)

    for d in CEGISPositiveList:
        checker.solver.push()
        arg_list = []
        for arg in st.VarDecList:
            arg_list.append(str(d[arg]))
        func_ret_str = '(assert (= ret ({0} {1})))'.format(st.SynFunExpr[1], ' '.join(arg_list))
        str_list.append(func_ret_str)
        str_CEGIS = "\n".join(str_list).encode('utf8')
        str_list.pop(-1)
        spec = parse_smt2_string(str_CEGIS)

        res = checker.solver.check(spec)
        if res == sat:
            res_model = checker.solver.model()
            ret = Int('ret')
            value = res_model.eval(ret)
            sexpr = value.sexpr()
            if sexpr.startswith('('):
                sexpr = sexpr[1:-1]
            val_str = sexpr.replace(' ', '')

            if not d['ret'] == int(val_str):
                return res_model

        checker.solver.pop()

    for d in CEGISNegativeList:
        checker.solver.push()
        arg_list = []
        for arg in st.VarDecList:
            arg_list.append(str(d[arg]))
        func_ret_str = '(assert (= ret ({0} {1})))'.format(st.SynFunExpr[1], ' '.join(arg_list))
        str_list.append(func_ret_str)
        str_CEGIS = "\n".join(str_list).encode('utf8')
        str_list.pop(-1)
        spec = parse_smt2_string(str_CEGIS)

        res = checker.solver.check(spec)
        if res == sat:
            res_model = checker.solver.model()
            ret = Int('ret')
            value = res_model.eval(ret)
            sexpr = value.sexpr()
            if sexpr.startswith('('):
                sexpr = sexpr[1:-1]
            val_str = sexpr.replace(' ', '')

            if d['ret'] == int(val_str):
                return res_model

        checker.solver.pop()

    return None
