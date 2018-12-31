import sys
import sexp
import translator
import copy
import cegis

max2 = '''
(set-logic LIA)

(synth-fun max2 ((x Int) (y Int)) Int
    ((Start Int (x
                 y
                 (ite StartBool Start Start)))
     (StartBool Bool (
                      (<=  Start Start)
                      (=   Start Start)
                      (>=  Start Start)))))

(declare-var x Int)
(declare-var y Int)

(constraint (>= (max2 x y) x))
(constraint >= (max2 x y) y)
(constraint (or (= x (max2 x y))
				(= y (max2 x y))))


(check-synth)
'''

s2 = '''
(set-logic LIA)

(synth-fun f ((x Int) (y Int)) Int
   ((Start Int (x
                y
                0 1 -1 2 -2
                 (+ Start Start)
                 (- Start Start)
                 (ite StartBool Start Start)))
     (StartBool Bool ((and StartBool StartBool)
                      (or  StartBool StartBool)
                      (not StartBool)
                      (<=  Start Start)
                      (=   Start Start)
                      (>=  Start Start)))))

(declare-var x Int)
(declare-var y Int)

(constraint (or (and (= x y) (= (f x y) (+ x y)))
            (or (and (> x y) (= (f x y) 1))
				(and (< x y) (= (f x y) -1)))))

(check-synth)
'''

idx2 = '''
(set-logic LIA)
(synth-fun findIdx ( (y1 Int) (y2 Int) (k1 Int)) Int ((Start Int ( 0 1 2 y1 y2 k1 (ite BoolExpr Start Start))) (BoolExpr Bool ((< Start Start) (<= Start Start) (> Start Start) (>= Start Start)))))
(declare-var x1 Int)
(declare-var x2 Int)
(declare-var k Int)
(constraint (=> (< x1 x2) (=> (< k x1) (= (findIdx x1 x2 k) 0))))
(constraint (=> (< x1 x2) (=> (> k x2) (= (findIdx x1 x2 k) 2))))
(constraint (=> (< x1 x2) (=> (and (> k x1) (< k x2)) (= (findIdx x1 x2 k) 1))))
(check-synth)
'''

idx3 = '''
(set-logic LIA)
(synth-fun findIdx ( (y1 Int) (y2 Int) (y3 Int) (y4 Int) (k1 Int)) Int ((Start Int ( 0 1 2 3 4 y1 y2 y3 y4 k1 (ite BoolExpr Start Start))) (BoolExpr Bool ((< Start Start) (<= Start Start) (> Start Start) (>= Start Start)))))
(declare-var x1 Int)
(declare-var x2 Int)
(declare-var x3 Int)
(declare-var x4 Int)
(declare-var k Int)
(constraint (=> (and (< x1 x2) (and (< x2 x3) (< x3 x4))) (=> (< k x1) (= (findIdx x1 x2 x3 x4 k) 0))))
(constraint (=> (and (< x1 x2) (and (< x2 x3) (< x3 x4))) (=> (> k x4) (= (findIdx x1 x2 x3 x4 k) 4))))
(constraint (=> (and (< x1 x2) (and (< x2 x3) (< x3 x4))) (=> (and (> k x1) (< k x2)) (= (findIdx x1 x2 x3 x4 k) 1))))
(constraint (=> (and (< x1 x2) (and (< x2 x3) (< x3 x4))) (=> (and (> k x2) (< k x3)) (= (findIdx x1 x2 x3 x4 k) 2))))
(constraint (=> (and (< x1 x2) (and (< x2 x3) (< x3 x4))) (=> (and (> k x3) (< k x4)) (= (findIdx x1 x2 x3 x4 k) 3))))
(check-synth)
'''

compare_op = ['<', '<=', '>=', '>']
arithmetic_op = ['+', '-', '*', '/', 'mod']
logic_op = ['and', 'or', 'not', 'imply']


def extend(Stmts, Productions, Types, hint_list, hint_cond_list):
    ret = []
    checknow = []
    for i in range(len(Stmts)):
        if not isinstance(Stmts[i], list):
            production_type = Types.get(Stmts[i])
            if production_type == 'Int':
                len_cond_list = len(hint_cond_list)
                if len_cond_list > 0:
                    new_list = []
                    cur_list = new_list
                    for idx in range(len_cond_list - 1):
                        t_cond = hint_cond_list[idx]
                        cond = t_cond[0]
                        expr = t_cond[1]
                        cur_list.append('ite')
                        cur_list.append(cond)
                        cur_list.append(expr)
                        next_list = []
                        cur_list.append(next_list)
                        cur_list = next_list
                    t_cond = hint_cond_list[-1]
                    cur_list.append(t_cond[1])

                    checknow.append(Stmts[0:i] + new_list + Stmts[i + 1:])
                    hint_cond_list = []

            if Productions.has_key(Stmts[i]):
                for extended in Productions[Stmts[i]]:
                    ret.append(Stmts[0:i] + [extended] + Stmts[i + 1:])
        else:
            TryExtend = extend(Stmts[i], Productions, Types, hint_list, hint_cond_list)
            if len(TryExtend) > 0:
                for extended in TryExtend:
                    ret.append(Stmts[0:i] + [extended] + Stmts[i + 1:])
    return ret, checknow


def strip_comments(bmFile):
    noComments = '('
    for line in bmFile:
        line = line.split(';', 1)[0]
        noComments += line
    return noComments + ')'


def sort_productions(productions, types):
    for start_name in productions:
        production_list = productions[start_name]
        production_type = types[start_name]
        if production_type == 'Int':
            new_list = []
            pending_list = []
            for expr in production_list:
                if isinstance(expr, list):
                    pending_list.append(expr)
                else:
                    new_list.append(expr)

            for expr in pending_list:
                new_list.append(expr)
            productions[start_name] = new_list
        elif production_type == 'Bool':
            new_list = []
            pending_list = []
            for expr in production_list:
                if isinstance(expr, list):
                    op = expr[0]
                    if op in logic_op:
                        pending_list.append(expr)
                    else:
                        new_list.append(expr)
                else:
                    new_list.append(expr)

            for expr in pending_list:
                new_list.append(expr)
            productions[start_name] = new_list


def build_parent_list(l, parent_tuple_list):
    for i in l:
        if isinstance(i, list):
            parent_tuple_list.append((i, l))
            build_parent_list(i, parent_tuple_list)


def get_form_parent_list(l, parent_tuple_list):
    for t in parent_tuple_list:
        if t[0] == l:
            return t[1]

    return None


def hint_from_constraints(hinted_constraints, func_list, parent_map):
    hint_cond_list = []  # type: tuple(cond, expr)
    hint_list = []
    # check function list
    for constraint in hinted_constraints:
        if not isinstance(constraint, list):
            continue
        check_i(constraint, func_list, parent_map, hint_list, hint_cond_list)

    return hint_list, hint_cond_list


def check_i(l, target_list, parent_list, hint_list, hint_cond_list):
    target_len = len(target_list)
    l_len = len(l)
    may_be_func = True
    has_func = -1
    for i in range(l_len):
        context = l[i]
        if isinstance(context, list):
            may_be_func = False
            result = check_i(context, target_list, parent_list, hint_list, hint_cond_list)
            if result:
                has_func = i

    if has_func > 0:
        op = l[0]
        if op == '=':
            other_expr = None
            if has_func == 1:
                other_expr = l[2]
            elif has_func == 2:
                other_expr = l[1]
            other_expr = format_expr(other_expr)

            if other_expr is not None:
                parent = get_form_parent_list(l, parent_list)
                if parent is None:
                    hint_list.append(other_expr)
                else:
                    parent_op = parent[0]
                    if parent_op == 'and' or parent_op == '=>':
                        cond_expr = None
                        if parent[1] == l:
                            cond_expr = parent[2]
                        elif parent[2] == l:
                            cond_expr = parent[1]
                        if cond_expr is not None:
                            hint_cond_list.append((cond_expr, other_expr))
                    elif parent_op == 'or':
                        hint_list.append(other_expr)
        elif op in compare_op:
            pass
        else:
            pass

    if not may_be_func:
        return False

    for i in range(target_len):
        if l[i] != target_list[i]:
            return False
    return True


def format_expr(expr):
    if isinstance(expr, tuple):
        expr = str(expr[1])
    return expr


def contain_func(l, func_name):
    for i in l:
        if isinstance(i, list):
            if contain_func(i, func_name):
                return True
        else:
            if i == func_name:
                return True
    return False


if __name__ == '__main__':
    benchmarkFile = open(sys.argv[1])
    # benchmarkFile = max2
    # benchmarkFile = idx3
    # benchmarkFile = s2

    bm = strip_comments(benchmarkFile)
    bmExpr = sexp.sexp.parseString(bm, parseAll=True).asList()[0]  # Parse string to python list
    checker, st = translator.read_query(bmExpr)

    FuncDefine = ['define-fun'] + st.SynFunExpr[1:4]  # copy function signature
    FuncDefineStr = translator.to_string(FuncDefine,
                                         ForceBracket=True)  # use Force Bracket = True on function definition. MAGIC CODE. DO NOT MODIFY THE ARGUMENT ForceBracket = True.
    FuncCallList = [st.SynFunExpr[1]]
    for var in st.VarDecList:
        FuncCallList.append(var)

    StartSym = 'My-Start-Symbol'  # virtual starting symbol
    Productions = {StartSym: []}
    Types = {StartSym: st.SynFunExpr[3]}  # set starting symbol's return type
    for NonTerm in st.SynFunExpr[4]:  # SynFunExpr[4] is the production rules
        NTName = NonTerm[0]
        NTType = NonTerm[1]
        if NTType == Types[StartSym]:
            Productions[StartSym].append(NTName)
        Types[NTName] = NTType;
        Productions[NTName] = []
        for NT in NonTerm[2]:
            if type(NT) == tuple:
                Productions[NTName].append(str(NT[
                                                   1]))  # deal with ('Int',0). You can also utilize type information, but you will suffer from these tuples.
            else:
                Productions[NTName].append(NT)

    cegis.add_positive_CEGIS(checker, st, FuncCallList)

    hinted_constraints = copy.deepcopy(st.Constraints)
    parent_list = []
    build_parent_list(hinted_constraints, parent_list)
    hint_list, hint_cond_list = hint_from_constraints(hinted_constraints, FuncCallList, parent_list)

    sort_productions(Productions, Types)

    Count = 0
    Ans = None
    BfsQueue = [[StartSym]]  # Top-down
    while len(BfsQueue) != 0:
        Curr = BfsQueue.pop(0)
        # print("Extending "+str(Curr))
        TryExtend, checknow = extend(Curr, Productions, Types, hint_list, hint_cond_list)
        break_flag = False
        if len(checknow) != 0:
            for check_stmt in checknow:
                cur_str = translator.to_string(check_stmt)
                stmt2_str = FuncDefineStr[:-1] + ' ' + cur_str + FuncDefineStr[
                    -1]
                counterexample = checker.check(stmt2_str)
                if counterexample is None:  # No counter-example
                    Ans = stmt2_str
                    break_flag = True
                    break
        if break_flag:
            break

        if len(TryExtend) == 0:  # Nothing to extend
            CurrStr = translator.to_string(Curr)
            Str = FuncDefineStr[:-1] + ' ' + CurrStr + FuncDefineStr[
                -1]  # insert Program just before the last bracket ')'
            Count += 1

            CEGIS_example = cegis.check_CEGIS(checker, st, Str)
            if CEGIS_example is None:
                counterexample = checker.check(Str)
                if counterexample is None:  # No counter-example
                    Ans = Str
                    break
                else:
                    cegis.add_negative_CEGIS(checker, st, counterexample, Str)

        TE_set = set()
        for TE in TryExtend:
            TE_str = str(TE)
            if not TE_str in TE_set:
                BfsQueue.append(TE)
                TE_set.add(TE_str)

    print(Ans)

# Examples of counter-examples
# print (checker.check('(define-fun max2 ((x Int) (y Int)) Int 0)'))
# print (checker.check('(define-fun max2 ((x Int) (y Int)) Int x)'))
# print (checker.check('(define-fun max2 ((x Int) (y Int)) Int (+ x y))'))
# print (checker.check('(define-fun max2 ((x Int) (y Int)) Int (ite (<= x y) y x))'))
