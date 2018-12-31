import sys
import sexp
import translator
import copy
import cegis
import hint

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

(constraint (<= x (max2 x y)))
(constraint <= y (max2 x y))
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

tutorial = '''
(set-logic LIA)

(synth-fun rec ((x Int) (y Int) (z Int)) Int
	   (
	   (Start Int (x
	               y
   		       z
		       (* Start Start)
		       (+ Start Start)
		       (- Start Start)
	   ))))

(declare-var x1 Int)
(declare-var x2 Int)
(declare-var x3 Int)

(constraint (= (rec x1 x2 x3) (* (+ x1 x1) (- x2 x3))))

(check-synth)
'''


def extend(Stmts, Productions, Types, hint_clc):
    ret = []
    checknow = []
    for i in range(len(Stmts)):
        if not isinstance(Stmts[i], list):
            production_type = Types.get(Stmts[i])
            if production_type == 'Int':
                len_cond_list = len(hint_clc.hint_cond_list)
                len_compare = len(hint_clc.hint_compare)
                len_hint_const = len(hint_clc.hint_const)
                len_hint_list = len(hint_clc.hint_list)
                if len_cond_list > 0:
                    new_list, cur_list = hint_clc.gen_stmt_from_cond()
                    t_cond = hint_clc.hint_cond_list[-1]
                    cur_list.append(t_cond[1])

                    checknow.append(Stmts[0:i] + new_list + Stmts[i + 1:])
                    hint_clc.hint_cond_list = []

                elif len_compare > 0:
                    new_list, cur_list = hint_clc.gen_stmt_from_compare()
                    t_cmp = hint_clc.hint_compare[-1]
                    cur_list.append(t_cmp[1])

                    checknow.append(Stmts[0:i] + new_list + Stmts[i + 1:])
                    hint_clc.hint_compare = []

                elif len_hint_const > 0:
                    pass

                elif len_hint_list > 0:
                    t_list = hint_clc.hint_list[-1]
                    new_list = [t_list]

                    checknow.append(Stmts[0:i] + new_list + Stmts[i + 1:])
                    hint_clc.hint_list = []


            if Productions.has_key(Stmts[i]):
                for extended in Productions[Stmts[i]]:
                    ret.append(Stmts[0:i] + [extended] + Stmts[i + 1:])
        else:
            TryExtend = extend(Stmts[i], Productions, Types, hint_clc)
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


if __name__ == '__main__':
    benchmarkFile = open(sys.argv[1])
    # benchmarkFile = max2
    # benchmarkFile = idx3
    # benchmarkFile = s2
    # benchmarkFile = tutorial

    bm = strip_comments(benchmarkFile)
    bmExpr = sexp.sexp.parseString(bm, parseAll=True).asList()[0]  # Parse string to python list
    checker, st = translator.read_query(bmExpr)

    FuncDefine = ['define-fun'] + st.SynFunExpr[1:4]  # copy function signature
    FuncDefineStr = translator.to_string(FuncDefine,
                                         ForceBracket=True)  # use Force Bracket = True on function definition. MAGIC CODE. DO NOT MODIFY THE ARGUMENT ForceBracket = True.
    FuncCallList = [st.SynFunExpr[1]]
    for var in st.SynFunExpr[2]:
        FuncCallList.append(var[0])

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
    hint_clc = hint.Hint()
    hint_clc.build_parent_list(hinted_constraints)
    hint_clc.build_hint_from_constraints(hinted_constraints, FuncCallList, st)

    hint.sort_productions(Productions, Types)

    Count = 0
    Ans = None
    BfsQueue = [[StartSym]]  # Top-down
    while len(BfsQueue) != 0:
        Curr = BfsQueue.pop(0)
        # print("Extending "+str(Curr))
        TryExtend, checknow = extend(Curr, Productions, Types, hint_clc)
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
