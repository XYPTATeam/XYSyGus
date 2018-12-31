from __future__ import print_function

import sys
import sexp
import translator
import copy
import cegis
import hint
import datetime


def eprint(*args, **kwargs):
    print(*args, file=sys.stderr, **kwargs)


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

s1 = '''
(set-logic LIA)

(synth-fun f ((x Int)) Int
   ((Start Int (x
                0 10 20 30 40 50 60 70 80 90 100
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

(constraint (= (f 0) 0))
(constraint (= (f 1) 10))
(constraint (= (f 2) 20))
(constraint (= (f 3) 30))
(constraint (= (f 4) 40))
(constraint (= (f 5) 50))
(constraint (or (and (> x 5) (= (f x) x)) (<= x 5)))



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

three = '''
(set-logic LIA)

(synth-fun f ((x Int)) Int
    ((Start Int (
                 x
                 3
                 7
                 10
                 (* Start Start)
                 (mod Start Start)))))

(declare-var x Int)

(constraint (= (f x) (f (+ x 10))))
(constraint (= (f 1) 3))
(constraint (= (f 2) 6))
(constraint (= (f 3) 9))
(constraint (= (f 4) 2))
(constraint (= (f 5) 5))
(constraint (= (f 6) 8))
(constraint (= (f 7) 1))
(constraint (= (f 8) 4))
(constraint (= (f 9) 7))
(constraint (= (f 0) 0))

(check-synth)
'''


def extend(Stmts, Productions, Types, hint_clc):
    ret = []
    checknow = []
    for i in range(len(Stmts)):
        if isinstance(Stmts[i], list):
            TryExtend, other = extend(Stmts[i], Productions, Types, hint_clc)
            if len(TryExtend) > 0:
                for extended in TryExtend:
                    if len(extended) != 0:
                        ret.append(Stmts[0:i] + [extended] + Stmts[i + 1:])
        else:
            production_type = Types.get(Stmts[i])

            if production_type == 'Int':
                new_list = hint_clc.gen_stmt_from_hint()
                if new_list is not None and len(new_list) > 0:
                    checknow.append(Stmts[0:i] + new_list + Stmts[i + 1:])

            if Productions.has_key(Stmts[i]):
                for extended in Productions[Stmts[i]]:
                    if len(extended) != 0:
                        ret.append(Stmts[0:i] + [extended] + Stmts[i + 1:])

    return ret, checknow


def strip_comments(bmFile):
    noComments = '('
    for line in bmFile:
        line = line.split(';', 1)[0]
        noComments += line
    return noComments + ')'


def calc_seq(l):
    global queue_seq
    queue_seq = []
    for i in l:
        seq = get_list_depth(i)
        queue_seq.append((l, seq))


def get_seq(i):
    global queue_seq
    for t in queue_seq:
        if t[0] == i:
            return t[1]
    return 0


def get_list_depth(l):
    if not isinstance(l, list):
        return 0

    max_depth = 0
    for i in l:
        t_depth = get_list_depth(i)
        if t_depth > max_depth:
            max_depth = t_depth
    return max_depth + 1


if __name__ == '__main__':
    if len(sys.argv) > 1:
        benchmarkFile = open(sys.argv[1])
    else:
        # benchmarkFile = max2
        # benchmarkFile = idx3
        # benchmarkFile = s1
        benchmarkFile = three
        # benchmarkFile = tutorial

    t_beginning = datetime.datetime.now()

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
                Productions[NTName].append(str(NT[1]))
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

        # calc_seq(BfsQueue)
        # BfsQueue.sort(key=get_seq)

    print(Ans)
    # timepassed = datetime.datetime.now() - t_beginning
    # rtimepassed = timepassed.seconds + timepassed.microseconds / 1000000.0
    # eprint('Time passed: ' + str(rtimepassed))

# Examples of counter-examples
# print (checker.check('(define-fun max2 ((x Int) (y Int)) Int 0)'))
# print (checker.check('(define-fun max2 ((x Int) (y Int)) Int x)'))
# print (checker.check('(define-fun max2 ((x Int) (y Int)) Int (+ x y))'))
# print (checker.check('(define-fun max2 ((x Int) (y Int)) Int (ite (<= x y) y x))'))
