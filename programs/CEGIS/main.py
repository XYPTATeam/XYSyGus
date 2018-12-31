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


def Extend(Stmts, Productions):
    ret = []
    for i in range(len(Stmts)):
        if type(Stmts[i]) == list:
            TryExtend = Extend(Stmts[i], Productions)
            if len(TryExtend) > 0:
                for extended in TryExtend:
                    ret.append(Stmts[0:i] + [extended] + Stmts[i + 1:])
        elif Productions.has_key(Stmts[i]):
            for extended in Productions[Stmts[i]]:
                ret.append(Stmts[0:i] + [extended] + Stmts[i + 1:])
    return ret


def stripComments(bmFile):
    noComments = '('
    for line in bmFile:
        line = line.split(';', 1)[0]
        noComments += line
    return noComments + ')'


if __name__ == '__main__':
    # benchmarkFile = open(sys.argv[1])
    benchmarkFile = max2
    bm = stripComments(benchmarkFile)
    bmExpr = sexp.sexp.parseString(bm, parseAll=True).asList()[0]  # Parse string to python list
    # checker = translator.ReadQuery(bmExpr)
    checker, st = translator.ReadQuery(bmExpr)
    StartSym = 'My-Start-Symbol'  # virtual starting symbol
    # SynFunExpr = []
    # for expr in bmExpr:
    #     if len(expr) == 0:
    #         continue
    #     elif expr[0] == 'synth-fun':
    #         SynFunExpr = expr
    FuncDefine = ['define-fun'] + st.SynFunExpr[1:4]  # copy function signature
    BfsQueue = [[StartSym]]  # Top-down
    Productions = {StartSym: []}
    FuncCallList = []
    FuncCallList.append(st.SynFunExpr[1])
    for var in st.VarDecList:
        FuncCallList.append(var)
    Type = {StartSym: st.SynFunExpr[3]}  # set starting symbol's return type

    for NonTerm in st.SynFunExpr[4]:  # SynFunExpr[4] is the production rules
        NTName = NonTerm[0]
        NTType = NonTerm[1]
        if NTType == Type[StartSym]:
            Productions[StartSym].append(NTName)
        Type[NTName] = NTType;
        Productions[NTName] = []
        for NT in NonTerm[2]:
            if type(NT) == tuple:
                Productions[NTName].append(str(NT[
                                                   1]))  # deal with ('Int',0). You can also utilize type information, but you will suffer from these tuples.
            else:
                Productions[NTName].append(NT)

    cegis.add_positive_CEGIS(checker, st, FuncCallList)

    Count = 0
    while (len(BfsQueue) != 0):
        Curr = BfsQueue.pop(0)
        # print("Extending "+str(Curr))
        TryExtend = Extend(Curr, Productions)
        if (len(TryExtend) == 0):  # Nothing to extend
            FuncDefineStr = translator.toString(FuncDefine,
                                                ForceBracket=True)  # use Force Bracket = True on function definition. MAGIC CODE. DO NOT MODIFY THE ARGUMENT ForceBracket = True.
            CurrStr = translator.toString(Curr)
            Str = FuncDefineStr[:-1] + ' ' + CurrStr + FuncDefineStr[
                -1]  # insert Program just before the last bracket ')'
            Count += 1

            CEGIS_example = cegis.check_CEGIS(checker, st, Str)
            if CEGIS_example == None:
                counterexample = checker.check(Str)
                # print counterexample
                if (counterexample == None):  # No counter-example
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
