# Author: Garvit Juniwal (garvitjuniwal@eecs.berkeley.edu)

# main.py is the main file that the user should run

import time
from translator import read_query
from synth import Synthesize
import sexp

benchmarkFileName = ""
doLog = False

max2 = '''

(set-logic LIA)

(synth-fun max3 ((x Int) (y Int) (z Int)) Int
    ((Start Int (x
                 y
                 z
                 0
                 1
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
(declare-var z Int)

(constraint (>= (max3 x y z) x))
(constraint (>= (max3 x y z) y))
(constraint (>= (max3 x y z) z))
(constraint (or (= x (max3 x y z))
            (or (= y (max3 x y z))
                (= z (max3 x y z)))))

(check-synth)
'''


# def parseArguments(args):
#     if not args:
#         return
#     option = args[0]
#     if option == "-file":
#         global benchmarkFileName
#         benchmarkFileName = args[1]
#         parseArguments(args[2:])
#     elif option == "-log":
#         global doLog
#         doLog = True
#         parseArguments(args[1:])
#     else:
#         raise Exception('Unknown command line option.')


def stripComments(bmFile):
    noComments = '('
    for line in bmFile:
        line = line.split(';', 1)[0]
        noComments += line
    return noComments + ')'


if __name__ == '__main__':
    # if (len(sys.argv) < 2):
    #     print 'Usage: %s -file <Synth File> \n' % sys.argv[0]
    #     sys.exit(1)
    AppStartTime = time.clock()

    # parseArguments(sys.argv[1:])
    # benchmarkFile = open(sys.argv[1])
    benchmarkFile = max2

    # try:
    # except:
    #     print 'No file found. Usage: %s -file <Synth File> \n' % sys.argv[0]
    bm = stripComments(benchmarkFile)
    bmExpr = sexp.sexp.parseString(bm, parseAll=True).asList()[0]

    numCopies = 1
    while True:
        (spec, specInputPorts,
         specConn, circuits) = read_query(bmExpr, numCopies)

        if Synthesize(spec, specInputPorts, specConn, circuits):
            break
        else:
            numCopies += 1

    AppFinishTime = time.clock()
    AppTotalTime = AppFinishTime - AppStartTime
