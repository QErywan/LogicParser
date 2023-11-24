MAX_CONSTANTS = 10

propositions = 'pqrs'
connectives = ['/\\', '\/', '=>']
predicates = 'PQRS'
variables = 'xyzw'
quantifiers = 'EA'
constants = [chr(i+97) for i in range(MAX_CONSTANTS)]


''' Helpers '''
def checkParenthesis(fmla):
    stack = []
    for char in fmla:
        if char == '(':
            stack.append(char)
        elif char == ')':
            if stack and stack[-1] == '(':
                stack.pop()
            else:
                return False
    return len(stack) == 0

def propLogic(fmla):
    if 'E' in fmla or 'A' in fmla:
        return False
    return True

def checkPredicates(fmla):
    if fmla[1] == '(' and fmla[-1] == ')':
        return fmla[2] in variables and fmla[4] in variables and fmla[3] == ',' and fmla[5] == ')'
    return False

def findCon(fmla):
    stack = []
    for i, char in enumerate(fmla):
        if char == '(':
            stack.append(char)
        elif char == ')':
            stack.pop()
        elif char in ['/', "\\", '='] and len(stack) == 1:
            if (fmla[i:i+2]) in connectives:
                return i
            return False
    return False


# Parse a formula, consult parseOutputs for return values.
def parse(fmla):
    if not checkParenthesis(fmla):
        return 0
    
    propositional = False

    if propLogic(fmla):
        propositional = True

    if fmla in propositions:
        return 6
    
    elif fmla[0] in predicates:
        if checkPredicates(fmla):
            return 1 
    
    elif fmla[0] == '~':
        if propositional:
            return 7 if parse(fmla[1:]) else 0
        return 2 if parse(fmla[1:]) else 0
    elif fmla[0] == '(':
        idx = findCon(fmla)
        if idx:
            if parse(fmla[1:idx]) and parse(fmla[idx+2:-1]):
                return 8 if propositional else 5
            return 0
    elif fmla[0] in quantifiers:
        if fmla[1] in variables:
            if fmla[0] == 'E':
                return 4 if parse(fmla[2:]) else 0
            elif fmla[0] == 'A':
                return 3 if parse(fmla[2:]) else 0
        return 0
    
    return 0

# Return the LHS of a binary connective formula
def lhs(fmla):
    idx = findCon(fmla)
    return fmla[1:idx]

# Return the connective symbol of a binary connective formula
def con(fmla):
    idx = findCon(fmla)
    return fmla[idx:idx+2]

# Return the RHS of a binary connective formula
def rhs(fmla):
    idx = findCon(fmla)
    return fmla[idx+2:-1]

# You may choose to represent a theory as a set or a list
def theory(fmla): # initialise a theory with a single formula in it
    theory = [fmla]
    return theory

''' Helpers 2'''

def gamma(fmla):
    return fmla[0] == 'A'

def gammaPred(fmla):
    if fmla[0] == 'A':
        if fmla[2] in predicates or gammaPred(fmla[2:]):
            return True
    return False

def gammaExistenstial(fmla, negation):
    if (fmla[0] == 'A' and fmla[2] == 'E') or (fmla[0] == 'E' and fmla[2] == 'A') and negation:
            return True
    return False

def branchClose(branch):
    for fmla in branch:
        if fmla[0] == '~' and fmla[1:] in branch:
            return True
        if '~' + fmla in branch:
            return True
    return False

def expanded(branch):
    for fmla in branch:
        if not literal(fmla):
            if not gammaPred(fmla):
                return False
    return True
        
def literal(fmla):
    if fmla[0] == '~':
        if fmla[1:] in propositions or fmla[1] in predicates:
            return True
    elif fmla in propositions or fmla[0] in predicates:
        return True
    return False

def swapVar(fmla, curConst):
    # Cases:
    '''
        ExPxx
        ExAyPxy
        ExAy(Pxy /\ Qxy)
        ExAy(Pxy /\ ExQxy)
    '''
    var = fmla[1]
    changedFmla = ""
    for i in range(2,len(fmla)):
        if fmla[i] in quantifiers and fmla[i+1] == var:
            changedFmla += fmla[i:]
            break
        if fmla[i] == var:
            changedFmla += constants[curConst]
        else:
            changedFmla += fmla[i]
    return changedFmla

def gammaSwap(fmla, curConst):
    var = fmla[1]
    fmlas = []
    for i in range(curConst):
        fmlas.append(fmla[2:].replace(var, constants[i]))
    return fmlas


#check for satisfiability
def sat(tableau):
#output 0 if not satisfiable, output 1 if satisfiable, output 2 if number of constants exceeds MAX_CONSTANTS
    q = tableau
    curConst = 0
    # fmla : [used terms]
    gammaMap = {}

    while q:
        branch = q.pop(0)

        if curConst >= MAX_CONSTANTS:
            return 2

        if branchClose(branch):
            continue
        if expanded(branch) and not branchClose(branch):
            return 1
        
        for i,fmla in enumerate(branch):
            negation = False
            if literal(fmla):
                continue

            if fmla[0] == '~':
                if fmla[1] == '~':
                    branch.pop(i)
                    branch.append(fmla[2:])
                    q.append(branch)
                    break
                negation = True
                fmla = fmla[1:]

            if fmla[0] in quantifiers:
                if gamma(fmla):
                    if negation:
                        # delta expansion
                        branch.pop(i)
                        fmla = swapVar(fmla, curConst)
                        curConst += 1
                        branch.append('~' + fmla)
                        q.append(branch)
                        break
                    else:
                        # gamma expansion
                        gammaFmla = branch.pop(i)
                        if gammaExistenstial(gammaFmla, negation):
                            for i in range(curConst):
                                fmla = swapVar(gammaFmla, i)
                                branch.extend([fmla] + [gammaFmla])
                            q.append(branch)
                            break
                        else:
                            if fmla in gammaMap:
                                for i in range(curConst+1):
                                    if constants[i] in gammaMap[fmla]:
                                        if i == curConst - 1:
                                            curConst += 1
                                        continue
                                    fmla = swapVar(gammaFmla, i)
                                    gammaMap[gammaFmla].append(constants[i])
                                    branch.extend([fmla] + [gammaFmla])
                                    q.append(branch)
                                    break
                            else:
                                gammaMap[gammaFmla] = []
                                for i in range(curConst):
                                    fmla = swapVar(gammaFmla, i)
                                    gammaMap[gammaFmla].append(constants[i])
                                    branch.extend([fmla] + [gammaFmla])
                                    q.append(branch)
                                    break

                else:
                    if negation:
                        # gamma expansion
                        gammaFmla = branch.pop(i)[1:]
                        if gammaExistenstial(gammaFmla, negation):
                            # might be wrong
                            for i in range(curConst):
                                print('here')
                                fmla = swapVar(gammaFmla, i)
                                branch.extend(['~' + fmla] + [gammaFmla])
                            q.append(branch)
                            break
                        else:
                            if fmla in gammaMap:
                                for i in range(curConst):
                                    if constants[i] in gammaMap[fmla]:
                                        continue
                                    fmla = swapVar(gammaFmla, i)
                                    gammaMap[gammaFmla].append(constants[i])
                                    branch.extend(['~' + fmla] + [gammaFmla])
                                    q.append(branch)
                                    break
                            else:
                                gammaMap[gammaFmla] = []
                                for i in range(curConst+1):
                                    fmla = swapVar(gammaFmla, i)
                                    gammaMap[gammaFmla].append(constants[i])
                                    branch.extend(['~' + fmla] + [gammaFmla])
                                    q.append(branch)
                                    break
                    else:
                        # delta expansion
                        branch.pop(i)
                        fmla = swapVar(fmla, curConst)
                        curConst += 1
                        branch.append(fmla)
                        q.append(branch)
                        break
                    
            
            elif con(fmla) == '/\\':
                branch.pop(i)
                if negation:
                    # beta expansion
                    branch1 = branch + [ '~' + lhs(fmla)]
                    branch2 = branch + [ '~' + rhs(fmla)]
                    q.extend([branch1, branch2])
                else:
                    # alpha expansion
                    branch.extend([lhs(fmla), rhs(fmla)])
                    q.append(branch)
                break
            elif con(fmla) == '\/':
                branch.pop(i)
                if negation:
                    # alpha expansion
                    branch.extend(['~' + lhs(fmla), '~' + rhs(fmla)])
                    q.append(branch)
                else:
                    # beta expansion
                    branch1 = branch + [lhs(fmla)]
                    branch2 = branch + [rhs(fmla)]
                    q.extend([branch1, branch2])
                break
            elif con(fmla) == '=>':
                branch.pop(i)
                if negation:
                    # alpha expansion
                    branch.extend([lhs(fmla), '~' + rhs(fmla)])
                    q.append(branch)
                else:
                    # beta expansion
                    branch1 = branch + ['~' + lhs(fmla)]
                    branch2 = branch + [rhs(fmla)]
                    q.extend([branch1, branch2])
                break
    return 0


            

#DO NOT MODIFY THE CODE BELOW
f = open('input.txt')

parseOutputs = ['not a formula', # 0
                'an atom', # 1
                'a negation of a first order logic formula', # 2
                'a universally quantified formula', # 3
                'an existentially quantified formula', # 4
                'a binary connective first order formula', # 5
                'a proposition', # 6
                'a negation of a propositional formula', # 7
                'a binary connective propositional formula'] # 8

satOutput = ['is not satisfiable', 'is satisfiable', 'may or may not be satisfiable']



firstline = f.readline()

PARSE = False
if 'PARSE' in firstline:
    PARSE = True

SAT = False
if 'SAT' in firstline:
    SAT = True

for line in f:
    if line[-1] == '\n':
        line = line[:-1]
    parsed = parse(line)

    if PARSE:
        output = "%s is %s." % (line, parseOutputs[parsed])
        if parsed in [5,8]:
            output += " Its left hand side is %s, its connective is %s, and its right hand side is %s." % (lhs(line), con(line) ,rhs(line))
        print(output)

    if SAT:
        if parsed:
            tableau = [theory(line)]
            print('%s %s.' % (line, satOutput[sat(tableau)]))
        else:
            print('%s is not a formula.' % line)
