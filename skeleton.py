# TODO
# 1. Change the parser

MAX_CONSTANTS = 10

prop = 'pqrs'
connectives = ['/\\', '', '=>']
preds = 'PQRS'
var = 'xyzw'
quantifiers = 'EA'
constants = ['c' + str(i) for i in range(MAX_CONSTANTS)]

''' Helper functions Parser'''

def is_prop(char):
    if char in prop:
        return True
    return False

def is_variable(char):
    if char in var:
        return True
    return False

def is_pred(fmla):
    if fmla[1] == '(' and fmla[-1] == ')':
        return is_variable(fmla[2]) and is_variable(fmla[4]) and fmla[3] == ',' and fmla[5] == ')'
    return False

def is_quantifier(fmla):
    if fmla[1] in var:
        if fmla[0] == 'E':
            return 1
        elif fmla[0] == 'A':
            return 2    
    return 0

def is_correct_parenthesis(input):
    stack = []
    for char in input:
        if char == '(':
            stack.append(char)
        elif char == ')':
            if stack and stack[-1] == '(':
                stack.pop()
            else:
                return False
    return len(stack) == 0

def findBinary(fmla):
    stack = []
    for i, char in enumerate(fmla):
        if char == '(':
            stack.append(char)
        elif char == ')':
            stack.pop()
        elif char in ['/', "\\", '='] and len(stack) == 1:
            if correct_connective(fmla[i:i+2]):
                return i
            return False
    return False

def correct_connective(connective):
    if connective in ['/\\', '\/', '=>']:
        return True
    return False

def is_fol(fmla):
    if 'E' in fmla or 'A' in fmla:
        return True
    return False


''' Helper functions Tableau '''



# Parse a formula, consult parseOutputs for return values.
def parse(fmla):
    if not is_correct_parenthesis(fmla):
        return 0
    
    if len(fmla) == 1:
        if is_prop(fmla):
            return 6
        return 0
    
    elif fmla[0] == '~' and len(fmla) > 1:
        if is_fol(fmla):
            return 2 if parse(fmla[1:]) else 0
        return 7 if parse(fmla[1:]) else 0
    
    elif fmla[0] in preds:
        return 6 if is_pred(fmla) else 0
    
    elif fmla[0] in quantifiers:
        num = is_quantifier(fmla)
        if num == 1:
            return 4 if parse(fmla[2:]) else 0
        elif num == 2:
            return 3 if parse(fmla[2:]) else 0
        return 0
    
    elif fmla[0] == '(':
        idx = findBinary(fmla)
        if idx:
            if parse(fmla[1:idx]) and parse(fmla[idx+2:-1]):
                if is_fol(fmla):
                    return 5
                return 8
        return 0

    return 0

# Return the LHS of a binary connective formula
def lhs(fmla):
    idx = findBinary(fmla)
    return fmla[1:idx]

# Return the connective symbol of a binary connective formula
def con(fmla):
    idx = findBinary(fmla)
    return fmla[idx:idx+2]

# Return the RHS symbol of a binary connective formula
def rhs(fmla):
    idx = findBinary(fmla)
    return fmla[idx+2:-1]


# You may choose to represent a theory as a set or a list
def theory(fmla):#initialise a theory with a single formula in it
    theory = [fmla]
    return theory

def branch_closes(list_of_formulas):
    s = set(list_of_formulas)
    for fmla in list_of_formulas:
        if '~' + fmla in s:
            return True
    return False


def clean_negations(fmla):
    i = 0
    while fmla[i] == '~':
        i += 1
    if i % 2 == 1:
        return fmla[i - 1:]
    return fmla[i:]

def is_gamma(fmla):
    if fmla[0] == 'A':
        return True
    return False

def is_existential(fmla):
    if fmla[0] == 'E':
        return True
    return False

def is_all_expanded(theory):
    for i in theory:
        if i[0] == '~':
            if (not is_prop(i[1:]) and not i[0] in preds) or is_existential(i):
                return False
        else:
            if (not is_prop(i) and not i[0] in preds) or is_gamma(i):
                return False
    return True


# 0 for ~~, 1 for /\, 2 for ~=>, 3 for ~\/
def alpha_expansion(fmla, t):
    if t == 0:
        return [fmla[2:]]
    elif t == 1:
        idx = findBinary(fmla)
        return [fmla[1:idx], fmla[idx+2:-1]]
    elif t == 2:
        idx = findBinary(fmla)
        return [fmla[1:idx], '~' + fmla[idx+2:-1]]
    elif t == 3:
        idx = findBinary(fmla)
        return ['~' + fmla[1:idx], '~' + fmla[idx+2:-1]]
    
# 0 for ~/\, 1 for \/, 2 for =>
def beta_expansion(fmla, t):
    idx = findBinary(fmla)
    if t == 0:
        return '~' + fmla[1:idx], '~' + fmla[idx+2:-1]
    elif t == 1:
        idx = findBinary(fmla)
        return fmla[1:idx], fmla[idx+2:-1]
    elif t == 2:
        return '~' + fmla[1:idx], fmla[idx+2:-1]
    
def delta_expansion(fmla, const):
    return fmla[2:].replace(fmla[1], constants[const])


def gamma_expansion(fmla, const):
    return fmla.replace(fmla[1], constants[const])

#check for satisfiability
def sat(tableau):
#output 0 if not satisfiable, output 1 if satisfiable, output 2 if number of constants exceeds MAX_CONSTANTS
    constCount = 0
    q = tableau.copy()

    while q:
        if constCount > MAX_CONSTANTS:
            return 2
        # print("q", q)
        branch = q.pop(0)
        
        # print("branch:", branch)
        # print(1,branch, q)
        # check if branch closes, if so no need to add bac to the queue
        if len(branch) == 0 or branch_closes(branch):
            continue

        # should be changed from is_all_proposition to fully expanded and check if its an not closed branch
        if is_all_expanded(branch) and not branch_closes(branch):
            return 1

        # iterate through the branch
        for fmla in branch:
            # print("formula:", fmla)
            if fmla[0] == '~':
                if fmla[1] == '~':
                    branch.remove(fmla)
                    branch = branch + alpha_expansion(fmla, 0)
                    q.append(branch)
                elif con(fmla[1:]) == '=>':
                    branch.remove(fmla)
                    branch = branch + alpha_expansion(fmla[1:], 2)
                    q.append(branch)
                elif con(fmla[1:]) == '\/':
                    branch.remove(fmla)
                    branch = branch + alpha_expansion(fmla[1:], 3)
                    q.append(branch)
                elif con(fmla[1:]) == '/\\':
                    branch.remove(fmla)
                    b1, b2 = beta_expansion(fmla[1:], 0)
                    branch1 = branch + [b1]
                    branch2 = branch + [b2]
                    q.append(branch1)
                    q.append(branch2)
                break
            if fmla[0] == '(':
                if con(fmla) == '/\\':
                    branch.remove(fmla)
                    branch = branch + alpha_expansion(fmla, 1)
                    q.append(branch)
                elif con(fmla) == '=>':
                    branch.remove(fmla)
                    b1, b2 = beta_expansion(fmla, 2)
                    branch1 = branch + [b1]
                    branch2 = branch + [b2]
                    q.append(branch1)
                    q.append(branch2)
                elif con(fmla) == '\/':
                    branch.remove(fmla)
                    b1, b2 = beta_expansion(fmla, 1)
                    branch1 = branch + [b1]
                    branch2 = branch + [b2]
                    q.append(branch1)
                    q.append(branch2)
                break
            if fmla[0] == 'A':
                branch.remove(fmla)
                branch.append(fmla)
                for i in range(constCount):
                    branch.append(gamma_expansion(fmla, i))
                q.append(branch)
                break
            if fmla[0] == 'E':
                branch.remove(fmla)
                branch.append(delta_expansion(fmla, constCount))
                constCount += 1
                q.append(branch)
                print("Delta")
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