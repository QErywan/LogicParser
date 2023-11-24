# Language for the parser

prop = 'pqrs'

def is_variable(char):
    if char in prop:
        return True
    return False

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
        

def parse(fmla):
    if not is_correct_parenthesis(fmla):
        return 0
    if len(fmla) == 1:
        if is_variable(fmla):
            return 1
    elif fmla[0] == '~' and len(fmla) > 1:
        return 7 if parse(fmla[1:]) else 0
    elif fmla[0] == '(':
        idx = findBinary(fmla)
        if idx:
            if parse(fmla[1:idx]) and parse(fmla[idx+2:-1]):
                return 8
        return 0
    return 0
    
def lhs(fmla):
    idx = findBinary(fmla)
    return fmla[1:idx]

def rhs(fmla):
    idx = findBinary(fmla)
    return fmla[idx+2:-1]

def con(fmla):
    idx = findBinary(fmla)
    return fmla[idx:idx+2]

    
if __name__ == '__main__':

    f = open('input.txt', 'r')

    firstLine = f.readline()

    parseOutputs = ['not a formula',
                'an atom',
                'a negation of a first order logic formula',
                'a universally quantified formula',
                'an existentially quantified formula',
                'a binary connective first order formula',
                'a proposition',
                'a negation of a propositional formula',
                'a binary connective propositional formula']
                
    PARSE = False
    if 'PARSE' in firstLine:
        PARSE = True
    SAT = False
    if 'SAT' in firstLine:
        SAT = True

    for line in f:
        if line[-1] == '\n':
            line = line[:-1]
        parsed = parse(line)
        # print(line, parsed)
        if PARSE:
            output = "%s is %s." % (line, parseOutputs[parsed])
            if parsed in [5,8]:
                output += " Its left hand side is %s, its connective is %s, and its right hand side is %s." % (lhs(line), con(line) ,rhs(line))
            print(output)

        # if SAT:
        #     if parsed:
        #         tableau = [theory(line)]
        #         print('%s %s.' % (line, satOutput[sat(tableau)]))
        #     else:
        #         print('%s is not a formula.' % line)
