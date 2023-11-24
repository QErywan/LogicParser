connectives = ['/\\', '', '=>']
preds = 'PQRS'
var = 'xyzw'
quantifiers = 'EA'

def is_variable(char):
    if char in var:
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
        elif char in ['/', '\\', '='] and len(stack) == 1:
            if correct_connective(fmla[i:i+2]):
                return i
            return False
    return False

def correct_connective(connective):
    if connective in ['/\\', '\/', '=>']:
        return True
    return False

def is_pred(fmla):
    if fmla[1] == '(' and fmla[-1] == ')':
        return is_variable(fmla[2]) and is_variable(fmla[4]) and fmla[3] == ','
    return False

def is_quantifier(fmla):
    if fmla[1] in var:
        if fmla[2] == '(' and fmla[-1] == ')':
            return 1
        return 2
    return 0

def parser(fmla):
    if not is_correct_parenthesis(fmla):
        return False
    if fmla[0] in preds:
        return is_pred(fmla)
    elif fmla[0] == '-':
        return parser(fmla[1:])
    # 0 = false, 1 = with (), 2 = without ()
    elif fmla[0] in quantifiers:
        num = is_quantifier(fmla)
        if num == 1:
            return parser(fmla[3:-1])
        elif num == 2:
            return parser(fmla[2:])
        return False
    elif fmla[0] == '(':
        idx = findBinary(fmla)
        if idx:
            return parser(fmla[1:idx]) and parser(fmla[idx+2:-1])
        return False
    return False