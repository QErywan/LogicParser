''' Language for the parser '''
# FMLA := PROP | -FMLA | (FMLA*FMLA)
# PROP := p | q | r | s
# * := /\ | \/ | => (and, or, implies)

# example
form = "- ( p => p )"

class TabParser():
    class Node:
        def __init__(self, fmla, children=None):
            self.fmla = fmla
            self.children = children if children else []

        def addChild(self, child):
            self.children.append(child)

    def __init__(self):
        self.tokens = []
    
    def parse(self, fmla):
        self.tokens = fmla.split()
        return self.parseFmla()
    
    def parseFmla(self):
        token = self.tokens.pop(0)
        if token in {'p', 'q', 'r', 's'}:
            return self.Node(token)
        elif token == '-':
            return self.Node('not', [self.parseFmla()])
        elif token == '(':
            left = self.parseFmla()
            operator = self.tokens.pop(0)
            right = self.parseFmla()
            if self.tokens.pop(0) != ')':
                raise Exception('Expected ")"')
            return self.Node(operator, [left, right])
        else:
            raise Exception('Unexpected token: ' + token)
    
    def isSatisfiable(self, node):
        def isClosed(branch):
            fmlas = []
            for child in branch:
                if isinstance(child, self.Node):
                    if child.fmla == 'not':
                        negatedFmla = child.children[0]
                        if negatedFmla in fmlas:
                            return True
                        fmlas.append(negatedFmla)
                    else:
                        if self.Node('not', [child]) in fmlas:
                            return True
                        fmlas.append(child)
            return False
    
        def expand(node):
            if isinstance(node, self.Node):
                if node.fmla == 'not':
                    negatedFmla = node.children[0]
                    if negatedFmla not in fmlas:
                        fmlas.append(negatedFmla)
                else:
                    fmlas.append(node)
                    for child in node.children:
                        expand(child)
        
        fmlas = [node.fmla]
        branches = [node.children]

        while branches:
            branch = branches.pop()
            for child in branch:
                if isClosed(branch):
                    return False
                expand(child)
        return True

if __name__ == '__main__':
    parser = TabParser()
    node = parser.parse(form)
    print(parser.isSatisfiable(node))


        
