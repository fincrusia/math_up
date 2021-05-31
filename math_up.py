# author : Hyunwoo Yang <hyunsdo.yang@samsung.com>
# project name : math_up
# description : a simple proof system I made to learn math without any mistakes
#
# some features are:
# 1. everything is wrote in Python, and you might freely add any code you want
# 2. it aims super-simplicity and short learning time
# 3. currently it is designed for NBG set theory only
#
# OK then, test yourself, enjoy your math!



TYPE_VARIABLE = 0
TYPE_FUNCTION = 1
TYPE_PROPERTY = 2
TYPE_ALL = 3
TYPE_EXIST = 4
TYPE_UNIQUELY_EXIST = 5
TYPE_NOT = 6
TYPE_AND = 7
TYPE_OR = 8
TYPE_IMPLY = 9
TYPE_IFF = 10
TYPE_TRUE = 11
TYPE_FALSE = 12

DEDUCE = 13
TAUTOLOGY = 14
DEFINE_PROPERTY = 15
DEFINE_FUNCTION = 16
DEFINE_CLASS = 17
DUAL = 18
FOUND = 19
CLAIM_UNIQUE = 20
BY_UNIQUE = 21
PUT = 22
REPLACE = 23
AXIOM = 24
LET = 30

callbacks = {}

proof_history = {}
class Node:
    counter = 0
    branch = [0]
    bounded = [set()]
    names = [set()]
    assumptions = [None]
    level = 0
    last = None
    fresh = set()

    def __init__(self, type_, **arguments):
        self.free = set()
        self.bounded = set()
        self.arguments = arguments

        if type_ == TYPE_VARIABLE:
            self.counter = Node.counter
            Node.counter += 1
            self.free.add(self.counter)
            self.defined_by = arguments.get("defined_by")
            Node.fresh.add(self.counter)
        elif type_ in [TYPE_PROPERTY, TYPE_FUNCTION]:
            self.name = arguments["name"]
            self.children = arguments["children"]
            for child in self.children:
                self.free |= child.free
        elif type_ in [TYPE_ALL, TYPE_EXIST, TYPE_UNIQUELY_EXIST]:
            self.bound = arguments["bound"]
            self.statement = arguments["statement"]
            self.free = self.statement.free.copy()
            self.bounded = self.statement.bounded.copy()
            assert self.bound.counter in self.free
            assert not self.bound.counter in self.bounded
            self.free.remove(self.bound.counter)
            self.bounded.add(self.bound.counter)
        elif type_ == TYPE_NOT:
            self.body = arguments["body"]
            self.free = self.body.free.copy()
            self.bounded = self.body.bounded.copy()
        elif type_ in [TYPE_AND, TYPE_OR, TYPE_IFF]:
            self.left = arguments["left"]
            self.right = arguments["right"]
            self.free = self.left.free | self.right.free
            self.bounded = self.left.bounded | self.right.bounded
        elif type_ == TYPE_IMPLY:
            self.assumption = arguments["assumption"]
            self.conclusion = arguments["conclusion"]
            self.free = self.assumption.free | self.conclusion.free
            self.bounded = self.assumption.bounded | self.conclusion.bounded
        elif type_ in [TYPE_TRUE, TYPE_FALSE]:
            pass
        else:
            assert False

        self.type_ = type_
        self.branch = None
        self.operator = None

        hashing = [self.type_]
        if self.type_ == TYPE_VARIABLE:
            hashing.append(self.counter)
        for key, value in sorted(self.arguments.items(), key = (lambda item : item[0])):
            hashing.append(key)
            if isinstance(value, list):
                for element in value:
                    hashing.append(hash(element))
            else:
                hashing.append(hash(value))
        self.hash = hash(tuple(hashing))

    def is_fresh(self):
        assert self.type_ == TYPE_VARIABLE
        return self.counter in Node.fresh

    def __hash__(self):
        return self.hash

    def is_sentence(self):
        return not self.type_ in [TYPE_VARIABLE, TYPE_FUNCTION]

    def is_generalizable(self):
        assert self.type_ == TYPE_VARIABLE
        for level in range(0, Node.level + 1):
            if self.counter in Node.bounded[level]:
                return False
        return True

    def is_proved(self):
        if self.branch == None:
            return False
        if len(self.branch) > len(Node.branch):
            return False
        for level in range(0, len(self.branch)):
            if self.branch[level] != Node.branch[level]:
                return False
        return True


    # when you just assume an axiom:
    # your_axiom.accept()
    # at the ground level(i.e. no Fitch-style assumptions),
    # the axiom must be closed
    def accept(self):
        assert self.is_sentence()
        self.branch = Node.branch[ : Node.level]
        for variable in self.free | self.bounded:
            if variable in Node.fresh:
                Node.fresh.remove(variable)
        Node.last = self
        return self
    
    # to save a sentence:
    # your_sentence.save("your_theorem_name")
    # or just:
    # your_sentence.save(number)
    # string name should be unique over the whold proof,
    # while the numbering overwrites the old one
    def save(self, save_as):
        assert self.is_sentence()
        if isinstance(save_as, str):
            assert proof_history.get(save_as) == None
        else:
            assert isinstance(save_as, int)
        proof_history[save_as] = self
        return self

    # deduction theorem
    # this let you write the Fitch-style proof
    # with assumption:
    #     # proof....
    #     conclustion
    # (assumption >> conclusion).deduce()
    def deduce(self):
        assert hash(self) == hash(Node.last)
        return self.accept()

    def __enter__(self):
        Node.level += 1
        if len(Node.branch) == Node.level:
            Node.branch.append(0)
            Node.bounded.append(set())
            Node.assumptions.append(self)
            Node.names.append(set())
        else:
            Node.branch[Node.level] += 1
            Node.bounded[Node.level] = set()
            Node.assumptions[Node.level] = self
            Node.names[Node.level] = set()
        Node.bounded[Node.level] |= self.free
        return self.accept()

    def __exit__(self, exc_type, exc_val, exc_tb):
        Node(TYPE_IMPLY, assumption = Node.assumptions[Node.level], conclusion = Node.last).accept()
        Node.level -= 1

    def substitute(self, old, new):
        assert old.type_ == TYPE_VARIABLE
        if self.type_ == TYPE_VARIABLE:
            if self.counter == old.counter:
                return new
            else:
                return self
        else:
            arguments = {}
            for key, value in self.arguments.items():
                if isinstance(value, list):
                    arguments[key] = [element.substitute(old, new) for element in value]
                elif isinstance(value, Node):
                    arguments[key] = value.substitute(old, new)
                else:
                    arguments[key] = value
            return Node(self.type_, **arguments)

    # define property
    # All(x, All(y, ... P(x, y, ...) iff Q(x, y, ...)))
    # where Q is a formula, but P is a newly defined atomic
    def define_property(self, name):
        for names in Node.names:
            assert not name in names
        Node.names[Node.level].add(name)

        cursor = self
        while cursor.type_ == TYPE_ALL:
            cursor = cursor.statement
        assert cursor.type_ == TYPE_IFF
        assert cursor.left.type_ == TYPE_PROPERTY
        assert cursor.left.name == name
        return self.accept()

    # define function
    # All(x, Q(x) >> UniquelyExist(y, P(x, y))).by(...).save(number)
    # All(x, Q(x) >> P(x, f(x))).functionize("your_function_name", number)
    def define_function(self, name, reason):
        for names in Node.names:
            assert not name in names
        Node.names[Node.level].add(name)

        reason = proof_history[reason]
        assert reason.is_proved()
        arguments = []
        cursor = reason
        while cursor.type_ == TYPE_ALL:
            arguments.append(cursor.bound)
            cursor = cursor.statement
        if cursor.type_ == TYPE_IMPLY:
            assumption = cursor.assumption
            cursor = cursor.conclusion
            assert cursor.type_ == TYPE_UNIQUELY_EXIST
            definition = Node(TYPE_IMPLY, assumption = assumption, conclusion = cursor.statement.substitute(cursor.bound, Node(TYPE_FUNCTION, name = name, children = arguments)))
        else:
            assert cursor.type_ == TYPE_UNIQUELY_EXIST
            definition = cursor.statement.substitute(cursor.bound, Node(TYPE_FUNCTION, name = name, children = arguments))
        for argument in reversed(arguments):
            definition = Node(TYPE_ALL, bound = argument, statement = definition)
        assert hash(self) == hash(definition)
        return self.accept()

    # prove Exist(x, P(x)) from t & P(t)
    def found(self, term, reason):
        reason = proof_history[reason]
        assert reason.is_proved()
        assert not term.is_sentence()
        assert self.type_ == TYPE_EXIST
        assert hash(self.statement.substitute(self.bound, term)) == hash(reason)
        return self.accept()

    # prove P(c) from c & Exist(x, P(x))
    # c must be FRESH, i.e. must NOT be used in the proof so far
    def let(self, variable, reason):
        reason = proof_history[reason]
        assert reason.is_proved()
        assert reason.type_ in [TYPE_EXIST, TYPE_UNIQUELY_EXIST]
        assert variable.is_fresh()
        variable.defined_by = reason
        Node.bounded[Node.level].add(variable.counter)
        assert hash(self) == hash(reason.statement.substitute(reason.bound, variable))
        return self.accept()
    
    # Exist(x, P(x)).save(key)
    # P(a).let(a, key)
    # P(b).let(b, key)
    # # ... some proofs
    # (a == b).save(number)
    # UniquelyExist(x, P(x)).unique(number)
    def claim_unique(self, reason):
        reason = proof_history[reason]
        assert reason.is_proved()
        assert reason.type_ == TYPE_PROPERTY
        assert reason.name == "equal"
        assert hash(reason.children[0].defined_by) == hash(reason.children[1].defined_by)
        assert self.type_ == TYPE_UNIQUELY_EXIST
        assert hash(Node(TYPE_EXIST, **self.arguments)) == hash(reason.children[0].defined_by)
        return self.accept()

    # prove (a == b) from UniquelyExist(x, P(x)), P(a) & P(b)
    def by_unique(self, reason, left, right):
        reason = proof_history[reason]
        left = proof_history[left]
        right = proof_history[right]
        assert reason.is_proved()
        assert left.is_proved()
        assert right.is_proved()
        assert self.type_ == TYPE_PROPERTY
        assert self.name == "equal"
        assert reason.type_ == TYPE_UNIQUELY_EXIST
        assert hash(reason.statement.substitute(reason.bound, self.children[0])) == hash(left)
        assert hash(reason.statement.substitute(reason.bound, self.children[1])) == hash(right)
        return self.accept()
    
    # prove P(t) from All(x, P(x))
    def put(self, replace_by, reason):
        reason = proof_history[reason]
        assert reason.is_proved()
        assert reason.type_ == TYPE_ALL
        assert not replace_by.is_sentence()
        assert hash(self) == hash(reason.statement.substitute(reason.bound, replace_by))
        return self.accept()

    # generalization
    # NOT applicable to BOUNDED variables,
    # which is a let-variable or a free variable of any assumption.
    def generalize(self, reason):
        reason = proof_history[reason]
        assert reason.is_proved()
        assert self.bound.is_generalizable()
        assert hash(self) == hash(Node(TYPE_ALL, bound = self.bound, statement = reason))
        return self.accept()

    def logical_form(self, mapping):
        if self.type_ == TYPE_NOT:
            return Node(TYPE_NOT, body = self.body.logical_form(mapping))
        elif self.type_ == TYPE_IMPLY:
            return Node(TYPE_IMPLY, assumption = self.assumption.logical_form(mapping), conclusion = self.conclusion.logical_form(mapping))
        elif self.type_ in [TYPE_AND, TYPE_OR, TYPE_IFF]:
            return Node(self.type_, left = self.left.logical_form(mapping), right = self.right.logical_form(mapping))
        elif self.type_ in [TYPE_TRUE, TYPE_FALSE]:
            return self
        else:
            if mapping.get(hash(self)) == None:
                mapping[hash(self)] = len(mapping)
            return Node(TYPE_PROPERTY, name = mapping[hash(self)], children = [])

    def logical_evaluate(self, truth_assign):
        if self.type_ == TYPE_PROPERTY:
            return truth_assign[self.name]
        elif self.type_ == TYPE_NOT:
            return not self.body.logical_evaluate(truth_assign)
        elif self.type_ == TYPE_AND:
            return self.left.logical_evaluate(truth_assign) and self.right.logical_evaluate(truth_assign)
        elif self.type_ == TYPE_OR:
            return self.left.logical_evaluate(truth_assign) or self.right.logical_evaluate(truth_assign)
        elif self.type_ == TYPE_IMPLY:
            return self.conclusion.logical_evaluate(truth_assign) or not self.assumption.logical_evaluate(truth_assign)
        elif self.type_ == TYPE_IFF:
            return self.left.logical_evaluate(truth_assign) == self.right.logical_evaluate(truth_assign)
        elif self.type_ == TYPE_TRUE:
            return True
        elif self.type_ == TYPE_FALSE:
            return False
        else:
            assert False

    # this namely deduces a tautological result from the given reasons
    def tautology(self, *reasons):
        mapping = {}
        logical_forms = []
        for reason in reasons:
            reason = proof_history[reason]
            assert reason.is_proved()
            logical_forms.append(reason.logical_form(mapping))
        target = self.logical_form(mapping)
        case_number = 2 ** len(mapping)
        for case_index in range(0, case_number):
            truth_assign = []
            for assign_index in range(0, len(mapping)):
                truth_assign.append(bool(case_index & (1 << assign_index)))
            consider = True
            for reason in logical_forms:
                if not reason.logical_evaluate(truth_assign):
                    consider = False
                    break
            if consider:
                assert target.logical_evaluate(truth_assign)
        return self.accept()

    def interchangable(self, counterpart, A, B):
        if hash(self) == hash(counterpart):
            return True
        elif hash(self) == hash(A) and hash(counterpart) == hash(B):
            return True
        elif hash(self) == hash(B) and hash(counterpart) == hash(A):
            return True
        else:
            if self.type_ != counterpart.type_:
                return False
            for key in self.arguments.keys():
                if counterpart.arguments.get(key) == None:
                    return False
            for key in counterpart.arguments.keys():
                if self.arguments.get(key) == None:
                    return False
            for key, value in self.arguments.items():
                value2 = counterpart.arguments[key]
                if isinstance(value, list):
                    if not isinstance(value2, list):
                        return False
                    if len(value) != len(value2):
                        return False
                    for index, element in enumerate(value):
                        if not element.interchangable(value2[index], A, B):
                            return False
                elif isinstance(value, Node):
                    if not value.interchangable(counterpart.arguments[key], A, B):
                        return False
                else:
                    if value != value2:
                        return False
            return True

    # reason : P, A == B
    # target : Q,
    # where P & Q are sentences, only differ by interchanging A & B
    def replace(self, reason, equality):
        reason = proof_history[reason]
        equality = proof_history[equality]
        assert reason.is_proved()
        assert equality.is_proved()
        assert equality.type_ == TYPE_PROPERTY
        assert equality.name == "equal"
        assert self.interchangable(reason, equality.children[0], equality.children[1])
        return self.accept()

    # class existence theorem
    # this is actually not an axiom, but is PROVABLE, due to Goedel
    # however, proving it requires recursively break down all the higher-level definitions to the primitive ones
    # I'm afraid our computers would not have enough resourse to do such tedious computation...

    # usage example for arity == 2
    # output : FRESH variable C
    # element : FRESH variable x
    # inputs : a, b
    # statement : P(a, b) # must includes a, b as FREE variables
    # 
    # "define" returns the following proved:
    # UniquelyExist(C, All(x, (x in C) iff UniquelyExist(a, UniquelyExist(b, (x == Tuple(a,b)) and Set(a) and Set(b) and P(a, b)))))
    def define_class(self, output, element, inputs, statement):
        assert statement.is_sentence()
        for input in inputs:
            assert input.type_ == TYPE_VARIABLE
            assert input in statement.free
        assert output.type_ == TYPE_VARIABLE
        assert output.is_fresh()

        def Tuple(*arguments):
            arity = len(arguments)
            if arity == 0:
                return Node(TYPE_FUNCTION, name = "empty", children = [])
            elif arity == 1:
                return arguments[0]
            elif arity == 2:
                return Node(TYPE_FUNCTION, name = "ordered_pair", children = [arguments[0], arguments[1]])
            else:
                return Node(TYPE_FUNCTION, name = "ordered_pair", children = [arguments[0], Tuple(*arguments[1 : ])])

        for input in reversed(inputs):
            statement = Node(TYPE_AND, left = Node(TYPE_PROPERTY, name = "set", children = [input]), right = statement)
        statement = Node(TYPE_AND, Node(TYPE_PROPERTY, name = "equal", children = [element, Tuple(inputs)]), statement)
        for input in reversed(inputs):
            statement = Node(TYPE_UNIQUELY_EXIST, bound = input, statement = statement)
        statement = Node(TYPE_IFF, left = Node(TYPE_PROPERTY, name = "membership", children = [element, output]), right = statement)
        statement = Node(TYPE_UNIQUELY_EXIST, bound = output, statement = Node(TYPE_ALL, bound = element, statement = statement))
        assert hash(self) == hash(statement)
        return self.accept()

    # duality
    # not All(x, P(x)) iff Exist not(x, P(x))
    # not Exist(x, P(x)) iff All not(x, P(x))
    def dual(self):
        assert self.type_ == TYPE_IFF
        if self.left.type_ == TYPE_NOT:
            if self.left.body.type_ == TYPE_ALL:
                assert self.right.type_ == TYPE_EXIST
                assert self.right.statement.type_ == TYPE_NOT
            elif self.left.body.type_ == TYPE_EXIST:
                assert self.right.type_ == TYPE_ALL
                assert self.right.statement.type_ == TYPE_NOT
            else:
                assert False
            assert self.left.body.bound.counter == self.right.bound.counter
            assert hash(self.left.body.statement) == hash(self.right.statement.body)
        elif self.right.type_ == TYPE_NOT:
            if self.right.body.type_ == TYPE_ALL:
                assert self.left.type_ == TYPE_EXIST
                assert self.left.statement.type_ == TYPE_NOT
            elif self.right.body.type_ == TYPE_EXIST:
                assert self.left.type_ == TYPE_ALL
                assert self.left.statement.type_ == TYPE_NOT
            else:
                assert False
        else:
            assert False

        return self.accept()


    # CAUTION!
    # actually, we need one more axiom: All(x, P and Q(x)) >> (P and All(x, Q(x)))
    # but I'll not implement this here... it may not, and should not be needed for readable proofs.
    # see Mendelson's logic book for some more about it.

    # operation overloading examples
    # (A +op/ B) gives you op(A, B)
    # similar for (A *op+ B), (A >op** B), whatever ...
    def overload(self, B):
        assert not self.is_sentence()
        if self.operator == None:
            self.operator = B
            return self
        else:
            assert isinstance(B, Node)
            assert not B.is_sentence()
            operator = self.operator
            self.operator = None
            return operator(self, B)

    def __invert__(self):
        return Node(TYPE_NOT, body = self)

    def __and__(self, B):
        return Node(TYPE_AND, left = self, right = B)

    def __or__(self, B):
        return Node(TYPE_OR, left = self, right = B)

    def __add__(self, B):
        return self.overload(B)

    def __sub__(self, B):
        return self.overload(B)
    
    def __mul__(self, B):
        return self.overload(B)

    def __floordiv__(self, B):
        return self.overload(B)
    
    def __truediv__(self, B):
        return self.overload(B)

    def __pow__(self, B):
        return self.overload(B)

    def __lt__(self, B):
        return self.overload(B)

    def __le__(self, B):
        return self.overload(B)
    
    def __gt__(self, B):
        return self.overload(B)

    def __ge__(self, B):
        return self.overload(B)

    def __lshift__(self, B):
        return self.overload(B)

    def __rshift__(self, B):
        if self.is_sentence():
            return Node(TYPE_IMPLY, assumption = self, conclusion = B)
        return self.overload(B)



    def __matmul__(self, B): # reserved!
        if not isinstance(B, tuple):
            return self.save(B)

        save_as = B[0]
        
        if len(B) == 1:
            return self.save(save_as)
        else:
            inference = B[1]
            arguments = B[2 : ]

            if inference == DEDUCE:
                return self.deduce(*arguments).save(save_as)
            elif inference == TAUTOLOGY:
                return self.tautology(*arguments).save(save_as)
            elif inference == DEFINE_PROPERTY:
                return self.define_property(*arguments).save(save_as)
            elif inference == DEFINE_FUNCTION:
                return self.define_function(*arguments).save(save_as)
            elif inference == DEFINE_CLASS:
                return self.define_class(*arguments).save(save_as)
            elif inference == DUAL:
                return self.dual(*arguments).save(save_as)
            elif inference == FOUND:
                return self.found(*arguments).save(save_as)
            elif inference == CLAIM_UNIQUE:
                return self.claim_unique(*arguments).save(save_as)
            elif inference == BY_UNIQUE:
                return self.by_unique(*arguments).save(save_as)
            elif inference == PUT:
                return self.put(*arguments).save(save_as)
            elif inference == REPLACE:
                return self.replace(*arguments).save(save_as)
            elif inference == AXIOM:
                return self.accept().save(save_as)
            else:
                return callbacks[inference](self, *arguments).save(save_as)

    def __eq__(self, B): # reserved!
        if self.is_sentence():
            return Node(TYPE_IFF, left = self, right = B)
        return Node(TYPE_PROPERTY, name = "equal", children = [self, B]) 

    def __ne__(self, B): # reserved!
        return Node(TYPE_NOT, body = Node(TYPE_PROPERTY, name = "equal", children = [self, B]))
    

true = Node(TYPE_TRUE)
false = Node(TYPE_FALSE)




def New():
    return Node(TYPE_VARIABLE)

def All(*arguments):
    bounds = arguments[ : -1]
    statement = arguments[-1]
    for bound in reversed(bounds):
        statement = Node(TYPE_ALL, bound = bound, statement = statement)
    return statement

def Exist(*arguments):
    bounds = arguments[ : -1]
    statement = arguments[-1]
    for bound in reversed(bounds):
        statement = Node(TYPE_EXIST, bound = bound, statement = statement)
    return statement

def UniquelyExist(*arguments):
    bounds = arguments[ : -1]
    statement = arguments[-1]
    for bound in reversed(bounds):
        statement = Node(TYPE_UNIQUELY_EXIST, bound = bound, statement = statement)
    return statement

def Tuple(*arguments):
    arity = len(arguments)
    if arity == 0:
        return Node(TYPE_FUNCTION, name = "empty", children = [])
    elif arity == 1:
        return arguments[0]
    elif arity == 2:
        return Node(TYPE_FUNCTION, name = "ordered_pair", children = [arguments[0], arguments[1]])
    else:
        return Node(TYPE_FUNCTION, name = "ordered_pair", children = [arguments[0], Tuple(*arguments[1 : ])])


# used in theorems
a_ = New()
b_ = New()
c_ = New()
d_ = New()
e_ = New()
f_ = New()
g_ = New()
h_ = New()
i_ = New()
j_ = New()
k_ = New()
l_ = New()
m_ = New()
n_ = New()
o_ = New()
p_ = New()
q_ = New()
r_ = New()
s_ = New()
t_ = New()
u_ = New()
v_ = New()
w_ = New()
x_ = New()
y_ = New()
z_ = New()
A_ = New()
B_ = New()
C_ = New()
D_ = New()
E_ = New()
F_ = New()
G_ = New()
H_ = New()
I_ = New()
J_ = New()
K_ = New()
L_ = New()
M_ = New()
N_ = New()
O_ = New()
P_ = New()
Q_ = New()
R_ = New()
S_ = New()
T_ = New()
U_ = New()
V_ = New()
W_ = New()
X_ = New()
Y_ = New()
Z_ = New()

# used in proofs
def clear():
    global a
    a = New()
    global b
    b = New()
    global c
    c = New()
    global d
    d = New()
    global e
    e = New()
    global f
    f = New()
    global g
    g = New()
    global h
    h = New()
    global i
    i = New()
    global j
    j = New()
    global k
    k = New()
    global l
    l = New()
    global m
    m = New()
    global n
    n = New()
    global o
    o = New()
    global p
    p = New()
    global q
    q = New()
    global r
    r = New()
    global s
    s = New()
    global t
    t = New()
    global u
    u = New()
    global v
    v = New()
    global w
    w = New()
    global x
    x = New()
    global y
    y = New()
    global z
    z = New()
    global A
    A = New()
    global B
    B = New()
    global C
    C = New()
    global D
    D = New()
    global E
    E = New()
    global F
    F = New()
    global G
    G = New()
    global H
    H = New()
    global I
    I = New()
    global J
    J = New()
    global K
    K = New()
    global L
    L = New()
    global M
    M = New()
    global N
    N = New()
    global O
    O = New()
    global P
    P = New()
    global Q
    Q = New()
    global R
    R = New()
    global S
    S = New()
    global T
    T = New()
    global U
    U = New()
    global V
    V = New()
    global W
    W = New()
    global X
    X = New()
    global Y
    Y = New()
    global Z
    Z = New()

# PROOF START!

def match(A, B, counters, mapping):
    if A.type_ == TYPE_VARIABLE:
        if A.counter in counters:
            if mapping.get(A.counter):
                assert hash(mapping[A.counter]) == hash(B)
            else:
                mapping[A.counter] == B
    else:
        assert A.type_ == B.type_
        for key, value in A.arguments:
            if isinstance(value, list):
                for index, element in enumerate(value):
                    match(element, B.arguments[key][index], counters, mapping)
            elif isinstance(value, Node):
                match(value, B.arguments[key], counters, mapping)
            else:
                assert B.arguments[key] == value

# theorem use
def by_theorem(target, name, *reasons):
    cursor = proof_history[name]
    bounds = set()
    while cursor.type_ == TYPE_ALL:
        bounds.add(cursor.bound.counter)
        cursor = cursor.statement
    if cursor.type_ == TYPE_IMPLY:
        assumption = cursor.assumption
        conclusion = cursor.conclusion
        mapping = {}
        match(cursor, target, bounds, mapping)
        cursor = proof_history[name]
        while cursor.type_ == TYPE_ALL:
            cursor = (cursor.statement.substitute(cursor.bound, mapping[cursor.bound.counter])).put(mapping[cursor.bound.counter])
        return conclusion.tautology(cursor, *reasons)
    else:
        mapping = {}
        match(cursor, target, bounds, mapping)
        cursor = proof_history[name]
        while cursor.type_ == TYPE_ALL:
            cursor = (cursor.statement.substitute(cursor.bound, mapping[cursor.bound.counter])).put(mapping[cursor.bound.counter])
        return cursor

BY_THEOREM = 25
callbacks[BY_THEOREM] = by_theorem

def make_property(name):
    def new_property(*arguments):
        return Node(TYPE_PROPERTY, name = name, children = [*arguments])
    return new_property

def make_function(name):
    def new_function(*arguments):
        return Node(TYPE_FUNCTION, name = name, children = [*arguments])
    return new_function

# membership
clear()
in_ = make_property("in")

# definition of set
clear()
Set = make_property("set")
(All(x_, Set(x_) == Exist(C_, x_ *in_* C_))) @ ("set", DEFINE_PROPERTY, "set")

# equality reflection
clear()
All(A_, A_ == A_) @ ("equality_reflection", AXIOM)

# extensionality
clear()
All(A_, B_, (A_ == B_) == All(x_, (x_ *in_* A_) == (x_ *in_* B_))) @ ("extensionality", AXIOM)

clear()
