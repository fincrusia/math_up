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
GENERALIZE = 31

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
            if arguments.get("counter") != None:
                self.counter = arguments["counter"]
            else:
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

    def __str__(self): # for debugging only
        if self.type_ == TYPE_VARIABLE:
            if self.counter < 52:
                if self.counter < 26:
                    return chr(ord('a') + self.counter) + "_"
                else:
                    return chr(ord('A') + self.counter - 26) + "_"
            else:
                count = self.counter % 52
                if count < 26:
                    return chr(ord('a') + count)
                else:
                    return chr(ord('A') + count - 26)

        elif self.type_ in [TYPE_FUNCTION, TYPE_PROPERTY]:
            ret = self.name + "("
            if len(self.children) > 0:
                for child in self.children[ : -1]:
                    ret += (str(child) + ", ")
                ret += str(self.children[-1])
            ret += ")"
            return ret
        elif self.type_ == TYPE_ALL:
            return "All(" + str(self.bound) + "," + str(self.statement) + ")"
        elif self.type_ == TYPE_EXIST:
            return "Exist(" + str(self.bound) + "," + str(self.statement) + ")"
        elif self.type_ == TYPE_UNIQUELY_EXIST:
            return "UniquelyExist(" + str(self.bound) + "," + str(self.statement) + ")"
        elif self.type_ == TYPE_NOT:
            return "(~ " + str(self.body) + ")"
        elif self.type_ == TYPE_AND:
            return "(" + str(self.left) + " & " + str(self.right) + ")"
        elif self.type_ == TYPE_OR:
            return "(" + str(self.left) + " | " + str(self.right) + ")"
        elif self.type_ == TYPE_IMPLY:
            return "(" + str(self.assumption) + " >> " + str(self.conclusion) + ")"
        elif self.type_ == TYPE_IFF:
            return "(" + str(self.left) + " == " + str(self.right) + ")"
        elif self.type_ == TYPE_TRUE:
            return "true"
        elif self.type_ == TYPE_FALSE:
            return "false"
        else:
            assert False

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
    # All(x, Q(x) >> P(x, f(x))).define_function("your_function_name", number)
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
    # UniquelyExist(C, All(x_, (x_ *in_* C) == (Set(x) & (...))))
    def define_class(self, output):
        assert output.type_ == TYPE_VARIABLE
        assert output.is_fresh()
    
        cursor = self
        assert cursor.type_ == TYPE_UNIQUELY_EXIST
        assert hash(cursor.bound) == hash(output)
        cursor = cursor.statement
        assert cursor.type_ == TYPE_ALL
        element = cursor.bound
        cursor = cursor.statement
        assert cursor.type_ == TYPE_IFF
        assert hash(cursor.left) == hash(Node(TYPE_PROPERTY, name = "in", children = [element, output]))
        cursor = cursor.right
        assert cursor.type_ == TYPE_AND
        assert hash(cursor.left) == hash(Node(TYPE_PROPERTY, name = "set", children = [element]))
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
            elif inference == GENERALIZE:
                return self.generalize(*arguments).save(save_as)
            elif inference == LET:
                return self.let(*arguments).save(save_as)
            else:
                return callbacks[inference](self, *arguments).save(save_as)

    def __getitem__(self, B): # reserved!
        assert not self.is_sentence()
        assert isinstance(B, Node)
        assert not b.is_sentence()
        return Node(TYPE_FUNCTION, name = "image", children = [self, B])

    def __call__(self, *arguments): # reserved!
        assert not self.is_sentence()
        for argument in arguments:
            assert isinstance(argument, Node)
            assert not argument.is_sentence()
        return Node(TYPE_FUNCTION, name = "put", children = [self, *arguments])

    def __eq__(self, B): # reserved!
        if B == None:
            return False
        if self.is_sentence():
            return Node(TYPE_IFF, left = self, right = B)
        return Node(TYPE_PROPERTY, name = "equal", children = [self, B]) 

    def __ne__(self, B): # reserved!
        if B == None:
            return True
        return Node(TYPE_NOT, body = Node(TYPE_PROPERTY, name = "equal", children = [self, B]))
    

true = Node(TYPE_TRUE)
false = Node(TYPE_FALSE)




def New(*counter):
    if len(counter) == 0:
        return Node(TYPE_VARIABLE)
    elif len(counter) == 1:
        return Node(TYPE_VARIABLE, counter = counter[0])
    else:
        assert False

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
    if arity == 2:
        return Node(TYPE_FUNCTION, name = "ordered_pair", children = [arguments[0], arguments[1]])
    elif arity > 2:
        return Node(TYPE_FUNCTION, name = "ordered_pair", children = [arguments[0], Tuple(*arguments[1 : ])])
    else:
        assert False

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


# theorem use
def match(A, B, counters, mapping):
    if A.type_ == TYPE_VARIABLE:
        if A.counter in counters:
            if mapping.get(A.counter) != None:
                assert hash(mapping[A.counter]) == hash(B)
            else:
                mapping[A.counter] = B
    else:
        assert A.type_ == B.type_
        for key, value in A.arguments.items():
            if isinstance(value, list):
                for index, element in enumerate(value):
                    match(element, B.arguments[key][index], counters, mapping)
            elif isinstance(value, Node):
                match(value, B.arguments[key], counters, mapping)
            else:
                assert B.arguments[key] == value

def by_theorem(target, name, *reasons):
    cursor = proof_history[name]
    bounds = set()
    while cursor.type_ == TYPE_ALL:
        bounds.add(cursor.bound.counter)
        cursor = cursor.statement
    if cursor.type_ == TYPE_IMPLY:
        mapping = {}
        conclusion = cursor.conclusion
        match(conclusion, target, bounds, mapping)
        cursor = proof_history[name] @ -1
        while cursor.type_ == TYPE_ALL:
            cursor = cursor.statement.substitute(cursor.bound, mapping[cursor.bound.counter]) @ (-1, PUT, mapping[cursor.bound.counter], -1)
        return target @ (-1, TAUTOLOGY, -1, *reasons)
    else:
        mapping = {}
        match(cursor, target, bounds, mapping)
        cursor = proof_history[name] @ -1
        while cursor.type_ == TYPE_ALL:
            cursor = (cursor.statement.substitute(cursor.bound, mapping[cursor.bound.counter])) @ (-1, PUT, mapping[cursor.bound.counter], -1)
        return target @ (-1, TAUTOLOGY, -1, *reasons)

BY_THEOREM = 25
callbacks[BY_THEOREM] = by_theorem

def put_theorem(target, name, hidden, *reasons):
    cursor = proof_history[name]
    assert cursor.is_proved()
    bounds = set()
    while cursor.type_ == TYPE_ALL:
        bounds.add(cursor.bound.counter)
        cursor = cursor.statement
    assert cursor.type_ == TYPE_IMPLY
    assert len(cursor.assumption.free) == len(cursor.conclusion.free) + 1
    mapping = {}
    conclusion = cursor.conclusion
    match(conclusion, target, bounds, mapping)
    cursor = proof_history[name] @ -1
    while cursor.type_ == TYPE_ALL:
        if mapping.get(cursor.bound.counter) != None:
            cursor = (cursor.statement.substitute(cursor.bound, mapping[cursor.bound.counter])) @ (-1, PUT, mapping[cursor.bound.counter], -1)
        else:
            cursor = (cursor.statement.substitute(cursor.bound, hidden)) @ (-1, PUT, hidden, -1)
    return target @ (-1, TAUTOLOGY, -1, *reasons)

PUT_THEOREM = 28
callbacks[PUT_THEOREM] = put_theorem


# bicondition
def try_match(A, B, counters, mapping):
    if A.type_ == TYPE_VARIABLE:
        if A.counter in counters:
            if mapping.get(A.counter) != None:
                if hash(mapping[A.counter]) != hash(B):
                    return False
            else:
                mapping[A.counter] = B
    else:
        if A.type_ != B.type_:
            return False
        for key, value in A.arguments.items():
            if isinstance(value, list):
                for index, element in enumerate(value):
                    if not try_match(element, B.arguments[key][index], counters, mapping):
                        return False
            elif isinstance(value, Node):
                if not try_match(value, B.arguments[key], counters, mapping):
                    return False
            else:
                if B.arguments[key] != value:
                    return False
    return True

def bicondition(target, name, *reasons):
    cursor = proof_history[name]
    bounds = set()
    while cursor.type_ == TYPE_ALL:
        bounds.add(cursor.bound.counter)
        cursor = cursor.statement
    assert cursor.type_ == TYPE_IFF
    mapping = {}
    conclusion = cursor.right
    if try_match(conclusion, target, bounds, mapping):
        cursor = proof_history[name] @ -1
        while cursor.type_ == TYPE_ALL:
            cursor = cursor.statement.substitute(cursor.bound, mapping[cursor.bound.counter]) @ (-1, PUT, mapping[cursor.bound.counter], -1)
        return target @ (-1, TAUTOLOGY, -1, *reasons)
    mapping = {}
    conclusion = cursor.left
    if try_match(conclusion, target, bounds, mapping):
        cursor = proof_history[name] @ -1
        while cursor.type_ == TYPE_ALL:
            cursor = cursor.statement.substitute(cursor.bound, mapping[cursor.bound.counter]) @ (-1, PUT, mapping[cursor.bound.counter], -1)
        return target @ (-1, TAUTOLOGY, -1, *reasons)
    assert False

BICONDITION = 38
callbacks[BICONDITION] = bicondition

def make_property(name):
    def new_property(*arguments):
        return Node(TYPE_PROPERTY, name = name, children = [*arguments])
    return new_property

def make_function(name):
    def new_function(*arguments):
        return Node(TYPE_FUNCTION, name = name, children = [*arguments])
    return new_function

def closing(target, reason):
    cursor = target
    free = {}
    reason = proof_history[reason]
    assert reason.is_proved()
    for counter in reason.free:
        free[counter % 52] = counter # 52 == number of alphabets, a-Z
    bounds = []
    closed = reason @ -1
    while cursor.type_ == TYPE_ALL:
        bounds.append(cursor.bound)
        cursor = cursor.statement
    for bound in reversed(bounds):
        variable = New(free[bound.counter])
        closed = All(variable, closed) @ (-1, GENERALIZE, -1)
    for bound in bounds:
        closed = closed.statement.substitute(closed.bound, bound) @ (-1, PUT, bound, -1)
    for bound in reversed(bounds):
        closed = All(bound, closed) @ (-1, GENERALIZE, -1)
    return target @ (-1, TAUTOLOGY, -1)

CLOSING = 26
callbacks[CLOSING] = closing

# membership
clear()
in_ = make_property("in")

# definition of set
clear()
Set = make_property("set")
(All(x_, Set(x_) == Exist(C_, x_ *in_* C_))) @ ("set", DEFINE_PROPERTY, "set")

# set condition
clear()
with (x *in_* C) @ 0:
    Exist(C_, x *in_* C_) @ (1, FOUND, C, 0)
    (Set(x) == Exist(C_, x *in_* C_)) @ (2, BY_THEOREM, "set")
    Set(x) @ (3, TAUTOLOGY, 1, 2)
((x *in_* C) >> Set(x)) @ (4, DEDUCE)
All(C_, x_, (x_ *in_* C_) >> Set(x_)) @ ("set_condition", CLOSING, 4)

# equality reflection
clear()
All(A_, A_ == A_) @ ("equality_reflection", AXIOM)

# equality symmetry
clear()
with (A == B) @ 0:
    (B == A) @ (1, REPLACE, 0, 0)
((A == B) >> (B == A)) @ (2, DEDUCE)
All(A_, B_, ((A_ == B_) >> (B_ == A_))) @ ("equality_symmetry", CLOSING, 2)

# equality transitivity
clear()
with (A == B) @ 0:
    with (B == C) @ 1:
        (A == C) @ (2, REPLACE, 0, 1)
    ((B == C) >> (A == C)) @ (3, DEDUCE)
((A == B) >> ((B == C) >> (A == C))) @ (4, DEDUCE)
(((A == B) & (B == C)) >> (A == C)) @ (5, TAUTOLOGY, 4)
All(A_, B_, C_, (((A_ == B_) & (B_ == C_)) >> (A_ == C_))) @ ("equality_transitivity", CLOSING, 5)

# reflection generic
def check_reflection(name, reflection):
    reflection = proof_history[reflection]
    assert reflection.is_proved()
    assert reflection.type_ == TYPE_ALL
    bound = reflection.bound
    assert hash(Node(TYPE_PROPERTY, name = name, children = [bound, bound])) == hash(reflection.statement)

# symmetry generic
def check_symmetry(name, symmetry):
    symmetry = proof_history[symmetry]
    assert symmetry.is_proved()
    assert symmetry.type_ == TYPE_ALL
    A0 = symmetry.bound
    assert symmetry.statement.type_ == TYPE_ALL
    B0 = symmetry.statement.bound
    assert hash(Node(TYPE_PROPERTY, name = name, children = [A0, B0]) >> Node(TYPE_PROPERTY, name = name, children = [B0, A0])) == hash(symmetry.statement.statement)

# transitivity generic
def check_transitivity(name, transitivity):
    transitivity = proof_history[transitivity]
    assert transitivity.is_proved()
    assert transitivity.type_ == TYPE_ALL
    A0 = transitivity.bound
    assert transitivity.statement.type_ == TYPE_ALL
    B0 = transitivity.statement.bound
    assert transitivity.statement.statement.type_ == TYPE_ALL
    C0 = transitivity.statement.statement.bound
    assert hash((Node(TYPE_PROPERTY, name = name, children = [A0, B0]) & Node(TYPE_PROPERTY, name = name, children = [B0, C0])) >> Node(TYPE_PROPERTY, name = name, children = [A0, C0])) == hash(transitivity.statement.statement.statement)

# equivalence relation generic
equivalence_relations = {}
def register_equivalence(name, reflection, symmetry, transitivity):
    if isinstance(name, str):
        assert equivalence_relations.get(name) == None
    check_reflection(name, reflection)
    check_symmetry(name, symmetry)
    check_transitivity(name, transitivity)
    equivalence_relations[name] = (reflection, symmetry, transitivity)

register_equivalence("equal", "equality_reflection", "equality_symmetry", "equality_transitivity")

def by_equivalence(target, *reasons):
    assert target.type_ == TYPE_PROPERTY
    name = target.name
    reflection, symmetry, transitivity = equivalence_relations[name]
    if not reasons:
        return target @ (-2, BY_THEOREM, reflection)
    else:
        statements = []
        for reason in reasons:
            reason = proof_history[reason]
            assert reason.is_proved()
            assert reason.type_ == TYPE_PROPERTY
            assert reason.name == name
            statements.append(reason)
        left = target.children[0]
        cursor = left
        marked = set()
        for _ in range(0, len(statements)):
            for index, reason in enumerate(statements):
                if index in marked:
                    continue
                if hash(reason.children[0]) == hash(cursor):
                    if len(marked) == 0:
                        reason @ -2
                    else:
                        reason @ -3
                        Node(TYPE_PROPERTY, name = name, children = [left, reason.children[1]]) @ (-2, PUT_THEOREM, transitivity, reason.children[0], -2, -3)
                    cursor = reason.children[1]
                    marked.add(index)
                    break
                elif hash(reason.children[1]) == hash(cursor):
                    reason @ -3
                    if len(marked) == 0:
                        Node(TYPE_PROPERTY, name = name, children = [reason.children[1], reason.children[0]]) @ (-2, BY_THEOREM, symmetry, -3)
                    else:
                        Node(TYPE_PROPERTY, name = name, children = [reason.children[1], reason.children[0]]) @ (-3, BY_THEOREM, symmetry, -3)
                        Node(TYPE_PROPERTY, name = name, children = [left, reason.children[0]]) @ (-2, PUT_THEOREM, transitivity, reason.children[1], -2, -3)
                    cursor = reason.children[0]
                    marked.add(index)
                    break
        return target @ (-2, TAUTOLOGY, -2)

BY_EQUIVALENCE = 33
callbacks[BY_EQUIVALENCE] = by_equivalence


# unique up to equality
clear()
(A == A) @ (0, PUT, A, "equality_reflection")
Exist(B_, B_ == A) @ (1, FOUND, A, 0)
(B == A) @ (2, LET, B, 1)
(C == A) @ (3, LET, C, 1)
(A == C) @ (6, BY_THEOREM, "equality_symmetry", 3)
(B == C) @ (4, PUT_THEOREM, "equality_transitivity", A, 2, 6)
UniquelyExist(B_, B_ == A) @ (5, CLAIM_UNIQUE, 4)
All(A_, UniquelyExist(B_, B_ == A_)) @ ("unique_up_to_equality", CLOSING, 5)

# composite
def composite_function(target, name):
    cursor = target
    inputs = []
    while cursor.type_ == TYPE_ALL:
        inputs.append(cursor.bound)
        cursor = cursor.statement
    assert cursor.type_ == TYPE_PROPERTY
    assert cursor.name == "equal"
    output = cursor.children[1]
    cursor = UniquelyExist(B_, B_ == output) @ (-1, PUT, output, "unique_up_to_equality")
    for input in reversed(inputs):
        cursor = All(input, cursor) @ (-1, GENERALIZE, -1)
    return target @ (-1, DEFINE_FUNCTION, name, -1)

COMPOSITE = 32
callbacks[COMPOSITE] = composite_function

# extensionality
clear()
All(A_, B_, All(x_, (x_ *in_* A_) == (x_ *in_* B_)) >> (A_ == B_)) @ ("extensionality", AXIOM)

# pairing
clear()
All(a_, b_, (Set(a_) & Set(b_)) >> UniquelyExist(p_, Set(p_) & All(x_, ((x_ *in_* p_) == ((x_ == a_) | (x_ == b_)))))) @ ("pairing", AXIOM)

# pair
clear()
Pair = make_function("pair")
All(a_, b_, (Set(a_) & Set(b_)) >> (Set(Pair(a_, b_)) & All(x_, ((x_ *in_* Pair(a_, b_)) == ((x_ == a_) | (x_ == b_)))))) @ ("pair", DEFINE_FUNCTION, "pair", "pairing")

# element of pair
clear()
with (Set(a) & Set(b)) @ 0:
    with (x *in_* Pair(a, b)) @ 1:
        (Set(Pair(a, b)) & All(x_, ((x_ *in_* Pair(a, b)) == ((x_ == a) | (x_ == b))))) @ (2, BY_THEOREM, "pair", 0)
        All(x_, ((x_ *in_* Pair(a, b)) == ((x_ == a) | (x_ == b)))) @ (3, TAUTOLOGY, 2)
        ((x *in_* Pair(a, b)) == ((x == a) | (x == b))) @ (4, PUT, x, 3)
        ((x == a) | (x == b)) @ (5, TAUTOLOGY, 1, 4)
    ((x *in_* Pair(a, b)) >> ((x == a) | (x == b))) @ (6, DEDUCE)
((Set(a) & Set(b)) >> ((x *in_* Pair(a, b)) >> ((x == a) | (x == b)))) @ (7, DEDUCE)
((((Set(a) & Set(b)) & (x *in_* Pair(a, b))) >> ((x == a) | (x == b)))) @ (8, TAUTOLOGY, 7)
All(a_, b_, x_, (((Set(a_) & Set(b_)) & (x_ *in_* Pair(a_, b_)))) >> ((x_ == a_) | (x_ == b_))) @ ("element_of_pair", CLOSING, 8)


# pair is a set
clear()
with (Set(a) & Set(b)) @ 0:
    (Set(Pair(a, b)) & All(x_, ((x_ *in_* Pair(a, b)) == ((x_ == a) | (x_ == b))))) @ (1, BY_THEOREM, "pair", 0)
    Set(Pair(a, b)) @ (2,TAUTOLOGY, 1)
((Set(a) & Set(b)) >> Set(Pair(a, b))) @ (3, DEDUCE)
All(a_, b_, ((Set(a_) & Set(b_)) >> Set(Pair(a_, b_)))) @ ("pair_is_set", CLOSING, 3)

# left in pair
clear()
with (Set(a) & Set(b)) @ 0:
    (Set(Pair(a, b)) & All(x_, ((x_ *in_* Pair(a, b)) == ((x_ == a) | (x_ == b))))) @ (1, BY_THEOREM, "pair", 0)
    All(x_, ((x_ *in_* Pair(a, b)) == ((x_ == a) | (x_ == b)))) @ (2, TAUTOLOGY, 1)
    ((a *in_* Pair(a, b)) == ((a == a) | (a == b))) @ (3, PUT, a, 2)
    (a == a) @ (4, BY_EQUIVALENCE)
    a *in_* Pair(a,b) @ (5, TAUTOLOGY, 3, 4)
((Set(a) & Set(b)) >> (a *in_* Pair(a, b))) @ (6, DEDUCE)
All(a_, b_, ((Set(a_) & Set(b_)) >> (a_ *in_* Pair(a_, b_)))) @ ("left_in_pair", CLOSING, 6)

# right in pair
clear()
with (Set(a) & Set(b)) @ 0:
    (Set(Pair(a, b)) & All(x_, ((x_ *in_* Pair(a, b)) == ((x_ == a) | (x_ == b))))) @ (1, BY_THEOREM, "pair", 0)
    All(x_, ((x_ *in_* Pair(a, b)) == ((x_ == a) | (x_ == b)))) @ (2, TAUTOLOGY, 1)
    ((b *in_* Pair(a, b)) == ((b == a) | (b == b))) @ (3, PUT, b, 2)
    (b == b) @ (4, BY_EQUIVALENCE)
    b *in_* Pair(a,b) @ (5, TAUTOLOGY, 3, 4)
((Set(a) & Set(b)) >> (b *in_* Pair(a, b))) @ (6, DEDUCE)
All(a_, b_, ((Set(a_) & Set(b_)) >> (b_ *in_* Pair(a_, b_)))) @ ("right_in_pair", CLOSING, 6)

# element of singleton
clear()
with Set(a) @ 0:
    (Set(Pair(a, a)) & All(x_, ((x_ *in_* Pair(a, a)) == ((x_ == a) | (x_ == a))))) @ (2, BY_THEOREM, "pair", 0)
    All(x_, ((x_ *in_* Pair(a, a)) == ((x_ == a) | (x_ == a)))) @ (3, TAUTOLOGY, 2)
    ((b *in_* Pair(a, a)) == ((b == a) | (b == a))) @ (4, PUT, b, 3)
    with (b *in_* Pair(a, a)) @ 1:
        (b == a) @ (5, TAUTOLOGY, 1, 4)
    ((b *in_* Pair(a, a)) >> (b == a)) @ (6, DEDUCE)
    (a *in_* Pair(a, a)) @ (8, BY_THEOREM, "left_in_pair", 0)
    with (b == a) @ 7:
        (b *in_* Pair(a, a)) @ (9, REPLACE, 8, 7)
    ((b == a) >> (b *in_* Pair(a, a))) @ (10, DEDUCE)
    ((b *in_* Pair(a, a)) == (b == a)) @ (11, TAUTOLOGY, 10, 6)
(Set(a) >> ((b *in_* Pair(a, a)) == (b == a))) @ (12, DEDUCE)
All(a_, b_, (Set(a_) >> (((b_ *in_* Pair(a_, a_))) == (b_ == a_)))) @ ("element_of_singleton", CLOSING, 12)

# ordered pair
clear()
OrderedPair = make_function("ordered_pair")
All(a_, b_, OrderedPair(a_, b_) == Pair(Pair(a_, a_), Pair(a_, b_))) @ ("ordered_pair", COMPOSITE, "ordered_pair")

# comparison of ordered pairs
clear()
with (Set(a) & Set(b) & Set(c) & Set(d)) @ 0:
    with (OrderedPair(a, b) == OrderedPair(c, d)) @ 1:
        (OrderedPair(a, b) == Pair(Pair(a, a), Pair(a, b))) @ (2, BY_THEOREM, "ordered_pair")
        (OrderedPair(c, d) == Pair(Pair(c, c), Pair(c, d))) @ (3, BY_THEOREM, "ordered_pair")

        Set(Pair(a, a)) @ (4, BY_THEOREM, "pair_is_set", 0)
        Set(Pair(a, b)) @ (5, BY_THEOREM, "pair_is_set", 0)
        Set(Pair(c, c)) @ (6, BY_THEOREM, "pair_is_set", 0)
        Set(Pair(c, d)) @ (7, BY_THEOREM, "pair_is_set", 0)

        (Set(Pair(Pair(a, a), Pair(a, b))) & All(x_, ((x_ *in_* Pair(Pair(a, a), Pair(a, b))) == ((x_ == Pair(a, a)) | (x_ == Pair(a, b)))))) @ (8, BY_THEOREM, "pair", 4, 5)
        (Set(Pair(Pair(c, c), Pair(c, d))) & All(x_, ((x_ *in_* Pair(Pair(c, c), Pair(c, d))) == ((x_ == Pair(c, c)) | (x_ == Pair(c, d)))))) @ (9, BY_THEOREM, "pair", 6, 7)

        (Pair(Pair(a, a), Pair(a, b)) == Pair(Pair(c, c), Pair(c, d))) @ (14, BY_EQUIVALENCE, 1, 2, 3)

        (Pair(a, a) *in_* Pair(Pair(a, a), Pair(a, b))) @ (15, BY_THEOREM, "left_in_pair", 4, 5)
        (Pair(a, a) *in_* Pair(Pair(c, c), Pair(c, d))) @ (18, REPLACE, 15, 14)
        All(x_, ((x_ *in_* Pair(Pair(c, c), Pair(c, d))) == ((x_ == Pair(c, c)) | (x_ == Pair(c, d))))) @ (16, TAUTOLOGY, 9)
        ((Pair(a, a) *in_* Pair(Pair(c, c), Pair(c, d))) == ((Pair(a, a) == Pair(c, c)) | (Pair(a, a) == Pair(c, d)))) @ (17, PUT, Pair(a, a), 16)

        ((Pair(a, a) == Pair(c, c)) | (Pair(a, a) == Pair(c, d))) @ (19, TAUTOLOGY, 18, 17)

        with (Pair(a, a) == Pair(c, d)) @ 30:
            (c *in_* Pair(c, d)) @ (31, BY_THEOREM, "left_in_pair", 0)
            (c *in_* Pair(a, a)) @ (32, REPLACE, 31, 30)
            ((c *in_* Pair(a, a)) == (c == a)) @ (33, BY_THEOREM, "element_of_singleton", 0)
            (c == a) @ (34, TAUTOLOGY, 32, 33)

            (d *in_* Pair(c, d)) @ (35, BY_THEOREM, "right_in_pair", 0)
            (d *in_* Pair(a, a)) @ (36, REPLACE, 35, 30)
            ((d *in_* Pair(a, a)) == (d == a)) @ (37, BY_THEOREM, "element_of_singleton", 0)
            (d == a) @ (38, TAUTOLOGY, 36, 37)

            (c == d) @ (39, BY_EQUIVALENCE, 34, 38)
            (Pair(Pair(a, a), Pair(a, b)) == Pair(Pair(c, c), Pair(c, c))) @ (40, REPLACE, 14, 39)
            (Pair(a, b) *in_* Pair(Pair(a, a), Pair(a, b))) @ (41, BY_THEOREM, "right_in_pair", 4, 5)
            (Pair(a, b) *in_* Pair(Pair(c, c), Pair(c, c))) @ (42, REPLACE, 41, 40)
            ((Pair(a, b) *in_* Pair(Pair(c, c), Pair(c, c))) == (Pair(a, b) == Pair(c, c))) @ (43, BY_THEOREM, "element_of_singleton", 6)
            (Pair(a, b) == Pair(c, c)) @ (44, TAUTOLOGY, 42, 43)
            (b *in_* Pair(a, b)) @ (45, BY_THEOREM, "right_in_pair", 0)
            (b *in_* Pair(c, c)) @ (46, REPLACE, 45, 44)
            ((b *in_* Pair(c, c)) == (b == c)) @ (47, BY_THEOREM, "element_of_singleton", 0)
            (b == c) @ (48, TAUTOLOGY, 47, 46)
            
            (a == c) @ (49, BY_EQUIVALENCE, 34)
            (b == d) @ (50, BY_EQUIVALENCE, 34, 38, 48)
            ((a == c) & (b == d)) @ (51, TAUTOLOGY, 49, 50)
        ((Pair(a, a) == Pair(c, d)) >> ((a == c) & (b == d))) @ (52, DEDUCE)


        with (Pair(a, a) != Pair(c, d)) @ 60:
            (Pair(a, a) == Pair(c, c)) @ (20, TAUTOLOGY, 19, 60)

            (a *in_* Pair(a, a)) @ (21, BY_THEOREM, "left_in_pair", 0)
            (a *in_* Pair(c, c)) @ (22, REPLACE, 21, 20)
            ((a *in_* Pair(c, c)) == (a == c)) @ (23, BY_THEOREM, "element_of_singleton", 0)
            (a == c) @ (24, TAUTOLOGY, 23, 22)

            with (d == a) @ 58:
                (a *in_* Pair(a, a)) @ (59, BY_THEOREM, "left_in_pair", 0)
                (d *in_* Pair(a, a)) @ (70, REPLACE, 59, 58)
                ((d *in_* Pair(a, a)) == (d == a)) @ (61, BY_THEOREM, "element_of_singleton", 0)
                (d == a) @ (62, TAUTOLOGY, 70, 61)
                (c == d) @ (63, BY_EQUIVALENCE, 62, 24)
                (Pair(c, c) == Pair(c, d)) @ (64, REPLACE, 20, 63)
                (Pair(a, a) == Pair(c, d)) @ (65, BY_EQUIVALENCE, 20, 64)
                false @ (66, TAUTOLOGY, 65, 60)
            ((d == a) >> false) @ (67, DEDUCE)
            (d != a) @ (71, TAUTOLOGY, 67)
            
            (Pair(c, d) *in_* Pair(Pair(c, c), Pair(c, d))) @ (72, BY_THEOREM, "right_in_pair", 6, 7)
            (Pair(c, d) *in_* Pair(Pair(a, a), Pair(a, b))) @ (73, REPLACE, 72, 14)

            ((Pair(c, d) == Pair(a, a)) | (Pair(c, d) == Pair(a, b))) @ (74, BY_THEOREM, "element_of_pair", 4, 5, 73)
            with (Pair(c, d) == Pair(a, a)) @ 75:
                (Pair(a, a) == Pair(c, d)) @ (76, BY_EQUIVALENCE, 75)
                false @ (77, TAUTOLOGY, 76, 60)
            ((Pair(c, d) == Pair(a, a)) >> false) @ (78, DEDUCE)
            (Pair(c, d) == Pair(a, b)) @ (79, TAUTOLOGY, 78, 74)

            (d *in_* Pair(c, d)) @ (80, BY_THEOREM, "right_in_pair", 0)
            (d *in_* Pair(a, b)) @ (81, REPLACE, 80, 79)
            ((d == a) | (d == b)) @ (82, BY_THEOREM, "element_of_pair", 81, 0)
            (d == b) @ (83, TAUTOLOGY, 71, 82)
            (b == d) @ (84, BY_EQUIVALENCE, 83)

            ((a == c) & (b == d)) @ (85, TAUTOLOGY, 84, 24)
        ((Pair(a, a) != Pair(c, d)) >> ((a == c) & (b == d))) @ (86, DEDUCE)

        ((a == c) & (b == d)) @ (87, TAUTOLOGY, 86, 52)
    ((OrderedPair(a, b) == OrderedPair(c, d)) >> ((a == c) & (b == d))) @ (88, DEDUCE)
((Set(a) & Set(b) & Set(c) & Set(d)) >> ((OrderedPair(a, b) == OrderedPair(c, d)) >> ((a == c) & (b == d)))) @ (89, DEDUCE)
(((Set(a) & Set(b) & Set(c) & Set(d)) & (OrderedPair(a, b) == OrderedPair(c, d))) >> ((a == c) & (b == d))) @ (90, TAUTOLOGY, 89)

All(a_, b_, c_, d_, ((Set(a_) & Set(b_) & Set(c_) & Set(d_)) & (OrderedPair(a_, b_) == OrderedPair(c_, d_))) >> ((a_ == c_) & (b_ == d_))) @ ("comparison_of_ordered_pairs", CLOSING, 90)

# arity 2
Arity2 = make_property("arity_2")
All(p_, Arity2(p_) == Exist(a_, b_, (Set(a_) & Set(b_)) & (p_ == OrderedPair(a_, b_)))) @ ("arity_2", DEFINE_PROPERTY, "arity_2")

# arity2 condition
with ((Set(a) & Set(b)) & (p == OrderedPair(a, b))) @ 0:
    Exist(b_, ((Set(a) & Set(b_)) & (p == OrderedPair(a, b_)))) @ (1, FOUND, b, 0)
    Exist(a_, b_, (((Set(a_) & Set(b_)) & (p == OrderedPair(a_, b_))))) @ (2, FOUND, a, 1)
    (Arity2(p) == Exist(a_, b_, (Set(a_) & Set(b_)) & (p == OrderedPair(a_, b_)))) @ (3, BY_THEOREM, "arity_2")
    Arity2(p) @ (4, TAUTOLOGY, 2, 3)
((((Set(a) & Set(b)) & (p == OrderedPair(a, b)))) >> Arity2(p)) @ (5, DEDUCE)
All(a_, b_, p_, (((Set(a_) & Set(b_)) & (p_ == OrderedPair(a_, b_)))) >> Arity2(p_)) @ ("arity_2_condition", CLOSING, 5)

def arity_2(target, Seta, Setb, po):
    Seta = proof_history[Seta]
    assert Seta.is_proved()
    Setb = proof_history[Setb]
    assert Setb.is_proved()
    po = proof_history[po]
    assert po.is_proved()
    assert Seta.type_ == TYPE_PROPERTY
    assert Seta.name == "set"
    a0 = Seta.children[0]
    assert Setb.type_ == TYPE_PROPERTY
    assert Setb.name == "set"
    b0 = Setb.children[0]
    assert po.type_ == TYPE_PROPERTY
    assert po.name == "equal"
    p0 = po.children[0]
    All(b_, p_, (((Set(a0) & Set(b_)) & (p_ == OrderedPair(a0, b_)))) >> Arity2(p_)) @ (-5, PUT, a0, "arity_2_condition")
    All(p_, (((Set(a0) & Set(b0)) & (p_ == OrderedPair(a0, b0)))) >> Arity2(p_)) @ (-5, PUT, b0, -5)
    ((((Set(a0) & Set(b0)) & (p0 == OrderedPair(a0, b0)))) >> Arity2(p0)) @ (-5, PUT, p0, -5)
    Seta @ -6
    Setb @ -7
    po @ -8
    Arity2(p0) @ (-5, TAUTOLOGY, -5, -6, -7, -8)
    return target @ (-5, TAUTOLOGY, -5)

ARITY_2 = 39
callbacks[ARITY_2] = arity_2

# ordered pair is arity 2
clear()
with (Set(a) & Set(b)) @ 0:
    (OrderedPair(a, b) == OrderedPair(a, b)) @ (1, BY_EQUIVALENCE)
    Set(a) @ (2, TAUTOLOGY, 0)
    Set(b) @ (3, TAUTOLOGY, 0)
    Arity2(OrderedPair(a, b)) @(4, ARITY_2, 2, 3, 1)
((Set(a) & Set(b)) >> Arity2(OrderedPair(a, b))) @ (5, DEDUCE)
All(a_, b_, (Set(a_) & Set(b_)) >> Arity2(OrderedPair(a_, b_))) @ ("ordered_pair_is_arity_2", CLOSING, 5)

# unique left
clear()
with Arity2(p) @ 0:
    (Arity2(p) == Exist(a_, b_, (Set(a_) & Set(b_)) & (p == OrderedPair(a_, b_)))) @ (1, PUT, p, "arity_2")
    Exist(a_, b_, (Set(a_) & Set(b_)) & (p == OrderedPair(a_, b_))) @ (2, TAUTOLOGY, 0, 1)
    Exist(b_, (Set(c) & Set(b_)) & (p == OrderedPair(c, b_))) @ (3, LET, c, 2)
    ((Set(c) & Set(d)) & (p == OrderedPair(c, d))) @ (4, LET, d, 3)
    Exist(b_, (Set(e) & Set(b_)) & (p == OrderedPair(e, b_))) @ (5, LET, e, 2)
    ((Set(e) & Set(f)) & (p == OrderedPair(e, f))) @ (6, LET, f, 5)
    (p == OrderedPair(c, d)) @ (7, TAUTOLOGY, 4)
    (p == OrderedPair(e, f)) @ (8, TAUTOLOGY, 6)
    (OrderedPair(c, d) == OrderedPair(e, f)) @ (9, BY_EQUIVALENCE, 7, 8)
    ((c == e) & (d == f)) @ (10, BY_THEOREM, "comparison_of_ordered_pairs", 4, 6, 9)
    (c == e) @ (11, TAUTOLOGY, 10)
    UniquelyExist(a_, Exist(b_, (Set(a_) & Set(b_)) & (p == OrderedPair(a_, b_)))) @ (12, CLAIM_UNIQUE, 11)
(Arity2(p) >> UniquelyExist(a_, Exist(b_, (Set(a_) & Set(b_)) & (p == OrderedPair(a_, b_))))) @ (13, DEDUCE)
All(p_, Arity2(p_) >> UniquelyExist(a_, Exist(b_, (Set(a_) & Set(b_)) & (p_ == OrderedPair(a_, b_))))) @ ("unique_left", CLOSING, 13)

# left
clear()
Left = make_function("left")
All(p_, Arity2(p_) >> Exist(b_, (Set(Left(p_)) & Set(b_)) & (p_ == OrderedPair(Left(p_), b_)))) @ ("left", DEFINE_FUNCTION, "left", "unique_left")

# ordered pair is set
clear()
with (Set(a) & Set(b)) @ 0:
    (OrderedPair(a, b) == Pair(Pair(a, a), Pair(a, b))) @ (1, BY_THEOREM, "ordered_pair")
    Set(Pair(a, a)) @ (2, BY_THEOREM, "pair_is_set", 0)
    Set(Pair(a, b)) @ (3, BY_THEOREM, "pair_is_set", 0)
    Set(Pair(Pair(a, a), Pair(a, b))) @ (4, BY_THEOREM, "pair_is_set", 2, 3)
    Set(OrderedPair(a, b)) @ (5, REPLACE, 4, 1)
((Set(a) & Set(b)) >> Set(OrderedPair(a, b))) @ (6, DEDUCE)
All(a_, b_, ((Set(a_) & Set(b_)) >> Set(OrderedPair(a_, b_)))) @ ("ordered_pair_is_set", CLOSING, 6)

# left of ordered pair
clear()
with (Set(a) & Set(b)) @ 0:
    Arity2(OrderedPair(a, b)) @ (1, BY_THEOREM, "ordered_pair_is_arity_2", 0)
    Set(OrderedPair(a, b)) @ (10, BY_THEOREM, "ordered_pair_is_set", 0)
    Exist(b_, (Set(Left(OrderedPair(a, b))) & Set(b_)) & (OrderedPair(a, b) == OrderedPair(Left(OrderedPair(a, b)), b_))) @ (2, BY_THEOREM, "left", 1)
    ((Set(Left(OrderedPair(a, b))) & Set(c)) & (OrderedPair(a, b) == OrderedPair(Left(OrderedPair(a, b)), c))) @ (3, LET, c, 2)
    ((a == Left(OrderedPair(a, b))) & (b == c)) @ (4, BY_THEOREM, "comparison_of_ordered_pairs", 3, 0, 10)
    (a == Left(OrderedPair(a, b))) @ (5, TAUTOLOGY, 4)
((Set(a) & Set(b)) >> (a == Left(OrderedPair(a, b)))) @ (6, DEDUCE)
All(a_, b_, (Set(a_) & Set(b_)) >> (a_ == Left(OrderedPair(a_, b_)))) @ ("left_of_ordered_pair", CLOSING, 6)

# unique right
clear()
with Arity2(p) @ 0:
    Exist(b_, (Set(Left(p)) & Set(b_)) & (p == OrderedPair(Left(p), b_))) @ (1, BY_THEOREM, "left", 0)
    ((Set(Left(p)) & Set(c)) & (p == OrderedPair(Left(p), c))) @ (2, LET, c, 1)
    ((Set(Left(p)) & Set(d)) & (p == OrderedPair(Left(p), d))) @ (3, LET, d, 1)
    (p == OrderedPair(Left(p), c)) @ (4, TAUTOLOGY, 2)
    (p == OrderedPair(Left(p), d)) @ (5, TAUTOLOGY, 3)
    (OrderedPair(Left(p), c) == OrderedPair(Left(p), d)) @ (6, BY_EQUIVALENCE, 4, 5)
    ((Left(p) == Left(p)) & (c == d)) @ (7, BY_THEOREM, "comparison_of_ordered_pairs", 2, 3, 6)
    (c == d) @ (8, TAUTOLOGY, 7)
    UniquelyExist(b_, (Set(Left(p)) & Set(b_)) & (p == OrderedPair(Left(p), b_))) @ (9, CLAIM_UNIQUE, 8)
(Arity2(p) >> UniquelyExist(b_, (Set(Left(p)) & Set(b_)) & (p == OrderedPair(Left(p), b_)))) @ (10, DEDUCE)
All(p_, Arity2(p_) >> UniquelyExist(b_, (Set(Left(p_)) & Set(b_)) & (p_ == OrderedPair(Left(p_), b_)))) @ ("unique_right", CLOSING, 10)

# right
clear()
Right = make_function("right")
All(p_, Arity2(p_) >> ((Set(Left(p_)) & Set(Right(p_))) & (p_ == OrderedPair(Left(p_), Right(p_))))) @ ("right", DEFINE_FUNCTION, "right", "unique_right")

# right of ordered pair
clear()
with (Set(a) & Set(b)) @ 0:
    Arity2(OrderedPair(a, b)) @ (1, BY_THEOREM, "ordered_pair_is_arity_2", 0)
    Set(OrderedPair(a, b)) @ (2, BY_THEOREM, "ordered_pair_is_set", 0)
    ((Set(Left(OrderedPair(a, b))) & Set(Right(OrderedPair(a, b)))) & (OrderedPair(a, b) == OrderedPair(Left(OrderedPair(a, b)), Right(OrderedPair(a, b))))) @ (3, BY_THEOREM, "right", 1)
    ((a == Left(OrderedPair(a, b))) & (b == Right(OrderedPair(a, b)))) @ (4, BY_THEOREM, "comparison_of_ordered_pairs", 0, 3)
    (b == Right(OrderedPair(a, b))) @ (5, TAUTOLOGY, 4)
((Set(a) & Set(b)) >> (b == Right(OrderedPair(a, b)))) @ (6, DEDUCE)
All(a_, b_, (Set(a_) & Set(b_)) >> (b_ == Right(OrderedPair(a_, b_)))) @ ("right_of_ordered_pair", CLOSING, 6)

# empty
clear()
Empty = make_function("empty")
UniquelyExist(E, All(x_, (x_ *in_* E) == (Set(x_) & false))) @ (0, DEFINE_CLASS, E)
All(x_, (x_ *in_* Empty()) == (Set(x_) & false)) @ (1, DEFINE_FUNCTION, "empty", 0)
((x *in_* Empty()) == (Set(x) & false)) @ (2, PUT, x, 1)
((x *in_* Empty()) == false) @ (3, TAUTOLOGY, 2)
All(x_, (x_ *in_* Empty()) == false) @ ("empty", CLOSING, 3)

# relation
clear()
Relation = make_property("relation")
All(R_, (Relation(R_) == All(x_, (x_ *in_* R_) >> Arity2(x_)))) @ ("relation", DEFINE_PROPERTY, "relation")

# domain
clear()
UniquelyExist(D, All(x_, (x_ *in_* D) == (Set(x_) & Exist(y_, ((y_ *in_* R) & Arity2(y_)) & (Left(y_) == x_))))) @ (0, DEFINE_CLASS, D)
All(R_, UniquelyExist(D, All(x_, (x_ *in_* D) == (Set(x_) & Exist(y_, ((y_ *in_* R_) & Arity2(y_)) & (Left(y_) == x_)))))) @ ("domain_exists", CLOSING, 0)
Domain = make_function("domain")
All(R_, x_, (x_ *in_* Domain(R_)) == (Set(x_) & Exist(y_, ((y_ *in_* R_) & Arity2(y_)) & (Left(y_) == x_)))) @ (1, DEFINE_FUNCTION, "domain", "domain_exists")
with (x *in_* Domain(R)) @ 2:
    (Set(x) & Exist(y_, ((y_ *in_* R) & Arity2(y_)) & (Left(y_) == x))) @ (3, BICONDITION, 1, 2)
    Exist(y_, ((y_ *in_* R) & Arity2(y_)) & (Left(y_) == x)) @ (4, TAUTOLOGY, 3)
((x *in_* Domain(R)) >> Exist(y_, ((y_ *in_* R) & Arity2(y_)) & (Left(y_) == x))) @ (5, DEDUCE)
with Exist(y_, ((y_ *in_* R) & Arity2(y_)) & (Left(y_) == x)) @ 6:
    (((y *in_* R) & Arity2(y)) & (Left(y) == x)) @ (7, LET, y, 6)
    Arity2(y) @ (8, TAUTOLOGY, 7)
    Exist(a_, b_, (Set(a_) & Set(b_)) & (y == OrderedPair(a_, b_))) @ (9, BICONDITION, "arity_2", 8)
    Exist(b_, (Set(a) & Set(b_)) & (y == OrderedPair(a, b_))) @ (10, LET, a, 9)
    ((Set(a) & Set(b)) & (y == OrderedPair(a, b))) @ (11, LET, b, 10)
    (a == Left(OrderedPair(a, b))) @ (12, BY_THEOREM, "left_of_ordered_pair", 11)
    (Left(y) == x) @ (13, TAUTOLOGY, 7)
    (y == OrderedPair(a, b)) @ (14, TAUTOLOGY, 11)
    (Left(OrderedPair(a, b)) == x) @ (15, REPLACE, 13, 14)
    (a == x) @ (16, BY_EQUIVALENCE, 15, 12)
    Set(a) @ (17, TAUTOLOGY, 11)
    Set(x) @ (18, REPLACE, 17, 16)
    (Set(x) & Exist(y_, ((y_ *in_* R) & Arity2(y_)) & (Left(y_) == x))) @ (19, TAUTOLOGY, 18, 6)
    (x *in_* Domain(R)) @ (20, BICONDITION, 1, 19)
((Exist(y_, ((y_ *in_* R) & Arity2(y_)) & (Left(y_) == x))) >> (x *in_* Domain(R))) @ (21, DEDUCE)
((x *in_* Domain(R)) == Exist(y_, ((y_ *in_* R) & Arity2(y_)) & (Left(y_) == x))) @ (22, TAUTOLOGY, 5, 21)
All(R_, x_, (x_ *in_* Domain(R_)) == Exist(y_, ((y_ *in_* R_) & Arity2(y_)) & (Left(y_) == x_))) @ ("domain", CLOSING, 22)

# domain condition
clear()
with (Set(x) & Exist(f_, Set(f_) & (OrderedPair(x, f_) *in_* R))) @ 0:
    ((x *in_* Domain(R)) == Exist(y_, (((y_ *in_* R) & Arity2(y_)) & (Left(y_) == x)))) @ (1, BY_THEOREM, "domain")
    
    Set(x) @ (2, TAUTOLOGY, 0)
    Exist(f_, Set(f_) & (OrderedPair(x, f_) *in_* R)) @ (3, TAUTOLOGY, 0)
    (Set(f) & (OrderedPair(x, f) *in_* R)) @ (4, LET, f, 3)
    Set(f) @ (5, TAUTOLOGY, 4)
    (OrderedPair(x, f) *in_* R) @ (6, TAUTOLOGY, 4)

    (OrderedPair(x, f) == OrderedPair(x, f)) @ (7, BY_EQUIVALENCE)
    Arity2(OrderedPair(x, f)) @ (8, ARITY_2, 2, 5, 7)
    (x == Left(OrderedPair(x, f))) @ (9, BY_THEOREM, "left_of_ordered_pair", 2, 5)
    (Left(OrderedPair(x, f)) == x) @ (10, BY_EQUIVALENCE, 9)

    (((OrderedPair(x, f) *in_* R) & Arity2(OrderedPair(x, f))) & (Left(OrderedPair(x, f)) == x)) @ (11, TAUTOLOGY, 10, 6, 8)
    Exist(y_, (((y_ *in_* R) & Arity2(y_)) & (Left(y_) == x))) @ (12, FOUND, OrderedPair(x, f), 11)
    (x *in_* Domain(R)) @ (13, TAUTOLOGY, 12, 1)
((Set(x) & Exist(f_, Set(f_) & (OrderedPair(x, f_) *in_* R))) >> (x *in_* Domain(R))) @ (14, DEDUCE)
All(R_, x_, (Set(x_) & Exist(f_, Set(f_) & (OrderedPair(x_, f_) *in_* R_))) >> (x_ *in_* Domain(R_))) @ (15, CLOSING, 14)

with (((Set(x) & Set(y)) & (OrderedPair(x, y) *in_* R))) @ 16:
    (Set(y) & (OrderedPair(x, y) *in_* R)) @ (17, TAUTOLOGY, 16)
    Exist(f_, Set(f_) & (OrderedPair(x, f_) *in_* R)) @ (18, FOUND, y, 17)
    (Set(x) & Exist(f_, Set(f_) & (OrderedPair(x, f_) *in_* R))) @ (19, TAUTOLOGY, 16, 18)
    (x *in_* Domain(R)) @ (20, BY_THEOREM, 15, 19)
((((Set(x) & Set(y)) & (OrderedPair(x, y) *in_* R))) >> (x *in_* Domain(R))) @ (21, DEDUCE)
All(x_, y_, R_, (((Set(x_) & Set(y_)) & (OrderedPair(x_, y_) *in_* R_))) >> (x_ *in_* Domain(R_))) @ ("domain_condition", CLOSING, 21)

# function
clear()
Function = make_property("function")
All(F_, Function(F_) == (Relation(F_) & All(a_, b_, (((a_ *in_* F_) & (b_ *in_* F_)) & (Left(a_) == Left(b_))) >> (a_ == b_)))) @ ("function", DEFINE_PROPERTY, "function")

# unique pair in function
clear()
with Function(F) @ 0:
    with x *in_* Domain(F) @ 1:
        ((x *in_* Domain(F)) == Exist(y_, ((y_ *in_* F) & Arity2(y_)) & (Left(y_) == x))) @ (2, BY_THEOREM, "domain")
        Exist(y_, ((y_ *in_* F) & Arity2(y_)) & (Left(y_) == x)) @ (3, TAUTOLOGY, 1, 2)
        (Function(F) == (Relation(F) & All(a_, b_, (((a_ *in_* F) & (b_ *in_* F)) & (Left(a_) == Left(b_))) >> (a_ == b_)))) @ (4, BY_THEOREM, "function", 0)
        Relation(F) @ (5, TAUTOLOGY, 0, 4)
        All(a_, b_, (((a_ *in_* F) & (b_ *in_* F)) & (Left(a_) == Left(b_))) >> (a_ == b_)) @ (6, TAUTOLOGY, 0, 4)

        (((a *in_* F) & Arity2(a)) & (Left(a) == x)) @ (7, LET, a, 3)
        (((b *in_* F) & Arity2(b)) & (Left(b) == x)) @ (8, LET, b, 3)
        (Left(a) == x) @ (9, TAUTOLOGY, 7)
        (Left(b) == x) @ (10, TAUTOLOGY, 8)
        (Left(a) == Left(b)) @ (11, BY_EQUIVALENCE, 9, 10)
        (a == b) @ (12, BY_THEOREM, 6, 7, 8, 11)
        UniquelyExist(y_, ((y_ *in_* F) & Arity2(y_)) & (Left(y_) == x)) @ (13, CLAIM_UNIQUE, 12)
    ((x *in_* Domain(F)) >> UniquelyExist(y_, ((y_ *in_* F) & Arity2(y_)) & (Left(y_) == x))) @ (14, DEDUCE)
((Function(F)) >> ((x *in_* Domain(F)) >> UniquelyExist(y_, ((y_ *in_* F) & Arity2(y_)) & (Left(y_) == x)))) @ (15, DEDUCE)
(((Function(F) & (x *in_* Domain(F)))) >> UniquelyExist(y_, ((y_ *in_* F) & Arity2(y_)) & (Left(y_) == x))) @ (16, TAUTOLOGY, 15)
All(F_, x_, ((Function(F_) & (x_ *in_* Domain(F_)))) >> UniquelyExist(y_, ((y_ *in_* F_) & Arity2(y_)) & (Left(y_) == x_))) @ ("unique_pair_in_function", CLOSING, 16)

# find pair
clear()
FindPair = make_function("find_pair")
All(F_, x_, ((Function(F_) & (x_ *in_* Domain(F_)))) >> (((FindPair(F_, x_) *in_* F_) & Arity2(FindPair(F_, x_))) & (Left(FindPair(F_, x_)) == x_))) @ ("find_pair", DEFINE_FUNCTION, "find_pair", "unique_pair_in_function")

# put
clear()
Put = make_function("put")
All(F_, x_, F_(x_) == Right(FindPair(F_, x_))) @ ("put", COMPOSITE, "put")

# structure of function
clear()
with Function(F) @ 0:
    with (x *in_* Domain(F)) @ 1:
        (F(x) == Right(FindPair(F, x))) @ (2, BY_THEOREM, "put")
        (((FindPair(F, x) *in_* F) & Arity2(FindPair(F, x))) & (Left(FindPair(F, x)) == x)) @ (3, BY_THEOREM, "find_pair", 0, 1)
        ((Set(Left(FindPair(F, x))) & Set(Right(FindPair(F, x)))) & (FindPair(F, x) == OrderedPair(Left(FindPair(F, x)), Right(FindPair(F, x))))) @ (4, BY_THEOREM, "right", 3)
        (FindPair(F, x) == OrderedPair(Left(FindPair(F, x)), Right(FindPair(F, x)))) @ (5, TAUTOLOGY, 4)
        (Left(FindPair(F, x)) == x) @ (6, TAUTOLOGY, 3)
        (FindPair(F, x) == OrderedPair(x, Right(FindPair(F, x)))) @ (7, REPLACE, 5, 6)
        (FindPair(F, x) == OrderedPair(x, F(x))) @ (8, REPLACE, 7, 2)
        (FindPair(F, x) *in_* F) @ (9, TAUTOLOGY, 3)
        (OrderedPair(x, F(x)) *in_* F) @ (10, REPLACE, 9, 8)
    ((x *in_* Domain(F)) >> (OrderedPair(x, F(x)) *in_* F)) @ (11, DEDUCE)
(Function(F) >> ((x *in_* Domain(F)) >> (OrderedPair(x, F(x)) *in_* F))) @ (12, DEDUCE)
((Function(F) & (x *in_* Domain(F))) >> (OrderedPair(x, F(x)) *in_* F)) @ (13, TAUTOLOGY, 12)
All(F_, x_, (Function(F_) & (x_ *in_* Domain(F_))) >> (OrderedPair(x_, F_(x_)) *in_* F_)) @ ("structure_of_function", CLOSING, 13)

# unique output
clear()
with Function(F) @ 0:
    with Exist(y, OrderedPair(x, y) *in_* F) @ 1:
        pass

# cap
clear()
UniquelyExist(C, (All(x_, (x_ *in_* C) == (Set(x_) & ((x_ *in_* A) & (x_ *in_* B)))))) @ (0, DEFINE_CLASS, C)
All(A_, B_, UniquelyExist(C, (All(x_, (x_ *in_* C) == (Set(x_) & ((x_ *in_* A_) & (x_ *in_* B_))))))) @ (1, CLOSING, 0)
cap = make_function("cap")
All(A_, B_, x_, (x_ *in_* (A_ *cap* B_)) == (Set(x_) & ((x_ *in_* A_) & (x_ *in_* B_)))) @ (20, DEFINE_FUNCTION, "cap", 1)

with ((x *in_* A) & (x *in_* B)) @ 0:
    (x *in_* A) @ (1, TAUTOLOGY, 0)
    Set(x) @ (2, PUT_THEOREM, "set_condition", A, 1)
    (Set(x) & ((x *in_* A) & (x *in_* B))) @ (3, TAUTOLOGY, 0, 2)
    (x *in_* (A *cap* B)) @ (4, BICONDITION, 20, 3)
(((x *in_* A) & (x *in_* B)) >> (x *in_* (A *cap* B))) @ (5, DEDUCE)

with (x *in_* (A *cap* B)) @ 6:
    (Set(x) & ((x *in_* A) & (x *in_* B))) @ (7, BICONDITION, 20, 6)
    ((x *in_* A) & (x *in_* B)) @ (8, TAUTOLOGY, 7)
((x *in_* (A *cap* B)) >> ((x *in_* A) & (x *in_* B))) @ (9, DEDUCE)
((x *in_* (A *cap* B)) == ((x *in_* A) & (x *in_* B))) @ (10, TAUTOLOGY, 9, 5)
All(A_, B_, x_, (x_ *in_* (A_ *cap* B_)) == ((x_ *in_* A_) & (x_ *in_* B_))) @ ("cap", CLOSING, 10)


# regularity
clear()
All(a_, (Set(a_) & (a_ != Empty())) >> Exist(u_, (u_ *in_* a) & ((u *cap* a) == Empty()))) @ ("regularity", AXIOM)

# image
clear()
UniquelyExist(C, All(x_, (x_ *in_* C) == (Set(x_) & Exist(a_, ((a_ *in_* A) & (a_ *in_* Domain(F))) & (x_ == F(a_)))))) @ (0, DEFINE_CLASS, C)
All(F_, A_, UniquelyExist(C, All(x_, (x_ *in_* C) == (Set(x_) & Exist(a_, ((a_ *in_* A_) & (a_ *in_* Domain(F_))) & (x_ == F_(a_))))))) @ (1, CLOSING, 0)
Image = make_function("image")
All(F_, A_, x_, (x_ *in_* F_[A_]) == (Set(x_) & Exist(a_, ((a_ *in_* A_) & (a_ *in_* Domain(F_))) & (x_ == F_(a_))))) @ ("image", DEFINE_FUNCTION, "image", 1)

# replacement
clear()
All(F_, a_, (Function(F_) & Set(a_)) >> Set(F_[a_])) @ ("replacement", AXIOM)

# union
clear()
UniquelyExist(C, All(x_, (x_ *in_* C) == (Set(x_) & Exist(a_, ((a_ *in_* A) & (x_ *in_* a_)))))) @ (0, DEFINE_CLASS, C)
All(A_, UniquelyExist(C, All(x_, (x_ *in_* C) == (Set(x_) & Exist(a_, ((a_ *in_* A_) & (x_ *in_* a_))))))) @ (1, CLOSING, 0)
Union = make_function("union")
All(A_, All(x_, (x_ *in_* Union(A_)) == (Set(x_) & Exist(a_, ((a_ *in_* A_) & (x_ *in_* a_)))))) @ (2, DEFINE_FUNCTION, "union", 1)

with (x *in_* Union(A)) @ 3:
    (Set(x) & Exist(a_, ((a_ *in_* A) & (x *in_* a_)))) @ (4, BICONDITION, 2, 3)
    Exist(a_, ((a_ *in_* A) & (x *in_* a_))) @ (5, TAUTOLOGY, 4)
((x *in_* Union(A)) >> Exist(a_, ((a_ *in_* A) & (x *in_* a_)))) @ (6, DEDUCE)
with Exist(a_, ((a_ *in_* A) & (x *in_* a_))) @ 7:
    ((a *in_* A) & (x *in_* a)) @ (8, LET, a, 7)
    (x *in_* a) @ (9, TAUTOLOGY, 8)
    Set(x) @ (10, PUT_THEOREM, "set_condition", a, 9)
    (Set(x) & Exist(a_, ((a_ *in_* A) & (x *in_* a_)))) @ (11, TAUTOLOGY, 10, 7)
    (x *in_* Union(A)) @ (12, BICONDITION, 2, 11)
(Exist(a_, ((a_ *in_* A) & (x *in_* a_))) >> (x *in_* Union(A))) @ (13, DEDUCE)
((x *in_* Union(A)) == Exist(a_, ((a_ *in_* A) & (x *in_* a_)))) @ (14, TAUTOLOGY, 6, 13)
All(A_, All(x_, (x_ *in_* Union(A_)) == Exist(a_, ((a_ *in_* A_) & (x_ *in_* a_))))) @ ("union", CLOSING, 14)

# union of set is set
clear()
All(a_, Set(a_) >> Set(Union(a_))) @ ("union_of_set_is_set", AXIOM)

# inclusion
clear()
inc = make_property("inclusion")
All(A_, B_, (A_ *inc* B_) == All(x_, (x_ *in_* A_) >> (x_ *in_* B_))) @ ("inclusion", DEFINE_PROPERTY, "inclusion")

# power
clear()
UniquelyExist(C, All(x_, (x_ *in_* C) == (Set(x_) & Exist(a_, ((a_ *in_* A) & (x_ *inc* a_)))))) @ (0, DEFINE_CLASS, C)
All(A_, UniquelyExist(C, All(x_, (x_ *in_* C) == (Set(x_) & Exist(a_, ((a_ *in_* A_) & (x_ *inc* a_))))))) @ (1, CLOSING, 0)
Power = make_function("power")
All(A_, All(x_, (x_ *in_* Power(A_)) == (Set(x_) & Exist(a_, ((a_ *in_* A_) & (x_ *inc* a_)))))) @ ("power", DEFINE_FUNCTION, "power", 1)

# power_of_set_is_set
clear()
All(a_, Set(a_) >> Set(Power(a_))) @ ("power_of_set_is_set", AXIOM)

# cup
clear()
UniquelyExist(C, All(x_, (x_ *in_* C) == (Set(x_) & ((x *in_* A) | (x *in_* B))))) @ (0, DEFINE_CLASS, C)
All(A_, B_, UniquelyExist(C, All(x_, (x_ *in_* C) == (Set(x_) & ((x *in_* A_) | (x *in_* B_)))))) @ (1, CLOSING, 0)
cup = make_function("cup")
All(A_, B_, All(x_, (x_ *in_* (A_ *cup* B_)) == (Set(x_) & ((x *in_* A_) | (x *in_* B_))))) @ ("cup", DEFINE_FUNCTION, "cup", 1)

# successor
clear()
Succ = make_function("successor")
All(x_, Succ(x_) == (x_ *cup* Pair(x_, x_))) @ ("successor", COMPOSITE, "successor")

# infinity
clear()
Exist(a_, (Set(a_) & (Empty() *in_* a_)) & All(x_, (x_ *in_* a_) >> (Succ(x_) *in_* a_))) @ ("infinity", AXIOM)

# choice
clear()
Exist(G_, Function(G_) & All(a_, (Set(a_) & Exist(x_, x_ *in_* a_)) >> (G_(a_) *in_* a_))) @ ("choice", AXIOM)

# identity
clear()
UniquelyExist(D, All(x_, (x_ *in_* D) == (Set(x_) & Exist(a_, (a_ *in_* A) & (x_ == OrderedPair(a_, a_)))))) @ (0, DEFINE_CLASS, D)
All(A_, UniquelyExist(D, All(x_, (x_ *in_* D) == (Set(x_) & Exist(a_, (a_ *in_* A_) & (x_ == OrderedPair(a_, a_))))))) @ (1, CLOSING, 0)
Identity = make_function("identity")
All(A_, x_, (x_ *in_* Identity(A_)) == (Set(x_) & Exist(a_, (a_ *in_* A_) & (x_ == OrderedPair(a_, a_))))) @ (2, DEFINE_FUNCTION, "identity", 1)

with Exist(a_, (a_ *in_* A) & (x == OrderedPair(a_, a_))) @ 3:
    ((a *in_* A) & (x == OrderedPair(a, a))) @ (4, LET, a, 3)
    (a *in_* A) @ (5, TAUTOLOGY, 4)
    Set(a) @ (6, PUT_THEOREM, "set_condition", A, 5)
    Set(OrderedPair(a, a)) @ (7, BY_THEOREM, "ordered_pair_is_set", 6)
    (x == OrderedPair(a, a)) @ (8, TAUTOLOGY, 4)
    Set(x) @ (9, REPLACE, 7, 8)
    (Set(x) & Exist(a_, (a_ *in_* A) & (x == OrderedPair(a_, a_)))) @ (10, TAUTOLOGY, 3, 9)
    (x *in_* Identity(A)) @ (11, BICONDITION, 2, 10)
(Exist(a_, (a_ *in_* A) & (x == OrderedPair(a_, a_))) >> (x *in_* Identity(A))) @ (12, DEDUCE)
with (x *in_* Identity(A)) @ 13:
    (Set(x) & Exist(a_, (a_ *in_* A) & (x == OrderedPair(a_, a_)))) @ (14, BICONDITION, 2, 13)
    Exist(a_, (a_ *in_* A) & (x == OrderedPair(a_, a_))) @ (15, TAUTOLOGY, 14)
((x *in_* Identity(A)) >> Exist(a_, (a_ *in_* A) & (x == OrderedPair(a_, a_)))) @ (16, DEDUCE)
((x *in_* Identity(A)) == Exist(a_, (a_ *in_* A) & (x == OrderedPair(a_, a_)))) @ (17, TAUTOLOGY, 16, 12)
All(A_, x_, (x_ *in_* Identity(A_)) == Exist(a_, (a_ *in_* A_) & (x_ == OrderedPair(a_, a_)))) @ ("identity", CLOSING, 17)

# element of identity
clear()
with (x *in_* Identity(A)) @ 0:
    ((x *in_* Identity(A)) == Exist(a_, (a_ *in_* A) & (x == OrderedPair(a_, a_)))) @ (1, BY_THEOREM, "identity")
    Exist(a_, (a_ *in_* A) & (x == OrderedPair(a_, a_))) @ (2, TAUTOLOGY, 0, 1)
    ((a *in_* A) & (x == OrderedPair(a, a))) @ (3, LET, a, 2)
    (a *in_* A) @ (4, TAUTOLOGY, 3)
    Exist(C_, a *in_* C_) @ (6, FOUND, A, 4)
    (Set(a) == Exist(C_, a *in_* C_)) @ (5, BY_THEOREM, "set")
    Set(a) @ (6, TAUTOLOGY, 5, 6)
    ((Set(a) & Set(a)) & (x == OrderedPair(a, a))) @ (7, TAUTOLOGY, 3, 6)
    Exist(b_, (Set(a) & Set(b_)) & (x == OrderedPair(a, b_))) @ (8, FOUND, a, 7)
    Exist(a_, b_, (Set(a_) & Set(b_)) & (x == OrderedPair(a_, b_))) @ (9, FOUND, a, 8)
    (Arity2(x) == Exist(a_, b_, (Set(a_) & Set(b_)) & (x == OrderedPair(a_, b_)))) @ (10, BY_THEOREM, "arity_2")
    Arity2(x) @ (11, TAUTOLOGY, 9, 10)
    ((Set(Left(x)) & Set(Right(x))) & (x == OrderedPair(Left(x), Right(x)))) @ (12, BY_THEOREM, "right", 11)
    (x == OrderedPair(a, a)) @ (13, TAUTOLOGY, 3)
    (x == OrderedPair(Left(x), Right(x))) @ (14, TAUTOLOGY, 12)
    (OrderedPair(a, a) == OrderedPair(Left(x), Right(x))) @ (15, BY_EQUIVALENCE, 13, 14)
    ((a == Left(x)) & (a == Right(x))) @ (16, BY_THEOREM, "comparison_of_ordered_pairs", 6, 12, 15)
    (a == Left(x)) @ (17, TAUTOLOGY, 16)
    (a == Right(x)) @ (18, TAUTOLOGY, 16)
    (Left(x) == Right(x)) @ (19, BY_EQUIVALENCE, 17, 18)
    ((Arity2(x) & (x == OrderedPair(Left(x), Right(x)))) & (Left(x) == Right(x))) @ (20, TAUTOLOGY, 19, 14, 11)
((x *in_* Identity(A)) >> ((Arity2(x) & (x == OrderedPair(Left(x), Right(x)))) & (Left(x) == Right(x)))) @ (21, DEDUCE)
All(A_, x_, (x_ *in_* Identity(A_)) >> ((Arity2(x_) & (x_ == OrderedPair(Left(x_), Right(x_)))) & (Left(x_) == Right(x_)))) @ ("element_of_identity", CLOSING, 21)

# identity is relation
clear()
with (x *in_* Identity(A)) @ 0:
    ((x *in_* Identity(A)) == Exist(a_, (a_ *in_* A) & (x == OrderedPair(a_, a_)))) @ (1, BY_THEOREM, "identity")
    Exist(a_, (a_ *in_* A) & (x == OrderedPair(a_, a_))) @ (2, TAUTOLOGY, 0, 1)
    ((a *in_* A) & (x == OrderedPair(a, a))) @ (3, LET, a, 2)
    (a *in_* A) @ (4, TAUTOLOGY, 3)
    Exist(C_, a *in_* C_) @ (5, FOUND, A, 4)
    (Set(a) == Exist(C_, a *in_* C_)) @ (6, BY_THEOREM, "set")
    Set(a) @ (7, TAUTOLOGY, 5, 6)
    ((Set(a) & Set(a)) & (x == OrderedPair(a, a))) @ (8, TAUTOLOGY, 7, 3)
    Exist(b_, (Set(a) & Set(b_)) & (x == OrderedPair(a, b_))) @ (9, FOUND, a, 8)
    Exist(a_, b_, (Set(a_) & Set(b_)) & (x == OrderedPair(a_, b_))) @ (10, FOUND, a, 9)
    (Arity2(x) == Exist(a_, b_, (Set(a_) & Set(b_)) & (x == OrderedPair(a_, b_)))) @ (11, BY_THEOREM, "arity_2")
    Arity2(x) @ (12, TAUTOLOGY, 10, 11)
((x *in_* Identity(A)) >> Arity2(x)) @ (13, DEDUCE)
All(x_, (x_ *in_* Identity(A)) >> Arity2(x_)) @ (14, CLOSING, 13)
(Relation(Identity(A)) == All(x_, (x_ *in_* Identity(A)) >> Arity2(x_))) @ (15, BY_THEOREM, "relation")
Relation(Identity(A)) @ (16, TAUTOLOGY, 14, 15)
All(A_, Relation(Identity(A_))) @ ("identity_is_relation", CLOSING, 16)

# identity is function
clear()
Relation(Identity(A)) @ (10, BY_THEOREM, "identity_is_relation")
with (((a *in_* Identity(A)) & (b *in_* Identity(A))) & (Left(a) == Left(b))) @ 0:
    (a *in_* Identity(A)) @ (1, TAUTOLOGY, 0)
    ((a *in_* Identity(A)) == Exist(a_, (a_ *in_* A) & (a == OrderedPair(a_, a_)))) @ (2, BY_THEOREM, "identity")
    Exist(a_, (a_ *in_* A) & (a == OrderedPair(a_, a_))) @ (3, TAUTOLOGY, 1, 2)
    ((u *in_* A) & (a == OrderedPair(u, u))) @ (4, LET, u, 3)
    (u *in_* A) @ (5, TAUTOLOGY, 4)
    Exist(C_, u *in_* C_) @ (6, FOUND, A, 5)
    (Set(u) == Exist(C_, u *in_* C_)) @ (7, BY_THEOREM, "set")
    Set(u) @ (8, TAUTOLOGY, 6, 7)
    ((Relation(Identity(A)) == All(x_, (x_ *in_* Identity(A)) >> Arity2(x_)))) @ (11, BY_THEOREM, "relation")
    All(x_, (x_ *in_* Identity(A)) >> Arity2(x_)) @ (12, TAUTOLOGY, 11, 10)
    Arity2(a) @ (13, BY_THEOREM, 12, 1)
    ((Set(Left(a)) & Set(Right(a))) & (a == OrderedPair(Left(a), Right(a)))) @ (14, BY_THEOREM, "right", 13)
    (a == OrderedPair(u, u)) @ (15, TAUTOLOGY, 4)
    (a == OrderedPair(Left(a), Right(a))) @ (36, TAUTOLOGY, 14)
    (OrderedPair(u, u) == OrderedPair(Left(a), Right(a))) @ (17, BY_EQUIVALENCE, 15, 36)
    (Set(u) & Set(Left(a)) & Set(Right(a))) @ (18, TAUTOLOGY, 14, 8)
    ((u == Left(a)) & (u == Right(a))) @ (19, BY_THEOREM, "comparison_of_ordered_pairs", 18, 17)
    (u == Left(a)) @ (20, TAUTOLOGY, 19)
    (u == Right(a)) @ (21, TAUTOLOGY, 19)
    (Left(a) == Right(a)) @ (30, BY_EQUIVALENCE, 20, 21)

    (b *in_* Identity(A)) @ (1, TAUTOLOGY, 0)
    ((b *in_* Identity(A)) == Exist(a_, (a_ *in_* A) & (b == OrderedPair(a_, a_)))) @ (2, BY_THEOREM, "identity")
    Exist(a_, (a_ *in_* A) & (b == OrderedPair(a_, a_))) @ (3, TAUTOLOGY, 1, 2)
    ((v *in_* A) & (b == OrderedPair(v, v))) @ (4, LET, v, 3)
    (v *in_* A) @ (5, TAUTOLOGY, 4)
    Exist(C_, v *in_* C_) @ (6, FOUND, A, 5)
    (Set(v) == Exist(C_, v *in_* C_)) @ (7, BY_THEOREM, "set")
    Set(v) @ (8, TAUTOLOGY, 6, 7)
    ((Relation(Identity(A)) == All(x_, (x_ *in_* Identity(A)) >> Arity2(x_)))) @ (11, BY_THEOREM, "relation")
    All(x_, (x_ *in_* Identity(A)) >> Arity2(x_)) @ (12, TAUTOLOGY, 11, 10)
    Arity2(b) @ (13, BY_THEOREM, 12, 1)
    (((Set(Left(b))) & Set(Right(b))) & (b == OrderedPair(Left(b), Right(b)))) @ (14, BY_THEOREM, "right", 13)
    (b == OrderedPair(v, v)) @ (15, TAUTOLOGY, 4)
    (b == OrderedPair(Left(b), Right(b))) @ (16, TAUTOLOGY, 14)
    (OrderedPair(v, v) == OrderedPair(Left(b), Right(b))) @ (17, BY_EQUIVALENCE, 15, 16)
    (Set(v) & Set(Left(b)) & Set(Right(b))) @ (18, TAUTOLOGY, 14, 8)
    ((v == Left(b)) & (v == Right(b))) @ (19, BY_THEOREM, "comparison_of_ordered_pairs", 18, 17)
    (v == Left(b)) @ (20, TAUTOLOGY, 19)
    (v == Right(b)) @ (21, TAUTOLOGY, 19)
    (Left(b) == Right(b)) @ (22, BY_EQUIVALENCE, 20, 21)

    (Left(a) == Left(b)) @ (23, TAUTOLOGY, 0)
    (Right(a) == Right(b)) @ (24, BY_EQUIVALENCE, 23, 22, 30)
    
    (a == OrderedPair(Left(b), Right(a))) @ (40, REPLACE, 36, 23)
    (a == OrderedPair(Left(b), Right(b))) @ (41, REPLACE, 40, 24)
    (a == b) @ (42, BY_EQUIVALENCE, 16, 41)

((((a *in_* Identity(A)) & (b *in_* Identity(A))) & (Left(a) == Left(b))) >> (a == b)) @ (43, DEDUCE)
All(A_, a_, b_, ((((a_ *in_* Identity(A_)) & (b_ *in_* Identity(A_))) & (Left(a_) == Left(b_))) >> (a_ == b_))) @ (44, CLOSING, 43)

All(a_, b_, ((((a_ *in_* Identity(A)) & (b_ *in_* Identity(A))) & (Left(a_) == Left(b_))) >> (a_ == b_))) @ (45, PUT, A, 44)
Relation(Identity(A)) @ (46, PUT, A, "identity_is_relation")
(Relation(Identity(A)) & All(a_, b_, (((a_ *in_* Identity(A)) & (b_ *in_* Identity(A))) & (Left(a_) == Left(b_))) >> (a_ == b_))) @ (47, TAUTOLOGY, 45, 46)
(Function(Identity(A)) == (Relation(Identity(A)) & All(a_, b_, (((a_ *in_* Identity(A)) & (b_ *in_* Identity(A))) & (Left(a_) == Left(b_))) >> (a_ == b_)))) @ (48, BY_THEOREM, "function")
Function(Identity(A)) @ (49, TAUTOLOGY, 48, 47)
All(A_, Function(Identity(A_))) @ ("identity_is_function", CLOSING, 49)

# domain of identity
clear()
with (x *in_* Domain(Identity(A))) @ 0:
    ((x *in_* Domain(Identity(A))) == Exist(y_, ((y_ *in_* Identity(A)) & Arity2(y_)) & (Left(y_) == x))) @ (1, BY_THEOREM, "domain")
    Exist(y_, ((y_ *in_* Identity(A)) & Arity2(y_)) & (Left(y_) == x)) @ (2, TAUTOLOGY, 0, 1)
    (((y *in_* Identity(A)) & Arity2(y)) & (Left(y) == x)) @ (3, LET, y, 2)
    (y *in_* Identity(A)) @ (4, TAUTOLOGY, 3)
    ((y *in_* Identity(A)) == Exist(a_, (a_ *in_* A) & (y == OrderedPair(a_, a_)))) @ (5, BY_THEOREM, "identity")
    Exist(a_, (a_ *in_* A) & (y == OrderedPair(a_, a_))) @ (6, TAUTOLOGY, 4, 5)
    ((a *in_* A) & (y == OrderedPair(a, a))) @ (7, LET, a, 6)
    (a *in_* A) @ (8, TAUTOLOGY, 7)
    Set(a) @ (9, PUT_THEOREM, "set_condition", A, 8)
    (a == Left(OrderedPair(a, a))) @ (10, BY_THEOREM, "left_of_ordered_pair", 9)
    (y == OrderedPair(a, a)) @ (11, TAUTOLOGY, 7)
    (a == Left(y)) @ (12, REPLACE, 10, 11)
    (Left(y) == x) @ (13, TAUTOLOGY, 3)
    (a == x) @ (14, BY_EQUIVALENCE, 12, 13)
    (x *in_* A) @ (15, REPLACE, 8, 14)
((x *in_* Domain(Identity(A))) >> (x *in_* A)) @ (16, DEDUCE)

with (x *in_* A) @ 17:
    Set(x) @ (18, PUT_THEOREM, "set_condition", A, 17)
    (OrderedPair(x, x) == OrderedPair(x, x)) @ (19, BY_EQUIVALENCE)
    ((x *in_* A) & (OrderedPair(x, x) == OrderedPair(x, x))) @ (20, TAUTOLOGY, 19, 17)
    Exist(a_, (a_ *in_* A) & (OrderedPair(x, x) == OrderedPair(a_, a_))) @ (21, FOUND, x, 20)
    ((OrderedPair(x, x) *in_* Identity(A)) == Exist(a_, (a_ *in_* A) & (OrderedPair(x, x) == OrderedPair(a_, a_)))) @ (22, BY_THEOREM, "identity")
    (OrderedPair(x, x) *in_* Identity(A)) @ (23, TAUTOLOGY, 21, 22)
    (x *in_* Domain(Identity(A))) @ (24, PUT_THEOREM, "domain_condition", x, 23, 18)
((x *in_* A) >> (x *in_* Domain(Identity(A)))) @ (25, DEDUCE)

((x *in_* A) == (x *in_* Domain(Identity(A)))) @ (26, TAUTOLOGY, 16, 25)
All(x_, (x_ *in_* A) == (x_ *in_* Domain(Identity(A)))) @ (27, CLOSING, 26)
(A == Domain(Identity(A))) @ (28, BY_THEOREM, "extensionality", 27)
All(A_, A_ == Domain(Identity(A_))) @ ("domain_of_identity", CLOSING, 28)

# put condition
clear()
with (Set(x) & Set(y)) @ 0:
    with (Function(F) & (OrderedPair(x, y) *in_* F)) @ 1:
        (OrderedPair(x, y) *in_* F) @ (2, TAUTOLOGY, 1)
        (x *in_* Domain(F)) @ (3, PUT_THEOREM, "domain_condition", y, 0, 2)
        (((FindPair(F, x) *in_* F) & Arity2(FindPair(F, x))) & (Left(FindPair(F, x)) == x)) @ (4, BY_THEOREM, "find_pair", 3, 1)
        (x == Left(OrderedPair(x, y))) @ (5, BY_THEOREM, "left_of_ordered_pair", 0)
        (Left(FindPair(F, x)) == x) @ (6, TAUTOLOGY, 4)
        (Left(FindPair(F, x)) == Left(OrderedPair(x, y))) @ (7, BY_EQUIVALENCE, 6, 5)
        (FindPair(F, x) *in_* F) @ (8, TAUTOLOGY, 4)
        (Function(F) == (Relation(F) & All(a_, b_, (((a_ *in_* F) & (b_ *in_* F)) & (Left(a_) == Left(b_))) >> (a_ == b_)))) @ (9, BY_THEOREM, "function")
        All(a_, b_, (((a_ *in_* F) & (b_ *in_* F)) & (Left(a_) == Left(b_))) >> (a_ == b_)) @ (10, TAUTOLOGY, 9, 1)
        (FindPair(F, x) == OrderedPair(x, y)) @ (11, BY_THEOREM, 10, 2, 8, 7)
        (y == Right(OrderedPair(x, y))) @ (12, BY_THEOREM, "right_of_ordered_pair", 0)
        (y == Right(FindPair(F, x))) @ (13, REPLACE, 12, 11)
        (F(x) == Right(FindPair(F, x))) @ (14, BY_THEOREM, "put")
        (y == F(x)) @ (15, REPLACE, 13, 14)
    ((Function(F) & (OrderedPair(x, y) *in_* F)) >> (y == F(x))) @ (16, DEDUCE)
((Set(x) & Set(y)) >> ((Function(F) & (OrderedPair(x, y) *in_* F)) >> (y == F(x)))) @ (17, DEDUCE)
(((Set(x) & Set(y)) & (Function(F) & (OrderedPair(x, y) *in_* F))) >> (y == F(x))) @ (18, TAUTOLOGY, 17)
All(x_, y_, F_, ((Set(x_) & Set(y_)) & (Function(F_) & (OrderedPair(x_, y_) *in_* F_))) >> (y_ == F_(x_))) @ ("put_condition", CLOSING, 18)

# identity output
clear()
with (a *in_* A) @ 0:
    All(x_, (x_ *in_* Identity(A)) == Exist(a_, (a_ *in_* A) & (x_ == OrderedPair(a_, a_)))) @ (1, PUT, A, "identity")
    ((OrderedPair(a, a) *in_* Identity(A)) == Exist(a_, (a_ *in_* A) & (OrderedPair(a, a) == OrderedPair(a_, a_)))) @ (2, PUT, OrderedPair(a, a), 1)
    (OrderedPair(a, a) == OrderedPair(a, a)) @ (3, BY_EQUIVALENCE)
    ((a *in_* A) & (OrderedPair(a, a) == OrderedPair(a, a))) @ (6, TAUTOLOGY, 0, 3)
    Exist(a_, (a_ *in_* A) & (OrderedPair(a, a) == OrderedPair(a_, a_))) @ (4, FOUND, a, 6)
    (OrderedPair(a, a) *in_* Identity(A)) @ (5, TAUTOLOGY, 2, 4)
    Function(Identity(A)) @ (6, BY_THEOREM, "identity_is_function")
    Set(a) @ (7, PUT_THEOREM, "set_condition", A, 0)
    (a == Identity(A)(a)) @ (8, BY_THEOREM, "put_condition", 5, 7, 6)
((a *in_* A) >> (a == Identity(A)(a))) @ (9, DEDUCE)
All(a_, A_, (a_ *in_* A_) >> (a_ == Identity(A_)(a_))) @ ("identity_output", CLOSING, 9)

# image of identity
clear()
with (x *in_* Identity(A)[B]) @ 0: # book
    ((x *in_* Identity(A)[B]) == (Set(x) & Exist(a_, ((a_ *in_* B) & (a_ *in_* Domain(Identity(A)))) & (x == Identity(A)(a_))))) @ (1, BY_THEOREM, "image")
    Exist(a_, ((a_ *in_* B) & (a_ *in_* Domain(Identity(A)))) & (x == Identity(A)(a_))) @ (2, TAUTOLOGY, 0, 1)
    (((a *in_* B) & (a *in_* Domain(Identity(A)))) & (x == Identity(A)(a))) @ (3, LET, a, 2)
    
    (a *in_* B) @ (4, TAUTOLOGY, 3)
    (a *in_* Domain(Identity(A))) @ (5, TAUTOLOGY, 3)
    (x == Identity(A)(a)) @ (6, TAUTOLOGY, 3)

    (A == Domain(Identity(A))) @ (7, BY_THEOREM, "domain_of_identity")
    (a *in_* A) @ (8, REPLACE, 5, 7)
    (a == Identity(A)(a)) @ (9, BY_THEOREM, "identity_output", 8)
    (x == a) @ (10, REPLACE, 6, 9)

    (x *in_* B) @ (11, REPLACE, 4, 10)
    (x *in_* A) @ (12, REPLACE, 8, 10)
    ((x *in_* (A *cap* B)) == ((x *in_* A) & (x *in_* B))) @ (13, BY_THEOREM, "cap")
    (x *in_* (A *cap* B)) @ (14, TAUTOLOGY, 13, 11, 12)
((x *in_* Identity(A)[B]) >> (x *in_* (A *cap* B))) @ (15, DEDUCE)

with (x *in_* (A *cap* B)) @ 16:
    ((x *in_* (A *cap* B)) == ((x *in_* A) & (x *in_* B))) @ (17, BY_THEOREM, "cap")
    (x *in_* A) @ (18, TAUTOLOGY, 16, 17)
    (x *in_* B) @ (19, TAUTOLOGY, 16, 17)
    ((x *in_* Identity(A)[B]) == (Set(x) & Exist(a_, ((a_ *in_* B) & (a_ *in_* Domain(Identity(A)))) & (x == Identity(A)(a_))))) @ (20, BY_THEOREM, "image")
    Set(x) @ (40, PUT_THEOREM, "set_condition", A, 18)
    (A == Domain(Identity(A))) @ (21, BY_THEOREM, "domain_of_identity")
    (x *in_* Domain(Identity(A))) @ (22, REPLACE, 18, 21)

    (x == Identity(A)(x)) @ (23, BY_THEOREM, "identity_output", 18)
    (((x *in_* B) & (x *in_* Domain(Identity(A)))) & (x == Identity(A)(x))) @ (24, TAUTOLOGY, 19, 22, 23)
    Exist(a_, ((a_ *in_* B) & (a_ *in_* Domain(Identity(A)))) & (x == Identity(A)(a_))) @ (25, FOUND, x, 24)
    (Set(x) & Exist(a_, ((a_ *in_* B) & (a_ *in_* Domain(Identity(A)))) & (x == Identity(A)(a_)))) @ (41, TAUTOLOGY, 25, 40)
    (x *in_* Identity(A)[B]) @ (26, TAUTOLOGY, 41, 20)
((x *in_* (A *cap* B)) >> (x *in_* Identity(A)[B])) @ (27, DEDUCE)

((x *in_* Identity(A)[B]) == (x *in_* (A *cap* B))) @ (28, TAUTOLOGY, 27, 15)
All(x_, (x_ *in_* Identity(A)[B]) == (x_ *in_* (A *cap* B))) @ (29, CLOSING, 28)
(Identity(A)[B] == (A *cap* B)) @ (30, BY_THEOREM, "extensionality", 29)
All(A_, B_, Identity(A_)[B_] == (A_ *cap* B_)) @ ("image_of_identity", CLOSING, 30)

# element of subset
clear()
with ((x *in_* A) & (A *inc* B)) @ 0:
    (x *in_* A) @ (1, TAUTOLOGY, 0)
    (A *inc* B) @ (2, TAUTOLOGY, 0)
    ((A *inc* B) == All(x_, (x_ *in_* A) >> (x_ *in_* B))) @ (3, BY_THEOREM, "inclusion")
    All(x_, (x_ *in_* A) >> (x_ *in_* B)) @ (4, TAUTOLOGY, 3, 2)
    ((x *in_* A) >> (x *in_* B)) @ (5, PUT, x, 4)
    (x *in_* B) @ (6, TAUTOLOGY, 5, 1)
(((x *in_* A) & (A *inc* B)) >> (x *in_* B)) @ (7, DEDUCE)
All(A_, B_, x_, ((x_ *in_* A_) & (A_ *inc* B_)) >> (x_ *in_* B_)) @ ("element_of_subset", CLOSING, 7)

# cap subset
clear()
with (A *inc* B) @ 0:
    with (x *in_* (A *cap* B)) @ 1:
        ((x *in_* (A *cap* B)) == ((x *in_* A) & (x *in_* B))) @ (2, BY_THEOREM, "cap")
        (x *in_* A) @ (3, TAUTOLOGY, 1, 2)
    ((x *in_* (A *cap* B)) >> (x *in_* A)) @ (4, DEDUCE)
    with (x *in_* A) @ 5:
        (x *in_* B) @ (6, PUT_THEOREM, "element_of_subset", A, 5, 0)
        ((x *in_* (A *cap* B)) == ((x *in_* A) & (x *in_* B))) @ (7, BY_THEOREM, "cap")
        (x *in_* (A *cap* B)) @ (8, TAUTOLOGY, 5, 6, 7)
    ((x *in_* A) >> (x *in_* (A *cap* B))) @ (8, DEDUCE)
    ((x *in_* (A *cap* B)) == (x *in_* A)) @ (9, TAUTOLOGY, 4, 8)
    All(x_, (x_ *in_* (A *cap* B)) == (x_ *in_* A)) @ (10, CLOSING, 9)
    ((A *cap* B) == A) @ (11, BY_THEOREM, "extensionality", 10)
((A *inc* B) >> ((A *cap* B) == A)) @ (12, DEDUCE)
All(A_, B_, (A_ *inc* B_) >> ((A_ *cap* B_) == A_)) @ ("cap_subset", CLOSING, 12)

# separation
clear()
with ((a *inc* b) & Set(b)) @ 0:
    (a *inc* b) @ (1, TAUTOLOGY, 0)
    Set(b) @ (2, TAUTOLOGY, 0)

    Function(Identity(a)) @ (3, BY_THEOREM, "identity_is_function")
    Set(Identity(a)[b]) @ (4, BY_THEOREM, "replacement", 3, 2)

    (Identity(a)[b] == (a *cap* b)) @ (5, BY_THEOREM, "image_of_identity")
    ((a *cap* b) == a) @ (6, BY_THEOREM, "cap_subset", 1)
    (a == Identity(a)[b]) @ (7, BY_EQUIVALENCE, 5, 6)

    Set(a) @ (8, REPLACE, 4, 7)
(((a *inc* b) & Set(b)) >> Set(a)) @ (9, DEDUCE)
All(a_, b_, ((a_ *inc* b_) & Set(b_)) >> Set(a_)) @ ("separation", CLOSING, 9)

# empty is set
clear()
((Set(a) & (Empty() *in_* a)) & All(x_, (x_ *in_* a) >> (Succ(x_) *in_* a))) @ (0, LET, a, "infinity")
(Empty() *in_* a) @ (1, TAUTOLOGY, 0)
Set(Empty()) @ ("empty_is_set", PUT_THEOREM, "set_condition", a, 1)

# inductive
clear()
Inductive = make_property("inductive")
All(a_, Inductive(a_) == ((Set(a_) & (Empty() *in_* a_)) & All(x_, (x_ *in_* a_) >> (Succ(x_) *in_* a_)))) @ ("inductive", DEFINE_PROPERTY, "inductive")

# inductive exist
clear()
((Set(a) & (Empty() *in_* a)) & All(x_, (x_ *in_* a) >> (Succ(x_) *in_* a))) @ (0, LET, a, "infinity")
Inductive(a) @ (1, BICONDITION, "inductive", 0)
Exist(a_, Inductive(a_)) @ ("inductive_exist", FOUND, a, 1)

# self inclusion
clear()
((x *in_* A) >> (x *in_* A)) @ (0, TAUTOLOGY)
All(x_, (x_ *in_* A) >> (x_ *in_* A)) @ (1, CLOSING, 0)
(A *inc* A) @ (2, BICONDITION, "inclusion", 1)
All(A_, A_ *inc* A_) @  ("self_inclusion", CLOSING, 2)

# nonempty
clear()
with (A != Empty()) @ 0:
    with All(x_, ~ (x_ *in_* A)) @ 1:
        (~ (x *in_* A)) @ (2, PUT, x, 1)
        ((x *in_* Empty()) == false) @ (3, BY_THEOREM, "empty")
        ((x *in_* A) == (x *in_* Empty())) @ (4, TAUTOLOGY, 2, 3)
        All(x_, (x_ *in_* A) == (x_ *in_* Empty())) @ (5, CLOSING, 4)
        (A == Empty()) @ (6, BY_THEOREM, "extensionality", 5)
        false @ (7, TAUTOLOGY, 0, 6)
    (All(x_, ~ (x_ *in_* A)) >> false) @ (8, DEDUCE)
    ((~ Exist(x_, (x_ *in_* A))) == All(x_, ~ (x_ *in_* A))) @ (9, DUAL)
    Exist(x_, (x_ *in_* A)) @ (10, TAUTOLOGY, 8, 9)
((A != Empty()) >> Exist(x_, (x_ *in_* A))) @ (11, DEDUCE)

with Exist(x_, (x_ *in_* A)) @ 12:
    (y *in_* A) @ (13, LET, y, 12)
    ((y *in_* Empty()) == false) @ (14, BY_THEOREM, "empty")
    with (A == Empty()) @ 15:
        (y *in_* Empty()) @ (16, REPLACE, 13, 15)
        false @ (17, TAUTOLOGY, 16, 14)
    ((A == Empty()) >> false) @ (18, DEDUCE)
    (A != Empty()) @ (19, TAUTOLOGY, 18)
(Exist(x_, x_ *in_* A) >> (A != Empty())) @ (20, DEDUCE)

((A != Empty()) == Exist(x_, (x_ *in_* A))) @ (21, TAUTOLOGY, 11, 20)
All(A_, (A_ != Empty()) == Exist(x_, (x_ *in_* A_))) @ ("nonempty", CLOSING, 21)

# nonempty condition
with (x *in_* A) @ 0:
    Exist(x_, x_ *in_* A) @ (1, FOUND, x, 0)
    (A != Empty()) @ (2, BICONDITION, "nonempty", 1)
((x *in_* A) >> (A != Empty())) @ (3, DEDUCE)
All(x_, A_, (x_ *in_* A_) >> (A_ != Empty())) @ (4, CLOSING, 3)

# naturals
clear()
UniquelyExist(C, All(x_, (x_ *in_* C) == (Set(x_) & All(A_, Inductive(A_) >> (x_ *in_* A_))))) @ (0, DEFINE_CLASS, C)
Naturals = make_function("naturals")
All(x_, (x_ *in_* Naturals()) == (Set(x_) & All(A_, Inductive(A_) >> (x_ *in_* A_)))) @ (1, DEFINE_FUNCTION, "naturals", 0)
with All(A_, Inductive(A_) >> (x *in_* A_)) @ 2:
    Inductive(a) @ (3, LET, a, "inductive_exist")
    (Inductive(a) >> (x *in_* a)) @ (4, PUT, a, 2)
    (x *in_* a) @ (5, TAUTOLOGY, 3, 4)
    Set(x) @ (6, PUT_THEOREM, "set_condition", a, 5)
    (Set(x) & All(A_, Inductive(A_) >> (x *in_* A_))) @ (7, TAUTOLOGY, 6, 2)
    (x *in_* Naturals()) @ (8, BICONDITION, 1, 7)
(All(A_, Inductive(A_) >> (x *in_* A_)) >> (x *in_* Naturals())) @ (9, DEDUCE)
with (x *in_* Naturals()) @ 10:
    (Set(x) & All(A_, Inductive(A_) >> (x *in_* A_))) @ (11, BICONDITION, 1, 10)
    All(A_, Inductive(A_) >> (x *in_* A_)) @ (12, TAUTOLOGY, 11)
((x *in_* Naturals()) >> All(A_, Inductive(A_) >> (x *in_* A_))) @ (13, DEDUCE)
((x *in_* Naturals()) == All(A_, Inductive(A_) >> (x *in_* A_))) @ (14, TAUTOLOGY, 13, 9)
All(x_, (x_ *in_* Naturals()) == All(A_, Inductive(A_) >> (x_ *in_* A_))) @ ("naturals", CLOSING, 14)


# empty in naturals
clear()
with Inductive(A) @ 0:
    ((Set(A) & (Empty() *in_* A)) & All(x_, (x_ *in_* A) >> (Succ(x_) *in_* A))) @ (1, BICONDITION, "inductive", 0)
    (Empty() *in_* A) @ (2, TAUTOLOGY, 1)
(Inductive(A) >> (Empty() *in_* A)) @ (3, DEDUCE)
All(A_, Inductive(A_) >> (Empty() *in_* A_)) @ (4, CLOSING, 3)
(Empty() *in_* Naturals()) @ ("empty_in_naturals",  BICONDITION, "naturals", 4)

# successor in naturals
clear()
with (x *in_* Naturals()) @ 0:
    All(A_, Inductive(A_) >> (x *in_* A_)) @ (1, BICONDITION, "naturals", 0)
    with Inductive(A) @ 2:
        (x *in_* A) @ (3, BY_THEOREM, 1, 2)
        ((Set(A) & (Empty() *in_* A)) & All(x_, (x_ *in_* A) >> (Succ(x_) *in_* A))) @ (4, BICONDITION, "inductive", 2)
        All(x_, (x_ *in_* A) >> (Succ(x_) *in_* A)) @ (5, TAUTOLOGY, 4)
        (Succ(x) *in_* A) @ (6, BY_THEOREM, 5, 3)
    (Inductive(A) >> (Succ(x) *in_* A)) @ (7, DEDUCE)
    All(A_, Inductive(A_) >> (Succ(x) *in_* A_)) @ (8, CLOSING, 7)
    (Succ(x) *in_* Naturals()) @ (9, BICONDITION, "naturals", 8)
((x *in_* Naturals()) >> (Succ(x) *in_* Naturals())) @ (10, DEDUCE)
All(x_, (x_ *in_* Naturals()) >> (Succ(x_) *in_* Naturals())) @ ("successor_in_naturals", CLOSING, 10)

# naturals is smallest
clear()
with Inductive(A) @ 0:
    with (x *in_* Naturals()) @ 1:
        All(A_, Inductive(A_) >> (x *in_* A_)) @ (2, BICONDITION, "naturals", 1)
        (x *in_* A) @ (3, BY_THEOREM, 2, 0)
    ((x *in_* Naturals()) >> (x *in_* A)) @ (4, DEDUCE)
    All(x_, (x_ *in_* Naturals()) >> (x_ *in_* A)) @ (5, CLOSING, 4)
    (Naturals() *inc* A) @ (6, BICONDITION, "inclusion", 5)
(Inductive(A) >> (Naturals() *inc* A)) @ (7, DEDUCE)
All(A_, Inductive(A_) >> (Naturals() *inc* A_)) @ ("naturals_is_smallest", CLOSING, 7)

# naturals is set
clear()
Inductive(a) @ (0, LET, a, "inductive_exist")
((Set(a) & (Empty() *in_* a)) & All(x_, (x_ *in_* a) >> (Succ(x_) *in_* a))) @ (1, BICONDITION, "inductive", 0)
Set(a) @ (2, TAUTOLOGY, 1)
(Naturals() *inc* a) @ (3, BY_THEOREM, "naturals_is_smallest", 0)
Set(Naturals()) @ ("naturals_is_set", PUT_THEOREM, "separation", a, 2, 3)

# naturals is inductive
clear()
((Set(Naturals()) & (Empty() *in_* Naturals())) & All(x_, (x_ *in_* Naturals()) >> (Succ(x_) *in_* Naturals()))) @ (0, TAUTOLOGY, "empty_in_naturals", "successor_in_naturals", "naturals_is_set")
Inductive(Naturals()) @ ("naturals_is_inductive", BICONDITION, "inductive", 0)

