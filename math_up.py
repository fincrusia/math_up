# author : Hyunwoo Yang <hyunsdo.yang@samsung.com>
# project name : math_up
# description : a simple proof system I made to learn math without any mistakes
#
# some features are:
# 1. everything is wrote in Python, and you might freely add any code you want
# 2. it is super-simply implemented- it took only one day
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

class Node:
    counter = 0
    branch = [0]
    bounded = [set()]
    names = [set()]
    assumptions = [None]
    level = 0
    history = {}
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
            self.free = self.statement.free.copy()
            self.bounded = self.statement.bounded.copy()
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
        for key, value in self.arguments.items():
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
            assert Node.history.get(save_as) == None
        else:
            assert isinstance(save_as, int)
        Node.history[save_as] = self
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

        reason = Node.history[reason]
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
        reason = Node.history[reason]
        assert reason.is_proved()
        assert not term.is_sentence()
        assert self.type_ == TYPE_EXIST
        assert hash(self.statement.substitute(self.bound, term)) == hash(reason)
        return self.accept()

    # prove P(c) from c & Exist(x, P(x))
    # c must be FRESH, i.e. must NOT be used in the proof so far
    def let(self, variable, reason):
        reason = Node.history[reason]
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
        reason = Node.history[reason]
        assert reason.is_proved()
        assert reason.type_ == TYPE_PROPERTY
        assert reason.name == "equal"
        assert hash(reason.children[0].defined_by) == hash(reason.children[1].defined_by)
        assert self.type_ == TYPE_UNIQUELY_EXIST
        assert hash(Node(TYPE_EXIST, **self.arguments)) == hash(reason.children[0].defined_by)
        return self.accept()

    # prove (a == b) from UniquelyExist(x, P(x)), P(a) & P(b)
    def by_unique(self, reason, left, right):
        reason = Node.history[reason]
        left = Node.history[left]
        right = Node.history[right]
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
        reason = Node.history[reason]
        assert reason.is_proved()
        assert reason.type_ == TYPE_ALL
        assert not replace_by.is_sentence()
        assert hash(self) == hash(reason.statement.substitute(reason.bound, replace_by))
        return self.accept()

    # generalization
    # NOT applicable to BOUNDED variables,
    # which is a let-variable or a free variable of any assumption.
    def generalize(self, reason):
        reason = Node.history[reason]
        assert reason.is_proved()
        assert self.bound.is_generalizable()
        assert hash(self) == hash(Node(TYPE_ALL, bound = self.bound, statement = reason))
        return self.accept()

    def logical_form(self, mapping):
        if self.type_ in [TYPE_NOT, TYPE_AND, TYPE_OR, TYPE_IMPLY, TYPE_IFF, TYPE_TRUE, TYPE_FALSE]:
            arguments = {}
            for key, value in self.arguments.items():
                arguments[key] = value.logical_form(mapping)
            return Node(self.type_, **arguments)
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
            reason = Node.history[reason]
            assert reason.is_proved()
            logical_forms.append(reason.logical_form(mapping))
        target = self.logical_form(mapping)
        case_number = 2 ** len(mapping)
        truth_assign = []
        for case_index in range(0, case_number):
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

    # reason : A == B
    # target : either (P >> Q), or (P == Q),
    # where P & Q are sentences, only differ by interchanging A & B
    def replace(self, reason):
        reason = Node.history[reason]
        assert reason.is_proved()
        assert reason.type_ == TYPE_PROPERTY
        assert reason.name == "equal"
        if self.type_ == TYPE_IMPLY:
            assert self.assumption.interchangable(self.conclustion, reason.children[0], reason.children[1])
        elif self.type_ == TYPE_IFF:
            assert self.left.interchangable(self.right, reason.children[0], reason.children[1])
        else:
            assert False
        return self.accept()

    # class existence theorem
    # this is actually not an axiom, but is PROVABLE, due to Goedel
    # however, proving it requires recursively break down all the higher-level definitions to the primitive ones
    # I'm afraid our computers would not have enough resourse to do such tedious computation...

    # usage example for arity == 2
    # output : FRESH variable C
    # element : FRESH varaible x
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
    # similar for (A *op+ B), (A >op@ B), whatever ...
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

    def __matmul__(self, B):
        return self.overload(B)

    def __eq__(self, B):
        if self.is_sentence():
            return Node(TYPE_IFF, left = self, right = B)
        return Node(TYPE_PROPERTY, name = "equal", children = [self, B]) # reserved!
    


true = Node(TYPE_TRUE)
false = Node(TYPE_FALSE)

def New():
    return Node(TYPE_VARIABLE)

def All(bound, statement):
    return Node(TYPE_ALL, bound = bound, statement = statement)

def Exist(bound, statement):
    return Node(TYPE_EXIST, bound = bound, statement = statement)

def UniquelyExist(bound, statement):
    return Node(TYPE_UNIQUELY_EXIST, bound = bound, statement = statement)

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



a = New()
b = New()
p = New()
x = New()
y = New()
A = New()
B = New()
C = New()

# PROOF START!

# membership
def in_(x, A):
    return Node(TYPE_PROPERTY, name = "membership", children = [x, A])

# definition of set
def Set(a):
    return Node(TYPE_PROPERTY, name = "set", children = [a])
(All(x, Set(x) == Exist(C, x @in_@ C))).define_property("set").save("set")

# extensionality
All(A, All(B, (All(x, (x @in_@ A) == (x @in_@ B)) == (A == B)))).accept().save("extensionality")

# pairing
def Pair(a, b):
    return Node(TYPE_FUNCTION, name = "pair", children = [a, b])
All(a, All(b, (Set(a) & Set(b)) >> UniquelyExist(p, Set(p) & All(x, (x @in_@ p) == ((x == a) | (x == b)))))).accept().save("pairing")
All(a, All(b, (Set(a) & Set(b)) >> (Set(Pair(a, b)) & All(x, (x @in_@ Pair(a, b)) == ((x == a) | (x == b)))))).define_function("pair", "pairing").save("pair")

# pair is a set
a0 = New()
b0 = New()
with Set(a0).save(0):
    with Set(b0).save(1):
        All(b, (Set(a0) & Set(b)) >> (Set(Pair(a0, b)) & All(x, (x @in_@ Pair(a0, b)) == ((x == a0) | (x == b))))).put(a0, "pair").save(2)
        ((Set(a0) & Set(b0)) >> (Set(Pair(a0, b0)) & All(x, (x @in_@ Pair(a0, b0)) == ((x == a0) | (x == b0))))).put(b0, 2).save(3)
        Set(Pair(a0, b0)).tautology(0, 1, 3).save(4)
    (Set(b0) >> Set(Pair(a0, b0))).deduce().save(5)
(Set(a0) >> (Set(b0) >> Set(Pair(a0, b0)))).deduce().save(6)
((Set(a0) & Set(b0)) >> Set(Pair(a0, b0))).tautology(6).save(7)
All(b0, (Set(a0) & Set(b0)) >> Set(Pair(a0, b0))).generalize(7).save(8)
All(a0, All(b0, (Set(a0) & Set(b0)) >> Set(Pair(a0, b0)))).generalize(8).save(9)
All(b0, (Set(a) & Set(b0)) >> Set(Pair(a, b0))).put(a, 9).save(10)
((Set(a) & Set(b)) >> Set(Pair(a, b))).put(b, 10).save(11)
All(b, (Set(a) & Set(b)) >> Set(Pair(a, b))).generalize(11).save(12)
All(a, All(b, (Set(a) & Set(b)) >> Set(Pair(a, b)))).generalize(12).save("pair_is_set")


# reflection of equality
All(A, A == A).accept().save("equality_reflection")

# symmetry of equality
with (A == B).save(0):
    ((A == B) == (B == A)).replace(0).save(1)
    (B == A).tautology(0, 1)
((A == B) >> (B == A)).deduce().save(2)
All(B, (A == B) >> (B == A)).generalize(2).save(3)
All(A, All(B, (A == B) >> (B == A))).generalize(3).save("equality_symmetry")

# transitivity of equality
with (A == B).save(0):
    with (C == B).save(1):
        ((A == B) == (A == C)).replace(1).save(2)
        ((A == C)).tautology(0, 1)
    ((C == B) >> (A == C)).deduce().save(3)
((A == B) >> ((C == B) >> (A == C))).deduce().save(4)
(((A == B) & (C == B)) >> (A == C)).tautology(4).save(5)
All(C, (((A == B) & (C == B)) >> (A == C))).generalize(5).save(6)
All(A, All(C, ((A == B) & (C == B)) >> (A == C))).generalize(6).save(7)
All(B, All(A, All(C, ((A == B) & (C == B)) >> (A == C)))).generalize(7).save("transitivity_equality")

# unique_up_to_equality
A0 = New()
(A0 == A0).put(A0, "equality_reflection").save(0)
Exist(B, B == A0).found(A0, 0).save(1)
B0 = New()
B1 = New()
(B0 == A0).let(B0, 1).save(2)
(B1 == A0).let(B1, 1).save(3)
All(A, All(C, ((A == A0) & (C == A0)) >> (A == C))).put(A0, "transitivity_equality").save(4)
All(C, ((B0 == A0) & (C == A0)) >> (B0 == C)).put(B0, 4).save(5)
(((B0 == A0) & (B1 == A0)) >> (B0 == B1)).put(B1, 5).save(6)
(B0 == B1).tautology(2, 3, 6).save(7)
UniquelyExist(B, B == A0).claim_unique(7).save(8)
All(A0, UniquelyExist(B, B == A0)).generalize(8).save(9)
UniquelyExist(B, B == A).put(A, 9).save(10)
All(A, UniquelyExist(B, B == A)).generalize(10).save("unqiue_up_to_equality")

# ordered_pair
def OrderedPair(a, b):
    return Node(TYPE_FUNCTION, name = "ordered_pair", children = [a, b])
a0 = New()
b0 = New()
UniquelyExist(B, B == Pair(Pair(a0, a0), Pair(a0, b0))).put(Pair(Pair(a0, a0), Pair(a0, b0)), "unqiue_up_to_equality").save(0)
All(b0, UniquelyExist(B, B == Pair(Pair(a0, a0), Pair(a0, b0)))).generalize(0).save(1)
All(a0, All(b0, UniquelyExist(B, B == Pair(Pair(a0, a0), Pair(a0, b0))))).generalize(1).save(2)
All(a0, All(b0, (OrderedPair(a0, b0) == Pair(Pair(a0, a0), Pair(a0, b0))))).define_function("ordered_pair", 2).save(3)
All(b0, (OrderedPair(a, b0) == Pair(Pair(a, a), Pair(a, b0)))).put(a, 3).save(4)
(OrderedPair(a, b) == Pair(Pair(a, a), Pair(a, b))).put(b, 4).save(5)
All(b, (OrderedPair(a, b) == Pair(Pair(a, a), Pair(a, b)))).generalize(5).save(6)
All(a, All(b, (OrderedPair(a, b) == Pair(Pair(a, a), Pair(a, b))))).generalize(6).save("ordered_pair")

# ordered_pair_is_set
a0 = New()
b0 = New()
with Set(a0).save(0):
    with Set(b0).save(1):
        All(b, (Set(a0) & Set(b)) >> Set(Pair(a0, b))).put(a0, "pair_is_set").save(2)
        ((Set(a0) & Set(b0)) >> Set(Pair(a0, b0))).put(b0, 2).save(3)
        Set(Pair(a0, b0)).tautology(0, 1, 3).save(4)
        (((Set(a0) & Set(a0)) >> Set(Pair(a0, a0)))).put(a0, 2).save(5)
        Set(Pair(a0, a0)).tautology(0, 1, 5).save(6)
        All(b, (Set(Pair(a0, a0)) & Set(b)) >> Set(Pair(Pair(a0, a0), b))).put(Pair(a0, a0), "pair_is_set").save(7)
        ((Set(Pair(a0, a0)) & Set(Pair(a0, b0))) >> Set(Pair(Pair(a0, a0), Pair(a0, b0)))).put(Pair(a0, b0), 7).save(8)
        Set(Pair(Pair(a0, a0), Pair(a0, b0))).tautology(4, 6, 8).save(9)
        All(b, (OrderedPair(a0, b) == Pair(Pair(a0, a0), Pair(a0, b)))).put(a0, "ordered_pair").save(10)
        (OrderedPair(a0, b0) == Pair(Pair(a0, a0), Pair(a0, b0))).put(b0, 10).save(11)
        (Set(OrderedPair(a0, b0)) == Set(Pair(Pair(a0, a0), Pair(a0, b0)))).replace(11).save(12)
        Set(OrderedPair(a0, b0)).tautology(9, 12).save(13)
    (Set(b0) >> Set(OrderedPair(a0, b0))).deduce().save(14)
(Set(a0) >> (Set(b0) >> Set(OrderedPair(a0, b0)))).deduce().save(15)
((Set(a0) & Set(b0)) >> Set(OrderedPair(a0, b0))).tautology(15).save(16)
All(b0, ((Set(a0) & Set(b0)) >> Set(OrderedPair(a0, b0)))).generalize(16).save(17)
All(a0, All(b0, ((Set(a0) & Set(b0)) >> Set(OrderedPair(a0, b0))))).generalize(17).save(18)
All(b0, ((Set(a) & Set(b0)) >> Set(OrderedPair(a, b0)))).put(a, 18).save(19)
((Set(a) & Set(b)) >> Set(OrderedPair(a, b))).put(b, 19).save(20)
All(b, (Set(a) & Set(b)) >> Set(OrderedPair(a, b))).generalize(20).save(21)
All(a, All(b, (Set(a) & Set(b)) >> Set(OrderedPair(a, b)))).generalize(21).save("ordered_pair_is_set")
        