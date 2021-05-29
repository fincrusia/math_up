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
    assumptions = []
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
            assert not self.bound.counter not in self.bounded
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
            self.bounded = self.bounded.bounded | self.conclusion.bounded
        elif type_ in [TYPE_TRUE, TYPE_FALSE]:
            pass
        else:
            assert False

        self.type_ = type_
        self.branch = None
        self.operator = None

        hashing = [self.type_]
        for key, value in self.arguments.items():
            hashing.append(key)
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
        Node.last = self
        return True

    def is_closed(self):
        assert self.is_sentence()
        return not self.free

    # when you just assume an axiom:
    # your_axiom.accept()
    # at the ground level(i.e. no Fitch-style assumptions),
    # the axiom must be closed
    def accept(self):
        assert self.is_sentence()
        if Node.level == 0:
            assert self.is_closed()
        self.branch = Node.branch.copy()
        for variable in self.free | self.bounded:
            if variable in Node.fresh:
                Node.fresh.remove(variable)
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
        else:
            Node.branch[Node.level] += 1
            Node.bounded[Node.level] = set()
            Node.assumptions[Node.level] = self
        Node.bounded[Node.level] |= self.free
        return self.accept()

    def __exit__(self, exc_type, exc_val, exc_tb):
        Node.last = Node(TYPE_IMPLY, assumption = Node.assumptions[Node.level], conclusion = Node.last).accept()
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
                arguments[key] = value.substitute(value, old, new)
            return Node(self.type_, **arguments)

    # define function
    # All(x, P(x, f(x))).functionize("your_function_name", All(x, UniquelyExist(y, P(x, y))))
    def functionize(self, name, reason):
        reason = Node.history[reason]
        assert reason.is_proved()
        arguments = []
        cursor = reason
        while cursor.type_ == TYPE_ALL:
            arguments.append(cursor.bound)
            cursor = cursor.statement
        assert cursor.type_ == TYPE_UNIQUELY_EXIST
        assert hash(self) == hash(cursor.statement.substitute(cursor.bound, Node(TYPE_FUNCTION, name = name, children = arguments)))
        return self.accept()

    # prove Exist(x, P(x)) from t & P(t)
    def found(self, term, reason):
        reason = Node.history[reason]
        assert reason.is_proved()
        assert not term.is_sentence()
        assert self.type_ == TYPE_EXIST
        assert hash(Node(TYPE_EXIST, bound = self.bound, statement = self.statement.substitute(self.bound, term))) == hash(reason)
        return self.accept()

    # prove P(c) from c & Exist(x, P(x))
    # c must be FRESH, i.e. must NOT be used in the proof so far
    def let(self, variable, reason):
        reason = Node.history[reason]
        assert reason.is_proved()
        assert reason.type_ in [TYPE_EXIST, TYPE_UNIQUELY_EXIST]
        assert variable.is_fresh()
        variable.defined_by = self
        Node.bounded[Node.level].add(variable.counter)
        assert hash(self) == hash(reason.statement.substitute(reason.bound, variable))
        return self.accept()
    
    # Exist(x, P(x)).save(key)
    # P(a).let(a, key)
    # P(b).let(b, key)
    # # ... some proofs
    # (a == b).save(number)
    # UniquelyExist(x, P(x)).unique(number)
    def unique(self, reason):
        reason = Node.history[reason]
        assert reason.is_proved()
        assert reason.type_ == TYPE_PROPERTY
        assert reason.name == "equal"
        assert hash(self.children[0].defined_by) == hash(self.children[1].defined_by)
        defined_by = self.children[0].defined_by
        assert self.type_ == TYPE_UNIQUELY_EXIST
        assert hash(Node(TYPE_EXIST, self.arguments)) == hash(defined_by)
        return self.accept()

    # prove (a == b) from UniquelyExist(x, P(x)), P(a) & P(b)
    def same(self, reason, left, right):
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
    
    # prove P(a) from All(x, P(x))
    def put(self, reason, replace_by):
        reason = Node.history[reason]
        assert reason.is_proved()
        assert reason.type_ == TYPE_ALL
        assert not replace_by.is_sentence()
        assert hash(self) == hash(reason.statement.substitute(reason.bound, replace_by))
        return self.accept()

    # generalization
    # NOT applicable to BOUNDED variables,
    # which is a let-variable or a free variable of any assumption.
    def generalize(self, reason, bound):
        reason = Node.history[reason]
        assert reason.is_proved
        assert bound.is_generalizable()
        assert hash(self) == hash(Node(TYPE_ALL, bound= bound, statement = self))
        return self.accept()

    def logical_form(self, mapping):
        if self.type_ in [TYPE_NOT, TYPE_AND, TYPE_OR, TYPE_IMPLY, TYPE_IFF, TYPE_TRUE, TYPE_FALSE]:
            arguments = {}
            for key, value in self.arguments.items():
                arguments[key] = value.logical_form(mapping)
            return Node(self.type_, arguments)
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
            return self.left.logical_evluate(truth_assign) and self.right.logical_evaluate(truth_assign)
        elif self.type_ == TYPE_OR:
            return self.left.logical_evluate(truth_assign) or self.right.logical_evaluate(truth_assign)
        elif self.type_ == TYPE_IMPLY:
            return self.conclusion.logical_evluate(truth_assign) or not self.assumption.logical_evaluate(truth_assign)
        elif self.type_ == TYPE_IFF:
            return self.left.logical_evluate(truth_assign) == self.right.logical_evaluate(truth_assign)
        elif self.type_ == TYPE_TRUE:
            return True
        elif self.type_ == TYPE_FALSE:
            return False
        else:
            assert False

    # this namely deduces a tautological result from the given reasons
    def tautology(self, *reasons):
        mapping = {}
        for index, reason in enumerate(reasons):
            reason = Node.history[reason]
            assert reason.is_proved()
            reasons[index] = reason.logical_form(mapping)
        target = self.logical_form(mapping)
        case_number = 2 ** len(mapping)
        truth_assign = []
        for case_index in range(0, case_number):
            for assign_index in range(0, len(mapping)):
                truth_assign.append(bool(case_index & (1 << assign_index)))
            consider = True
            for reason in reasons:
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
                if counterpart.argumnets.get(key) == None:
                    return False
            for key in counterpart.arguments.keys():
                if self.argumnets.get(key) == None:
                    return False
            for key, value in self.arguments.items():
                if not value.interchangable(counterpart.arguments[key], A, B):
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
    def define(self, output, element, inputs, statement):
        assert statement.is_sentence()
        for input in inputs:
            assert input.type_ == TYPE_VARIABLE
            assert input in statement.free
        assert output.type_ == TYPE_VARIABLE
        assert output.is_fresh()

        for input in reversed(inputs):
            statement = Node(TYPE_AND, left = Node(TYPE_PROPERTY, name = "set", children = [input]), right = statement)
        statement = Node(TYPE_AND, Node(TYPE_PROPERTY, name = "equal", children = [element, Tuple(inputs)]), statement)
        for input in reversed(inputs):
            statement = Node(TYPE_UNIQUELY_EXIST, bound = input, statement = statement)
        statement = Node(TYPE_IFF, left = Node(TYPE_PROPERTY, name = "in", children = [element, output]), right = statement)
        statement = Node(TYPE_UNIQUELY_EXIST, bound = output, statement = Node(TYPE_ALL, bound = element, statement = statement))
        assert hash(self) == hash(statement)
        return self.accept()

    def remove_exist(self):
        if self.type_ == TYPE_EXIST:
            return Node(TYPE_NOT, body = Node(TYPE_ALL, bound = self.bound, statement = Node(TYPE_NOT, body = self.statement.remove_exist())))
        else:
            return self

    # duality
    # not all == exist not
    # not exist == not all
    def dual(self, reason):
        reason = Node.history[reason]
        assert reason.is_proved()
        assert hash(self.remove_exist(), reason.remove_exist())
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
        return Node(TYPE_FUNCTION, name = "tuple", children = [arguments[0], arguments[1]])
    else:
        return Node(TYPE_FUNCTION, name = "tuple", children = [arguments[0], Tuple(*arguments[1 : ])])




# PROOF START!