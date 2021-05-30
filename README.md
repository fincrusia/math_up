# math_up
a simple proof system I made to learn math without any mistakes
___________________________________________________________________
<br><br>

## 0. Short Introduction


<br>*test yourself, enjoy your math!*<br>

**math_up** is an <ins>NBG-based, very simple but programmable proof verifier written in Python</ins>.<br>
Some notable features are:
* super-simplicity, short learning time
* programmability
* fully written in Python (including all the proofs!)
* trade-off between runtime efficiency & reductionism
* non-generic implementation (supports only 1st-order logic, NBG set theory)
* supports on Fitch-style proofs, "let" variables and many other intuitive APIs
* rule-based, without any AI-like things

<br>
The following sections assumes you already know basic concepts on logic and set theory.<br>
<br>
Author : Hyunwoo Yang<br>

* Department of Mathematical Sciences, Seoul National University (2013 ~ 2019)
* Modem R&D Group, Samsung Networks (2019 ~ )

<br>

## 1. Sentence Generation
<br>
1-1. Variables

You may use alphabets from a to z, and also from A to Z.<br>
Just calling *clear()* assures all the variables are new:<br>
```
clear() # clear all alphabets
```
<br>

1-2. Atomic Properties
```
YourPropertyName = make_property("its_formal_name") # required at the first time
YourPropertyName(a, b) # usage
```
<br>

1-3. Logical Connections
    
```
~ P         # not P
P & Q       # P and Q
P | Q       # P or Q
P >> Q      # P imply Q
P == Q      # P iff Q
true        # true
false       # false
```
<br>

1-4. Quantifiers

```
All(x, y, P(x, y)) # for all x and y, P(x, y)
Exist(x, y, z, P(x, y, z)) # there exists x, y and z such that P(x, y, z)
UniquelyExist(a, P(a, t)) # a is the only one such that P(a, t) 
```
<br>

1-5. Functions
```
YourFunctionName = make_function("its_formal_name") # required at the first time
YourFunctionName(x, y, z) # usage
```
<br>



## 2. Numbering or Naming Statements
```
(your_sentence) @ 193
(your_sentence) @ "my_theorem"
```
Each number allows reuses, but the string names must be unique.<br>
Hence, please number the sentences during the proof, but name the theorem at the last.<br>
<br>

## 3. Inferences
```
(your_sentence) @ (save_as, INFERENCE_TO_USE, *arguments, *reasons)
```
*save_as* is a number or string you'd like to save *your_sentence* as.<br>
*INFERENCE_TO_USE* depends on the inference you want to use to deduce *your_sentence*.<br>
Some *arguments* are required or not, depending on the *INFERENCE_TO_USE*<br>
*reasons* are the numbers or strings corresponding to the sentences already proved, which are now being used to deduce *your_sentence*.<br>
<br>

3-1. DEDUCE<br>
```
with (your_assumption) @ 27 :
    # your proof ...
    (your_conclusion) @ (39, SOME_INFERENCE, argument0, argument1, reason0, reason1)
(your_assumption >> your_conclusion) @ (40, DEDUCE)
```
**math_up** supports **Fitch-style** proofs.<br>
That means, you may make an assumption *P*, prove *Q* and then deduce *(P implies Q)*.<br>
The inference to use is *DEDUCE*.
*DEDUCE* doesn't require any arguments or reasons, but it must follow right after the end of the previous *with* block. 
<br><br>

3-2. TAUTOLOGY
```
(A >> B) @ (152, INFERENCE0, argument0, reason0, reason1)
A @ (153, INFERENCE1, argument1, argument2, reason2)
B @ (154, TAUTOLOGY, 152, 153)
```
When is statement is a logical conclusion of previously proved sentences, and it can be checked by simply drawing the truth table, use *TAUTOLOGY*.<br>
It doesn't require any arguments.<br>
Put the sentences needed to draw the truth table as reasons.<br>
<br>

3-2. DEFINE_PROPERTY
```
(NewProperty(x, y) == definition) @ ("save_as", DEFINE_PROPERTY, "formal_name_of_the_property")
```
You can freely define new properties with *DEFINE_PROPERTY*.<br>
It does not requires any reasoning, but requires the formal name of the new property as the only argument.<br>
<br>

3-3. DEFINE_FUNCTION
```
All(x, y, some_condition(x, y) >> UniquelyExist(z, P(x, y, z))) @ (70, INFERENCE0)
All(x, y, some_condition(x, y) >> P(x, y, NewFunction(z))) @ ("save_as", DEFINE_FUNCTION, 70)
```
Defining new function requires a sentence with a uniquely-exist quantifier.<br>
Using *DEFINE_FUNCTION*, you can convert *(for all x and y, if P(x, y) there is only one z such that Q(x, y, z))* into *(for all x and y, if P(x, y) then Q(x, y, f(x, y)))*<br>
It requires no arguments, but one uniquely-exist setence as the only reason.<br>
<br><br>
3-4. DUAL
```
(~All(x, P(x)) == Exist(x, ~P(x))) @ (32, DUAL)
((~Exist(y, Q(z, y))) == All(y, ~Q(z, y))) @ (33, DUAL)
```
*not all == exist not*, while *not exist == all not*.<br>
To use these equivalences, use *DUAL*.<br>
It requires no arguments or reasons.<br>
<br>
3-5. FOUND
```
P(f(c)) @ (5, INFERENCE0, argument0)
Exist(x, P(x)) @ (6, FOUND, f(c), 5)
```
If you found a term satisfying the desired property, you can deduce the existence by *FOUND*.<br>
It requires the term you actually found as an argument, and a sentence showing the desired property as the only reason.<br>
<br>
3-6. LET
```
Exist(x, P(x)) @ (6, INFERENCE0, argument0, 5)
P(c) @ (7, LET, c, 6)
```
This one is the inverse of *FOUND*- i.e. it gives a real example from the existence.<br>
It requires a fresh variable(i.e. never been used after the last *clean()*) to use as an existential bound variable as an argument.<br>
Also, of course, an existential statement is required as the only reason.<br>
<br>
3-7. PUT
```
All(x, P(x, z)) @ (13, INFERENCE0, 7, 9)
P(f(u), z) @ (14, PUT, f(u), 13)
```
*PUT* is used to deduce a specific example from the universally quantifiered sentence.<br>
The term you want to put is an argument, and of course, the universally quantifiered sentence is the only reason.<br>
<br>
3-8. REPLACE
```
P(x, a, a)
(a == f(c)) @ (8, INFERENCE0, argument0, 7)
P(x, a, f(c)) @ (9, REPLACE, 8)
```
When the two terms *s* and *t* are shown to be equal to each other, and the sentence *Q* is obtained from a previously proved *P* by interchainging *s* and *t* several times, *REPLACE* deduces *Q* from the two reasoning, i.e. *s == t* and *P*.<br>
No arguments are needed.<br>
<br>
3-9. AXIOM
```
any_sentence @ ("save_as", AXIOM)
```
*AXIOM* requires no inputs, but simply makes a sentence to be proved.<br>
<br>
3-10. BY_UNIQUE
```
UniquelyExist(x, P(x)) @ (0, INFERENCE0)
P(a) @ (1, INFERENCE1, argument0)
P(f(b)) @ (2, INFERENCE2, argument1)
(a == f(b)) @ (3, BY_UNIQUE, 0, 1, 2)
```
*BY_UNIQUE* requires no arguments, but requires three reasons.<br>
The first one is about unique existence, and the last two are specifications.<br>
You can conclude two terms used for specifications respectively are equal to each other.
<br>
3-10. CLAIM_UNIQUE
```
Exist(x, P(x)) @ (6, INFERENCE0, argument0, 5)
P(c) @ (7, LET, c, 6)
P(d) @ (8, LET, d, 6)
# your proof ...
(c == d) @ (13, INFERENCE0, 12)
UniquelyExist(x, P(x)) @ (14, CLAIM_UNIQUE, 13)
```
*CLAIM_UNIQUE* upgrades an existence statement to a unique-existence statement.<br>
Before you use it, you have to apply *LET* two times, and show the result variables are the same.<br>
No arguments are required, but the equality is consumed as the only reason.<br>
<br>
3-11. DEFINE_CLASS
```
UniquelyExist(C, All(x, (x in C) == UniquelyExist(a, UniquelyExist(b, (x == Tuple(a,b)) and Set(a) & Set(b) & P(a, b))))) @ (17, DEFINE_CLASS, C, x, [a, b], P(a, b))
```
This implements the class existence theorem of the NBG set theory.<br>
No reasoning is required, but there are four arguments:<br>
*C* : a fresh variable, to be a newly defined class<br>
*x* : a fresh variable, to indicate the elements of *C*<br>
*[a, b, ...]* : list of the components of *x*<br>
*P(a, b)* : a condition satisfied by the components<br>
<br>

<br>

## 4. Remarks

<br>
4-1. Trade-Off : Runtime Efficiency vs. Reductionism<br><br>

The class existence theorem is actually not an axiom, but is PROVABLE, due to Goedel<br>
However, proving it requires recursively break down all the higher-level definitions to the primitive ones<br>
I'm afraid our computers would not have enough resourse to do such tedious computation...<br>
Similarly, meta-theorems such as deduction theorem, RULE-C, function definition are NOT reduced by this program.<br>

<br>
4-2. Trade-Off : Readability vs. Completeness<br><br>

Actually, we need one more axiom: All(x, P and Q(x)) >> (P and All(x, Q(x)))<br>
But I'll not implement this here... it may not, and should not be needed for readable proofs.<br>
For the similar reasons, the program doesn't allow weird sentences like *All(x, All(x, P(x)))* or *All(x, P(y))*.<br>
Strictly speaking, **math_up** is an incomplete system to restrict the proofs more readable.


<br>
4-3. Acknowledgement<br><br>

Thanks to everyone taught me math & CS.<br>
Mendelson's excellent book, *Introduction to Mathematical Logic* was extremely helpful.<br>
Jech's *Set Theory* was hard to read but great.<br>
<br>

