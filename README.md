# math_up
a simple proof system I made to learn math without any mistakes
___________________________________________________________________
<br><br>
The following description assumes you already know first-order logical concepts.
<br><br>

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
~P          # not P
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
It requires a fresh variable to use as an existential bound variable as an argument.<br>
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
3-9. 



