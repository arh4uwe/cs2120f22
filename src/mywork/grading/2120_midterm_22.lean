
/-
This is the CS2120 (Sullivan) midterm exam. 

The exam has 100 points total distributed over four
multi-part questions. There's an extra credit question
at the end. Points for each part are indicated.
-/

-- ****************** #1 [30 points] *******************

/- A. [5 points] 

Is it true in predicate logic that  
(false → true) ∧ (false → false)?
Answer:

Yes because false implies anything is true, using the false
elimination rule. Therefore, both the left and the right 
proposition evaluate to true, and the conjunction of true and true is 
true.

-/

/- B. [10 points] 

Give a formal proof by completing the 
following "example" in Lean, or state 
in English that there is no such proof.

-/
example : (false → true) ∧ (true → true) :=
begin
split,
assume false,
apply false.elim,
assume true,
exact true,
end

/- C [15 points]. 

Give an English language proof of the proposition. 
Identify each inference  rule you use at each point
in your argument. For example, at a certain point 
you might say something like this: By the ____ rule, 
it will suffice to show ____. Then you would go on
to show that what remains to be proved is valid. 


Answer:
By the and introduction inference rule, it will suffice to show 
that (false implies true) and (true implies true) is true.
Starting with the left side (false implies true), to use
arrow introduction rule, we have to assume the premise. So, 
assume that we have a proof of false. However, because
that is a contradiction, then by the false elimination rule,
true is true. On the right hand side (true implies true), again, to apply the 
arrow introduction rule, we assume that we have a proof of true. Since
we have already a proof of true, then we have a proof of the conclusion,
and the goal is accomplished. 

-/


-- ****************** #2 [30 points] *******************


/- 
"Resolution" is an inference rule that we 
haven't talked about before. It's valid in
propositional, classical, and constructive
predicate logic. We will present the rule,
in both propositional and predicate logic,
and will ask you to prove that is's valid
in each case.


In propositional logic, the resolution rule 
is ¬P ∨ Q, P ⊢ Q. To check its validity, we 
can write it as  (¬P ∨ Q) ∧ P → Q. Note: ∧ 
has higher precedence than →, so there are 
implicit parentheses around (¬P ∨ Q) ∧ P, 
making the overall proposition an implication.
-/


/- A. [5 points].

Give a brief English language explanation why this
inference rules makes sense: not a rigorous proof,
just an explanation of why Q has to be true under
the conditions give by the assumptions/premises.

Answer: 
(not P or Q) is assumed true and P is assumed true. So, as P is true,
not P is false. Therefore, the disjuctnion simplies to (false or Q). 
In order for disjunction to be true, one side has to be 
true. Therefore, Q must be true. 
-/


/- B. [5 points]

Prove that this inference rule is valid in
propositional logic by giving a truth table for it. 
We'll give you a start. Fill in the rows then state
how you know from the truth table that the overall
proposition is valid.

P   Q   (¬P ∨ Q)    (¬P ∨ Q) ∧ P    ((¬P ∨ Q) ∧ P) → Q
------------------------------------------------------
f   f   t           f               t
f   t   t           f               t
t   f   f           f               t
t   t   t           t               t


Statement:
The overall proposition is valid because in all possible interpretations
of P and Q, it (the right column) evaluates to true. A proposition is 
valid when all interpretations evaluate to true. 
-/  


/- C. [10 points] 

Give a formal proof that the inference rule is 
valid in our constructive predicate logic. Fill
in a proof script here to construct your proof.
Hint: remember that the cases tactic applied to
a proof of a conjunction applied and.elim both
left and right, and when applied to a proof of 
a disjunction gives you two cases to consider,
where you need to show that the remining goal
is true in either case. 
-/

example : ∀ (P Q : Prop), (¬P ∨ Q) ∧ P → Q :=
begin
assume P Q a,
cases a with nPQ p,
cases nPQ with np q,
let false := np p,
apply false.elim,
exact q,
end


/-
D. [10 points] Give an informal (English) proof 
that the inference rule is valid in predicate logic. 
Name each inference rule you use in your reasoning.

Answer:
Assume that P and Q are some arbitrary propositions. Assume that 
((¬P ∨ Q) ∧ P) is true. Applying and elimination right rule to that proposition
will derive a proof of P. Applying and elimination left rule will derive a proof of
(¬P ∨ Q). To apply or elimination to (¬P ∨ Q), we have to use case analysis. In the 
case that not P is true, not P is the same as P implies false, so applying not P to P 
derives a proof of false. Using false elimination, we get a proof of Q. In the case that
Q is true, we have a proof of the conclusion, achieving the goal. 
-/


-- ****************** #3 [20 points] *******************


/- 
A. [10 points]. Write formally (in constructive logic) 
the proposition that, for any propositions P and Q, if 
P is equivalent to Q (iff), then if P is true, then Q
is true.  Hint: put parentheses around your ↔ expression. 
-/

-- Don't try to write a proof here; just the proposition
def if_p_iff_q_then_if_also_p_then_q : Prop :=
∀(P Q : Prop), (P ↔ Q) → P → Q 


/-
B. [10 points] Give *either* a precise, complete English
language proof that this proposition is valid, naming 
each inference you you use in your reasoning, *or* give 
a formal proof of it using Lean. You do not have to give
both. 
-/


/- Option #1: Informal proof:

-/


/-
Option #2: Formal proof. Reminders: the iff elim
rules are called iff.mp and iff.mpr in Lean; or you
can use "cases" to apply the two elimination rules 
to a proof of a bi-implication automatically.
-/

example : if_p_iff_q_then_if_also_p_then_q :=
begin
unfold if_p_iff_q_then_if_also_p_then_q,
assume P Q pq p,
cases pq with pq qp,
exact pq p,
end


-- ****************** #4 [20 points] *******************

/- #

A. [10 points] Suppose P is any proposition. In plain
English give a step by step explanation of how you would 
go about proving ¬P using proof *by negation*. 

Answer:
Proof by negation uses the negation introdcution rule.
We want to prove not P using proof by negation, so assume that we have a proof of P. 
Then, by using inference rules, arrive at a contradiction, concluding that P is false. 
not P is the same as P implies false. So, as P is false, false implies false is
true (false elimination rule). 

-/

/- B. [10 points] 

In plain English explain each step in a proof of P
*by contradiction*. Identify where a proof by negation 
(¬ introduction) occurs in the proof by contradiction. 
Explain what classical rule of inference you need to 
use to finish off such a proof. 

Answer: 
Proof by contradiction uses the negation elimination rule.
We want to prove P using proof by contradiction, so assume that we have a proof of
not P. As mentioned before, not P is also P implies false. Use inference rules
to show that P is true, resulting in a contradiction, so not P is false.
Therefore, not (not P) is true. However, double negation(negation elimiantion) 
does not exist in constructive logic, so we can't use negation elimination to get 
a proof of P. The Law of the Excluded Middle needs to be applyed to get a proof of 
P and not P. In the case that P is true, then we have a proof of the conclusion. 
In the case that P is not true, then not not P can be applied to not P to get a 
proof of false, which is a contradiction, so then P is true by the false elimination 
rule. 
-/



/- Extra Credit [10 points for all three answers correct]

Suppose that "if it's sunny, it's hot, and also that if 
it's not sunny, it's hot. 

A. Is it hot in classical logic? 

Answer: Yes because a proposition is either true or false according
to the Law of the Excluded Middle. So, given that in either case 
(sunny or not sunny), it is hot, then it's hot is always true (valid).


B. Is it hot "constructively?" Briefly explain your answer. 

Answer: No because a proposition can be either true, false, or in between. 
So, just because in the case that sunny is true and in the case that sunny is false,
hot is true, it doesn't mean that it is always true as sunny can be in between. The
Law of Excluded Middle doesn't exist in constructive logic. 


C. Give a formal proof of your answer to the classical question. 
Use S and H as names to stand for the propositions, "it's sunny" 
and "it's hot," where S stands for "it's sunny" and H stands for
"it's hot."
-/

-- it's hot
example : ∀ (S H : Prop), (S → H) → (¬S → H) → H :=
begin
assume S H sh nsh,
cases (classical.em S) with s ns,
let h := sh s,
exact h,

let h := nsh ns,
exact h,
end

