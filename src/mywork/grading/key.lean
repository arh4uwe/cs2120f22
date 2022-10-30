
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
Answer: Yes

-/

/- B. [10 points] 

Give a formal proof by completing the 
following "example" in Lean, or state 
in English that there is no such proof.

-/

example : (false → true) ∧ (true → true) :=
begin
apply and.intro,
assume h, contradiction,
assume h, exact h,
end


/- C [15 points]. 

Give an English language proof of the proposition. 
Identify each inference  rule you use at each point
in your argument. For example, at a certain point 
you might say something like this: By the ____ rule, 
it will suffice to show ____. Then you would go on
to show that what remains to be proved is valid. 


Answer: To prove the proposition it will suffice (by
and intro) to prove each conjunct separately. For the
first, assume false. By false elimination the goal is
true. For the second, assume true. In this (or any)
context, true is true. QED. (We will accept variations
in wording of course.)

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

Answer: We assume P is true and so is ¬P ∨ Q. The
latter cannot be true because ¬P is true, so Q has
to be true. 

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

Statement: The proposition is valid because it's 
true under all interpretations.
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
assume P Q,
assume h,
cases h with nporq p,
cases nporq with np q,
contradiction,
assumption,
end


/-
D. [10 points] Give an informal (English) proof 
that the inference rule is valid in predicate logic. 
Name each inference rule you use in your reasoning.

Answer: Assume P and Q are arbitrary propositions
and (h) that (¬P ∨ Q) ∧ P. From h we can deduce 
(¬P ∨ Q) and P. By case analysis on (¬P ∨ Q), either
¬P is true or Q is true. In the first case we have
a contradiction with P. In the second case we've
have the assumption that Q is true, which is the 
goal. So in either case the conclusion holds. QED.
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
    ∀ (P Q : Prop), (P ↔ Q) → P → Q


/-
B. [10 points] Give *either* a precise, complete English
language proof that this proposition is valid, naming 
each inference you you use in your reasoning, *or* give 
a formal proof of it using Lean. You do not have to give
both. 
-/


/- Option #1: Informal proof:
Assume P and Q are propositions and P ↔ Q (h). From 
h we can deduce (by left elimination, iff.mp) that 
P → Q, which is our goal.
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
assume P Q h,
exact iff.mp h,
end




-- ****************** #4 [20 points] *******************

/- #



A. [10 points] Suppose P is any proposition. In plain
English give a step by step explanation of how you would 
go about proving ¬P using proof *by negation*. 

Answer: To show ¬P, assume P and show a contradiction.
Conclude that P must be false, i.e., ¬P.


-/


/- B. [10 points] 

In plain English explain each step in a proof of P
*by contradiction*. Identify where a proof by negation 
(¬ introduction) occurs in the proof by contradiction. 
Explain what classical rule of inference you need to 
use to finish off such a proof. 

Answer: (1) To prove P, assume ¬P and show that this
leads to a contradiction. (2) Conclude ¬(¬P). The use
(classical) negation elimination to conclude P. 
-/



/- Extra Credit [10 points for all three answers correct]

Suppose that "if it's sunny, it's hot, and also that if 
it's not sunny, it's hot. 


A. Is it hot in classical logic? 

Answer: Yes, because it's sunny or it's not sunny is true
by the axiom of the excluded middle. And in either case we
have said it's hot. Those are the only cases to consider.
So it's hot. 


B. Is it hot "constructively?" Briefly explain your answer.
    
Answer: It might be but we can't prove it because we don't
know if it's hot, not hot, or indeterminate.


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
exact sh s,
exact nsh ns,
end

