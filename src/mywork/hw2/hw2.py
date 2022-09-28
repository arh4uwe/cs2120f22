# Be sure you've done pip install z3-solver
from telnetlib import X3PAD
from z3 import *


# Here's a file you can often copy as a starting 
# point on a working program to solve some problem
# of interest. Here the problem is to compute and
# return a non-negative square root of argument, n 
def hw2():
    
    
    # Create z3 variable(s) representing the unknown
    # Here, the unknown, x, is the square root of n.
    X, Y, Z = Bools('X Y Z')
    
    s = Solver()
    
    # 1. X ∨ Y, X ⊢ ¬Y 
    # As proposition in PL: ((X \/ Y) /\ X) -> ~Y
    C1 = Implies(And(Or(X,Y),X),Not(Y))
    
    s.add(Not(C1))
    # I believe it's not valid
  
    r = s.check()
    
    # If there's a model/solution return it 
    if (r == unsat):
        print("C1 is valid")
    # otherwise return inconsistent value for error
    else :
        print("Here's a counter-example to C1: ", s.model() )
        # If X is true and Y is true, then X or Y is true and X is true.
        # However, since Y is true, not Y is false.
    
    # 2. X, Y ⊢ X ∧ Y 
    C2 = Implies(And(X,Y), And(X,Y))
    # If X is true and Y is true, then X and Y are true.
    s.reset()
    s.add(Not(C2))
    # I believe that the rule is valid.
    if (s.check() == unsat):
        print("C2 is valid")
    else:
        print("Here's a counter-example to C2: ", s.model())

    # 3. X ∧ Y ⊢ X
    C3 = Implies(And(X,Y), X)
    # If X and Y are true, then X is true.
    s.reset()
    s.add(Not(C3))
    # I believe that the rule is valid.
    if (s.check() == unsat):
        print("C3 is valid")
    else:
        print("Here's a counter-example to C3: ", s.model())
    
    # 4. X ∧ Y ⊢ Y
    C4 = Implies(And(X,Y), Y)
    # If X and Y are true, then X is true.
    s.reset()
    s.add(Not(C4))
    # I believe that the rule is valid.
    if (s.check() == unsat):
        print("C4 is valid")
    else:
        print("Here's a counter-example to C4: ", s.model())
    
    # 5. ¬¬X ⊢ X
    C5 = Implies(Not(Not(X)), X)
    # If it's false that X is false, then X is true.
    s.reset()
    s.add(Not(C5))
    # I believe that the rule is valid.
    if (s.check() == unsat):
        print("C5 is valid")
    else:
        print("Here's a counter-example to C5: ", s.model())
    
    # 6. ¬(X ∧ ¬X)
    C6 = Not(And(X, Not(X)))
    # X and not X cannot be true.
    s.reset()
    s.add(Not(C6))
    # I believe that the rule is valid.
    if (s.check() == unsat):
        print("C6 is valid")
    else:
        print("Here's a counter-example to C6: ", s.model())
    
    # 7. X ⊢ X ∨ Y
    C7 = Implies(X, Or(X, Y))
    # If X is true, then X or Y is true.
    s.reset()
    s.add(Not(C7))
    # I believe that the rule is valid.
    if (s.check() == unsat):
        print("C7 is valid")
    else:
        print("Here's a counter-example to C7: ", s.model())

    # 8. Y ⊢ X ∨ Y 
    C8 = Implies(Y, Or(X, Y))
    # If Y is true, then X or Y is true.
    s.reset()
    s.add(Not(C8))
    # I believe that the rule is valid.
    if (s.check() == unsat):
        print("C8 is valid")
    else:
        print("Here's a counter-example to C8: ", s.model())
    
    # 9. X → Y, ¬X ⊢ ¬ Y
    C9 = Implies(And(Implies(X, Y), Not(X)), Not(Y))
    # If X implies Y and X is false, then Y is false.
    s.reset()
    s.add(Not(C9))
    # I don't believe that the rule is valid.
    if (s.check() == unsat):
        print("C9 is valid")
    else:
        print("Here's a counter-example to C9: ", s.model())
        # If X is false and Y is true, then not X is true and it's 
        # vacuously true that X implies Y. However, since Y is true, 
        # not Y is false.
    
    # 10. X → Y, Y → X ⊢ X ↔ Y
    C10 = Implies(And(Implies(X, Y), Implies(Y, X)), X == Y)
    # If X implies Y and Y implies X, then X is true if and only if Y is true.
    s.reset()
    s.add(Not(C10))
    # I believe that the rule is valid.
    if (s.check() == unsat):
        print("C10 is valid")
    else:
        print("Here's a counter-example to C10: ", s.model())
    
    # 11. X ↔ Y ⊢ X → Y
    C11 = Implies(X == Y, Implies(X, Y))
    # If X is true if and only if Y is true, then X implies Y.
    s.reset()
    s.add(Not(C11))
    # I believe that the rule is valid.
    if (s.check() == unsat):
        print("C11 is valid")
    else:
        print("Here's a counter-example to C11: ", s.model())
    
    # 12. X ↔ Y ⊢ Y → X
    C12 = Implies(X == Y, Implies(Y, X))
    # If X is true if and only if Y is true, then Y implies X.
    s.reset()
    s.add(Not(C12))
    # I believe that the rule is valid.
    if (s.check() == unsat):
        print("C12 is valid")
    else:
        print("Here's a counter-example to C12: ", s.model())
    
    # 13. X ∨ Y, X → Z, Y → Z ⊢ Z
    C13 = Implies(And(Or(X, Y), Implies(X, Z), Implies(Y, Z)), Z)
    # If X or Y is true, X implies Z, and Y implies Z, then Z is true.
    s.reset()
    s.add(Not(C13))
    # I believe that the rule is valid.
    if (s.check() == unsat):
        print("C13 is valid")
    else:
        print("Here's a counter-example to C13: ", s.model())
    
    # 14. X → Y, Y ⊢ X
    C14 = Implies(And(Implies(X, Y), Y), X)
    # If X implies Y and Y is true, then X is true.
    s.reset()
    s.add(Not(C14))
    # I don't believe that the rule is valid.
    if (s.check() == unsat):
        print("C14 is valid")
    else:
        print("Here's a counter-example to C14: ", s.model())
        # If X is false and Y is true, then not only is Y true, but it's 
        # vacuously true that X implies Y. However, X is not true.
    
    # 15. X → Y, X ⊢ Y
    C15 = Implies(And(Implies(X, Y), X), Y)
    # If X implies Y and X is true, then Y is true.
    s.reset()
    s.add(Not(C15))
    # I believe that the rule is valid.
    if (s.check() == unsat):
        print("C15 is valid")
    else:
        print("Here's a counter-example to C15: ", s.model())
    
    # 16. X → Y, Y → Z ⊢ X → Z
    C16 = Implies(And(Implies(X, Y), Implies(Y, Z)), Implies(X, Z))
    # If X implies Y and Y implies Z, then X implies Z.
    s.reset()
    s.add(Not(C16))
    # I believe that the rule is valid.
    if (s.check() == unsat):
        print("C16 is valid")
    else:
        print("Here's a counter-example to C16: ", s.model())
    
    # 17. X → Y ⊢ Y → X
    C17 = Implies(Implies(X, Y), Implies(Y, X))
    # If X implies Y, then Y implies X.
    s.reset()
    s.add(Not(C17))
    # I don't believe that the rule is valid.
    if (s.check() == unsat):
        print("C17 is valid")
    else:
        print("Here's a counter-example to C17: ", s.model())
        # If X is false and Y is true, then it's vacuously true that X 
        # implies Y. However, since Y is true and X is false, Y does not 
        # imply X.
    
    # 18. X → Y ⊢ ¬Y → ¬X
    C18 = Implies(Implies(X, Y), Implies(Not(Y), Not(X)))
    # If X implies Y, then not Y implies not X.
    s.reset()
    s.add(Not(C18))
    # I believe that the rule is valid.
    if (s.check() == unsat):
        print("C18 is valid")
    else:
        print("Here's a counter-example to C18: ", s.model())
    
    # 19. ¬(X ∨ Y) ↔ ¬X ∧ ¬Y
    C19 = Not(Or(X, Y)) == And(Not(X), Not(Y))
    # It's false that X or Y is true if and only if X is false and Y is false.
    s.reset()
    s.add(Not(C19))
    # I believe that the rule is valid.
    if (s.check() == unsat):
        print("C19 is valid")
    else:
        print("Here's a counter-example to C19: ", s.model())
    
    # 20. ¬(X ∧ Y) ↔ ¬X ∨ ¬Y
    C20 = Not(And(X, Y)) == Or(Not(X), Not(Y))
    # It's false that X and Y are true if and only if X is false or Y is false.
    s.reset()
    s.add(Not(C20))
    # I believe that the rule is valid.
    if (s.check() == unsat):
        print("C20 is valid")
    else:
        print("Here's a counter-example to C20: ", s.model())

hw2()