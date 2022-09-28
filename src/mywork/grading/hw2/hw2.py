from z3 import *

x, y, z = Bools('x y z')

C1 = Implies(Or(x, y), Implies(x, Not(y))) # 1. X ∨ Y, X ⊢ ¬Y             -- affirming the disjunct
# if x or y, then x being true means y isn't, not valid
# if both x and y are true, then their OR is true and x is true, but y is not false

C2 = Implies(x, Implies(y, And(x, y))) # 2. X, Y ⊢ X ∧ Y              -- and introduction
# given x is true and y is true, x AND y is true, valid

C3 = Implies(And(x, y), x) # 3. X ∧ Y ⊢ X                 -- and elimination left
# given x AND y, x is true, valid

C4 = Implies(And(x, y), x) # 4. X ∧ Y ⊢ Y                 -- and elimination right
# given x AND y, y is true, valid

C5 = Implies(Not(Not(x)), x) # 5. ¬¬X ⊢ X                   -- negation elimination 
# if NOT NOT x is true, x is true, valid

C6 = Not(And(x, Not(x))) # 6. ¬(X ∧ ¬X)                 -- no contradiction
# x and NOT x cannot both be true, valid

C7 = Implies(x, Or(x, y)) # 7. X ⊢ X ∨ Y                 -- or introduction left
# if x is true, x OR y is true, valid

C8 = Implies(y, Or(x, y)) # 8. Y ⊢ X ∨ Y                 -- or introduction right
# if y is true, x OR y is true, valid

C9 = Implies(Implies(x, y), Implies(Not(x), Not(y))) # 9. X → Y, ¬X ⊢ ¬ Y           -- denying the antecedent
# if x implies y, then NOT x implies NOT y, not valid
# if x is false and y is true, then x implies y, but not the opposite

C10 = Implies(And(Implies(x, y), Implies(y, x)), x == y) # 10. X → Y, Y → X ⊢ X ↔ Y      -- iff introduction
# if x implies y and y implies x, then x and y are the same, valid

C11 = Implies(x == y, Implies(x, y)) # 11. X ↔ Y ⊢ X → Y            -- iff elimination left
# if x and y are the same, x implies y, valid

C12 = Implies(x == y, Implies(y, x)) # 12. X ↔ Y ⊢ Y → X            -- iff elimination right
# if x and y are the same, y implies x, valid

C13 = Implies(And(Or(x, y), Implies(x, z), Implies(y, z)), z) # 13. X ∨ Y, X → Z, Y → Z ⊢ Z  -- or elimination
# if x OR y, x implies z, and y implies z, then z is true, valid

C14 = Implies(And(Implies(x, y), y), x) # 14. X → Y, Y ⊢ X             -- affirming the conclusion
# if x implies y and y is true, then x is true, not valid
# if x is false and y is true, then x implies y and y is true, but this doesn't mean x is true

C15 = Implies(And(Implies(x, y), x), y) # 15. X → Y, X ⊢ Y             -- arrow elimination
# if x implies y and x is true, then y is true, valid

C16 = Implies(And(Implies(x, y), Implies(y, z)), Implies(x, z)) # 16. X → Y, Y → Z ⊢ X → Z     -- transitivity of → 
# if x implies y and y implies z, then x implies z, valid

C17 = Implies(Implies(x, y), Implies(y, x)) # 17. X → Y ⊢ Y → X            -- converse
# if x implies y, then y implies x, not valid
# if x is true and y is false, then x implies y but y doesn't imply x

C18 = Implies(Implies(x, y), Implies(Not(y), Not(x))) # 18. X → Y ⊢ ¬Y → ¬X          -- contrapositive
# if x implies y, then NOT y implies NOT x, valid

C19 = Not(Or(x, y)) == And(Not(x), Not(y)) # 19. ¬(X ∨ Y) ↔ ¬X ∧ ¬Y       -- DeMorgan #1 (¬ distributes over ∨)
# the opposite of x OR y is equivalent to the AND of NOT x and NOT y, valid

C20 = Not(And(x, y)) == Or(Not(x), Not(y)) # 20. ¬(X ∧ Y) ↔ ¬X ∨ ¬Y       -- Demorgan #2 (¬ distributes over ∧)
# the opposite of x AND y is equivalent to the OR of NOT x and NOT y, valid

conditions = C1, C2, C3, C4, C5, C6, C7, C8, C9, C10, C11, C12, C13, C14, C15, C16, C17, C18, C19, C20

s = Solver()
for i, cond in enumerate(conditions):
    s.add(Not(cond))
    s.check()
    if s.check() == unsat:
        print(f'Rule #{i + 1} is valid')
    else:
        print(f"Rule #{i + 1} isn't valid, counter example of", s.model())
    s.reset()