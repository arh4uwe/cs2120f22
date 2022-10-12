variable T : Type
variable P : T → T → T → Prop
variable Q : T → T → Prop

def proof : 
  (∀ (t1 : T), ∃ (t2 : T), ∀ (t3 : T), P t1 t2 t3)
  ↔ (∀ (t1 t3 : T), ∃ (t2 : T), P t1 t2 t3)
  :=
begin
  split,
  {
    intros h t1 t3,
    have exists_t2 := h t1,
    cases exists_t2 with t2 forall_t3,
    apply exists.intro t2,
    apply forall_t3 t3,
  },
  {
    intros h t1,
    -- this cannot be proven.
  }
end

def proof2 :
  (∀ (t1 t4 : T), Q t1 t4)
  ↔ (∀ (t1 : T), Q t1 t1)
  :=
begin
  split,
  {
    intros h t1,
    exact h t1 t1,
  },
  {
    intros h t1 t4,
    -- this cannot be proven.
  }
end

def proof3 :
  (∀ (t1 : T), ∀ (t2 : T), Q t1 t2)
  ↔ (∀ (t1 t2 : T), Q t1 t2)
  :=
begin
  split,
  repeat {
    intros h t1 t2,
    apply h t1 t2,
  }
end

def proof4:
  (∀ (t1 : T), ∃ (t2 : T), Q t1 t2 ∧ ∃ (t3 : T), Q t2 t3)
  ↔ (∀ (t1 : T), ∃ (t2 t3 : T), Q t1 t2 ∧ Q t2 t3)
  :=
begin
  split,
  {
    intros h t1,
    have exists_t2 := h t1,
    cases exists_t2 with t2 and,
    cases and with q_t1_t2 exists_t3,
    cases exists_t3 with t3 q_t2_t3,
    apply exists.intro t2,
    apply exists.intro t3,
    apply and.intro,
    exact q_t1_t2,
    exact q_t2_t3,
  },
  {
    intros h t1,
    have exists_t2_t3 := h t1,
    cases exists_t2_t3 with t2 exists_t3,
    apply exists.intro t2,
    cases exists_t3 with t3 and,
    cases and with q_t1_t2 q_t2_t3,
    apply and.intro,
    exact q_t1_t2,
    apply exists.intro t3,
    exact q_t2_t3,
  }
end