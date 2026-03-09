/-
# S04: Verified Computation and Trust

The payoff: verified computation with Subtype, axiom tracing with
`#print axioms`, and the trust model.
-/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Cases



/-!
## (Inductive) type classes and their instances

### Inhabited
-/

#check Inhabited
#check @instInhabitedNat

#eval @Inhabited.default Nat _


-- This works and shows `0`because `Nat` is shown to be an instance of type class `Inhabited` ...
#eval @Inhabited.default Nat _

-- ... by providing its zero constructor as thge default element
instance : Inhabited Nat where
  default := Nat.zero

/-!
### Nonempty
-/

#check Nonempty

-- This works ...
#check Nonempty.intro Nat

-- ... but `eval` complains about `proofs are not computationally relevant` ...
-- #eval Nonempty.intro Nat
#check Nonempty.intro Nat

-- A `Prop` is nonempty if it has a term `p` ...
variable (P : Prop) (p : P)
instance : Nonempty P := Nonempty.intro p

-- ... but `eval` again does not work because `Prop` is stateless
-- #eval Nonempty.intro Nat
#check Nonempty.intro P

/-!
### Decidable and DecidablePred
-/

#check Decidable
#check DecidablePred

#check @instDecidableAnd

def p_nat_even := (fun n : Nat => n  % 2 = 0) 

noncomputable instance pNatEvenDecidableClassical : DecidablePred p_nat_even :=
    Classical.decPred p_nat_even


-- instance pNatEvenDecidableConstructive : DecidablePred p_nat_even :=
  -- intro n
  -- | isFalse => sorry
  -- | isTrue => sorry

/-!
## Verified computation

The pattern:
1. Write an algorithm with a plain type signature.
2. Prove a property as a separate theorem.
3. Bundle into Subtype — the return type carries the guarantee.
-/

section VerifiedFilter

variable {α : Type}

-- Step 1: algorithm. `[DecidablePred p]` lets `if` branch on a Prop.

/-
`List` is defined inductively on lean with constructors for an empty
list (`nil`) and an dependent constructor `cons` that appends and element
`(head : α)` to a given existing list `(tail : List α)`.

inductive List (α : Type u) where
  | nil : List α 
  | cons (head : α) (tail : List α) : List α

We can use `[...]` notation with `[] = List.nil`
-/

def propFilter (p : α → Prop) [DecidablePred p] : List α → List α
  | [] => [] 
  | head :: tail =>
      let filtered_tail := propFilter p tail
      if (p head) then
        head :: filtered_tail
      else
        filtered_tail

-- We can actually evaluate this computationally ...
#eval propFilter (fun n : Nat => n  % 2 = 0)  [1, 2, 3, 4, 5, 6]


-- ... but only if we know `DecidablePred` holds and is computable

noncomputable instance : DecidablePred p_nat_even := Classical.decPred p_nat_even

-- Complains about `Classical.choice` axiom being used
-- #eval propFilter p_nat_even [1, 2, 3, 4, 5, 6]

-- Exercise: prove that `propFilter` is sound
-- Step 2a: prove soundness — everything in the output satisfies p.
theorem propFilter_sound (p : α → Prop) [DecidablePred p] (xs : List α) :
    ∀ x ∈ propFilter p xs, p x := by
  intro x hx
  induction xs with
  | nil =>
     unfold propFilter at hx  -- optional
     exfalso
     exact (List.mem_nil_iff x).mp hx
  | cons y ys ih => 
     unfold propFilter at hx -- not optional
     split at hx
     case isTrue h =>
      cases hx with
       | head => exact h
       | tail _ hmem => exact ih hmem
     case isFalse h =>
      exact ih hx

-- example (p : α → Prop) [DecidablePred p] (xs : List α) :
--     ∀ x ∈ propFilter p xs, p x := by
--   intro x hx
--   induction' xs with y ih
--   · contradiction
--   · unfold propFilter at hx -- optional not optional
--     split at hx
--     by_cases h : p y
--     · cases hx with
--       | head => assumption
--       | tail _ hmem => exact ih hmem
--     · exact ih hx

-- Step 2b: prove completeness - everyhting not in the output does not satisfy p.
theorem propFilter_complete (p : α → Prop) [DecidablePred p] (xs : List α) :
    ∀ x ∉ propFilter p xs, ¬ p x := by
  sorry

-- Step 3: bundle algorithm + proof into Subtype.
def verifiedFilter (p : α → Prop) [DecidablePred p] (xs : List α) :
    { ys : List α // (∀ x ∈ ys, p x) ∧ (∀ x ∉ ys, ¬ p x) } :=
  ⟨propFilter p xs, propFilter_sound p xs, propFilter_complete p xs⟩

-- #eval (verifiedFilter (fun n : Nat => n % 2 = 0) [1, 2, 3, 4, 5, 6]).val




end VerifiedFilter
