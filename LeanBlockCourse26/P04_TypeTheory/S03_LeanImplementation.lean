/-
# S03: Lean's Implementation

Minimal demos: how Lean realizes dependent type theory.
Inductive types, structures, classes, and instances.
-/

import Mathlib.Tactic.Basic
import Mathlib.Logic.Basic

-- We have a boolean type in lean ...
#check true   -- `Bool`
#check false  -- `Bool`
#check Bool   -- `Type`

-- ... which is separate from the proposition type
#check True   -- `Prop`
#check False  -- `Prop`
#check Prop   -- `Type`

-- A structure: single-constructor inductive with named projections
structure Point (α : Type) where
  x : α
  y : α
  deriving Repr

def origin : Point Int := { x := 0, y := 0 }
#eval origin.x

-- An inductive type: you specify constructors, the kernel generates a recursor
inductive Weekday where
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  deriving Repr

#print Weekday
#print Weekday.monday
#check @Weekday.rec

-- A class: structure + automatic instance resolution via [...]
class Greet (α : Type*) where
  greet : α → String

def actual_greeting {α : Type*} [Greet α] (x : α) := Greet.greet x

instance : Greet Weekday where greet 
  | .monday => "ugh"
  | .friday => "finally"
  | _ => "meh"

def monday : Weekday := Weekday.monday

#eval actual_greeting monday

-- Decidable: bridges Prop and Bool
#print Decidable
#eval if (3 : Nat) < 5 then "yes" else "no"
