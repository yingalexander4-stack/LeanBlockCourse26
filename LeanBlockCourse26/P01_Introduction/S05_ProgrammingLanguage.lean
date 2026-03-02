import Mathlib.Tactic.Basic

set_option linter.style.emptyLine false

/-
# Introduction to Lean as a Programming Language
=====================

## Basic Values and Printing
In Lean, we declare values using `def`. The type can be inferred or explicitly stated.
-/

-- Basic Hello World
def hello : String := "Hello, World!"
#check hello

-- Types can be infered
def hello2 := "Hello, World!"
#check hello2

/-
Compare with:
Python: message = "Hello, World!"    # Dynamic typing
C:      const char* hello = "Hello, World!";  // Static typing
-/

def printHello : IO Unit := -- 'IO Unit' is an Explicit type for IO operations
 IO.println hello

#check printHello -- tells us this is of type 'IO Unit'
#eval printHello -- actually executes the method and prints "Hello, World!"


/-
## Basic Arithmetic
Lean uses natural numbers (Nat) by default for integers. Functions can be defined
with explicit type annotations, similar to C but with a different syntax.
-/

def add (x y : Nat) : Nat := x + y

/-
Compare with:
Python: def add(x, y): return x + y
C:      int add(int x, int y) { return x + y; }
-/

#eval add 2 3   -- 2 + 3 = 5
#check add      -- 'add' has type Nat → Nat → Nat
#check add 2 3  -- 2 + 3 = 5 is of type Nat
#check add 2    -- we can partially apply: 'add 2' is of type Nat → Nat

def triple_multiply (x y z : Nat) : Nat := x * y * z

#eval triple_multiply 1 2 3    -- 1 * 2 * 3 = 6
#check triple_multiply 1 2 3   -- 1 * 2 * 3 = 6 is of type Nat
#check triple_multiply         -- 'triple_multiply' is of type Nat → Nat → Nat → Nat


/-
## Pattern Matching and Control Flow
Lean uses pattern matching as its primary control flow mechanism. This is more
powerful than traditional if/switch statements found in C or Python.
-/

def calculator (op : String) (x y : Nat) : Nat :=
  match op with
  | "+" => x + y
  | "-" => x - y
  | "*" => x * y
  | _   => 0 -- default

/-
Compare with:
Python:
def calculator(op, x, y):
    if op == "+": return x + y
    elif op == "-": return x - y
    elif op == "*": return x * y
    else: return 0

C:
int calculator(char* op, int x, int y) {
    if (strcmp(op, "+") == 0) return x + y;
    else if (strcmp(op, "-") == 0) return x - y;
    else if (strcmp(op, "*") == 0) return x * y;
    else return 0;
}
-/

#eval calculator "*" 2 3   -- 2 * 3 = 6
#check calculator          -- 'calculator' is of type String → Nat → Nat → Nat


/-
## String Interpolation
Lean provides string interpolation similar to modern programming languages.
-/

def greeting (name : String) : String :=
  s!"Hello, {name}!"

/-
Compare with:
Python:
def greeting(name):
    return f"Hello, {name}!"
-/

#eval greeting "Martin"    -- "Hello, Martin!"
#check greeting            -- 'greeting' is of type String → String
#check greeting "Martin"   -- 'greeting "Martin"' is of type String


/-
## Type Inference
Lean has a powerful type inference system that can automatically determine types in many cases.
This makes code more concise while maintaining type safety. The compiler will infer the most
general type that satisfies the constraints.
-/

-- Type inference for simple values
def inferredNumber := 42        -- Inferred as Nat
def inferredText := "Hello"     -- Inferred as String
def inferredList := [1, 2, 3]   -- Inferred as List Nat

-- def mixedList := [1, "test"] -- Fails because List cannot have mixed type elements

#check inferredList


-- Type inference for functions
def inferredAdd (x : Nat) y := x + y          -- type of `y` and of output is inferred as `Nat`
def inferredConcat (x : String) y := x ++ y   -- type of `y` and output is inferred as `String`

-- Sometimes explicit types are clearer or necessary
def explicitSubNat (x y : Nat) := x - y  -- Forces `Nat` arithmetic
#check explicitSubNat     -- Nat → Nat → Nat
#check explicitSubNat 2 3 -- Nat
#eval explicitSubNat 2 3  -- 2 - 3 = 0 in Nat

def explicitSubInt (x y : Int) := x - y
#check explicitSubInt 2 3    -- Int
#eval explicitSubInt 2 3     -- 2 - 3 = -1 in Int

-- def implictSub (x y) := x - y -- unable to infer type
-- def implictSub (x y) : Int := x - y -- unable to infer type
def implictSub (x : Int) y := x - y -- able to infer Int for y and output
def implictSub' x (y : Int) := x - y -- able to infer Int for x and output

#check implictSub'
#eval implictSub' 2 3

/-
Compare with:
Python: Type hints are optional
def add(x, y):  # No types needed
    return x + y

TypeScript: Type inference with explicit options
let inferredNumber = 42;  // number
let explicitNumber: number = 42;
-/

/-
## Type Coercion
Some types can be coerced into other types, like Nat to Int.
-/

def implictSub'' (x : Nat) (y : Int) := x - y -- able to coerce y into Int and output

#check implictSub''
#eval implictSub'' 2 3

def implictSub''' (x : Int) (y : Nat) := x - y -- able to coerce y to Int

#check implictSub'''
#eval implictSub''' 2 3

def inferredAdd' (x : Nat) (y : Int) := x + y

def coercedOutputAdd (x y : Nat) : Int := x - y

#check coercedOutputAdd 2 3 -- Nat → Nat → Int, but it uses the
                            -- Int subtraction and coereces the Nat to Int
#eval coercedOutputAdd 2 3  -- 2 - 3 = -1 since x and y are both first coerced to Int

/-
## Data Structures
Lean provides several ways to structure data. Here we demonstrate:
1. Simple structures (similar to C structs or Python classes)
2. Namespace organization
3. Method-like function definitions
-/

structure Rectangle where
  width : Float
  height : Float
deriving Repr

def myRectangle : Rectangle := { width := 4.0, height := 2.0 }

def Rectangle.area (r : Rectangle) : Float :=
  r.width * r.height

#eval Rectangle.area myRectangle
#eval myRectangle.area

def Rectangle.perimeter (r : Rectangle) :=
   2.0 * (r.width + r.height)

#eval myRectangle.perimeter

structure Point where
  x : Float
  y : Float
deriving Repr

/-
Compare with:
Python:
class Point:
    def __init__(self, x, y):
        self.x = x
        self.y = y

C:
struct Point {
    double x;
    double y;
};
-/

structure Circle where
  center : Point
  radius : Float
deriving Repr

def π : Float := 3.14159265358979323846 -- don't do this!!

-- Instead of 'Rectangle.' we can also use 'namespace'
namespace Circle

-- putting this into the namespace has the same effect
-- as naming it Circle.area
def area (c : Circle) : Float :=
  π * c.radius * c.radius

def circumference (c : Circle) : Float :=
  2.0 * π * c.radius

def containsPoint (c : Circle) (p : Point) : Bool :=
  let dx := c.center.x - p.x
  let dy := c.center.y - p.y
  dx * dx + dy * dy ≤ c.radius * c.radius

end Circle

def myCircle : Circle := {
  center := { x := 1.0, y := 1.0 }
  radius := 2.5
}

#eval myCircle               -- Shows the full structure
#eval myCircle.area          -- Calculates area
#eval myCircle.circumference -- Calculates circumference
#eval myCircle.containsPoint { x := 2.0, y := 2.0 }  -- Tests point containment

/-
-------------------------------------------------------------
## Propositions as Types – A Glimpse into Proofs in Lean

In Lean, every proposition is just a type, and a proof is a value (or term) of that type.
This is the essence of the propositions-as-types (or Curry–Howard) correspondence.
In other words, proving a proposition amounts to constructing a term that inhabits the type
representing that proposition.
-------------------------------------------------------------
-/

-- This function claims it returns a Nat
def t1 : Nat := 0 -- putting a string here would be a type error

#check t1 -- Nat
#eval t1  -- 0

def t2 : Nat := 0

def t3 (n : Nat) : Nat := n

-- def t4' n := n  -- Thus doesn't work because Lean cannot infer a type

/-
Compare with:
Python:
def foo(x):
  return x
-/

-- But we can "hack" our way around this by making
-- the arbitrary type of 'n' an argument of the method
def t4 (T : Type) (n : T) : T := n

#eval t4 Nat 2

def t4' {T : Type} (n : T) : T := n -- curly brackets make T implicit

#eval t4' 2

-- We can prove that t3 and t4 applied to Nat return the same output!
def t4_Nat_eq_t3 : t4 Nat = t3 := rfl

-- doesn't really matter if we use 'def' or 'theorem' here
theorem t4_Nat_eq_t3' : t4 Nat = t3 := rfl

-- This does not work because not only the type is checked (Nat)
-- but also the specific instance, which is not the same (0 != n)
-- example : t4 Nat = t2 := rfl

-- A constructive proof of the type of the statement `P → P`
def t5 (P : Prop) (p : P) : P := p

theorem t6 (P : Prop) (p : P) : P := by
  exact p -- same proof / method


-- Blurring the lines between programming a method and writing a proof:
-- How to proof P ∧ Q → P

-- Term mode proof
theorem t7 (P Q : Prop) : P ∧ Q → P := fun ⟨p, _⟩ => p

theorem t7' (P Q : Prop) : (P ∧ Q → P : Prop) := fun ⟨p, _⟩ => p

-- Same proof in tactic mode
theorem t7'' (P Q : Prop) : P ∧ Q → P := by
  intro ⟨p, _⟩
  exact p

-- They all have the same type and hence are proving the same theorem
#check t7     -- ∀ (P Q : Prop), P ∧ Q → P
#check t7'    -- ∀ (P Q : Prop), P ∧ Q → P
#check t7''   -- ∀ (P Q : Prop), P ∧ Q → P

-- sorry skips the proof but type checker is happy
example (P Q : Prop) : P ∧ Q → P := by sorry

-- axioms don't require proofs!
-- but this one is unnecessary, since it is inferred by our type system
axiom this_is_our_first_axiom (P Q : Prop) : P ∧ Q → P
