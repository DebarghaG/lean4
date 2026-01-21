/-
Simple definitions that can be parsed with minimal parser (no operators, no tactics).
Used for testing PCFG extraction.
-/

def id (x : Nat) : Nat := x

def const (x y : Nat) : Nat := x

def apply (f : Nat → Nat) (x : Nat) : Nat := f x

def compose (f g : Nat → Nat) (x : Nat) : Nat := f (g x)

def twice (f : Nat → Nat) (x : Nat) : Nat := f (f x)

structure Point where
  x : Nat
  y : Nat

def origin : Point := { x := 0, y := 0 }

def moveX (p : Point) (dx : Nat) : Point := { p with x := dx }

inductive MyList (α : Type) where
  | nil : MyList α
  | cons : α → MyList α → MyList α

def empty : MyList Nat := MyList.nil

def singleton (x : Nat) : MyList Nat := MyList.cons x MyList.nil

namespace MyList

def head? : MyList α → Option α
  | nil => none
  | cons x _ => some x

def tail : MyList α → MyList α
  | nil => nil
  | cons _ xs => xs

end MyList

-- Theorems removed for minimal parser compatibility
