import Mathlib.Data.Nat.Basic
import BarringtonTheorem.GroupPrograms

open BarringtonTheorem

inductive Formula (n : ℕ): Type where
  | var : Fin n → Formula n
  | not : Formula n → Formula n
  | and : Formula n → Formula n → Formula n

def Formula.eval : Formula n → Input n→ Bool
| Formula.var i, env => env i
| Formula.not f, env => ¬(Formula.eval f env)
| Formula.and f1 f2, env => (Formula.eval f1 env) && (Formula.eval f2 env)

def Formula.size : Formula n→ Nat
| Formula.var _ => 1
| Formula.not f => 1 + Formula.size f
| Formula.and f1 f2 => 1 + Formula.size f1 + Formula.size f2

def Formula.depth : Formula n → Nat
| Formula.var _ => 0
| Formula.not f => 1 + Formula.depth f
| Formula.and f1 f2 => 1 + Nat.max (Formula.depth f1) (Formula.depth f2)

def computed_by_formula (f : Input n→ Bool) (d : ℕ) : Prop :=
  ∃ φ : Formula n, Formula.depth φ ≤ d ∧ ∀ x : Input n, Formula.eval φ x = f x

-- building an example

def l : List Bool := [true, false, true, false,
true, true, true, false]
#eval l[2]!

def env1 : Fin 8 → Bool :=
  fun i => if i < l.length then l[i]! else false

def example_formula : Formula 8 :=
  Formula.and (Formula.var 2) (Formula.not (Formula.var 3))
#eval Formula.eval example_formula env1
#eval Formula.size example_formula
#eval Formula.depth example_formula
