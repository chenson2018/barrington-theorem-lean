import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.Algebra.Group.Conj
import BarringtonTheorem.GroupPrograms
import BarringtonTheorem.Formula
import Mathlib.Data.Fin.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Tactic
import Mathlib.Data.Nat.Basic

open BarringtonTheorem

variable {n m : ℕ}

def α_computes {G : Type} [Group G] (α : G)
    (P : GroupProgram G m) (f : Input m → Bool) : Prop :=
  ∀ (x : Input m), evalProgram x P = if f x then α else 1

lemma evalProgram_conjugate (P : GroupProgram (Equiv.Perm (Fin n)) m)
  (γ : Equiv.Perm (Fin n)) (x : Input m) :
  evalProgram x (P.map (λ t =>
    { i := t.i,
      g₀ := γ * t.g₀ * γ⁻¹,
      g₁ := γ * t.g₁ * γ⁻¹ })) =
  γ * evalProgram x P * γ⁻¹ := by
  sorry

lemma computable_for_conj_cycles
  (α β : Equiv.Perm (Fin n))
  (P : GroupProgram (Equiv.Perm (Fin n)) m)
  (f : Input m → Bool)
  (hα : Equiv.Perm.IsCycle α)
  (hβ : Equiv.Perm.IsCycle β)
  (hαβ : α.support.card = β.support.card)
  (hα_computes : α_computes α P f) :
  ∃ (Q : GroupProgram (Equiv.Perm (Fin n)) m),
    Q.length = P.length ∧ α_computes β Q f := by
    obtain ⟨γ , hγ⟩ := Equiv.Perm.IsCycle.isConj hα hβ hαβ
    let Q : GroupProgram (Equiv.Perm (Fin n)) m:= P.map (λ t =>
    { i := t.i,
      g₀ := γ * t.g₀ * γ⁻¹,
      g₁ := γ * t.g₁ * γ⁻¹ })
    use Q
    constructor
    · simp [Q, List.length_map]
    . intro x
      simp [Q]
      rw [evalProgram_conjugate P γ x]
      simp [α_computes] at hα_computes
      have h1 := evalProgram_conjugate P γ x
      rw [SemiconjBy] at hγ
      sorry

lemma inverse_computable
  (α : Equiv.Perm (Fin n))
  (P : GroupProgram (Equiv.Perm (Fin n)) m)
  (f : Input m→ Bool)
  (hα_cycle : Equiv.Perm.IsCycle α)
  (hα : α_computes α P f) :
  ∃ (Q : GroupProgram (Equiv.Perm (Fin n)) m),
    Q.length = P.length ∧ α_computes α Q (λ x => ¬ f x) := by
  sorry

lemma and_computable
  (α β : Equiv.Perm (Fin n))
  (hα : Equiv.Perm.IsCycle α)
  (hβ : Equiv.Perm.IsCycle β)
  (hαβ : α.support.card = β.support.card)
  (f : Input m → Bool)
  (g : Input m → Bool)
  (P : GroupProgram (Equiv.Perm (Fin n)) m)
  (Q : GroupProgram (Equiv.Perm (Fin n)) m)
  (hα_computes : α_computes α P f)
  (hβ_computes : α_computes β Q g)
  (hPQ : P.length = Q.length):
  ∃ (R : GroupProgram (Equiv.Perm (Fin n)) m),
    R.length = 4 * P.length ∧
    α_computes (α * β * α⁻¹ * β⁻¹) R (λ x => f x ∧ g x) := by
    sorry

lemma product_cycles_conjugate_cycle:
  ∃ (α β : Equiv.Perm (Fin n)),
    Equiv.Perm.IsCycle α ∧
    Equiv.Perm.IsCycle β ∧
    α.support.card = β.support.card ∧
    Equiv.Perm.IsCycle (α * β * α⁻¹ * β⁻¹) := by
    sorry

def example_perm : Equiv.Perm (Fin 5) :=
  (Equiv.swap 0 4) * (Equiv.swap 0 3) * (Equiv.swap 0 2) * (Equiv.swap 0 1)

lemma example_perm_is_cycle : Equiv.Perm.IsCycle example_perm := by
  sorry

#eval example_perm 0
#eval example_perm 1
#eval example_perm 2
#eval example_perm 3
#eval example_perm 4


theorem barrington_theorem
  (f : Input m → Bool)
  (hfcomputed : computed_by_formula f d) :
  ∃ (α : Equiv.Perm (Fin 5)) (P : GroupProgram (Equiv.Perm (Fin 5)) m),
    Equiv.Perm.IsCycle α ∧
      P.length ≤ 4 ^ d ∧
      α_computes α P f := by
    obtain ⟨φ, hφd, hφf⟩ := hfcomputed
    induction φ generalizing f d
    case var a =>
      let α := example_perm
      use α
      simp[Formula.eval] at hφf
      let gpt : GPTriple (Equiv.Perm (Fin 5)) m :={
        i := a
        g₀ := 1
        g₁ := α
      }
      let P : GroupProgram (Equiv.Perm (Fin 5)) m := [gpt]
      use P
      constructor
      case left =>
        exact example_perm_is_cycle
      case right =>
        constructor
        case left =>
          simp [P]
          have h1 : 0 < 4 := by linarith
          exact Nat.one_le_pow d 4 h1
        case right =>
          simp [P, gpt, α_computes, evalProgram, evalTriple]
          intro x
          rw [← hφf x]
    case not F F_ih =>
      rw [Formula.depth] at hφd
      simp [Formula.eval] at hφf
      have h0: F.depth ≤ d := by
        rw [← Nat.succ_eq_one_add] at hφd
        exact Nat.le_of_succ_le hφd
      have h2 : ∀ (x : Input m), F.eval x = decide ¬f x = true := by
        simp
        exact hφf
      have h1: ∃ (α : Equiv.Perm (Fin 5))(P : GroupProgram (Equiv.Perm (Fin 5)) m), α.IsCycle ∧ P.length ≤ 4 ^ d ∧ α_computes α P (λ x => ¬ f x) := by
        exact F_ih (λ x => ¬ f x) h0 h2
      obtain ⟨α, P, hαcycle, hPlen, hα_computesP⟩ := h1
      have hQ := inverse_computable α P (λ x => ¬ f x) hαcycle hα_computesP
      simp at hQ
      obtain ⟨Q, hEqLen, hα_computesQ⟩ := hQ
      use α
      use Q
      constructor
      case left => exact hαcycle
      constructor
      case left =>
        rw [hEqLen]
        exact hPlen
      case right => exact hα_computesQ
    case and F1 F2 hF1 hF2 =>
      sorry
