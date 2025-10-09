import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.Algebra.Group.Conj
import BarringtonTheorem.GroupPrograms
import BarringtonTheorem.Formula

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

theorem computable_for_conj_cycles
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

theorem inverse_computable
  (α : Equiv.Perm (Fin n))
  (P : GroupProgram (Equiv.Perm (Fin n)) m)
  (f : Input m→ Bool)
  (hα_cycle : Equiv.Perm.IsCycle α)
  (hα : α_computes α P f) :
  ∃ (Q : GroupProgram (Equiv.Perm (Fin n)) m),
    Q.length = P.length ∧ α_computes α Q (λ x => ¬ f x) := by
  sorry

theorem and_computable
  (α β : Equiv.Perm (Fin n))
  (hα : Equiv.Perm.IsCycle α)
  (hβ : Equiv.Perm.IsCycle β)
  (hαβ : α.support.card = β.support.card)
  (f : Input m→ Bool)
  (g : Input m→ Bool)
  (P : GroupProgram (Equiv.Perm (Fin n)) m)
  (Q : GroupProgram (Equiv.Perm (Fin n)) m)
  (hα_computes : α_computes α P f)
  (hβ_computes : α_computes β Q g)
  (hPQ : P.length = Q.length):
  ∃ (R : GroupProgram (Equiv.Perm (Fin n)) m),
    R.length = 4 * P.length ∧
    α_computes (α * β * α⁻¹ * β⁻¹) R (λ x => f x ∧ g x) := by
    sorry

theorem product_cycles_conjugate_cycle:
  ∃ (α β : Equiv.Perm (Fin n)),
    Equiv.Perm.IsCycle α ∧
    Equiv.Perm.IsCycle β ∧
    α.support.card = β.support.card ∧
    Equiv.Perm.IsCycle (α * β * α⁻¹ * β⁻¹) := by
    sorry

theorem barrington_theorem
  (f : Input m → Bool)
  (hfcomputed : computed_by_formula f d) :
  ∃ (α : Equiv.Perm (Fin 5)) (P : GroupProgram (Equiv.Perm (Fin 5)) m),
    Equiv.Perm.IsCycle α ∧
      P.length ≤ 4 ^ d ∧
      α_computes α P f := by
      sorry
