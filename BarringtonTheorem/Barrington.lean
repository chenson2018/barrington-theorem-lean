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

lemma evalProgram_conjugate
    (P : GroupProgram (Equiv.Perm (Fin n)) m)
    (γ : Equiv.Perm (Fin n)) (x : Input m) :
    evalProgram x
      (P.map (λ t =>
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
  obtain ⟨γ, hγ⟩ := Equiv.Perm.IsCycle.isConj hα hβ hαβ
  let Q : GroupProgram (Equiv.Perm (Fin n)) m :=
    P.map (λ t =>
      { i := t.i,
        g₀ := γ * t.g₀ * γ⁻¹,
        g₁ := γ * t.g₁ * γ⁻¹ })
  use Q
  constructor
  · simp [Q, List.length_map]
  · intro x
    simp [Q]
    rw [evalProgram_conjugate P γ x]
    simp [α_computes] at hα_computes
    have h1 := evalProgram_conjugate P γ x
    rw [SemiconjBy] at hγ
    sorry

lemma inverse_computable
    (α : Equiv.Perm (Fin n))
    (P : GroupProgram (Equiv.Perm (Fin n)) m)
    (f : Input m → Bool)
    (hα_cycle : Equiv.Perm.IsCycle α)
    (hα : α_computes α P f) :
    ∃ (Q : GroupProgram (Equiv.Perm (Fin n)) m),
      Q.length = P.length ∧ α_computes α Q (λ x => ¬ f x) := by
  sorry

lemma and_computable
    (α β : Equiv.Perm (Fin n))
    (hα : Equiv.Perm.IsCycle α)
    (hβ : Equiv.Perm.IsCycle β)
    (f : Input m → Bool)
    (g : Input m → Bool)
    (P : GroupProgram (Equiv.Perm (Fin n)) m)
    (Q : GroupProgram (Equiv.Perm (Fin n)) m)
    (hα_computes : α_computes α P f)
    (hβ_computes : α_computes β Q g) :
    ∃ (R : GroupProgram (Equiv.Perm (Fin n)) m),
      R.length = 2 * (P.length + Q.length) ∧
      α_computes (α * β * α⁻¹ * β⁻¹) R (λ x => f x ∧ g x) := by
  sorry

lemma product_cycles_conjugate_cycle :
    ∃ (α β : Equiv.Perm (Fin n)),
      Equiv.Perm.IsCycle α ∧
      Equiv.Perm.IsCycle β ∧
      α.support.card = β.support.card ∧
      Equiv.Perm.IsCycle (α * β * α⁻¹ * β⁻¹) := by
  sorry

def example_perm : Equiv.Perm (Fin 5) :=
  (Equiv.swap 0 4) *
  (Equiv.swap 0 3) *
  (Equiv.swap 0 2) *
  (Equiv.swap 0 1)

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
    simp [Formula.eval] at hφf
    let gpt : GPTriple (Equiv.Perm (Fin 5)) m :=
      { i := a, g₀ := 1, g₁ := α }
    let P : GroupProgram (Equiv.Perm (Fin 5)) m := [gpt]
    use P
    constructor
    · exact example_perm_is_cycle
    constructor
    · simp [P]
      have h1 : 0 < 4 := by linarith
      exact Nat.one_le_pow d 4 h1
    · simp [P, gpt, α_computes, evalProgram, evalTriple]
      intro x
      rw [← hφf x]
  case not F F_ih =>
    rw [Formula.depth] at hφd
    simp [Formula.eval] at hφf
    have h0 : F.depth ≤ d := by
      rw [← Nat.succ_eq_one_add] at hφd
      exact Nat.le_of_succ_le hφd
    have h2 : ∀ (x : Input m), F.eval x = decide ¬f x = true := by
      simp
      exact hφf
    have h1 :
        ∃ (α : Equiv.Perm (Fin 5)) (P : GroupProgram (Equiv.Perm (Fin 5)) m),
          α.IsCycle ∧ P.length ≤ 4 ^ d ∧ α_computes α P (λ x => ¬ f x) := by
      exact F_ih (λ x => ¬ f x) h0 h2
    obtain ⟨α, P, hαcycle, hPlen, hα_computesP⟩ := h1
    have hQ := inverse_computable α P (λ x => ¬ f x) hαcycle hα_computesP
    simp at hQ
    obtain ⟨Q, hEqLen, hα_computesQ⟩ := hQ
    use α
    use Q
    constructor
    · exact hαcycle
    constructor
    · rw [hEqLen]
      exact hPlen
    · exact hα_computesQ
  case and F1 F2 hF1 hF2 =>
    let f1 : Input m → Bool := λ x => F1.eval x
    let f2 : Input m → Bool := λ x => F2.eval x
    have hf1depth_le_d : F1.depth ≤ d - 1 := by
      rw [Formula.depth] at hφd
      have h_one_le_d := Nat.le_of_add_right_le hφd
      apply Nat.lt_of_succ_le at h_one_le_d
      apply Nat.one_add_le_iff.mp at hφd
      have hdepthF1lemax : F1.depth ≤ max F1.depth F2.depth :=
        le_max_left F1.depth F2.depth
      have hF1depthled : F1.depth < d :=
        lt_of_le_of_lt hdepthF1lemax hφd
      exact (Nat.le_sub_one_iff_lt h_one_le_d).mpr hF1depthled
    have hf2depth_le_d : F2.depth ≤ d - 1 := by
      rw [Formula.depth] at hφd
      have h_one_le_d := Nat.le_of_add_right_le hφd
      apply Nat.lt_of_succ_le at h_one_le_d
      apply Nat.one_add_le_iff.mp at hφd
      have hdepthF1lemax : F2.depth ≤ max F1.depth F2.depth :=
        le_max_right F1.depth F2.depth
      have hF2depthled : F2.depth < d :=
        lt_of_le_of_lt hdepthF1lemax hφd
      exact (Nat.le_sub_one_iff_lt h_one_le_d).mpr hF2depthled
    have hf1computable : ∀ (x : Input m), F1.eval x = f1 x := by simp [f1]
    have hf2computable : ∀ (x : Input m), F2.eval x = f2 x := by simp [f2]
    have h1 :
        ∃ α P, Equiv.Perm.IsCycle α ∧ List.length P ≤ 4 ^ (d - 1) ∧
          α_computes α P f1 :=
      hF1 f1 hf1depth_le_d hf1computable
    have h2 :
        ∃ α P, Equiv.Perm.IsCycle α ∧ List.length P ≤ 4 ^ (d - 1) ∧
          α_computes α P f2 :=
      hF2 f2 hf2depth_le_d hf2computable
    obtain ⟨α, P, hαcycle, hPLength, hα_computes⟩ := h1
    obtain ⟨β, Q, hβcycle, hQLength, hβ_computes⟩ := h2
    use (α * β * α⁻¹ * β⁻¹)
    have hexistsR :
        ∃ (R : GroupProgram (Equiv.Perm (Fin 5)) m),
          R.length = 2 * (P.length + Q.length) ∧
          α_computes (α * β * α⁻¹ * β⁻¹) R (λ x => f1 x ∧ f2 x) :=
      and_computable α β hαcycle hβcycle f1 f2 P Q hα_computes hβ_computes
    obtain ⟨R, hRLength, hComputes⟩ := hexistsR
    use R
    constructor
    · sorry
    constructor
    · have h := add_le_add hPLength hQLength
      rw [← two_mul] at h
      rw [hRLength]
      have h1 : 2 * (P.length + Q.length) ≤ 2 * (2 * 4 ^ (d - 1)) :=
        by exact Nat.mul_le_mul_left 2 h
      rw [← Nat.mul_assoc 2 2 (4 ^ (d - 1))] at h1
      simp at h1
      rw [mul_comm 4 (4 ^ (d - 1))] at h1
      rw [← Nat.pow_succ 4 (d - 1)] at h1
      rw [← Nat.pred_eq_sub_one] at h1
      have h_one_le_d := Nat.le_of_add_right_le hφd
      apply Nat.lt_of_succ_le at h_one_le_d
      rw [Nat.succ_pred_eq_of_pos h_one_le_d] at h1
      exact h1
    · rw [α_computes] at hComputes
      rw [α_computes]
      have f1_and_f2_eq_f : ∀ (x : Input m), (f1 x ∧ f2 x) = f x := sorry
      intro x
      have hx := hComputes x
      have hfx := f1_and_f2_eq_f x
      rw [hx]
      have hdec : decide (f1 x = true ∧ f2 x = true) = decide (f x = true) :=
        Bool.decide_congr (iff_of_eq hfx)
      rw [hdec]
      simp
