import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.Algebra.Group.Conj
import BarringtonTheorem.GroupPrograms
import BarringtonTheorem.Formula
import Mathlib.Data.Fin.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Tactic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.FinCases
import Mathlib.GroupTheory.Perm.Basic

open BarringtonTheorem

variable {n m : ℕ} [hn : NeZero n] [hm : NeZero m]

def computes_with {G : Type} [Group G] (α : G)
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
    (hcomputes_with : computes_with α P f) :
    ∃ (Q : GroupProgram (Equiv.Perm (Fin n)) m),
      Q.length = P.length ∧ computes_with β Q f := by
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
    have h1 := evalProgram_conjugate P γ x
    rw [SemiconjBy] at hγ
    rw [computes_with] at hcomputes_with
    rw [hcomputes_with x]
    by_cases f x
    case pos hpos =>
      rw [hpos]
      simp
      rw [hγ]
      rw [mul_inv_cancel_right β ↑γ]
    case neg hneg =>
      simp [hneg]

lemma not_computable
    (α : Equiv.Perm (Fin n))
    (P : GroupProgram (Equiv.Perm (Fin n)) m)
    (f : Input m → Bool)
    (hα_cycle : Equiv.Perm.IsCycle α)
    (hαcomputes : computes_with α P f) :
    ∃ (Q : GroupProgram (Equiv.Perm (Fin n)) m),
      Q.length = P.length ∧ computes_with α Q (λ x => ¬ f x) := by
  have hαinv_cycle : Equiv.Perm.IsCycle α⁻¹ := Equiv.Perm.IsCycle.inv hα_cycle
  have α_card_eq_α_inv_card : α.support.card = α⁻¹.support.card := by simp
  have hαinvcomputes := computable_for_conj_cycles α α⁻¹ P f hα_cycle hαinv_cycle α_card_eq_α_inv_card hαcomputes
  obtain ⟨Q, hQLen, hQcomputes⟩ := hαinvcomputes
  let R : GroupProgram (Equiv.Perm (Fin n)) m := Q.map
   (λ t =>
   if t.i = Fin.ofNat m 0 then
      {
        i := t.i
        g₀ := α * t.g₀
        g₁ := α * t.g₁
      }
      else t)
  use R
  constructor
  . simp [R, List.length_map]
    exact hQLen
  . rw [computes_with]
    intro x
    by_cases f x
    case pos hpos =>
      simp [hpos]
      simp [R]
      rw [computes_with] at hQcomputes
      rw [evalProgram]
      sorry
    sorry

lemma and_computable
    (α β : Equiv.Perm (Fin n))
    (hα : Equiv.Perm.IsCycle α)
    (hβ : Equiv.Perm.IsCycle β)
    (f : Input m → Bool)
    (g : Input m → Bool)
    (P : GroupProgram (Equiv.Perm (Fin n)) m)
    (Q : GroupProgram (Equiv.Perm (Fin n)) m)
    (hcomputes_with : computes_with α P f)
    (hβ_computes : computes_with β Q g) :
    ∃ (R : GroupProgram (Equiv.Perm (Fin n)) m),
      R.length = 2 * (P.length + Q.length) ∧
      computes_with (α * β * α⁻¹ * β⁻¹) R (λ x => f x ∧ g x) := by
  sorry

lemma product_cycles_conjugate_cycle :
    ∃ (α β : Equiv.Perm (Fin 5)),
      Equiv.Perm.IsCycle α ∧
      α.support.card = 5 ∧
      Equiv.Perm.IsCycle β ∧
      β.support.card = 5 ∧
      Equiv.Perm.IsCycle (α * β * α⁻¹ * β⁻¹) ∧
      (α * β * α⁻¹ * β⁻¹).support.card = 5 := by
  -- Define two explicit 5-cycles α = (0 1 2 3 4) and β = (0 2 4 3 1)
  let α : Equiv.Perm (Fin 5) :=
    (Equiv.swap 0 4) * (Equiv.swap 0 3) * (Equiv.swap 0 2) * (Equiv.swap 0 1)
  let β : Equiv.Perm (Fin 5) :=
    (Equiv.swap 0 1) * (Equiv.swap 0 3) * (Equiv.swap 0 4) *(Equiv.swap 0 2)
  -- The commutator of the two 5-cycles is equal to (0 3 2 4 1)
  have hαβ : α * β * α⁻¹ * β⁻¹ = (Equiv.swap 0 1) * (Equiv.swap 0 4) * (Equiv.swap 0 2) * (Equiv.swap 0 3) := by decide
  refine ⟨α, β, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- IsCycle α
  . use 0
    constructor
    . trivial -- α 0 ≠ 0
    -- ∀ y ∈ (Fin 5), SameCycle 0 y in α
    . intro y hy
      fin_cases y
      . use 0; trivial -- (α ^ 0) 0 = 0
      . use 1; trivial -- (α ^ 1) 0 = 1
      . use 2; trivial -- (α ^ 2) 0 = 2
      . use 3; trivial -- (α ^ 3) 0 = 3
      . use 4; trivial -- (α ^ 4) 0 = 4
  -- α.support.card = 5
  . decide
  -- IsCycle β
  . use 0
    constructor
    . trivial
    . intro y hy
      fin_cases y
      . use 0; trivial -- (β ^ 0) 0 = 0
      . use 4; trivial -- (β ^ 4) 0 = 1
      . use 1; trivial -- (β ^ 1) 0 = 2
      . use 3; trivial -- (β ^ 3) 0 = 3
      . use 2; trivial -- (β ^ 2) 0 = 4
  -- β.support.card = 5
  . decide
  -- IsCycle (α * β * α⁻¹ * β⁻¹)
  . rw [hαβ]
    . use 0
      constructor
      . trivial
      . intro y hy;
        fin_cases y
        . use 0; trivial -- ((α * β * α⁻¹ β⁻¹) ^ 0) 0 = 0
        . use 4; trivial -- ((α * β * α⁻¹ β⁻¹) ^ 4) 0 = 1
        . use 2; trivial -- ((α * β * α⁻¹ β⁻¹) ^ 2) 0 = 2
        . use 1; trivial -- ((α * β * α⁻¹ β⁻¹) ^ 1) 0 = 3
        . use 3; trivial -- ((α * β * α⁻¹ β⁻¹) ^ 3) 0 = 4
  -- (α * β * α⁻¹ * β⁻¹).support.card = 5
  . decide

def example_perm1 : Equiv.Perm (Fin 5) :=
  (Equiv.swap 0 1) *
  (Equiv.swap 0 3) *
  (Equiv.swap 0 4) *
  (Equiv.swap 0 2)

def example_perm2 : Equiv.Perm (Fin 5) :=
  (Equiv.swap 0 4) *
  (Equiv.swap 0 3) *
  (Equiv.swap 0 2) *
  (Equiv.swap 0 1)

def example_perm : Equiv.Perm (Fin 5) :=
  example_perm2 * example_perm1 * example_perm2⁻¹ * example_perm1⁻¹

#eval example_perm 0
#eval example_perm 1
#eval example_perm 2
#eval example_perm 3
#eval example_perm 4

theorem barrington_theorem
    (f : Input m → Bool)
    (hfcomputed : computed_by_formula f d) :
    ∀ (α : Equiv.Perm (Fin 5)), Equiv.Perm.IsCycle α → α.support.card = 5 → ∃ (P : GroupProgram (Equiv.Perm (Fin 5)) m),
      P.length ≤ 4 ^ d ∧
      computes_with α P f := by
  obtain ⟨φ, hφd, hφf⟩ := hfcomputed
  induction φ generalizing f d
  case var a =>
    intro α hαcycle hαsupport
    simp [Formula.eval] at hφf
    let P : GroupProgram (Equiv.Perm (Fin 5)) m :=
      [{i := a, g₀ := 1, g₁ := α}]
    refine ⟨P, ?_, ?_⟩
    · exact Nat.one_le_pow d 4 (by linarith)
    · intro x; simp [P, evalProgram, evalTriple, hφf]
  case not F F_ih =>
    rw [Formula.depth] at hφd
    simp [Formula.eval] at hφf
    have h0 : F.depth ≤ d := by
      rw [← Nat.succ_eq_one_add] at hφd
      exact Nat.le_of_succ_le hφd
    have h2 : ∀ (x : Input m), F.eval x = decide ¬f x = true := by
      simp
      exact hφf
    intro α hαcycle hαsupport
    have h1 :
        Equiv.Perm.IsCycle α → α.support.card = 5 → ∃ (P : GroupProgram (Equiv.Perm (Fin 5)) m),
          P.length ≤ 4 ^ d ∧ computes_with α P (λ x => ¬ f x) := by
      exact F_ih (λ x => ¬ f x) h0 h2 α
    have hαcycle' := hαcycle
    apply h1 at hαcycle
    apply hαcycle at hαsupport
    obtain ⟨P, hPlen, hcomputes_withP⟩ := hαsupport
    have hQ := not_computable α P (λ x => ¬ f x) hαcycle' hcomputes_withP
    simp at hQ
    obtain ⟨Q, hEqLen, hcomputes_withQ⟩ := hQ
    use Q
    constructor
    · rw [hEqLen]
      exact hPlen
    · exact hcomputes_withQ
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
    have hαβProdCycle := product_cycles_conjugate_cycle
    obtain ⟨α, β, hαcycle, hαsupport, hβcycle, hβsupport, hαβConjProd, hαβConjProdSupport⟩ := hαβProdCycle
    have h1 := hF1 f1 hf1depth_le_d hf1computable α
    have h2 := hF2 f2 hf2depth_le_d hf2computable β
    have hαcycle' := hαcycle
    have hαsupport' := hαsupport
    have hβcycle' := hβcycle
    have hβsupport' := hβsupport
    apply h1 at hαcycle'
    apply hαcycle' at hαsupport'
    apply h2 at hβcycle'
    apply hβcycle' at hβsupport'
    obtain ⟨P, hPLength, hcomputesf1⟩ := hαsupport'
    obtain ⟨Q, hQLength, hcomputesf2⟩ := hβsupport'
    have hexistsR :
        ∃ (R : GroupProgram (Equiv.Perm (Fin 5)) m),
          R.length = 2 * (P.length + Q.length) ∧
          computes_with (α * β * α⁻¹ * β⁻¹) R (λ x => f1 x ∧ f2 x) :=
          and_computable α β hαcycle hβcycle f1 f2 P Q hcomputesf1 hcomputesf2
    obtain ⟨R, hRLength, hComputes⟩ := hexistsR
    have existsαP :
      ∃ (α : Equiv.Perm (Fin 5)),
      α.IsCycle ∧ α.support.card = 5 ∧ ∃ P,
      List.length P ≤ 4 ^ d ∧ computes_with α P f := by
      use (α * β * α⁻¹ * β⁻¹)
      constructor
      . exact hαβConjProd
      . constructor
        . exact hαβConjProdSupport
        . use R
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
          · rw [computes_with] at hComputes
            rw [computes_with]
            have f1_and_f2_eq_f : ∀ (x : Input m), (f1 x ∧ f2 x) = f x := by
              intro x
              have h := hφf x
              rw [← h]
              simp [f1, f2]
              rw [Formula.eval]
              simp
            intro x
            have hx := hComputes x
            have hfx := f1_and_f2_eq_f x
            rw [hx]
            have hdec : decide (f1 x = true ∧ f2 x = true) = decide (f x = true) :=
              Bool.decide_congr (iff_of_eq hfx)
            rw [hdec]
            simp
    intro γ hγcycle hγsupport
    obtain ⟨δ, hδCycle, hδSupport, S, hSlen, hSComputes⟩ := existsαP
    have δ_card_eq_γ_card : δ.support.card = γ.support.card := by
      rw [hδSupport, hγsupport]
    have hCompγ := @computable_for_conj_cycles 5 m (by infer_instance) (hm) δ γ S f hδCycle hγcycle δ_card_eq_γ_card hSComputes
    obtain ⟨T, hTlen, hTcomputes⟩ := hCompγ
    use T
    rw [hTlen]
    exact And.intro hSlen hTcomputes
