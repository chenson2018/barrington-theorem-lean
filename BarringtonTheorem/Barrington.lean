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
  rcases computable_for_conj_cycles α α⁻¹ P f hα_cycle (Equiv.Perm.IsCycle.inv hα_cycle) (by simp) hαcomputes with ⟨Q, hQLen, hQcomputes⟩
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
  -- ∀ y ∈ (Fin 5), SameCycle 0 y in β
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
      -- ∀ y ∈ (Fin 5), SameCycle 0 y in (α * β * α⁻¹ * β⁻¹)
      . intro y hy;
        fin_cases y
        . use 0; trivial -- ((α * β * α⁻¹ β⁻¹) ^ 0) 0 = 0
        . use 4; trivial -- ((α * β * α⁻¹ β⁻¹) ^ 4) 0 = 1
        . use 2; trivial -- ((α * β * α⁻¹ β⁻¹) ^ 2) 0 = 2
        . use 1; trivial -- ((α * β * α⁻¹ β⁻¹) ^ 1) 0 = 3
        . use 3; trivial -- ((α * β * α⁻¹ β⁻¹) ^ 3) 0 = 4
  -- (α * β * α⁻¹ * β⁻¹).support.card = 5
  . decide

lemma nat_le_sub_one_of_max_le_left (n m k : ℕ) (h_one_add_max_le : 1 + max n m ≤ k) : n ≤ k - 1 := by
  have zero_lt_k : 0 < k := Nat.lt_of_succ_le (Nat.le_of_add_right_le h_one_add_max_le)
  have hn_lt_k : n < k := lt_of_le_of_lt (le_max_left n m) (Nat.one_add_le_iff.mp h_one_add_max_le)
  exact (Nat.le_sub_one_iff_lt zero_lt_k).mpr hn_lt_k

lemma nat_le_sub_one_of_max_le_right (n m k : ℕ) (h_one_add_max_le : 1 + max n m ≤ k) : m ≤ k - 1 := by
  have zero_lt_k : 0 < k := Nat.lt_of_succ_le (Nat.le_of_add_right_le h_one_add_max_le)
  have h_m_lt_k : m < k := lt_of_le_of_lt (le_max_right n m) (Nat.one_add_le_iff.mp h_one_add_max_le)
  exact (Nat.le_sub_one_iff_lt zero_lt_k).mpr h_m_lt_k

lemma two_mul_add_le_pow_succ_of_le_pow_pred
 (n m k d f1 f2 : ℕ) (hn : n ≤ 4 ^ (d - 1))
 (hm : m ≤ 4 ^ (d - 1)) (hk : k = 2 * (n + m))
 (h_one_add_max_le_d : 1 + max f1 f2 ≤ d) : k ≤ 4 ^ d := by
  have h1 := add_le_add hn hm
  rw [← two_mul] at h1
  rw [hk]
  have h2 : 2 * (n + m) ≤ 2 * (2 * 4 ^ (d - 1)) :=
    by exact Nat.mul_le_mul_left 2 h1
  rw [← Nat.mul_assoc 2 2 (4 ^ (d - 1))] at h2
  simp at h2
  rw [mul_comm 4 (4 ^ (d - 1)), ← Nat.pow_succ 4 (d - 1), ← Nat.pred_eq_sub_one] at h2
  rw [Nat.succ_pred_eq_of_pos (Nat.lt_of_succ_le (Nat.le_of_add_right_le h_one_add_max_le_d))] at h2
  exact h2

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
    unfold Formula.depth at hφd
    have hF_le : F.depth ≤ d := by
      rw [← Nat.succ_eq_one_add] at hφd
      exact Nat.le_of_succ_le hφd
    simp [Formula.eval] at hφf
    have hF_eval_eq : ∀ (x : Input m), F.eval x = decide ¬f x = true := by
      simp [hφf]
    have ih := F_ih (λ x => ¬ f x) hF_le hF_eval_eq
    intro α hαcycle hαsupport
    rcases ih α hαcycle hαsupport with ⟨P, hPlen, hcomputes_withP⟩
    rcases not_computable α P (λ x => ¬ f x) hαcycle hcomputes_withP with
      ⟨Q, hEqLen, hcomputes_withQ⟩
    use Q
    constructor
    · rw [hEqLen]; exact hPlen
    · simp at hcomputes_withQ
      exact hcomputes_withQ

  case and F1 F2 hF1 hF2 =>
    let f1 : Input m → Bool := λ x => F1.eval x
    let f2 : Input m → Bool := λ x => F2.eval x
    unfold Formula.depth at hφd
    have hf1depth_le_d : F1.depth ≤ d - 1 :=
      nat_le_sub_one_of_max_le_left F1.depth F2.depth d hφd
    have hf2depth_le_d : F2.depth ≤ d - 1 :=
      nat_le_sub_one_of_max_le_right F1.depth F2.depth d hφd
    rcases product_cycles_conjugate_cycle with ⟨α, β, hαcycle, hαsupport, hβcycle, hβsupport, hαβConjProd, hαβConjProdSupport⟩
    rcases (hF1 f1 hf1depth_le_d (by simp [f1]) α) hαcycle hαsupport with ⟨P, hPLength, hcomputesf1⟩
    rcases (hF2 f2 hf2depth_le_d (by simp [f2]) β) hβcycle hβsupport with ⟨Q, hQLength, hcomputesf2⟩
    rcases and_computable α β hαcycle hβcycle f1 f2 P Q hcomputesf1 hcomputesf2 with ⟨R, hRLength, hComputes⟩
    have existsαP :
      ∃ (α : Equiv.Perm (Fin 5)),
      α.IsCycle ∧ α.support.card = 5 ∧ ∃ P,
      List.length P ≤ 4 ^ d ∧ computes_with α P f := by
      refine ⟨(α * β * α⁻¹ * β⁻¹), hαβConjProd, hαβConjProdSupport, ?_⟩
      . use R
        constructor
        · exact two_mul_add_le_pow_succ_of_le_pow_pred P.length Q.length R.length d F1.depth F2.depth hPLength hQLength hRLength hφd
        · rw [computes_with] at hComputes
          have f1_and_f2_eq_f : ∀ (x : Input m), (f1 x ∧ f2 x) = f x := by
            intro x
            rw [← hφf x]
            simp [f1, f2, Formula.eval]
          intro x
          simp [hComputes x, Bool.decide_congr (iff_of_eq (f1_and_f2_eq_f x))]
    intro γ hγcycle hγsupport
    rcases existsαP with ⟨δ, hδCycle, hδSupport, S, hSlen, hSComputes⟩
    rcases @computable_for_conj_cycles 5 m (by infer_instance) (hm) δ γ S f hδCycle hγcycle (by rw [hδSupport, hγsupport]) hSComputes with ⟨T, hTlen, hTcomputes⟩
    use T
    rw [hTlen]
    exact And.intro hSlen hTcomputes
