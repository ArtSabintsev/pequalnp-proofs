import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_608_aux

private lemma poly_add_pow_two_pow (p q : Polynomial (ZMod 2)) :
    ∀ k : ℕ, (p + q) ^ (2 ^ k) = p ^ (2 ^ k) + q ^ (2 ^ k) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have hpow : 2 ^ (k + 1) = 2 ^ k * 2 := by ring
    rw [hpow, pow_mul, pow_mul, pow_mul, ih]
    have hsq : ∀ a b : Polynomial (ZMod 2), (a + b) ^ 2 = a ^ 2 + b ^ 2 := by
      intro a b
      have hself : ∀ r : Polynomial (ZMod 2), r + r = 0 := by
        intro r
        ext n
        simp only [Polynomial.coeff_add, Polynomial.coeff_zero]
        generalize r.coeff n = c
        fin_cases c <;> decide
      calc
        (a + b) ^ 2 = a ^ 2 + (a * b + a * b) + b ^ 2 := by ring
        _ = a ^ 2 + 0 + b ^ 2 := by rw [hself (a * b)]
        _ = a ^ 2 + b ^ 2 := by ring
    exact hsq _ _

private lemma coeff_X_add_one_pow (z : ℕ) :
    ∀ k : ℕ, ((Polynomial.X + 1 : Polynomial (ZMod 2)) ^ z).coeff k =
      ((Nat.choose z k : ℕ) : ZMod 2) := by
  induction z with
  | zero =>
    intro k
    cases k with
    | zero => simp [Polynomial.coeff_one]
    | succ k => simp [Polynomial.coeff_one]
  | succ z ih =>
    intro k
    rw [pow_succ, mul_add, mul_one, Polynomial.coeff_add]
    cases k with
    | zero =>
      rw [Polynomial.coeff_mul_X_zero, zero_add, ih 0]
      simp
    | succ k =>
      rw [Polynomial.coeff_mul_X, ih k, ih (k + 1), Nat.choose_succ_succ, Nat.cast_add]

private lemma choose_two_pow_mod_two (z k : ℕ) (hz : z < 2 * 2 ^ k) :
    Nat.choose z (2 ^ k) % 2 = 1 ↔ 2 ^ k ≤ z := by
  by_cases hle : 2 ^ k ≤ z
  · suffices h : Nat.choose z (2 ^ k) % 2 = 1 by simp [hle, h]
    set q := z - 2 ^ k
    have hz_eq : z = 2 ^ k + q := by omega
    have hq_lt : q < 2 ^ k := by omega
    have hpoly :
        ((Polynomial.X + 1 : Polynomial (ZMod 2)) ^ z) =
          (Polynomial.X ^ (2 ^ k) + 1) * (Polynomial.X + 1) ^ q := by
      rw [hz_eq, pow_add, poly_add_pow_two_pow, one_pow]
    have hcoeff_lhs :
        ((Polynomial.X + 1 : Polynomial (ZMod 2)) ^ z).coeff (2 ^ k) =
          ((Nat.choose z (2 ^ k) : ℕ) : ZMod 2) :=
      coeff_X_add_one_pow z (2 ^ k)
    have hcoeff_rhs :
        ((Polynomial.X ^ (2 ^ k) + 1 : Polynomial (ZMod 2)) * (Polynomial.X + 1) ^ q).coeff (2 ^ k) =
          1 := by
      rw [add_mul, one_mul, Polynomial.coeff_add, Polynomial.coeff_X_pow_mul']
      simp only [le_refl, ↓reduceIte, Nat.sub_self]
      have h0 : ((Polynomial.X + 1 : Polynomial (ZMod 2)) ^ q).coeff 0 = 1 := by
        rw [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_pow, Polynomial.eval_add,
          Polynomial.eval_X, Polynomial.eval_one, zero_add, one_pow]
      have hhi : ((Polynomial.X + 1 : Polynomial (ZMod 2)) ^ q).coeff (2 ^ k) = 0 := by
        apply Polynomial.coeff_eq_zero_of_natDegree_lt
        have hdeg1 : (Polynomial.X + 1 : Polynomial (ZMod 2)).natDegree ≤ 1 := by
          compute_degree!
        calc
          ((Polynomial.X + 1 : Polynomial (ZMod 2)) ^ q).natDegree
              ≤ q * (Polynomial.X + 1 : Polynomial (ZMod 2)).natDegree := Polynomial.natDegree_pow_le
          _ ≤ q * 1 := Nat.mul_le_mul_left q hdeg1
          _ < 2 ^ k := by omega
      rw [h0, hhi, add_zero]
    have hzmod : ((Nat.choose z (2 ^ k) : ℕ) : ZMod 2) = 1 := by
      rw [← hcoeff_lhs, hpoly, hcoeff_rhs]
    have hcast : ((Nat.choose z (2 ^ k) % 2 : ℕ) : ZMod 2) = 1 := by
      simpa [ZMod.natCast_mod] using hzmod
    have hlt : Nat.choose z (2 ^ k) % 2 < 2 := Nat.mod_lt _ (by decide)
    interval_cases h : Nat.choose z (2 ^ k) % 2
    · exact absurd hcast (by decide)
    · rfl
  · have h0 : Nat.choose z (2 ^ k) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp [hle, h0]

private lemma testBit_add_shift_lt (a l j : ℕ) (b : Bool) (hjl : j < l) :
    (a + (b.toNat <<< l)).testBit j = a.testBit j := by
  rw [Nat.shiftLeft_eq]
  cases b
  · simp
  · simp only [Bool.toNat_true, one_mul]
    rw [Nat.testBit, Nat.testBit]
    have hpow : 2 ^ l = 2 ^ j * 2 ^ (l - j) := by
      rw [← pow_add, Nat.add_sub_of_le (le_of_lt hjl)]
    have hdiv : (a + 2 ^ l) / 2 ^ j = a / 2 ^ j + 2 ^ (l - j) := by
      rw [hpow, Nat.add_mul_div_left _ _ (Nat.two_pow_pos j)]
    have hshift : (a + 2 ^ l) >>> j = (a >>> j) + 2 ^ (l - j) := by
      simpa [Nat.shiftRight_eq_div_pow] using hdiv
    rw [hshift]
    have heven : 2 ∣ 2 ^ (l - j) := by
      have hpos : 1 ≤ l - j := by omega
      rw [show l - j = (l - j - 1) + 1 by omega, pow_succ]
      exact dvd_mul_left 2 _
    rcases heven with ⟨t, ht⟩
    rw [ht]
    simp [Nat.and_one_is_mod]

private lemma testBit_add_shift_eq (a l : ℕ) (b : Bool) (ha : a < 2 ^ l) :
    (a + (b.toNat <<< l)).testBit l = b := by
  rw [Nat.shiftLeft_eq]
  rw [Nat.testBit]
  have hdiv : (a + b.toNat * 2 ^ l) / 2 ^ l = b.toNat := by
    rw [Nat.add_mul_div_right _ _ (Nat.two_pow_pos l), Nat.div_eq_of_lt ha, zero_add]
  have hshift : (a + b.toNat * 2 ^ l) >>> l = b.toNat := by
    simpa [Nat.shiftRight_eq_div_pow] using hdiv
  rw [hshift]
  cases b <;> decide

private def monEval {α : Type} (mon : Finset α) (x : α → Bool) : ZMod 2 :=
  if ∀ p ∈ mon, x p = true then 1 else 0

private lemma monEval_union {α : Type} [DecidableEq α] (A B : Finset α) (x : α → Bool) :
    monEval (A ∪ B) x = monEval A x * monEval B x := by
  unfold monEval
  by_cases hA : ∀ p ∈ A, x p = true <;> by_cases hB : ∀ p ∈ B, x p = true
  · have hAB : ∀ p ∈ A ∪ B, x p = true := by
      intro p hp
      rcases Finset.mem_union.mp hp with hpA | hpB
      · exact hA p hpA
      · exact hB p hpB
    rw [if_pos hAB, if_pos hA, if_pos hB, mul_one]
  · have hAB : ¬ ∀ p ∈ A ∪ B, x p = true := fun h => hB (fun p hp => h p (Finset.mem_union_right A hp))
    rw [if_neg hAB, if_pos hA, if_neg hB, mul_zero]
  · have hAB : ¬ ∀ p ∈ A ∪ B, x p = true := fun h => hA (fun p hp => h p (Finset.mem_union_left B hp))
    rw [if_neg hAB, if_neg hA, if_pos hB, zero_mul]
  · have hAB : ¬ ∀ p ∈ A ∪ B, x p = true := fun h => hA (fun p hp => h p (Finset.mem_union_left B hp))
    rw [if_neg hAB, if_neg hA, if_neg hB, zero_mul]

private lemma monEval_singleton {α : Type} (p : α) (x : α → Bool) :
    monEval {p} x = if x p = true then 1 else 0 := by
  unfold monEval
  simp

private lemma monEval_empty {α : Type} (x : α → Bool) :
    monEval (∅ : Finset α) x = 1 := by
  unfold monEval
  simp

private lemma prod_monEval_singleton {α : Type} [DecidableEq α] (S : Finset α) (x : α → Bool) :
    (∏ p ∈ S, monEval {p} x) = monEval S x := by
  induction S using Finset.induction with
  | empty => simp [monEval_empty]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, ih, ← Finset.singleton_union, monEval_union]

private lemma eval_terms_par {α : Type} [DecidableEq α]
    (terms : Finset (Finset α)) (x : α → Bool) :
    (((terms.filter (fun mon => ∀ p ∈ mon, x p = true)).card % 2 == 1) : Bool) =
      decide ((∑ mon ∈ terms, monEval mon x) = 1) := by
  have hsum : (∑ mon ∈ terms, monEval mon x) =
      (((terms.filter (fun mon => ∀ p ∈ mon, x p = true)).card : ℕ) : ZMod 2) := by
    unfold monEval
    rw [Finset.sum_boole]
  rw [hsum]
  have hcast :
      (((terms.filter (fun mon => ∀ p ∈ mon, x p = true)).card : ℕ) : ZMod 2) =
      ((((terms.filter (fun mon => ∀ p ∈ mon, x p = true)).card % 2) : ℕ) : ZMod 2) := by
    rw [ZMod.natCast_mod]
  rw [hcast]
  have hlt : (terms.filter (fun mon => ∀ p ∈ mon, x p = true)).card % 2 < 2 := Nat.mod_lt _ (by decide)
  generalize (terms.filter (fun mon => ∀ p ∈ mon, x p = true)).card % 2 = c at hlt ⊢
  interval_cases c <;> decide

private lemma deg_of_sum_families {α : Type} [DecidableEq α] {ι : Type}
    (u : ℕ) (A : Finset ι) (M : ι → Finset (Finset α))
    (hdeg : ∀ a ∈ A, ∀ mon ∈ M a, mon.card ≤ u)
    (f : (α → Bool) → Bool)
    (hf : ∀ x, f x = decide ((∑ a ∈ A, ∑ mon ∈ M a, monEval mon x) = 1)) :
    ∃ terms : Finset (Finset α), (∀ mon ∈ terms, mon.card ≤ u) ∧
      ∀ x, f x = (((terms.filter (fun mon => ∀ p ∈ mon, x p = true)).card % 2 == 1) : Bool) := by
  let allMon : Finset (Finset α) := A.biUnion M
  let coeff : Finset α → ZMod 2 := fun mon => ∑ a ∈ A, if mon ∈ M a then 1 else 0
  let terms : Finset (Finset α) := allMon.filter (fun mon => coeff mon = 1)
  refine ⟨terms, ?_, ?_⟩
  · intro mon hmon
    rcases Finset.mem_biUnion.mp (Finset.mem_filter.mp hmon).1 with ⟨a, ha, hma⟩
    exact hdeg a ha mon hma
  · intro x
    rw [hf x, eval_terms_par]
    suffices hsum :
        (∑ a ∈ A, ∑ mon ∈ M a, monEval mon x) = ∑ mon ∈ terms, monEval mon x by
      rw [hsum]
    have hinner : ∀ a ∈ A,
        (∑ mon ∈ M a, monEval mon x) =
          ∑ mon ∈ allMon, (if mon ∈ M a then (1 : ZMod 2) else 0) * monEval mon x := by
      intro a ha
      have hrhs :
          (∑ mon ∈ allMon, (if mon ∈ M a then (1 : ZMod 2) else 0) * monEval mon x) =
            ∑ mon ∈ allMon, if mon ∈ M a then monEval mon x else 0 := by
        refine Finset.sum_congr rfl fun mon _ => ?_
        by_cases hm : mon ∈ M a
        · simp [hm]
        · simp [hm]
      rw [hrhs, ← Finset.sum_filter]
      have hsub : allMon.filter (fun mon => mon ∈ M a) = M a := by
        ext mon
        simp only [allMon, Finset.mem_filter, Finset.mem_biUnion]
        constructor
        · exact fun h => h.2
        · intro hm; exact ⟨⟨a, ha, hm⟩, hm⟩
      rw [hsub]
    calc
      (∑ a ∈ A, ∑ mon ∈ M a, monEval mon x)
          = ∑ a ∈ A, ∑ mon ∈ allMon, (if mon ∈ M a then (1 : ZMod 2) else 0) * monEval mon x :=
            Finset.sum_congr rfl hinner
      _ = ∑ mon ∈ allMon, ∑ a ∈ A, (if mon ∈ M a then (1 : ZMod 2) else 0) * monEval mon x :=
            Finset.sum_comm
      _ = ∑ mon ∈ allMon, coeff mon * monEval mon x := by
            refine Finset.sum_congr rfl fun mon _ => ?_
            rw [← Finset.sum_mul]
      _ = ∑ mon ∈ terms, monEval mon x := by
            rw [Finset.sum_filter]
            refine Finset.sum_congr rfl fun mon _ => ?_
            have hc : coeff mon = 0 ∨ coeff mon = 1 := by
              generalize coeff mon = z
              fin_cases z
              · left; rfl
              · right; rfl
            rcases hc with h0 | h1
            · simp [h0]
            · simp [h1]

private def litTarget (pos path : ℕ) (j : ℕ) : Bool :=
  if j < pos then path.testBit j else false

private lemma indicator_block_expand {g m r : ℕ} (grp : Fin g) (pos path : ℕ) (hpos : pos < r)
    (S : Finset (Fin m)) (x : (Fin g × Fin m × Fin r) → Bool) :
    let cols : Finset (Fin r) := Finset.univ.filter (fun j : Fin r => j.val ≤ pos)
    let dom : Finset (Fin g × Fin m × Fin r) := ({grp} : Finset (Fin g)) ×ˢ (S ×ˢ cols)
    let posL : Finset (Fin g × Fin m × Fin r) := dom.filter (fun p => litTarget pos path p.2.2.val = true)
    let negL : Finset (Fin g × Fin m × Fin r) := dom.filter (fun p => litTarget pos path p.2.2.val = false)
    (if ∀ i ∈ S, (∀ j : Fin r, j.val < pos → x (grp, i, j) = path.testBit j.val) ∧
        x (grp, i, ⟨pos, hpos⟩) = false then (1 : ZMod 2) else 0) =
      ∑ mon ∈ negL.powerset.image (fun T => posL ∪ T), monEval mon x := by
  intro cols dom posL negL
  have hcond_iff :
      (∀ i ∈ S, (∀ j : Fin r, j.val < pos → x (grp, i, j) = path.testBit j.val) ∧
          x (grp, i, ⟨pos, hpos⟩) = false) ↔
      (∀ p ∈ dom, x p = litTarget pos path p.2.2.val) := by
    constructor
    · intro h p hp
      rcases Finset.mem_product.mp hp with ⟨hg, hip⟩
      have hge : p.1 = grp := Finset.mem_singleton.mp hg
      rcases Finset.mem_product.mp hip with ⟨hi, hj⟩
      have hjle : p.2.2.val ≤ pos := (Finset.mem_filter.mp hj).2
      unfold litTarget
      by_cases hlt : p.2.2.val < pos
      · simp only [hlt, ↓reduceIte]
        have h1 := (h p.2.1 hi).1 p.2.2 hlt
        cases p with
        | mk p1 p2 =>
          cases p2 with
          | mk p21 p22 =>
            dsimp only at hge h1 ⊢
            subst hge
            exact h1
      · simp only [hlt, ↓reduceIte]
        have hpeq : p.2.2 = ⟨pos, hpos⟩ := Fin.ext (by dsimp; omega)
        have h2 := (h p.2.1 hi).2
        cases p with
        | mk p1 p2 =>
          cases p2 with
          | mk p21 p22 =>
            dsimp only at hge hpeq h2 ⊢
            subst hge
            subst hpeq
            exact h2
    · intro h i hi
      refine ⟨fun j hj => ?_, ?_⟩
      · have hmem : (grp, i, j) ∈ dom :=
          Finset.mem_product.mpr ⟨Finset.mem_singleton_self grp,
            Finset.mem_product.mpr ⟨hi, Finset.mem_filter.mpr ⟨Finset.mem_univ j, le_of_lt hj⟩⟩⟩
        have := h (grp, i, j) hmem
        unfold litTarget at this
        simpa [hj] using this
      · have hmem : (grp, i, (⟨pos, hpos⟩ : Fin r)) ∈ dom :=
          Finset.mem_product.mpr ⟨Finset.mem_singleton_self grp,
            Finset.mem_product.mpr ⟨hi, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl⟩⟩⟩
        have := h (grp, i, ⟨pos, hpos⟩) hmem
        unfold litTarget at this
        simpa using this
  have hprod :
      (if ∀ p ∈ dom, x p = litTarget pos path p.2.2.val then (1 : ZMod 2) else 0) =
        ∏ p ∈ dom, (if x p = litTarget pos path p.2.2.val then (1 : ZMod 2) else 0) := by
    by_cases hall : ∀ p ∈ dom, x p = litTarget pos path p.2.2.val
    · rw [if_pos hall]
      symm
      exact Finset.prod_eq_one fun p hp => by rw [if_pos (hall p hp)]
    · rw [if_neg hall]
      push_neg at hall
      rcases hall with ⟨p, hp, hne⟩
      symm
      exact Finset.prod_eq_zero hp (by rw [if_neg hne])
  have hpart : dom = posL ∪ negL := by
    ext p
    simp only [posL, negL, Finset.mem_union, Finset.mem_filter]
    cases litTarget pos path p.2.2.val <;> simp
  have hdisj : Disjoint posL negL := by
    rw [Finset.disjoint_left]
    intro p h1 h2
    have a1 := (Finset.mem_filter.mp h1).2
    have a2 := (Finset.mem_filter.mp h2).2
    rw [a1] at a2
    cases a2
  have hprod_split :
      (∏ p ∈ dom, (if x p = litTarget pos path p.2.2.val then (1 : ZMod 2) else 0)) =
        (∏ p ∈ posL, monEval {p} x) * (∏ p ∈ negL, (1 + monEval {p} x)) := by
    rw [hpart, Finset.prod_union hdisj]
    congr 1
    · refine Finset.prod_congr rfl fun p hp => ?_
      have ht : litTarget pos path p.2.2.val = true := (Finset.mem_filter.mp hp).2
      rw [ht, monEval_singleton]
    · refine Finset.prod_congr rfl fun p hp => ?_
      have hf : litTarget pos path p.2.2.val = false := (Finset.mem_filter.mp hp).2
      rw [hf, monEval_singleton]
      cases x p <;> decide
  have hneg_expand :
      (∏ p ∈ negL, (1 + monEval {p} x)) = ∑ T ∈ negL.powerset, monEval T x := by
    rw [Finset.prod_one_add]
    refine Finset.sum_congr rfl fun T _ => prod_monEval_singleton T x
  have hinj : Set.InjOn (fun T => posL ∪ T) (↑negL.powerset : Set (Finset (Fin g × Fin m × Fin r))) := by
    intro T1 hT1 T2 hT2 heq
    dsimp only at heq
    have h1 : T1 ⊆ negL := Finset.mem_powerset.mp hT1
    have h2 : T2 ⊆ negL := Finset.mem_powerset.mp hT2
    have hd1 : Disjoint posL T1 := Disjoint.mono_right h1 hdisj
    have hd2 : Disjoint posL T2 := Disjoint.mono_right h2 hdisj
    ext p
    constructor
    · intro hp
      have : p ∈ posL ∪ T2 := by rw [← heq]; exact Finset.mem_union_right posL hp
      rcases Finset.mem_union.mp this with hpP | hp2
      · exfalso; exact Finset.disjoint_left.mp hd1 hpP hp
      · exact hp2
    · intro hp
      have : p ∈ posL ∪ T1 := by rw [heq]; exact Finset.mem_union_right posL hp
      rcases Finset.mem_union.mp this with hpP | hp1
      · exfalso; exact Finset.disjoint_left.mp hd2 hpP hp
      · exact hp1
  rw [if_congr hcond_iff rfl rfl, hprod, hprod_split, prod_monEval_singleton, hneg_expand,
    Finset.mul_sum, Finset.sum_image hinj]
  refine Finset.sum_congr rfl fun T _ => (monEval_union posL T x).symm

private def skipVal {M : ℕ} (c : Fin M) (i : Fin (M - 1)) : Fin M :=
  ⟨if i.val < c.val then i.val else i.val + 1, by
    have hc := c.isLt
    have hi := i.isLt
    split_ifs <;> omega⟩

private lemma skipVal_ne {M : ℕ} (c : Fin M) (i : Fin (M - 1)) : skipVal c i ≠ c := by
  intro h
  have hv := congrArg Fin.val h
  dsimp only [skipVal] at hv
  split_ifs at hv <;> omega

private lemma exists_skipVal_eq {M : ℕ} (c y : Fin M) (hne : y ≠ c) :
    ∃ i : Fin (M - 1), skipVal c i = y := by
  have hval : y.val ≠ c.val := fun h => hne (Fin.ext h)
  by_cases hlt : y.val < c.val
  · refine ⟨⟨y.val, by have := c.isLt; omega⟩, ?_⟩
    apply Fin.ext
    dsimp only [skipVal]
    simp [hlt]
  · refine ⟨⟨y.val - 1, by have := y.isLt; omega⟩, ?_⟩
    apply Fin.ext
    dsimp only [skipVal]
    have hnot : ¬ y.val - 1 < c.val := by omega
    simp only [hnot, ↓reduceIte]
    omega

private lemma runN_step {α : Type} (ask : ℕ → ℕ → α → Bool) (x : α) (s : ℕ) :
    (List.range (s + 1)).foldl (fun h pos => h + ((ask pos h x).toNat <<< pos)) 0 =
      (List.range s).foldl (fun h pos => h + ((ask pos h x).toNat <<< pos)) 0 +
        ((ask s ((List.range s).foldl (fun h pos => h + ((ask pos h x).toNat <<< pos)) 0) x).toNat <<< s) := by
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

private lemma runN_lt {α : Type} (ask : ℕ → ℕ → α → Bool) (x : α) (s : ℕ) :
    (List.range s).foldl (fun h pos => h + ((ask pos h x).toNat <<< pos)) 0 < 2 ^ s := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [runN_step, Nat.shiftLeft_eq]
    set prev := (List.range s).foldl (fun h pos => h + ((ask pos h x).toNat <<< pos)) 0
    have hb : (ask s prev x).toNat ≤ 1 := by cases ask s prev x <;> decide
    have hpow : 2 ^ (s + 1) = 2 ^ s + 2 ^ s := by ring
    have hmul : (ask s prev x).toNat * 2 ^ s ≤ 2 ^ s := by
      calc
        (ask s prev x).toNat * 2 ^ s ≤ 1 * 2 ^ s := Nat.mul_le_mul_right _ hb
        _ = 2 ^ s := one_mul _
    omega

private lemma runN_testBit_prefix {α : Type} (ask : ℕ → ℕ → α → Bool) (x : α)
    (k1 k2 p : ℕ) (hpk : p < k1) (hle : k1 ≤ k2) :
    ((List.range k2).foldl (fun h pos => h + ((ask pos h x).toNat <<< pos)) 0).testBit p =
      ((List.range k1).foldl (fun h pos => h + ((ask pos h x).toNat <<< pos)) 0).testBit p := by
  induction k2 with
  | zero => omega
  | succ k2 ih =>
    by_cases hEq : k1 = k2 + 1
    · subst hEq; rfl
    · have hle' : k1 ≤ k2 := by omega
      rw [runN_step, testBit_add_shift_lt _ _ _ _ (by omega)]
      exact ih hle'

private lemma sum_zmod2_eq_zero_of_invol {α : Type} [Fintype α]
    (f : α → ZMod 2) (τ : α → α)
    (hinv : ∀ a, τ (τ a) = a) (hfix : ∀ a, τ a ≠ a) (hpres : ∀ a, f (τ a) = f a) :
    (∑ a : α, f a) = 0 := by
  classical
  have hself : ∀ z : ZMod 2, z + z = 0 := by
    intro z; fin_cases z <;> decide
  have hbij : ∀ s : Finset α, (∀ a ∈ s, τ a ∈ s) → (∑ a ∈ s, f a) = 0 := by
    intro s
    induction hcard : s.card using Nat.strong_induction_on generalizing s with
    | ind n ih =>
      intro hclosed
      by_cases hemp : s = ∅
      · subst hemp; simp
      · obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hemp
        have hta : τ a ∈ s := hclosed a ha
        have hne : τ a ≠ a := hfix a
        let s' := (s.erase a).erase (τ a)
        have ha_mem : a ∈ s.erase (τ a) := Finset.mem_erase.mpr ⟨hne.symm, ha⟩
        have hs_eq : s = insert a (insert (τ a) s') := by
          ext b
          simp only [s', Finset.mem_insert, Finset.mem_erase]
          by_cases hba : b = a
          · subst hba; simp [ha]
          · by_cases hbta : b = τ a
            · subst hbta; simp [hta, hba]
            · simp [hba, hbta]
        have hnot1 : a ∉ insert (τ a) s' := by
          simp only [s', Finset.mem_insert, Finset.mem_erase]
          tauto
        have hnot2 : τ a ∉ s' := by
          simp [s']
        have hs'_closed : ∀ b ∈ s', τ b ∈ s' := by
          intro b hb
          simp only [s', Finset.mem_erase] at hb ⊢
          refine ⟨?_, ?_, hclosed b hb.2.2⟩
          · intro h
            have := congrArg τ h
            rw [hinv, hinv] at this
            exact hb.2.1 this
          · intro h
            have := congrArg τ h
            rw [hinv] at this
            exact hb.1 this
        have hcard_lt : s'.card < n := by
          rw [← hcard, hs_eq, Finset.card_insert_of_notMem hnot1, Finset.card_insert_of_notMem hnot2]
          omega
        rw [hs_eq, Finset.sum_insert hnot1, Finset.sum_insert hnot2, hpres a,
          ih s'.card hcard_lt s' rfl hs'_closed, add_zero, hself]
  exact hbij Finset.univ (fun a _ => Finset.mem_univ (τ a))

private lemma exists_line_step {g M : ℕ} (f : (Fin g → Fin M) → Bool)
    (y0 y1 : Fin g → Fin M) (hne : f y0 ≠ f y1) :
    ∃ (j0 : Fin g) (bg : Fin g → Fin M) (c0 c1 : Fin M),
      f (Function.update bg j0 c0) ≠ f (Function.update bg j0 c1) := by
  let hyb : ℕ → (Fin g → Fin M) := fun k j => if j.val < k then y1 j else y0 j
  have h0 : hyb 0 = y0 := by funext j; simp [hyb]
  have hg : hyb g = y1 := by funext j; simp [hyb, j.isLt]
  have hex : ∀ k, k ≤ g → f (hyb 0) ≠ f (hyb k) →
      ∃ i, i < k ∧ f (hyb i) ≠ f (hyb (i + 1)) := by
    intro k
    induction k with
    | zero => intro _ h; exact absurd rfl h
    | succ k ih =>
      intro hk hne'
      by_cases hmid : f (hyb k) = f (hyb (k + 1))
      · obtain ⟨i, hi, hstep⟩ := ih (by omega) (by rwa [hmid])
        exact ⟨i, by omega, hstep⟩
      · exact ⟨k, Nat.lt_succ_self k, hmid⟩
  obtain ⟨i, hi, hstep⟩ := hex g le_rfl (by rwa [h0, hg])
  let j0 : Fin g := ⟨i, hi⟩
  refine ⟨j0, hyb i, y0 j0, y1 j0, ?_⟩
  have hupd0 : Function.update (hyb i) j0 (y0 j0) = hyb i := by
    funext j
    by_cases h : j = j0
    · subst h; simp [hyb, j0]
    · simp [Function.update, h]
  have hupd1 : Function.update (hyb i) j0 (y1 j0) = hyb (i + 1) := by
    funext j
    by_cases h : j = j0
    · subst h; simp [hyb, j0]
    · simp only [Function.update, h, ↓reduceDIte, hyb]
      have hjne : j.val ≠ i := fun hv => h (Fin.ext hv)
      by_cases hlt : j.val < i
      · have hlt2 : j.val < i + 1 := by omega
        simp [hlt, hlt2]
      · have hlt2 : ¬ j.val < i + 1 := by omega
        simp [hlt, hlt2]
  rw [hupd0, hupd1]
  exact hstep

end PEqualNP.Outside.L_lib_608_aux

theorem PEqualNP.Outside.L_lib_608 : (∀ (g a : Nat), 0 < g → 0 < a →
  let M := 2^a
  let m := M-1
  let d := g*a
  let V := Fin g × Fin m × Fin a
  let W := V → Bool
  let deg := fun (b : Nat) (f : W → Bool) =>
    ∃ terms : Finset (Finset V), (∀ mon ∈ terms, mon.card ≤ b) ∧
      ∀ input, f input = (((terms.filter (fun mon => ∀ j ∈ mon, input j = true)).card % 2) == 1)
  let Y := Fin g → Fin M
  let valid := fun (x : W) (choice : Y) =>
    ∀ j i, ∃ v : Fin a, x (j,i,v) ≠ (choice j).val.testBit v.val
  let run := fun (ask : Nat → Nat → W → Bool) (x : W) =>
    (List.range d).foldl (fun h pos => h + ((ask pos h x).toNat <<< pos)) 0
  (∃ (choose : Nat → Nat → W → Bool) (decode : Nat → Y),
    (∀ (u : Fin d) (h : Nat),
      deg ((u.val % a + 1) * 2 ^ (a - 1 - u.val % a)) (choose u.val h)) ∧
    ∀ input, valid input (decode (run choose input))) ∧
  (∀ (n : Nat) (choose : Nat → Nat → W → Bool) (decode : Nat → Y),
    (∀ input, valid input (decode ((List.range n).foldl (fun trace tick =>
      trace + ((choose tick trace input).toNat <<< tick)) 0))) → d ≤ n) ∧
  ∀ (ask : Fin d → W → Bool) (report : (Fin d → Bool) → Y)
    (label : Fin g → Fin m → Fin M → Fin a → Bool),
    (∀ x j i, (fun rawBit => x (j,i,rawBit)) ≠ label j i (report (fun u => ask u x) j)) →
    ∀ (mask : Finset (Fin d)), mask.Nonempty → ∀ b : Nat,
      deg b (fun word => (((mask.filter (fun bitId => ask bitId word = true)).card % 2) == 1)) →
      2^(a-1) ≤ b) := by
  intro g a hg ha M m d V W deg Y valid run
  have hM_pos : 0 < M := Nat.two_pow_pos a
  have hm_lt : m < 2 ^ a := by dsimp only [m, M]; omega
  refine ⟨?_, ?_, ?_⟩
  · let choose : ℕ → ℕ → W → Bool := fun pos h x =>
      if hpos : pos < d then
        let grp : Fin g := ⟨pos / a, Nat.div_lt_of_lt_mul (by dsimp only [d] at hpos; rw [mul_comm]; exact hpos)⟩
        let loc : ℕ := pos % a
        have hloc : loc < a := Nat.mod_lt pos ha
        let path : ℕ := h >>> (grp.val * a)
        let Z : Finset (Fin m) := (Finset.univ : Finset (Fin m)).filter (fun i =>
          (∀ j : Fin a, j.val < loc → x (grp, i, j) = path.testBit j.val) ∧
          x (grp, i, ⟨loc, hloc⟩) = false)
        decide (Nat.choose Z.card (2 ^ (a - 1 - loc)) % 2 = 1)
      else false
    let decode : ℕ → Y := fun t j =>
      ⟨(t >>> (j.val * a)) % M, Nat.mod_lt _ hM_pos⟩
    refine ⟨choose, decode, ?_, ?_⟩
    · intro u h
      have hu : u.val < d := u.isLt
      let grp : Fin g := ⟨u.val / a, Nat.div_lt_of_lt_mul (by dsimp only [d] at hu; rw [mul_comm]; exact hu)⟩
      let loc : ℕ := u.val % a
      have hloc : loc < a := Nat.mod_lt u.val ha
      let path : ℕ := h >>> (grp.val * a)
      let K : ℕ := 2 ^ (a - 1 - loc)
      let A : Finset (Finset (Fin m)) := (Finset.univ : Finset (Fin m)).powersetCard K
      let cols : Finset (Fin a) := Finset.univ.filter (fun j : Fin a => j.val ≤ loc)
      have hcols_card : cols.card = loc + 1 := by
        have heq : cols = (Finset.range (loc + 1)).attach.image
            (fun t => (⟨t.1, by have := Finset.mem_range.mp t.2; omega⟩ : Fin a)) := by
          ext j
          simp only [cols, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
            Finset.mem_attach, Subtype.exists, Finset.mem_range]
          constructor
          · intro hj
            exact ⟨j.val, by omega, Fin.ext rfl⟩
          · rintro ⟨w, hw, rfl⟩
            dsimp only
            omega
        rw [heq, Finset.card_image_of_injective]
        · simp
        · intro x1 x2 hx
          apply Subtype.ext
          exact congrArg Fin.val hx
      let Mfam : Finset (Fin m) → Finset (Finset V) := fun S =>
        let dom : Finset V := ({grp} : Finset (Fin g)) ×ˢ (S ×ˢ cols)
        let posL : Finset V := dom.filter (fun p => PEqualNP.Outside.L_lib_608_aux.litTarget loc path p.2.2.val = true)
        let negL : Finset V := dom.filter (fun p => PEqualNP.Outside.L_lib_608_aux.litTarget loc path p.2.2.val = false)
        negL.powerset.image (fun T => posL ∪ T)
      dsimp only [deg, W]
      have hres := PEqualNP.Outside.L_lib_608_aux.deg_of_sum_families ((loc + 1) * K) A Mfam ?_ (choose u.val h) ?_
      · rcases hres with ⟨terms, hdeg, heval⟩
        exact ⟨terms, hdeg, fun input => by convert heval input⟩
      · intro S hS mon hmon
        have hScard : S.card = K := (Finset.mem_powersetCard.mp hS).2
        dsimp only [Mfam] at hmon
        rcases Finset.mem_image.mp hmon with ⟨T, hT, rfl⟩
        have hsub :
            (({grp} : Finset (Fin g)) ×ˢ (S ×ˢ cols)).filter
                (fun p => PEqualNP.Outside.L_lib_608_aux.litTarget loc path p.2.2.val = true) ∪ T ⊆
              ({grp} : Finset (Fin g)) ×ˢ (S ×ˢ cols) := by
          refine Finset.union_subset (Finset.filter_subset _ _) ?_
          exact Finset.Subset.trans (Finset.mem_powerset.mp hT) (Finset.filter_subset _ _)
        calc
          ((({grp} : Finset (Fin g)) ×ˢ (S ×ˢ cols)).filter
              (fun p => PEqualNP.Outside.L_lib_608_aux.litTarget loc path p.2.2.val = true) ∪ T).card
              ≤ (({grp} : Finset (Fin g)) ×ˢ (S ×ˢ cols)).card := Finset.card_le_card hsub
          _ = 1 * (S.card * cols.card) := by
            rw [Finset.card_product, Finset.card_singleton, Finset.card_product]
          _ = (loc + 1) * K := by rw [one_mul, hScard, hcols_card, mul_comm]
      · intro x
        dsimp only [choose]
        rw [dif_pos hu]
        let Z : Finset (Fin m) := (Finset.univ : Finset (Fin m)).filter (fun i =>
          (∀ j : Fin a, j.val < loc → x (grp, i, j) = path.testBit j.val) ∧
          x (grp, i, ⟨loc, hloc⟩) = false)
        have hsum_eq :
            (∑ S ∈ A, ∑ mon ∈ Mfam S, PEqualNP.Outside.L_lib_608_aux.monEval mon x) =
              ((Nat.choose Z.card K : ℕ) : ZMod 2) := by
          have hstep : ∀ S ∈ A,
              (∑ mon ∈ Mfam S, PEqualNP.Outside.L_lib_608_aux.monEval mon x) =
                if S ⊆ Z then (1 : ZMod 2) else 0 := by
            intro S _
            rw [← PEqualNP.Outside.L_lib_608_aux.indicator_block_expand grp loc path hloc S x]
            refine if_congr ?_ rfl rfl
            constructor
            · intro h1 i hi
              exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, h1 i hi⟩
            · intro h1 i hi
              exact (Finset.mem_filter.mp (h1 hi)).2
          rw [Finset.sum_congr rfl hstep, Finset.sum_boole]
          congr 1
          have hflt : A.filter (fun S => S ⊆ Z) = Z.powersetCard K := by
            ext S
            simp only [A, Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and]
            tauto
          rw [hflt, Finset.card_powersetCard]
        rw [hsum_eq]
        have hcast : ((Nat.choose Z.card K : ℕ) : ZMod 2) =
            (((Nat.choose Z.card K % 2) : ℕ) : ZMod 2) := by
          rw [ZMod.natCast_mod]
        rw [hcast]
        have hlt : Nat.choose Z.card K % 2 < 2 := Nat.mod_lt _ (by decide)
        generalize Nat.choose Z.card K % 2 = c at hlt ⊢
        interval_cases c <;> decide
    · intro input j i
      let tr : ℕ → ℕ := fun s =>
        (List.range s).foldl (fun h pos => h + ((choose pos h input).toNat <<< pos)) 0
      have hinv : ∀ l : ℕ, l ≤ a →
          ((Finset.univ : Finset (Fin m)).filter (fun r =>
            ∀ v : Fin a, v.val < l →
              input (j, r, v) = (tr (j.val * a + l)).testBit (j.val * a + v.val))).card < 2 ^ (a - l) := by
        intro l
        induction l with
        | zero =>
          intro _
          simp only [Nat.sub_zero]
          calc
            ((Finset.univ : Finset (Fin m)).filter (fun r =>
                ∀ v : Fin a, v.val < 0 →
                  input (j, r, v) = (tr (j.val * a + 0)).testBit (j.val * a + v.val))).card
                ≤ (Finset.univ : Finset (Fin m)).card := Finset.card_le_card (Finset.filter_subset _ _)
            _ = m := by simp
            _ < 2 ^ a := hm_lt
        | succ l ih =>
          intro hl
          have hl_lt : l < a := by omega
          have hprev := ih (by omega)
          let pos := j.val * a + l
          have hpos_lt : pos < d := by
            have hj := j.isLt
            dsimp only [pos, d]
            calc
              j.val * a + l < j.val * a + a := Nat.add_lt_add_left hl_lt _
              _ = (j.val + 1) * a := by ring
              _ ≤ g * a := Nat.mul_le_mul_right a hj
          set prev := tr pos
          set bit := choose pos prev input
          set next := tr (pos + 1)
          have hnext_eq : next = prev + (bit.toNat <<< pos) :=
            PEqualNP.Outside.L_lib_608_aux.runN_step choose input pos
          have hprev_lt : prev < 2 ^ pos :=
            PEqualNP.Outside.L_lib_608_aux.runN_lt choose input pos
          have hpos_div : pos / a = j.val := by
            dsimp only [pos]
            rw [mul_comm j.val a, Nat.mul_add_div ha, Nat.div_eq_of_lt hl_lt, add_zero]
          have hpos_mod : pos % a = l := by
            dsimp only [pos]
            rw [mul_comm j.val a, Nat.mul_add_mod, Nat.mod_eq_of_lt hl_lt]
          let Ml : Finset (Fin m) := (Finset.univ : Finset (Fin m)).filter (fun r =>
            ∀ v : Fin a, v.val < l → input (j, r, v) = prev.testBit (j.val * a + v.val))
          let M0 : Finset (Fin m) := Ml.filter (fun r => input (j, r, ⟨l, hl_lt⟩) = false)
          let M1 : Finset (Fin m) := Ml.filter (fun r => input (j, r, ⟨l, hl_lt⟩) = true)
          have hM_split : M0.card + M1.card = Ml.card := by
            rw [← Finset.card_union_of_disjoint]
            · congr 1
              ext r
              simp only [M0, M1, Finset.mem_union, Finset.mem_filter]
              cases input (j, r, ⟨l, hl_lt⟩) <;> simp
            · rw [Finset.disjoint_left]
              intro r h0 h1
              have a0 := (Finset.mem_filter.mp h0).2
              have a1 := (Finset.mem_filter.mp h1).2
              rw [a0] at a1; cases a1
          have hpow_split : 2 ^ (a - l) = 2 * 2 ^ (a - (l + 1)) := by
            rw [show a - l = (a - (l + 1)) + 1 by omega, pow_succ]
            ring
          have hMl_lt : Ml.card < 2 * 2 ^ (a - (l + 1)) := by
            rw [← hpow_split]; exact hprev
          have hM0_lt : M0.card < 2 * 2 ^ (a - (l + 1)) := by omega
          have hM0_eq_Z : M0 = (Finset.univ : Finset (Fin m)).filter (fun r =>
              (∀ v : Fin a, v.val < pos % a →
                input (⟨pos / a, Nat.div_lt_of_lt_mul (by dsimp only [d] at hpos_lt; rw [mul_comm]; exact hpos_lt)⟩, r, v) =
                  (prev >>> ((pos / a) * a)).testBit v.val) ∧
              input (⟨pos / a, Nat.div_lt_of_lt_mul (by dsimp only [d] at hpos_lt; rw [mul_comm]; exact hpos_lt)⟩, r,
                ⟨pos % a, Nat.mod_lt pos ha⟩) = false) := by
            ext r
            simp only [M0, Ml, Finset.mem_filter, Finset.mem_univ, true_and]
            have hgrp : (⟨pos / a, Nat.div_lt_of_lt_mul (by dsimp only [d] at hpos_lt; rw [mul_comm]; exact hpos_lt)⟩ : Fin g) = j :=
              Fin.ext hpos_div
            have hloc_fin : (⟨pos % a, Nat.mod_lt pos ha⟩ : Fin a) = ⟨l, hl_lt⟩ := Fin.ext hpos_mod
            rw [hgrp, hloc_fin, hpos_div, hpos_mod]
            constructor
            · rintro ⟨h1, h2⟩
              refine ⟨fun v hv => ?_, h2⟩
              rw [Nat.testBit_shiftRight]
              exact h1 v hv
            · rintro ⟨h1, h2⟩
              refine ⟨fun v hv => ?_, h2⟩
              have := h1 v hv
              rwa [Nat.testBit_shiftRight] at this
          have hbit_iff : bit = true ↔ 2 ^ (a - (l + 1)) ≤ M0.card := by
            have hbit_def : bit = decide (Nat.choose M0.card (2 ^ (a - 1 - l)) % 2 = 1) := by
              dsimp only [bit, choose]
              rw [dif_pos hpos_lt]
              rw [← hM0_eq_Z, hpos_mod]
            rw [hbit_def, decide_eq_true_eq]
            have hexp : a - 1 - l = a - (l + 1) := by omega
            rw [hexp]
            exact PEqualNP.Outside.L_lib_608_aux.choose_two_pow_mod_two M0.card (a - (l + 1)) hM0_lt
          have hnext_set :
              (Finset.univ : Finset (Fin m)).filter (fun r =>
                ∀ v : Fin a, v.val < l + 1 →
                  input (j, r, v) = next.testBit (j.val * a + v.val)) =
              if bit = true then M1 else M0 := by
            ext r
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            have hlt_bit : ∀ v : Fin a, v.val < l →
                next.testBit (j.val * a + v.val) = prev.testBit (j.val * a + v.val) :=
              fun v hv => by
                rw [hnext_eq]
                exact PEqualNP.Outside.L_lib_608_aux.testBit_add_shift_lt prev pos (j.val * a + v.val) bit (by dsimp [pos]; omega)
            have heq_bit : next.testBit pos = bit := by
              rw [hnext_eq]; exact PEqualNP.Outside.L_lib_608_aux.testBit_add_shift_eq prev pos bit hprev_lt
            cases hb : bit
            · simp only [Bool.false_eq_true, ↓reduceIte, M0, Ml, Finset.mem_filter, Finset.mem_univ, true_and]
              constructor
              · intro h1
                refine ⟨fun v hv => ?_, ?_⟩
                · rw [← hlt_bit v hv]; exact h1 v (by omega)
                · have := h1 ⟨l, hl_lt⟩ (Nat.lt_succ_self l)
                  dsimp only at this
                  rwa [show j.val * a + l = pos from rfl, heq_bit, hb] at this
              · rintro ⟨h1, h2⟩ v hv
                by_cases hvl : v.val < l
                · rw [hlt_bit v hvl]; exact h1 v hvl
                · have hv_eq : v = ⟨l, hl_lt⟩ := Fin.ext (by dsimp; omega)
                  rw [hv_eq]; dsimp only
                  rw [show j.val * a + l = pos from rfl, heq_bit, hb]; exact h2
            · simp only [↓reduceIte, M1, Ml, Finset.mem_filter, Finset.mem_univ, true_and]
              constructor
              · intro h1
                refine ⟨fun v hv => ?_, ?_⟩
                · rw [← hlt_bit v hv]; exact h1 v (by omega)
                · have := h1 ⟨l, hl_lt⟩ (Nat.lt_succ_self l)
                  dsimp only at this
                  rwa [show j.val * a + l = pos from rfl, heq_bit, hb] at this
              · rintro ⟨h1, h2⟩ v hv
                by_cases hvl : v.val < l
                · rw [hlt_bit v hvl]; exact h1 v hvl
                · have hv_eq : v = ⟨l, hl_lt⟩ := Fin.ext (by dsimp; omega)
                  rw [hv_eq]; dsimp only
                  rw [show j.val * a + l = pos from rfl, heq_bit, hb]; exact h2
          have hpos_succ : j.val * a + (l + 1) = pos + 1 := by dsimp [pos]; omega
          rw [hpos_succ]
          change ((Finset.univ : Finset (Fin m)).filter (fun r =>
            ∀ v : Fin a, v.val < l + 1 → input (j, r, v) = next.testBit (j.val * a + v.val))).card < 2 ^ (a - (l + 1))
          rw [hnext_set]
          cases hb : bit
          · simp only [Bool.false_eq_true, ↓reduceIte]
            have hnot : ¬ 2 ^ (a - (l + 1)) ≤ M0.card := by
              intro hle
              have := hbit_iff.mpr hle
              rw [hb] at this; cases this
            omega
          · simp only [↓reduceIte]
            have hle : 2 ^ (a - (l + 1)) ≤ M0.card := hbit_iff.mp hb
            omega
      have hcard0 : ((Finset.univ : Finset (Fin m)).filter (fun r =>
          ∀ v : Fin a, v.val < a →
            input (j, r, v) = (tr (j.val * a + a)).testBit (j.val * a + v.val))).card = 0 := by
        have hlt := hinv a le_rfl
        simp only [Nat.sub_self, pow_zero] at hlt
        omega
      have hnot_all : ¬ ∀ v : Fin a, input (j, i, v) = (decode (run choose input) j).val.testBit v.val := by
        intro hall
        have hmem : i ∈ (Finset.univ : Finset (Fin m)).filter (fun r =>
            ∀ v : Fin a, v.val < a →
              input (j, r, v) = (tr (j.val * a + a)).testBit (j.val * a + v.val)) := by
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ i, fun v _ => ?_⟩
          rw [hall v]
          dsimp only [decode]
          rw [Nat.testBit_mod_two_pow, decide_eq_true v.isLt, Bool.true_and, Nat.testBit_shiftRight]
          have hle_d : j.val * a + a ≤ d := by
            have hj := j.isLt
            dsimp only [d]
            calc
              j.val * a + a = (j.val + 1) * a := by ring
              _ ≤ g * a := Nat.mul_le_mul_right a hj
          exact PEqualNP.Outside.L_lib_608_aux.runN_testBit_prefix choose input
            (j.val * a + a) d (j.val * a + v.val) (by have := v.isLt; omega) hle_d
        have hpos_card : 0 < ((Finset.univ : Finset (Fin m)).filter (fun r =>
            ∀ v : Fin a, v.val < a →
              input (j, r, v) = (tr (j.val * a + a)).testBit (j.val * a + v.val))).card :=
          Finset.card_pos.mpr ⟨i, hmem⟩
        omega
      push_neg at hnot_all
      exact hnot_all
  · intro n choose decode hvalid
    let gmap : Fin (2 ^ n) → Y := fun t => decode t.val
    have hsurj : Function.Surjective gmap := by
      intro choice
      let x : W := fun p => (PEqualNP.Outside.L_lib_608_aux.skipVal (choice p.1) p.2.1).val.testBit p.2.2.val
      let tval : ℕ := (List.range n).foldl (fun trace tick => trace + ((choose tick trace x).toNat <<< tick)) 0
      have htlt : tval < 2 ^ n := PEqualNP.Outside.L_lib_608_aux.runN_lt choose x n
      refine ⟨⟨tval, htlt⟩, ?_⟩
      funext j
      by_contra hne
      obtain ⟨i, hi⟩ := PEqualNP.Outside.L_lib_608_aux.exists_skipVal_eq (choice j) (gmap ⟨tval, htlt⟩ j) hne
      obtain ⟨v, hv⟩ := hvalid x j i
      dsimp only [x] at hv
      rw [hi] at hv
      exact hv rfl
    have hcard : Fintype.card Y ≤ Fintype.card (Fin (2 ^ n)) :=
      Fintype.card_le_of_surjective gmap hsurj
    have hYcard : Fintype.card Y = 2 ^ d := by
      dsimp only [Y, M, d]
      rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, ← pow_mul, mul_comm]
    rw [hYcard, Fintype.card_fin] at hcard
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hcard
  · intro ask report label havoid mask hmask b hdeg
    have hsurj : Function.Surjective report := by
      intro choice
      let x : W := fun p => label p.1 p.2.1 (PEqualNP.Outside.L_lib_608_aux.skipVal (choice p.1) p.2.1) p.2.2
      refine ⟨fun u => ask u x, ?_⟩
      funext j
      by_contra hne
      obtain ⟨i, hi⟩ := PEqualNP.Outside.L_lib_608_aux.exists_skipVal_eq (choice j) (report (fun u => ask u x) j) hne
      have hne_fn := havoid x j i
      apply hne_fn
      funext v
      dsimp only [x]
      rw [hi]
    have hcard_eq : Fintype.card (Fin d → Bool) = Fintype.card Y := by
      dsimp only [Y, M, d]
      rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
        Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, ← pow_mul, mul_comm]
    have hbij : Function.Bijective report :=
      (Fintype.bijective_iff_surjective_and_card report).mpr ⟨hsurj, hcard_eq⟩
    let erep : (Fin d → Bool) ≃ Y := Equiv.ofBijective report hbij
    let parT : (Fin d → Bool) → Bool := fun t =>
      (((mask.filter (fun bitId => t bitId = true)).card % 2) == 1)
    let parY : Y → Bool := fun y => parT (erep.symm y)
    have hpar_eq : ∀ x : W, parT (fun u => ask u x) = parY (report (fun u => ask u x)) := by
      intro x
      dsimp only [parY]
      have hinv : erep.symm (report (fun u => ask u x)) = (fun u => ask u x) :=
        erep.symm_apply_apply (fun u => ask u x)
      rw [hinv]
    obtain ⟨u0, hu0⟩ := hmask
    let t0 : Fin d → Bool := fun _ => false
    let t1 : Fin d → Bool := fun u => decide (u = u0)
    have hpar0 : parT t0 = false := by
      dsimp only [parT, t0]
      have hemp : mask.filter (fun _ => false = true) = ∅ := by
        ext u; simp
      rw [hemp]; simp
    have hpar1 : parT t1 = true := by
      dsimp only [parT, t1]
      have hsing : mask.filter (fun u => decide (u = u0) = true) = {u0} := by
        ext u
        simp only [Finset.mem_filter, decide_eq_true_eq, Finset.mem_singleton]
        constructor
        · exact fun h => h.2
        · rintro rfl; exact ⟨hu0, rfl⟩
      rw [hsing]; simp
    have hnonconst : parY (erep t0) ≠ parY (erep t1) := by
      dsimp only [parY]
      rw [erep.symm_apply_apply, erep.symm_apply_apply, hpar0, hpar1]
      decide
    obtain ⟨j0, bg, c0, c1, hline⟩ :=
      PEqualNP.Outside.L_lib_608_aux.exists_line_step parY (erep t0) (erep t1) hnonconst
    let g1 : Fin M → Bool := fun c => parY (Function.update bg j0 c)
    let Strue : Finset (Fin M) := Finset.univ.filter (fun c => g1 c = true)
    let Sfalse : Finset (Fin M) := Finset.univ.filter (fun c => g1 c = false)
    have hStf : Strue.card + Sfalse.card = M := by
      rw [← Finset.card_union_of_disjoint]
      · have hunion : Strue ∪ Sfalse = Finset.univ := by
          ext c
          simp only [Strue, Sfalse, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
          cases g1 c <;> simp
        rw [hunion, Finset.card_univ, Fintype.card_fin]
      · rw [Finset.disjoint_left]
        intro c h1 h2
        have a1 := (Finset.mem_filter.mp h1).2
        have a2 := (Finset.mem_filter.mp h2).2
        rw [a1] at a2; cases a2
    have hStrue_ne : Strue.Nonempty := by
      cases hc0 : g1 c0
      · cases hc1 : g1 c1
        · exact absurd (hc0.trans hc1.symm) hline
        · exact ⟨c1, Finset.mem_filter.mpr ⟨Finset.mem_univ c1, hc1⟩⟩
      · exact ⟨c0, Finset.mem_filter.mpr ⟨Finset.mem_univ c0, hc0⟩⟩
    have hSfalse_ne : Sfalse.Nonempty := by
      cases hc0 : g1 c0
      · exact ⟨c0, Finset.mem_filter.mpr ⟨Finset.mem_univ c0, hc0⟩⟩
      · cases hc1 : g1 c1
        · exact ⟨c1, Finset.mem_filter.mpr ⟨Finset.mem_univ c1, hc1⟩⟩
        · exact absurd (hc0.trans hc1.symm) hline
    have hM_split : M = 2 * 2 ^ (a - 1) := by
      dsimp only [M]
      conv_lhs => rw [show a = (a - 1) + 1 by omega, pow_succ]
      ring
    have hex_cut : ∃ (targetBool : Bool) (T : Finset (Fin M)) (cstar : Fin M),
        2 ^ (a - 1) ≤ T.card ∧
        (∀ c : Fin M, c ∈ T ↔ g1 c = targetBool) ∧
        g1 cstar = !targetBool := by
      by_cases hge : 2 ^ (a - 1) ≤ Strue.card
      · obtain ⟨cs, hcs⟩ := hSfalse_ne
        exact ⟨true, Strue, cs, hge, fun c => by simp [Strue], (Finset.mem_filter.mp hcs).2⟩
      · obtain ⟨cs, hcs⟩ := hStrue_ne
        refine ⟨false, Sfalse, cs, by omega, fun c => by simp [Sfalse], ?_⟩
        simpa using (Finset.mem_filter.mp hcs).2
    obtain ⟨targetBool, T, cstar, hTcard, hTiff, hcstar⟩ := hex_cut
    have hcstar_notT : cstar ∉ T := by
      intro hmem
      have h1 := (hTiff cstar).mp hmem
      rw [hcstar] at h1
      cases targetBool <;> cases h1
    let embed : (T → Bool) → W := fun u p =>
      if p.1 = j0 then
        let y := PEqualNP.Outside.L_lib_608_aux.skipVal cstar p.2.1
        if hy : y ∈ T then
          if u ⟨y, hy⟩ then label j0 p.2.1 cstar p.2.2 else label j0 p.2.1 y p.2.2
        else
          label j0 p.2.1 y p.2.2
      else
        label p.1 p.2.1 (PEqualNP.Outside.L_lib_608_aux.skipVal (bg p.1) p.2.1) p.2.2
    have hrep_other : ∀ (u : T → Bool) (j : Fin g), j ≠ j0 →
        report (fun bitId => ask bitId (embed u)) j = bg j := by
      intro u j hj
      by_contra hne
      obtain ⟨i, hi⟩ := PEqualNP.Outside.L_lib_608_aux.exists_skipVal_eq (bg j) (report (fun bitId => ask bitId (embed u)) j) hne
      apply havoid (embed u) j i
      funext v
      dsimp only [embed]
      simp only [hj, ↓reduceIte]
      rw [hi]
    have hrep_eq : ∀ u : T → Bool,
        report (fun bitId => ask bitId (embed u)) =
          Function.update bg j0 (report (fun bitId => ask bitId (embed u)) j0) := by
      intro u
      funext j
      by_cases hj : j = j0
      · subst hj; simp
      · simp [Function.update, hj, hrep_other u j hj]
    have hout_zero : parT (fun bitId => ask bitId (embed (fun _ => false))) = !targetBool := by
      rw [hpar_eq, hrep_eq (fun _ => false)]
      change g1 (report (fun bitId => ask bitId (embed (fun _ => false))) j0) = !targetBool
      have hr_eq : report (fun bitId => ask bitId (embed (fun _ => false))) j0 = cstar := by
        by_contra hne
        obtain ⟨i, hi⟩ := PEqualNP.Outside.L_lib_608_aux.exists_skipVal_eq cstar
          (report (fun bitId => ask bitId (embed (fun _ => false))) j0) hne
        apply havoid (embed (fun _ => false)) j0 i
        funext v
        dsimp only [embed]
        simp only [↓reduceIte, Bool.false_eq_true, hi]
        split_ifs <;> rfl
      rw [hr_eq, hcstar]
    have hout_nz : ∀ u : T → Bool, u ≠ (fun _ => false) →
        parT (fun bitId => ask bitId (embed u)) = targetBool := by
      intro u hne_u
      rw [hpar_eq, hrep_eq u]
      change g1 (report (fun bitId => ask bitId (embed u)) j0) = targetBool
      rw [← hTiff]
      have hne_cstar : report (fun bitId => ask bitId (embed u)) j0 ≠ cstar := by
        have hex_true : ∃ z : T, u z = true := by
          by_contra hall
          push_neg at hall
          apply hne_u
          funext z
          cases hz : u z
          · rfl
          · exact absurd hz (hall z)
        obtain ⟨z, hz⟩ := hex_true
        have hzne : z.1 ≠ cstar := fun h => hcstar_notT (h ▸ z.2)
        obtain ⟨i0, hi0⟩ := PEqualNP.Outside.L_lib_608_aux.exists_skipVal_eq cstar z.1 hzne
        intro hrc
        apply havoid (embed u) j0 i0
        funext v
        dsimp only [embed]
        simp only [↓reduceIte]
        have hmem : PEqualNP.Outside.L_lib_608_aux.skipVal cstar i0 ∈ T := by
          rw [hi0]; exact z.2
        rw [dif_pos hmem]
        have hsub : (⟨PEqualNP.Outside.L_lib_608_aux.skipVal cstar i0, hmem⟩ : T) = z := Subtype.ext hi0
        rw [hsub, hz, hrc]
        simp
      by_contra hnotT
      obtain ⟨i, hi⟩ := PEqualNP.Outside.L_lib_608_aux.exists_skipVal_eq cstar
        (report (fun bitId => ask bitId (embed u)) j0) hne_cstar
      apply havoid (embed u) j0 i
      funext v
      dsimp only [embed]
      simp only [↓reduceIte]
      have hnot_mem : PEqualNP.Outside.L_lib_608_aux.skipVal cstar i ∉ T := by
        rw [hi]; exact hnotT
      rw [dif_neg hnot_mem, hi]
    rcases hdeg with ⟨terms, hdeg_le, heval⟩
    by_contra hlt_b
    have hb_lt : b < T.card := by omega
    have hTpos : 0 < T.card := lt_of_lt_of_le (Nat.two_pow_pos (a - 1)) hTcard
    have hsum_lhs : (∑ u : (T → Bool), if parT (fun bitId => ask bitId (embed u)) = true then (1 : ZMod 2) else 0) = 1 := by
      have hsplit : (∑ u : (T → Bool), if parT (fun bitId => ask bitId (embed u)) = true then (1 : ZMod 2) else 0) =
          (if parT (fun bitId => ask bitId (embed (fun _ => false))) = true then (1 : ZMod 2) else 0) +
          ∑ u ∈ Finset.univ.erase (fun _ : T => false),
            if parT (fun bitId => ask bitId (embed u)) = true then (1 : ZMod 2) else 0 := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (fun _ : T => false))]
      rw [hsplit, hout_zero]
      have hrest : (∑ u ∈ Finset.univ.erase (fun _ : T => false),
            if parT (fun bitId => ask bitId (embed u)) = true then (1 : ZMod 2) else 0) =
          ∑ _u ∈ Finset.univ.erase (fun _ : T => false),
            if targetBool = true then (1 : ZMod 2) else 0 := by
        refine Finset.sum_congr rfl fun u hu => ?_
        rw [hout_nz u (Finset.mem_erase.mp hu).1]
      rw [hrest, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _),
        Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_coe, nsmul_eq_mul]
      have heven : ((2 ^ T.card : ℕ) : ZMod 2) = 0 := by
        conv_lhs => rw [show T.card = (T.card - 1) + 1 by omega, pow_succ]
        have h20 : ((2 : ℕ) : ZMod 2) = 0 := by decide
        rw [Nat.cast_mul, h20, mul_zero]
      cases targetBool
      · simp
      · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, zero_add, mul_one]
        have hpos2 : 1 ≤ 2 ^ T.card := Nat.one_le_pow _ _ (by decide)
        rw [Nat.cast_sub hpos2, heven]
        decide
    have hsum_rhs : (∑ u : (T → Bool), if parT (fun bitId => ask bitId (embed u)) = true then (1 : ZMod 2) else 0) = 0 := by
      have hpt : ∀ u : (T → Bool),
          (if parT (fun bitId => ask bitId (embed u)) = true then (1 : ZMod 2) else 0) =
            ∑ mon ∈ terms, PEqualNP.Outside.L_lib_608_aux.monEval mon (embed u) := by
        intro u
        have h1 : parT (fun bitId => ask bitId (embed u)) =
            decide ((∑ mon ∈ terms, PEqualNP.Outside.L_lib_608_aux.monEval mon (embed u)) = 1) := by
          have h2 := heval (embed u)
          dsimp only [parT] at h2 ⊢
          rw [h2]
          convert PEqualNP.Outside.L_lib_608_aux.eval_terms_par terms (embed u)
        rw [h1]
        generalize ∑ mon ∈ terms, PEqualNP.Outside.L_lib_608_aux.monEval mon (embed u) = z
        revert z; decide
      rw [Finset.sum_congr rfl fun u _ => hpt u, Finset.sum_comm]
      refine Finset.sum_eq_zero fun mon hmon => ?_
      have hmon_lt : mon.card < T.card := lt_of_le_of_lt (hdeg_le mon hmon) hb_lt
      let varOf : V → Option T := fun p =>
        if p.1 = j0 then
          let y := PEqualNP.Outside.L_lib_608_aux.skipVal cstar p.2.1
          if hy : y ∈ T then some ⟨y, hy⟩ else none
        else none
      let used : Finset T := mon.biUnion (fun p => (varOf p).toFinset)
      have hused_card : used.card ≤ mon.card := by
        calc
          used.card ≤ ∑ p ∈ mon, ((varOf p).toFinset).card := Finset.card_biUnion_le
          _ ≤ ∑ _p ∈ mon, 1 := Finset.sum_le_sum fun p _ => by cases varOf p <;> simp
          _ = mon.card := by simp
      have hnot_univ : used ≠ Finset.univ := by
        intro hEq
        have hc := congrArg Finset.card hEq
        rw [Finset.card_univ, Fintype.card_coe] at hc
        omega
      have hex_free : ∃ z : T, z ∉ used := by
        by_contra hall
        push_neg at hall
        apply hnot_univ
        ext z
        simp [hall z]
      obtain ⟨zfree, hzfree⟩ := hex_free
      let τ : (T → Bool) → (T → Bool) := fun u => Function.update u zfree (!u zfree)
      refine PEqualNP.Outside.L_lib_608_aux.sum_zmod2_eq_zero_of_invol _ τ ?_ ?_ ?_
      · intro u
        funext z
        by_cases hz : z = zfree
        · subst hz; simp [τ]
        · simp [τ, Function.update, hz]
      · intro u h
        have hv := congrFun h zfree
        dsimp only [τ] at hv
        rw [Function.update_self] at hv
        cases hu : u zfree <;> rw [hu] at hv <;> cases hv
      · intro u
        have hpoint : ∀ p ∈ mon, embed (τ u) p = embed u p := by
          intro p hp
          have hnot_z : varOf p ≠ some zfree := by
            intro hEq
            apply hzfree
            exact Finset.mem_biUnion.mpr ⟨p, hp, by simp [hEq]⟩
          dsimp only [embed]
          by_cases hp1 : p.1 = j0
          · simp only [hp1, ↓reduceIte]
            by_cases hy : PEqualNP.Outside.L_lib_608_aux.skipVal cstar p.2.1 ∈ T
            · rw [dif_pos hy, dif_pos hy]
              have hne_z : (⟨PEqualNP.Outside.L_lib_608_aux.skipVal cstar p.2.1, hy⟩ : T) ≠ zfree := by
                intro hEq
                apply hnot_z
                dsimp only [varOf]
                simp only [hp1, ↓reduceIte, dif_pos hy, hEq]
              dsimp only [τ]
              simp only [Function.update, hne_z, ↓reduceDIte]
            · rw [dif_neg hy, dif_neg hy]
          · simp only [hp1, ↓reduceIte]
        unfold PEqualNP.Outside.L_lib_608_aux.monEval
        have hiff : (∀ p ∈ mon, embed (τ u) p = true) ↔ (∀ p ∈ mon, embed u p = true) :=
          forall₂_congr fun p hp => by rw [hpoint p hp]
        by_cases hcond : ∀ p ∈ mon, embed u p = true
        · rw [if_pos (hiff.mpr hcond), if_pos hcond]
        · rw [if_neg (fun h => hcond (hiff.mp h)), if_neg hcond]
    rw [hsum_lhs] at hsum_rhs
    exact absurd hsum_rhs (by decide)
