import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_595_aux

private lemma sum_fin_val_two (Q : ℕ) :
    2 * (∑ a : Fin Q, (a.val : ℤ)) = (Q : ℤ) * ((Q : ℤ) - 1) := by
  induction Q with
  | zero => simp
  | succ Q ih =>
    rw [Fin.sum_univ_castSucc, mul_add]
    simp only [Fin.val_castSucc, Fin.val_last, Nat.cast_add, Nat.cast_one]
    rw [ih]
    ring

private lemma sum_fin_sq_six (Q : ℕ) :
    6 * (∑ a : Fin Q, ((a.val : ℤ) ^ 2)) = (Q : ℤ) * ((Q : ℤ) - 1) * (2 * (Q : ℤ) - 1) := by
  induction Q with
  | zero => simp
  | succ Q ih =>
    rw [Fin.sum_univ_castSucc, mul_add]
    simp only [Fin.val_castSucc, Fin.val_last, Nat.cast_add, Nat.cast_one]
    rw [ih]
    ring

private def gTerm {Q : ℕ} (a b : Fin Q) : ℤ :=
  6 * ((a.val : ℤ) - (b.val : ℤ)) ^ 2 - ((Q : ℤ) ^ 2 - 1)

private lemma sum_gTerm_zero (Q : ℕ) :
    (∑ a : Fin Q, ∑ b : Fin Q, gTerm a b) = 0 := by
  unfold gTerm
  have h1 : (∑ a : Fin Q, ∑ b : Fin Q, (6 * ((a.val : ℤ) - (b.val : ℤ)) ^ 2 - ((Q : ℤ) ^ 2 - 1))) =
      (∑ a : Fin Q, ∑ b : Fin Q, 6 * ((a.val : ℤ) ^ 2 - 2 * (a.val : ℤ) * (b.val : ℤ) + (b.val : ℤ) ^ 2)) -
      (∑ _a : Fin Q, ∑ _b : Fin Q, ((Q : ℤ) ^ 2 - 1)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [h1]
  have hc : (∑ _a : Fin Q, ∑ _b : Fin Q, ((Q : ℤ) ^ 2 - 1)) = (Q : ℤ) ^ 2 * ((Q : ℤ) ^ 2 - 1) := by
    simp [Finset.sum_const]
    ring
  have hexp :
      (∑ a : Fin Q, ∑ b : Fin Q, 6 * ((a.val : ℤ) ^ 2 - 2 * (a.val : ℤ) * (b.val : ℤ) + (b.val : ℤ) ^ 2)) =
      2 * (Q : ℤ) * (6 * ∑ a : Fin Q, (a.val : ℤ) ^ 2) - 3 * (2 * ∑ a : Fin Q, (a.val : ℤ)) ^ 2 := by
    have hsplit : ∀ a : Fin Q,
        (∑ b : Fin Q, 6 * ((a.val : ℤ) ^ 2 - 2 * (a.val : ℤ) * (b.val : ℤ) + (b.val : ℤ) ^ 2)) =
        (Q : ℤ) * (6 * (a.val : ℤ) ^ 2) - 12 * (a.val : ℤ) * (∑ b : Fin Q, (b.val : ℤ)) +
        (6 * ∑ b : Fin Q, (b.val : ℤ) ^ 2) := by
      intro a
      have hterm : ∀ b : Fin Q,
          6 * ((a.val : ℤ) ^ 2 - 2 * (a.val : ℤ) * (b.val : ℤ) + (b.val : ℤ) ^ 2) =
          6 * (a.val : ℤ) ^ 2 + (- (12 * (a.val : ℤ)) * (b.val : ℤ)) + 6 * (b.val : ℤ) ^ 2 := by
        intro b; ring
      rw [Finset.sum_congr rfl fun b _ => hterm b, Finset.sum_add_distrib, Finset.sum_add_distrib]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        ← Finset.mul_sum, ← Finset.mul_sum]
      ring
    rw [Finset.sum_congr rfl fun a _ => hsplit a, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    have h12 : (∑ a : Fin Q, 12 * (a.val : ℤ) * ∑ b : Fin Q, (b.val : ℤ)) =
        12 * (∑ a : Fin Q, (a.val : ℤ)) * (∑ b : Fin Q, (b.val : ℤ)) := by
      rw [← Finset.sum_mul, ← Finset.mul_sum]
    have h6 : (∑ a : Fin Q, (Q : ℤ) * (6 * (a.val : ℤ) ^ 2)) =
        (Q : ℤ) * (6 * ∑ a : Fin Q, (a.val : ℤ) ^ 2) := by
      rw [← Finset.mul_sum, ← Finset.mul_sum]
    rw [h6, h12, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [hexp, hc, sum_fin_sq_six Q, sum_fin_val_two Q]
  ring

private lemma gTerm_sq_le {Q : ℕ} (a b : Fin Q) :
    (gTerm a b) ^ 2 ≤ 36 * (Q : ℤ) ^ 4 := by
  unfold gTerm
  have ha : (0 : ℤ) ≤ a.val := Nat.cast_nonneg _
  have hb : (0 : ℤ) ≤ b.val := Nat.cast_nonneg _
  have ha_lt : (a.val : ℤ) < Q := Nat.cast_lt.mpr a.isLt
  have hb_lt : (b.val : ℤ) < Q := Nat.cast_lt.mpr b.isLt
  have hdiff_lo : - (Q : ℤ) ≤ (a.val : ℤ) - (b.val : ℤ) := by omega
  have hdiff_hi : (a.val : ℤ) - (b.val : ℤ) ≤ Q := by omega
  have hsq_le : ((a.val : ℤ) - (b.val : ℤ)) ^ 2 ≤ (Q : ℤ) ^ 2 := by nlinarith
  have hsq_nn : (0 : ℤ) ≤ ((a.val : ℤ) - (b.val : ℤ)) ^ 2 := sq_nonneg _
  have hQ_pos : (1 : ℤ) ≤ Q := by
    have : 0 < Q := lt_of_le_of_lt (Nat.zero_le _) a.isLt
    omega
  have hg_lo : - (6 * (Q : ℤ) ^ 2) ≤ 6 * ((a.val : ℤ) - (b.val : ℤ)) ^ 2 - ((Q : ℤ) ^ 2 - 1) := by
    nlinarith
  have hg_hi : 6 * ((a.val : ℤ) - (b.val : ℤ)) ^ 2 - ((Q : ℤ) ^ 2 - 1) ≤ 6 * (Q : ℤ) ^ 2 := by
    nlinarith
  nlinarith

private lemma sum_orthog_coord {m Q : ℕ} (hQ : 0 < Q) (j : Fin m)
    (f : ((Fin m → Fin Q) × (Fin m → Fin Q)) → ℤ)
    (hind : ∀ p a b, f (Function.update p.1 j a, Function.update p.2 j b) = f p) :
    (∑ p : (Fin m → Fin Q) × (Fin m → Fin Q), gTerm (p.1 j) (p.2 j) * f p) = 0 := by
  let setJ : Fin Q → Fin Q → ((Fin m → Fin Q) × (Fin m → Fin Q)) →
      ((Fin m → Fin Q) × (Fin m → Fin Q)) :=
    fun a b p => (Function.update p.1 j a, Function.update p.2 j b)
  have h1 : (∑ p : (Fin m → Fin Q) × (Fin m → Fin Q),
      ∑ a : Fin Q, ∑ b : Fin Q, gTerm a b * f (setJ a b p)) = 0 := by
    refine Finset.sum_eq_zero fun p _ => ?_
    have hinner : (∑ a : Fin Q, ∑ b : Fin Q, gTerm a b * f (setJ a b p)) =
        (∑ a : Fin Q, ∑ b : Fin Q, gTerm a b) * f p := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [hind p a b]
    rw [hinner, sum_gTerm_zero Q, zero_mul]
  have h2 : (∑ p : (Fin m → Fin Q) × (Fin m → Fin Q),
      ∑ a : Fin Q, ∑ b : Fin Q, gTerm a b * f (setJ a b p)) =
      ((Q : ℤ) ^ 2) * (∑ q : (Fin m → Fin Q) × (Fin m → Fin Q), gTerm (q.1 j) (q.2 j) * f q) := by
    rw [Finset.sum_comm]
    have hswap : (∑ a : Fin Q, ∑ p : (Fin m → Fin Q) × (Fin m → Fin Q), ∑ b : Fin Q, gTerm a b * f (setJ a b p)) =
        ∑ a : Fin Q, ∑ b : Fin Q, ∑ p : (Fin m → Fin Q) × (Fin m → Fin Q), gTerm a b * f (setJ a b p) := by
      refine Finset.sum_congr rfl fun a _ => Finset.sum_comm
    rw [hswap]
    have hfib_ab : ∀ a b : Fin Q,
        (∑ p : (Fin m → Fin Q) × (Fin m → Fin Q), gTerm a b * f (setJ a b p)) =
        ((Q : ℤ) ^ 2) * ∑ q ∈ Finset.univ.filter (fun q : (Fin m → Fin Q) × (Fin m → Fin Q) =>
          q.1 j = a ∧ q.2 j = b), gTerm (q.1 j) (q.2 j) * f q := by
      intro a b
      have hpart := Finset.sum_fiberwise_of_maps_to
        (s := (Finset.univ : Finset ((Fin m → Fin Q) × (Fin m → Fin Q))))
        (t := Finset.univ.filter (fun q : (Fin m → Fin Q) × (Fin m → Fin Q) => q.1 j = a ∧ q.2 j = b))
        (g := setJ a b)
        (fun p _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [setJ]⟩)
        (fun p => gTerm a b * f (setJ a b p))
      rw [← hpart, Finset.mul_sum]
      refine Finset.sum_congr rfl fun q hq => ?_
      have hqab := (Finset.mem_filter.mp hq).2
      have hconst : ∀ p ∈ Finset.univ.filter (fun p => setJ a b p = q),
          gTerm a b * f (setJ a b p) = gTerm (q.1 j) (q.2 j) * f q := by
        intro p hp
        rw [(Finset.mem_filter.mp hp).2, hqab.1, hqab.2]
      rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
      have hcard : (Finset.univ.filter (fun p : (Fin m → Fin Q) × (Fin m → Fin Q) => setJ a b p = q)).card = Q ^ 2 := by
        have hbij : (Finset.univ.filter (fun p : (Fin m → Fin Q) × (Fin m → Fin Q) => setJ a b p = q)).card =
            (Finset.univ : Finset (Fin Q × Fin Q)).card := by
          refine Finset.card_bij (fun p _ => (p.1 j, p.2 j)) ?_ ?_ ?_
          · intro _ _; exact Finset.mem_univ _
          · intro p1 hp1 p2 hp2 hEq
            have hs1 := (Finset.mem_filter.mp hp1).2
            have hs2 := (Finset.mem_filter.mp hp2).2
            apply Prod.ext
            · funext i
              by_cases hij : i = j
              · subst hij; exact congrArg Prod.fst hEq
              · have e1 := congrFun (congrArg Prod.fst hs1) i
                have e2 := congrFun (congrArg Prod.fst hs2) i
                simp only [setJ, Function.update, hij, ↓reduceDIte] at e1 e2
                rw [e1, e2]
            · funext i
              by_cases hij : i = j
              · subst hij; exact congrArg Prod.snd hEq
              · have e1 := congrFun (congrArg Prod.snd hs1) i
                have e2 := congrFun (congrArg Prod.snd hs2) i
                simp only [setJ, Function.update, hij, ↓reduceDIte] at e1 e2
                rw [e1, e2]
          · intro c _
            refine ⟨setJ c.1 c.2 q, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, by simp [setJ]⟩
            apply Prod.ext
            · funext i
              by_cases hij : i = j
              · subst hij; simp [setJ, hqab.1]
              · simp [setJ, Function.update, hij]
            · funext i
              by_cases hij : i = j
              · subst hij; simp [setJ, hqab.2]
              · simp [setJ, Function.update, hij]
        rw [hbij, Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
        ring
      rw [hcard, Nat.cast_pow]
    rw [Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => hfib_ab a b]
    have hpull : (∑ a : Fin Q, ∑ b : Fin Q, ((Q : ℤ) ^ 2) *
        ∑ q ∈ Finset.univ.filter (fun q : (Fin m → Fin Q) × (Fin m → Fin Q) => q.1 j = a ∧ q.2 j = b),
          gTerm (q.1 j) (q.2 j) * f q) =
        ((Q : ℤ) ^ 2) * ∑ p : Fin Q × Fin Q,
          ∑ q ∈ Finset.univ.filter (fun q : (Fin m → Fin Q) × (Fin m → Fin Q) => (q.1 j, q.2 j) = p),
            gTerm (q.1 j) (q.2 j) * f q := by
      rw [← Finset.sum_product']
      rw [← Finset.mul_sum]
      congr 1
    rw [hpull]
    congr 1
    exact Finset.sum_fiberwise_of_maps_to (fun _ _ => Finset.mem_univ _) _
  rw [h2] at h1
  have hQne : ((Q : ℤ) ^ 2) ≠ 0 := by positivity
  exact (mul_eq_zero.mp h1).resolve_left hQne

private lemma natDist_sq_int (u v : ℕ) :
    ((Nat.dist u v : ℕ) : ℤ) ^ 2 = ((u : ℤ) - (v : ℤ)) ^ 2 := by
  by_cases h : u ≤ v
  · have hd : Nat.dist u v = v - u := by
      unfold Nat.dist; omega
    rw [hd, Nat.cast_sub h]; ring
  · have h2 : v ≤ u := by omega
    have hd : Nat.dist u v = u - v := by
      unfold Nat.dist; omega
    rw [hd, Nat.cast_sub h2]

private lemma card_row_kernel {ι : Type} [Fintype ι] [DecidableEq ι]
    (v : ι → ZMod 2) (hv : v ≠ 0) :
    2 * (Finset.univ.filter (fun row : ι → ZMod 2 => (∑ p : ι, row p * v p) = 0)).card =
      Fintype.card (ι → ZMod 2) := by
  have hex : ∃ p0 : ι, v p0 ≠ 0 := by
    by_contra hall
    push_neg at hall
    apply hv; funext p; exact hall p
  rcases hex with ⟨p0, hp0⟩
  have hp01 : v p0 = 1 := by
    generalize hv0 : v p0 = z at hp0
    fin_cases z
    · exact absurd rfl hp0
    · rfl
  let K0 := Finset.univ.filter (fun row : ι → ZMod 2 => (∑ p : ι, row p * v p) = 0)
  let K1 := Finset.univ.filter (fun row : ι → ZMod 2 => (∑ p : ι, row p * v p) = 1)
  let τ : (ι → ZMod 2) → (ι → ZMod 2) := fun row => Function.update row p0 (row p0 + 1)
  have hinv : ∀ row, τ (τ row) = row := by
    intro row
    funext p
    by_cases hp : p = p0
    · subst hp
      simp only [τ, Function.update_self]
      generalize row p = z; revert z; decide
    · simp [τ, Function.update, hp]
  have hadd1 : ∀ row, (∑ p : ι, τ row p * v p) = (∑ p : ι, row p * v p) + 1 := by
    intro row
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ p0), ← Finset.add_sum_erase _ _ (Finset.mem_univ p0)]
    have hrest : (∑ p ∈ Finset.univ.erase p0, τ row p * v p) = ∑ p ∈ Finset.univ.erase p0, row p * v p := by
      refine Finset.sum_congr rfl fun p hp => ?_
      have hne : p ≠ p0 := (Finset.mem_erase.mp hp).1
      simp [τ, Function.update, hne]
    rw [hrest]
    simp only [τ, Function.update_self, hp01]
    ring
  have hcard_eq : K0.card = K1.card := by
    refine Finset.card_bij (fun row _ => τ row) ?_ ?_ ?_
    · intro row hrow
      have h0 := (Finset.mem_filter.mp hrow).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rw [hadd1, h0, zero_add]
    · intro r1 _ r2 _ hEq
      have := congrArg τ hEq
      rwa [hinv, hinv] at this
    · intro row hrow
      have h1 := (Finset.mem_filter.mp hrow).2
      refine ⟨τ row, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hinv row⟩
      rw [hadd1, h1]
      decide
  have hdisj : Disjoint K0 K1 := by
    rw [Finset.disjoint_left]
    intro r h0 h1
    have a0 := (Finset.mem_filter.mp h0).2
    have a1 := (Finset.mem_filter.mp h1).2
    rw [a0] at a1; exact absurd a1 (by decide)
  have hunion : K0 ∪ K1 = Finset.univ := by
    ext r
    simp only [K0, K1, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    generalize ∑ p : ι, r p * v p = z
    fin_cases z
    · left; rfl
    · right; rfl
  have htot : K0.card + K1.card = Fintype.card (ι → ZMod 2) := by
    rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ]
  change 2 * K0.card = Fintype.card (ι → ZMod 2)
  omega

private def bitsToNat (b : ℕ) (w : Fin b → ZMod 2) : ℕ :=
  ∑ k : Fin b, if w k = 1 then 2 ^ k.val else 0

private lemma bitsToNat_lt (b : ℕ) (w : Fin b → ZMod 2) :
    bitsToNat b w < 2 ^ b := by
  unfold bitsToNat
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    have hprev := ih (fun k => w k.castSucc)
    have hlast : (if w (Fin.last b) = 1 then 2 ^ b else 0) ≤ 2 ^ b := by
      split_ifs <;> omega
    have hpow : 2 ^ (b + 1) = 2 ^ b + 2 ^ b := by ring
    omega

private lemma bitsToNat_testBit (b : ℕ) (w : Fin b → ZMod 2) (k : Fin b) :
    (bitsToNat b w).testBit k.val = decide (w k = 1) := by
  unfold bitsToNat
  induction b with
  | zero => exact Fin.elim0 k
  | succ b ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    have hprev_lt : (∑ i : Fin b, if w i.castSucc = 1 then 2 ^ i.val else 0) < 2 ^ b :=
      bitsToNat_lt b (fun i => w i.castSucc)
    set S := ∑ i : Fin b, if w i.castSucc = 1 then 2 ^ i.val else 0
    by_cases hk : k.val < b
    · have hk_eq : k = (⟨k.val, hk⟩ : Fin b).castSucc := Fin.ext rfl
      rw [hk_eq]
      simp only [Fin.val_castSucc]
      have hmod : (S + if w (Fin.last b) = 1 then 2 ^ b else 0).testBit k.val = S.testBit k.val := by
        by_cases hw : w (Fin.last b) = 1
        · rw [if_pos hw]
          have hpow : 2 ^ b = 2 ^ k.val * 2 ^ (b - k.val) := by
            rw [← pow_add, Nat.add_sub_of_le (le_of_lt hk)]
          rw [Nat.testBit, Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow,
            hpow, Nat.add_mul_div_left _ _ (Nat.two_pow_pos k.val)]
          have heven : 2 ∣ 2 ^ (b - k.val) := by
            rw [show b - k.val = (b - k.val - 1) + 1 by omega, pow_succ]
            exact dvd_mul_left 2 _
          rcases heven with ⟨t, ht⟩
          rw [ht]
          simp
        · rw [if_neg hw, add_zero]
      rw [hmod]
      exact ih (fun i => w i.castSucc) ⟨k.val, hk⟩
    · have hkl : k = Fin.last b := Fin.ext (by have := k.isLt; simp; omega)
      rw [hkl]
      simp only [Fin.val_last]
      rw [Nat.testBit, Nat.shiftRight_eq_div_pow]
      by_cases hw : w (Fin.last b) = 1
      · rw [if_pos hw, Nat.add_div_right _ (Nat.two_pow_pos b), Nat.div_eq_of_lt hprev_lt]
        simp [hw]
      · rw [if_neg hw, add_zero, Nat.div_eq_of_lt hprev_lt]
        simp [hw]

private lemma bitsToNat_inj (b : ℕ) {w1 w2 : Fin b → ZMod 2}
    (h : bitsToNat b w1 = bitsToNat b w2) : w1 = w2 := by
  funext k
  have hb1 := bitsToNat_testBit b w1 k
  have hb2 := bitsToNat_testBit b w2 k
  rw [h] at hb1
  have hdec : decide (w1 k = 1) = decide (w2 k = 1) := hb1.symm.trans hb2
  generalize w1 k = a at hdec ⊢
  generalize w2 k = c at hdec ⊢
  fin_cases a <;> fin_cases c <;> first | rfl | exact absurd hdec (by decide)

end PEqualNP.Outside.L_lib_595_aux

theorem PEqualNP.Outside.L_lib_595 : (∀ (m b : ℕ), 0 < m → 0 < b →
  let Q := 2^b
  let X := Fin m → Fin Q
  let radius := 12*Q^2*(Nat.sqrt m + 1)
  let center := m*(Q^2-1)
  let dist := fun (x y : X) => ∑ j : Fin m, (Nat.dist (x j).val (y j).val)^2
  let edges := Finset.univ.filter (fun p : X × X => Nat.dist (6*dist p.1 p.2) center ≤ radius)
  let f := 1 + radius * Nat.clog 2 (m*Q+1)
  let vec := fun (x : X) (j : Fin m × Fin b) => if (x j.1).val.testBit j.2.val then
    (1 : ZMod 2) else 0
  2^(2*m*b) ≤ 2*edges.card ∧
    ∃ H : ((Fin m × Fin b) → ZMod 2) →ₗ[ZMod 2] (Fin f → ZMod 2),
      (∀ x y : X, x ≠ y → (Finset.univ.filter (fun j : Fin m => x j ≠ y j)).card ≤ radius →
        H (vec x) ≠ H (vec y)) ∧
      ∀ p ∈ edges, ∀ r ∈ edges, p ≠ r →
        (∀ j : Fin m, (p.1 j).val + (p.2 j).val = (r.1 j).val + (r.2 j).val) →
        H (vec p.1) = H (vec r.1) →
          p.1 ≠ r.1 ∧ p.2 ≠ r.2 ∧ (p.1, r.2) ∉ edges ∧ (r.1, p.2) ∉ edges) := by
  classical
  intro m b hm hb Q X radius center dist edges f vec
  have hQ_pos : 0 < Q := Nat.two_pow_pos b
  have hQ_ge1 : 1 ≤ Q := hQ_pos
  have hcard_XX : Fintype.card (X × X) = 2 ^ (2 * m * b) := by
    dsimp only [X, Q]
    rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
      ← pow_mul, ← pow_add]
    congr 1; ring
  have hpart1 : 2 ^ (2 * m * b) ≤ 2 * edges.card := by
    let G : (X × X) → ℤ := fun p => ∑ j : Fin m, PEqualNP.Outside.L_lib_595_aux.gTerm (p.1 j) (p.2 j)
    have hG_eq : ∀ p : X × X, G p = 6 * (dist p.1 p.2 : ℤ) - (center : ℤ) := by
      intro p
      dsimp only [G, dist, center]
      have hQ2 : ((Q ^ 2 - 1 : ℕ) : ℤ) = (Q : ℤ) ^ 2 - 1 := by
        rw [Nat.cast_sub (Nat.one_le_pow 2 Q hQ_ge1), Nat.cast_pow, Nat.cast_one]
      rw [Nat.cast_mul, hQ2, Nat.cast_sum, Finset.mul_sum]
      have h1 : (m : ℤ) * ((Q : ℤ) ^ 2 - 1) = ∑ _j : Fin m, ((Q : ℤ) ^ 2 - 1) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [h1, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      unfold PEqualNP.Outside.L_lib_595_aux.gTerm
      rw [Nat.cast_pow (Nat.dist (p.1 j).val (p.2 j).val) 2, PEqualNP.Outside.L_lib_595_aux.natDist_sq_int]
    have hsum_sq : (∑ p : X × X, (G p) ^ 2) ≤ 36 * (m : ℤ) * (Q : ℤ) ^ 4 * (Fintype.card (X × X) : ℤ) := by
      have hexp : (∑ p : X × X, (G p) ^ 2) =
          ∑ j : Fin m, ∑ k : Fin m, ∑ p : X × X,
            PEqualNP.Outside.L_lib_595_aux.gTerm (p.1 j) (p.2 j) *
              PEqualNP.Outside.L_lib_595_aux.gTerm (p.1 k) (p.2 k) := by
        have hpt : ∀ p : X × X, (G p) ^ 2 =
            ∑ j : Fin m, ∑ k : Fin m,
              PEqualNP.Outside.L_lib_595_aux.gTerm (p.1 j) (p.2 j) *
                PEqualNP.Outside.L_lib_595_aux.gTerm (p.1 k) (p.2 k) := by
          intro p
          dsimp only [G]
          rw [sq, Finset.sum_mul]
          refine Finset.sum_congr rfl fun j _ => Finset.mul_sum _ _ _
        rw [Finset.sum_congr rfl fun p _ => hpt p, Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => Finset.sum_comm
      rw [hexp]
      have hdiag : ∀ j : Fin m,
          (∑ k : Fin m, ∑ p : X × X,
            PEqualNP.Outside.L_lib_595_aux.gTerm (p.1 j) (p.2 j) *
              PEqualNP.Outside.L_lib_595_aux.gTerm (p.1 k) (p.2 k)) =
          ∑ p : X × X, (PEqualNP.Outside.L_lib_595_aux.gTerm (p.1 j) (p.2 j)) ^ 2 := by
        intro j
        rw [Finset.sum_eq_single j]
        · refine Finset.sum_congr rfl fun p _ => (sq _).symm
        · intro k _ hkj
          apply PEqualNP.Outside.L_lib_595_aux.sum_orthog_coord hQ_pos j
          intro p a b
          simp [Function.update, hkj]
        · intro h; exact absurd (Finset.mem_univ j) h
      rw [Finset.sum_congr rfl fun j _ => hdiag j]
      have hj_le : ∀ j : Fin m,
          (∑ p : X × X, (PEqualNP.Outside.L_lib_595_aux.gTerm (p.1 j) (p.2 j)) ^ 2) ≤
          36 * (Q : ℤ) ^ 4 * (Fintype.card (X × X) : ℤ) := by
        intro j
        calc
          ∑ p : X × X, (PEqualNP.Outside.L_lib_595_aux.gTerm (p.1 j) (p.2 j)) ^ 2
              ≤ ∑ _p : X × X, (36 * (Q : ℤ) ^ 4) :=
                Finset.sum_le_sum fun p _ => PEqualNP.Outside.L_lib_595_aux.gTerm_sq_le (p.1 j) (p.2 j)
          _ = 36 * (Q : ℤ) ^ 4 * (Fintype.card (X × X) : ℤ) := by
                rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]
      calc
        ∑ j : Fin m, ∑ p : X × X, (PEqualNP.Outside.L_lib_595_aux.gTerm (p.1 j) (p.2 j)) ^ 2
            ≤ ∑ _j : Fin m, (36 * (Q : ℤ) ^ 4 * (Fintype.card (X × X) : ℤ)) :=
              Finset.sum_le_sum fun j _ => hj_le j
        _ = 36 * (m : ℤ) * (Q : ℤ) ^ 4 * (Fintype.card (X × X) : ℤ) := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
    let bad := Finset.univ.filter (fun p : X × X => ¬ (Nat.dist (6 * dist p.1 p.2) center ≤ radius))
    have hbad_sq : (bad.card : ℤ) * (radius : ℤ) ^ 2 ≤ ∑ p : X × X, (G p) ^ 2 := by
      have h1 : (bad.card : ℤ) * (radius : ℤ) ^ 2 ≤ ∑ p ∈ bad, (G p) ^ 2 := by
        calc
          (bad.card : ℤ) * (radius : ℤ) ^ 2 = ∑ _p ∈ bad, (radius : ℤ) ^ 2 := by
            rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ ∑ p ∈ bad, (G p) ^ 2 := by
            refine Finset.sum_le_sum fun p hp => ?_
            have hgt : radius < Nat.dist (6 * dist p.1 p.2) center := by
              have := (Finset.mem_filter.mp hp).2; omega
            have hcast6 : 6 * (dist p.1 p.2 : ℤ) - (center : ℤ) =
                ((6 * dist p.1 p.2 : ℕ) : ℤ) - (center : ℤ) := by push_cast; rfl
            rw [hG_eq p, hcast6, ← PEqualNP.Outside.L_lib_595_aux.natDist_sq_int]
            have hle : (radius : ℤ) ≤ (Nat.dist (6 * dist p.1 p.2) center : ℤ) := by exact_mod_cast le_of_lt hgt
            nlinarith
      exact le_trans h1 (Finset.sum_le_univ_sum_of_nonneg fun p => sq_nonneg (G p))
    have hrad_gt : 2 * (36 * (m : ℤ) * (Q : ℤ) ^ 4) < (radius : ℤ) ^ 2 := by
      have hsqrt : m < (Nat.sqrt m + 1) ^ 2 := by
        have := Nat.lt_succ_sqrt m
        simpa [sq] using this
      have hsqrt_z : (m : ℤ) < ((Nat.sqrt m + 1 : ℕ) : ℤ) ^ 2 := by exact_mod_cast hsqrt
      have hQ4_pos : (0 : ℤ) < (Q : ℤ) ^ 4 := by positivity
      have hrad_sq : (radius : ℤ) ^ 2 = 144 * (Q : ℤ) ^ 4 * ((Nat.sqrt m + 1 : ℕ) : ℤ) ^ 2 := by
        dsimp only [radius]; push_cast; ring
      rw [hrad_sq]
      nlinarith
    have h2bad : 2 * bad.card ≤ Fintype.card (X × X) := by
      have hrad_pos : (0 : ℤ) < (radius : ℤ) ^ 2 := by
        have : 0 < radius := by dsimp only [radius]; positivity
        positivity
      have hcomb : (2 * (bad.card : ℤ)) * (radius : ℤ) ^ 2 ≤
          2 * (36 * (m : ℤ) * (Q : ℤ) ^ 4) * (Fintype.card (X × X) : ℤ) := by
        linarith
      have hcomb2 : (2 * (bad.card : ℤ)) * (radius : ℤ) ^ 2 ≤
          (radius : ℤ) ^ 2 * (Fintype.card (X × X) : ℤ) := by
        have htot_nn : (0 : ℤ) ≤ (Fintype.card (X × X) : ℤ) := Nat.cast_nonneg _
        nlinarith
      have hz : 2 * (bad.card : ℤ) ≤ (Fintype.card (X × X) : ℤ) := by nlinarith
      exact_mod_cast hz
    have hsum_card : edges.card + bad.card = Fintype.card (X × X) := by
      have hdisj : Disjoint edges bad := by
        rw [Finset.disjoint_left]
        intro p h1 h2
        exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
      have hunion : edges ∪ bad = Finset.univ := by
        ext p
        simp only [edges, bad, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
        exact em _
      rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ]
    rw [← hcard_XX]
    omega
  refine ⟨hpart1, ?_⟩
  let ι := Fin m × Fin b
  let Diffs : Finset (ι → ZMod 2) := Finset.univ.filter (fun v =>
    v ≠ 0 ∧ (Finset.univ.filter (fun j : Fin m => ∃ k : Fin b, v (j, k) ≠ 0)).card ≤ radius)
  have hDiffs_lt : Diffs.card < 2 ^ f := by
    have hrad_pos : 0 < radius := by dsimp only [radius]; positivity
    let enc : (ι → ZMod 2) → (Fin radius → Option (Fin m × Fin Q)) := fun v t =>
      let S := (Finset.univ.filter (fun j : Fin m => ∃ k : Fin b, v (j, k) ≠ 0)).sort (· ≤ ·)
      if ht : t.val < S.length then
        let j := S.get ⟨t.val, ht⟩
        some (j, ⟨PEqualNP.Outside.L_lib_595_aux.bitsToNat b (fun k => v (j, k)),
          PEqualNP.Outside.L_lib_595_aux.bitsToNat_lt b _⟩)
      else none
    have henc_inj : Set.InjOn enc (↑Diffs : Set (ι → ZMod 2)) := by
      intro v1 hv1 v2 hv2 hEq
      have hcard1 := (Finset.mem_filter.mp hv1).2.2
      have hcard2 := (Finset.mem_filter.mp hv2).2.2
      let S1 := Finset.univ.filter (fun j : Fin m => ∃ k : Fin b, v1 (j, k) ≠ 0)
      let S2 := Finset.univ.filter (fun j : Fin m => ∃ k : Fin b, v2 (j, k) ≠ 0)
      have hlen1 : (S1.sort (· ≤ ·)).length ≤ radius := by rw [Finset.length_sort]; exact hcard1
      have hlen2 : (S2.sort (· ≤ ·)).length ≤ radius := by rw [Finset.length_sort]; exact hcard2
      have hmem_iff : ∀ (v : ι → ZMod 2) (hcard : (Finset.univ.filter (fun j : Fin m => ∃ k : Fin b, v (j, k) ≠ 0)).card ≤ radius)
          (j : Fin m) (q : Fin Q),
          (∃ t : Fin radius, enc v t = some (j, q)) ↔
            (∃ k : Fin b, v (j, k) ≠ 0) ∧
              q.val = PEqualNP.Outside.L_lib_595_aux.bitsToNat b (fun k => v (j, k)) := by
        intro v hcard j q
        let Sv := Finset.univ.filter (fun j' : Fin m => ∃ k : Fin b, v (j', k) ≠ 0)
        constructor
        · rintro ⟨t, ht⟩
          dsimp only [enc] at ht
          by_cases hlt : t.val < (Sv.sort (· ≤ ·)).length
          · rw [dif_pos hlt] at ht
            injection ht with hp
            have hj_eq : (Sv.sort (· ≤ ·)).get ⟨t.val, hlt⟩ = j := congrArg Prod.fst hp
            have hq_eq : (⟨PEqualNP.Outside.L_lib_595_aux.bitsToNat b (fun k => v ((Sv.sort (· ≤ ·)).get ⟨t.val, hlt⟩, k)),
                PEqualNP.Outside.L_lib_595_aux.bitsToNat_lt b _⟩ : Fin Q) = q := congrArg Prod.snd hp
            have hj_mem : j ∈ Sv := by
              rw [← Finset.mem_sort (r := (· ≤ ·)), ← hj_eq]
              exact List.get_mem _ _
            refine ⟨(Finset.mem_filter.mp hj_mem).2, ?_⟩
            have hvq := congrArg Fin.val hq_eq
            dsimp only at hvq
            rw [← hvq, hj_eq]
          · rw [dif_neg hlt] at ht; cases ht
        · rintro ⟨hj_ex, hq_eq⟩
          have hj_mem : j ∈ Sv.sort (· ≤ ·) :=
            (Finset.mem_sort (r := (· ≤ ·))).mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj_ex⟩)
          obtain ⟨idx, hidx⟩ := List.mem_iff_get.mp hj_mem
          have hidx_lt : idx.val < radius :=
            lt_of_lt_of_le idx.isLt (by rw [Finset.length_sort]; exact hcard)
          refine ⟨⟨idx.val, hidx_lt⟩, ?_⟩
          dsimp only [enc]
          rw [dif_pos idx.isLt]
          congr 1
          apply Prod.ext
          · exact hidx
          · apply Fin.ext
            dsimp only
            rw [hidx, ← hq_eq]
      funext ⟨j, k⟩
      by_cases hj1 : ∃ k' : Fin b, v1 (j, k') ≠ 0
      · let q1 : Fin Q := ⟨PEqualNP.Outside.L_lib_595_aux.bitsToNat b (fun k' => v1 (j, k')),
          PEqualNP.Outside.L_lib_595_aux.bitsToNat_lt b _⟩
        have hex1 : ∃ t : Fin radius, enc v1 t = some (j, q1) :=
          (hmem_iff v1 hcard1 j q1).mpr ⟨hj1, rfl⟩
        rw [hEq] at hex1
        have h2 := (hmem_iff v2 hcard2 j q1).mp hex1
        have hfn := PEqualNP.Outside.L_lib_595_aux.bitsToNat_inj b h2.2
        exact congrFun hfn k
      · push_neg at hj1
        have hj2 : ∀ k' : Fin b, v2 (j, k') = 0 := by
          by_contra hex2
          push_neg at hex2
          let q2 : Fin Q := ⟨PEqualNP.Outside.L_lib_595_aux.bitsToNat b (fun k' => v2 (j, k')),
            PEqualNP.Outside.L_lib_595_aux.bitsToNat_lt b _⟩
          have h2 : ∃ t : Fin radius, enc v2 t = some (j, q2) :=
            (hmem_iff v2 hcard2 j q2).mpr ⟨hex2, rfl⟩
          rw [← hEq] at h2
          rcases (hmem_iff v1 hcard1 j q2).mp h2 with ⟨⟨k', hk'⟩, _⟩
          exact hk' (hj1 k')
        rw [hj1 k, hj2 k]
    have hDiffs_le : Diffs.card ≤ (m * Q + 1) ^ radius := by
      calc
        Diffs.card ≤ (Finset.univ : Finset (Fin radius → Option (Fin m × Fin Q))).card :=
          Finset.card_le_card_of_injOn enc (fun _ _ => Finset.mem_univ _) henc_inj
        _ = (m * Q + 1) ^ radius := by
          rw [Finset.card_univ, Fintype.card_fun, Fintype.card_option, Fintype.card_prod,
            Fintype.card_fin, Fintype.card_fin, Fintype.card_fin]
    have hclog : m * Q + 1 ≤ 2 ^ Nat.clog 2 (m * Q + 1) := Nat.le_pow_clog (by decide : 1 < 2) _
    have hpow_le : (m * Q + 1) ^ radius ≤ 2 ^ (radius * Nat.clog 2 (m * Q + 1)) := by
      calc
        (m * Q + 1) ^ radius ≤ (2 ^ Nat.clog 2 (m * Q + 1)) ^ radius := Nat.pow_le_pow_left hclog _
        _ = 2 ^ (radius * Nat.clog 2 (m * Q + 1)) := by rw [← pow_mul, mul_comm]
    have h2f : 2 ^ f = 2 * 2 ^ (radius * Nat.clog 2 (m * Q + 1)) := by
      dsimp only [f]; rw [pow_add, pow_one]
    have hpos_pow : 0 < 2 ^ (radius * Nat.clog 2 (m * Q + 1)) := Nat.two_pow_pos _
    omega
  let Mat := Fin f → (ι → ZMod 2)
  let applyM : Mat → (ι → ZMod 2) → (Fin f → ZMod 2) := fun M v i => ∑ p : ι, M i p * v p
  have hbadM_card : ∀ v ∈ Diffs,
      2 ^ f * (Finset.univ.filter (fun M : Mat => applyM M v = 0)).card = Fintype.card Mat := by
    intro v hv
    have hv0 : v ≠ 0 := (Finset.mem_filter.mp hv).2.1
    let K0 := Finset.univ.filter (fun row : ι → ZMod 2 => (∑ p : ι, row p * v p) = 0)
    have hK0 : 2 * K0.card = Fintype.card (ι → ZMod 2) :=
      PEqualNP.Outside.L_lib_595_aux.card_row_kernel v hv0
    have hfilt : (Finset.univ.filter (fun M : Mat => applyM M v = 0)).card = K0.card ^ f := by
      have hbij : (Finset.univ.filter (fun M : Mat => applyM M v = 0)).card =
          Fintype.card (Fin f → K0) := by
        refine Finset.card_bij
          (fun M hM => fun i => ⟨M i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, congrFun (Finset.mem_filter.mp hM).2 i⟩⟩)
          ?_ ?_ ?_
        · intro _ _; exact Finset.mem_univ _
        · intro M1 _ M2 _ hEq
          funext i
          exact congrArg Subtype.val (congrFun hEq i)
        · intro g _
          refine ⟨fun i => (g i).1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
          · funext i
            exact (Finset.mem_filter.mp (g i).2).2
          · funext i; exact Subtype.ext rfl
      rw [hbij, Fintype.card_fun, Fintype.card_coe, Fintype.card_fin]
    rw [hfilt, ← mul_pow, hK0]
    dsimp only [Mat]
    conv_rhs => rw [Fintype.card_fun, Fintype.card_fin]
  have hexM : ∃ M : Mat, ∀ v ∈ Diffs, applyM M v ≠ 0 := by
    let badAll : Finset Mat := Diffs.biUnion (fun v => Finset.univ.filter (fun M : Mat => applyM M v = 0))
    have hle : 2 ^ f * badAll.card ≤ Diffs.card * Fintype.card Mat := by
      have hbi : badAll.card ≤ ∑ v ∈ Diffs, (Finset.univ.filter (fun M : Mat => applyM M v = 0)).card :=
        Finset.card_biUnion_le
      calc
        2 ^ f * badAll.card ≤ 2 ^ f * ∑ v ∈ Diffs, (Finset.univ.filter (fun M : Mat => applyM M v = 0)).card :=
          Nat.mul_le_mul_left _ hbi
        _ = ∑ v ∈ Diffs, 2 ^ f * (Finset.univ.filter (fun M : Mat => applyM M v = 0)).card := Finset.mul_sum _ _ _
        _ = ∑ _v ∈ Diffs, Fintype.card Mat := Finset.sum_congr rfl hbadM_card
        _ = Diffs.card * Fintype.card Mat := by rw [Finset.sum_const, smul_eq_mul]
    have htot_pos : 0 < Fintype.card Mat := Fintype.card_pos
    have hlt_tot : badAll.card < Fintype.card Mat := by
      have hstrict : 2 ^ f * badAll.card < 2 ^ f * Fintype.card Mat :=
        lt_of_le_of_lt hle (Nat.mul_lt_mul_of_pos_right hDiffs_lt htot_pos)
      exact Nat.lt_of_mul_lt_mul_left hstrict
    have hnot_univ : badAll ≠ Finset.univ := by
      intro hEq
      have hc := congrArg Finset.card hEq
      rw [Finset.card_univ] at hc
      omega
    have hex : ∃ M : Mat, M ∉ badAll := by
      by_contra hall
      push_neg at hall
      apply hnot_univ
      ext M; simp [hall M]
    rcases hex with ⟨M, hM⟩
    refine ⟨M, fun v hv h0 => hM ?_⟩
    exact Finset.mem_biUnion.mpr ⟨v, hv, Finset.mem_filter.mpr ⟨Finset.mem_univ M, h0⟩⟩
  rcases hexM with ⟨M, hM⟩
  let H : (ι → ZMod 2) →ₗ[ZMod 2] (Fin f → ZMod 2) :=
    { toFun := applyM M
      map_add' := fun u v => by
        funext i
        dsimp only [applyM]
        simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := fun c v => by
        funext i
        dsimp only [applyM]
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun p _ => by ring }
  have hvec_inj : ∀ x y : X, vec x = vec y → x = y := by
    intro x y hEq
    funext j
    apply Fin.ext
    apply Nat.eq_of_testBit_eq
    intro k
    by_cases hkb : k < b
    · have hv := congrFun hEq (j, ⟨k, hkb⟩)
      dsimp only [vec] at hv
      by_cases h1 : (x j).val.testBit k = true <;> by_cases h2 : (y j).val.testBit k = true
      · rw [h1, h2]
      · rw [if_pos h1, if_neg h2] at hv; exact absurd hv (by decide)
      · rw [if_neg h1, if_pos h2] at hv; exact absurd hv (by decide)
      · cases hb1 : (x j).val.testBit k <;> cases hb2 : (y j).val.testBit k <;> simp_all
    · have hxlt : (x j).val < 2 ^ k := lt_of_lt_of_le (x j).isLt (Nat.pow_le_pow_right (by decide) (by omega))
      have hylt : (y j).val < 2 ^ k := lt_of_lt_of_le (y j).isLt (Nat.pow_le_pow_right (by decide) (by omega))
      rw [Nat.testBit_lt_two_pow hxlt, Nat.testBit_lt_two_pow hylt]
  have hsyndrome : ∀ x y : X, x ≠ y → (Finset.univ.filter (fun j : Fin m => x j ≠ y j)).card ≤ radius →
      H (vec x) ≠ H (vec y) := by
    intro x y hne hcard hHeq
    have hsub0 : H (vec x - vec y) = 0 := by
      rw [map_sub, hHeq, sub_self]
    have hdiff_ne : vec x - vec y ≠ 0 := by
      intro h0
      exact hne (hvec_inj x y (sub_eq_zero.mp h0))
    have hsupp_sub :
        Finset.univ.filter (fun j : Fin m => ∃ k : Fin b, (vec x - vec y) (j, k) ≠ 0) ⊆
          Finset.univ.filter (fun j : Fin m => x j ≠ y j) := by
      intro j hj
      rcases (Finset.mem_filter.mp hj).2 with ⟨k, hk⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ j, ?_⟩
      intro hxy
      apply hk
      simp only [Pi.sub_apply, vec, hxy, sub_self]
    have hmemD : vec x - vec y ∈ Diffs :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdiff_ne, le_trans (Finset.card_le_card hsupp_sub) hcard⟩
    exact hM (vec x - vec y) hmemD hsub0
  refine ⟨H, hsyndrome, ?_⟩
  intro p hp r hr hpr hsum hHeq
  have hp1_ne : p.1 ≠ r.1 := by
    intro h1
    apply hpr
    apply Prod.ext h1
    funext j
    apply Fin.ext
    have hj := hsum j
    rw [h1] at hj
    omega
  have hp2_ne : p.2 ≠ r.2 := by
    intro h2
    apply hpr
    apply Prod.ext ?_ h2
    funext j
    apply Fin.ext
    have hj := hsum j
    rw [h2] at hj
    omega
  have hham : radius < (Finset.univ.filter (fun j : Fin m => p.1 j ≠ r.1 j)).card := by
    by_contra hle
    exact hsyndrome p.1 r.1 hp1_ne (by omega) hHeq
  have hdist_gt : radius < dist p.1 r.1 := by
    have h1 : (Finset.univ.filter (fun j : Fin m => p.1 j ≠ r.1 j)).card ≤ dist p.1 r.1 := by
      dsimp only [dist]
      calc
        (Finset.univ.filter (fun j : Fin m => p.1 j ≠ r.1 j)).card
            = ∑ _j ∈ Finset.univ.filter (fun j : Fin m => p.1 j ≠ r.1 j), 1 := by simp
        _ ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin m => p.1 j ≠ r.1 j), (Nat.dist (p.1 j).val (r.1 j).val) ^ 2 := by
            refine Finset.sum_le_sum fun j hj => ?_
            have hne : p.1 j ≠ r.1 j := (Finset.mem_filter.mp hj).2
            have hvne : (p.1 j).val ≠ (r.1 j).val := fun h => hne (Fin.ext h)
            have hd1 : 1 ≤ Nat.dist (p.1 j).val (r.1 j).val := by
              unfold Nat.dist; omega
            nlinarith
        _ ≤ ∑ j : Fin m, (Nat.dist (p.1 j).val (r.1 j).val) ^ 2 :=
            Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
    omega
  have hpar1 : 2 * (dist p.1 r.2 : ℤ) + 2 * (dist p.1 r.1 : ℤ) = (dist p.1 p.2 : ℤ) + (dist r.1 r.2 : ℤ) := by
    dsimp only [dist]
    push_cast
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [PEqualNP.Outside.L_lib_595_aux.natDist_sq_int, PEqualNP.Outside.L_lib_595_aux.natDist_sq_int,
      PEqualNP.Outside.L_lib_595_aux.natDist_sq_int, PEqualNP.Outside.L_lib_595_aux.natDist_sq_int]
    have hj : ((p.1 j).val : ℤ) + ((p.2 j).val : ℤ) = ((r.1 j).val : ℤ) + ((r.2 j).val : ℤ) := by
      exact_mod_cast hsum j
    nlinarith
  have hpar2 : 2 * (dist r.1 p.2 : ℤ) + 2 * (dist p.1 r.1 : ℤ) = (dist p.1 p.2 : ℤ) + (dist r.1 r.2 : ℤ) := by
    dsimp only [dist]
    push_cast
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [PEqualNP.Outside.L_lib_595_aux.natDist_sq_int, PEqualNP.Outside.L_lib_595_aux.natDist_sq_int,
      PEqualNP.Outside.L_lib_595_aux.natDist_sq_int, PEqualNP.Outside.L_lib_595_aux.natDist_sq_int]
    have hj : ((p.1 j).val : ℤ) + ((p.2 j).val : ℤ) = ((r.1 j).val : ℤ) + ((r.2 j).val : ℤ) := by
      exact_mod_cast hsum j
    nlinarith
  have hband : ∀ u v : X, (u, v) ∈ edges →
      (center : ℤ) - (radius : ℤ) ≤ 6 * (dist u v : ℤ) ∧ 6 * (dist u v : ℤ) ≤ (center : ℤ) + (radius : ℤ) := by
    intro u v huv
    have hd : Nat.dist (6 * dist u v) center ≤ radius := (Finset.mem_filter.mp huv).2
    unfold Nat.dist at hd
    omega
  have hp_b := hband p.1 p.2 hp
  have hr_b := hband r.1 r.2 hr
  refine ⟨hp1_ne, hp2_ne, ?_, ?_⟩
  · intro hmem
    have hc := hband p.1 r.2 hmem
    have hgt_z : (radius : ℤ) + 1 ≤ (dist p.1 r.1 : ℤ) := by exact_mod_cast hdist_gt
    linarith
  · intro hmem
    have hc := hband r.1 p.2 hmem
    have hgt_z : (radius : ℤ) + 1 ≤ (dist p.1 r.1 : ℤ) := by exact_mod_cast hdist_gt
    linarith
