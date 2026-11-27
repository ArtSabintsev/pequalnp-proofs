import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.L_lib_513

namespace PEqualNP.Outside.L_lib_526_aux

private abbrev Rows := Nat → Nat → Bool

private def massF (w : Nat) (rows : Rows) (h seed tail : Nat) : Nat :=
  ((List.range (2 ^ (w + h))).filter (fun bits =>
    bits % (2 ^ w) == seed && (bits >>> h) % (2 ^ w) == tail &&
    (List.range h).all (fun i => rows i ((bits >>> i) % (2 * 2 ^ w))))).length

private def patAt (w n word site : Nat) : Nat :=
  (List.range (w + 1)).foldl (fun (acc bit : Nat) =>
    acc ||| ((word.testBit ((site + bit) % n)).toNat <<< bit)) 0

private def rawCount (w t : Nat) (left right : Rows) : Nat :=
  let L := w + t
  let n := L + w
  ((List.range (2 ^ n)).filter (fun word => (List.range n).all (fun site =>
    let pat := patAt w n word site
    if site < L then left site pat else right (site - L) pat))).length

private def countF (w t m : Nat) (left right : Rows) : Nat :=
  rawCount w t left right % m

private def goodF (w t : Nat) (tables : Rows) : Prop :=
  let D := 2 ^ w
  let L := w + t
  ∃ a b : Fin D → Nat, (∀ i, 0 < a i) ∧ (∀ j, 0 < b j) ∧
    ∀ s z : Fin D, massF w tables L s.val z.val = a s * b z

private def rightOk (w : Nat) (right : Rows) (s z : Nat) : Bool :=
  let D := 2 ^ w
  (List.range w).all (fun j => right j (((z + s * D) >>> j) % (2 * D)))

private theorem foldl_bits_spec (f : Nat → Bool) :
    ∀ (k b : Nat),
      ((List.range k).foldl (fun (acc bit : Nat) => acc ||| ((f bit).toNat <<< bit)) 0).testBit b =
      if b < k then f b else false := by
  intro k
  induction k with
  | zero => intro b; simp
  | succ k ih =>
    intro b
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [Nat.testBit_or, ih b, Nat.testBit_shiftLeft]
    by_cases hbk : b < k
    · have hlt : b < k + 1 := by omega
      have hge : ¬ (k ≤ b) := by omega
      simp [hbk, hlt, hge]
    · by_cases hbe : b = k
      · subst hbe
        simp only [lt_self_iff_false, ↓reduceIte, Nat.lt_add_one, le_refl,
          decide_true, Nat.sub_self, Bool.true_and, Bool.false_or]
        cases f b <;> decide
      · have hgt : ¬ (b < k + 1) := by omega
        have hpos : b - k ≠ 0 := by omega
        have hzero : (f k).toNat.testBit (b - k) = false := by
          cases f k
          · simp
          · simp only [Bool.toNat_true, Nat.testBit_eq_decide_div_mod_eq, decide_eq_false_iff_not]
            have hdiv0 : 1 / 2 ^ (b - k) = 0 := Nat.div_eq_of_lt (Nat.one_lt_two_pow hpos)
            simp [hdiv0]
        simp [hbk, hgt, hzero]

private theorem testBit_add_mul_two_pow (z s w k : Nat) (hz : z < 2 ^ w) :
    (z + s * 2 ^ w).testBit k = if k < w then z.testBit k else s.testBit (k - w) := by
  simp only [Nat.testBit_eq_decide_div_mod_eq]
  split_ifs with hlt
  · have hpow : 2 ^ w = 2 ^ k * 2 ^ (w - k) := by rw [← pow_add, Nat.add_sub_of_le (le_of_lt hlt)]
    have hdiv : (z + s * 2 ^ w) / 2 ^ k = z / 2 ^ k + s * 2 ^ (w - k) := by
      rw [hpow, ← Nat.mul_assoc, Nat.mul_comm s (2 ^ k), Nat.mul_assoc,
        Nat.add_mul_div_left _ _ (by positivity)]
    have heven : 2 ∣ 2 ^ (w - k) := by
      have : w - k = (w - k - 1) + 1 := by omega
      rw [this, pow_succ']; exact dvd_mul_right 2 _
    rw [hdiv, Nat.add_mod, Nat.mul_mod, Nat.mod_eq_zero_of_dvd heven, Nat.mul_zero, Nat.zero_mod,
      Nat.add_zero, Nat.mod_mod]
  · have hge : w ≤ k := by omega
    have hpow : 2 ^ k = 2 ^ w * 2 ^ (k - w) := by rw [← pow_add, Nat.add_sub_of_le hge]
    rw [hpow, ← Nat.div_div_eq_div_mul, Nat.mul_comm s (2 ^ w),
      Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hz, Nat.zero_add]

private theorem patAt_left (w t word site : Nat) (hsite : site < w + t) :
    patAt w (w + t + w) word site = (word >>> site) % (2 * 2 ^ w) := by
  apply Nat.eq_of_testBit_eq
  intro b
  unfold patAt
  rw [foldl_bits_spec]
  have h2 : 2 * 2 ^ w = 2 ^ (w + 1) := by rw [pow_succ']
  rw [h2, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
  by_cases hb : b < w + 1
  · have hmod : (site + b) % (w + t + w) = site + b := Nat.mod_eq_of_lt (by omega)
    simp [hb, hmod]
  · simp [hb]

private theorem patAt_right (w t word j : Nat) (hj : j < w) :
    let D := 2 ^ w
    let L := w + t
    patAt w (L + w) word (L + j) = (((word >>> L) % D + (word % D) * D) >>> j) % (2 * D) := by
  intro D L
  apply Nat.eq_of_testBit_eq
  intro b
  unfold patAt
  rw [foldl_bits_spec]
  have h2 : 2 * D = 2 ^ (w + 1) := by dsimp [D]; rw [pow_succ']
  rw [h2, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
  by_cases hb : b < w + 1
  · simp only [hb, ↓reduceIte, decide_true, Bool.true_and]
    rw [testBit_add_mul_two_pow _ _ w (j + b) (Nat.mod_lt _ (by positivity))]
    by_cases hjb : j + b < w
    · have hmod : (L + j + b) % (L + w) = L + (j + b) := by
        rw [Nat.mod_eq_of_lt (by omega)]; omega
      simp only [hjb, ↓reduceIte, hmod, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, decide_true, Bool.true_and]
    · have hmod : (L + j + b) % (L + w) = j + b - w := by
        have h1 : L + j + b = (L + w) + (j + b - w) := by omega
        rw [h1, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
      have hlt : j + b - w < w := by omega
      simp only [hjb, ↓reduceIte, hmod]
      dsimp only [D]
      rw [Nat.testBit_mod_two_pow]
      simp [hlt]
  · simp [hb]

private theorem list_filter_length_eq_finset_card (N : Nat) (p : Nat → Bool) :
    ((List.range N).filter p).length =
      ((Finset.univ : Finset (Fin N)).filter (fun x => p x.val = true)).card := by
  have h1 : ((List.range N).filter p).length = ((Finset.range N).filter (fun x => p x = true)).card := by
    rw [← List.toFinset_card_of_nodup ((List.nodup_range).filter p)]
    congr 1
    ext x
    simp [List.mem_range, Finset.mem_filter, Finset.mem_range]
  rw [h1]
  refine Finset.card_bij (fun x hx => ⟨x, Finset.mem_range.mp (Finset.mem_filter.mp hx).1⟩) ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (Finset.mem_filter.mp hx).2
  · intro x1 _ x2 _ h
    exact congrArg Fin.val h
  · intro x hx
    refine ⟨x.val, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr x.isLt, (Finset.mem_filter.mp hx).2⟩, rfl⟩

private theorem rawCount_eq_sum_mass (w t : Nat) (left right : Rows) :
    let D := 2 ^ w
    let L := w + t
    rawCount w t left right =
      ∑ s : Fin D, ∑ z : Fin D, if rightOk w right s.val z.val then massF w left L s.val z.val else 0 := by
  intro D L
  let n := L + w
  have hwn : w + L = n := by dsimp [n, L]; omega
  unfold rawCount
  dsimp only
  rw [list_filter_length_eq_finset_card (2 ^ n)]
  have hpart : ∀ x : Fin (2 ^ n),
      ((Finset.univ : Finset (Fin D)).product (Finset.univ : Finset (Fin D))).filter
        (fun p => x.val % D = p.1.val ∧ (x.val >>> L) % D = p.2.val) =
      {(⟨x.val % D, Nat.mod_lt _ (by positivity)⟩, ⟨(x.val >>> L) % D, Nat.mod_lt _ (by positivity)⟩)} := by
    intro x
    ext ⟨s, z⟩
    simp [Fin.ext_iff, eq_comm]
  have hfib := Finset.card_eq_sum_card_fiberwise
    (f := fun x : Fin (2 ^ n) =>
      ((⟨x.val % D, Nat.mod_lt _ (by positivity)⟩ : Fin D),
       (⟨(x.val >>> L) % D, Nat.mod_lt _ (by positivity)⟩ : Fin D)))
    (s := (Finset.univ : Finset (Fin (2 ^ n))).filter (fun word =>
      (List.range n).all (fun site =>
        let pat := patAt w n word.val site
        if site < L then left site pat else right (site - L) pat) = true))
    (t := (Finset.univ : Finset (Fin D × Fin D)))
    (fun _ _ => Finset.mem_univ _)
  rw [hfib, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro z _
  have hcard : massF w left L s.val z.val =
      ((Finset.univ : Finset (Fin (2 ^ n))).filter (fun word =>
        word.val % D = s.val ∧ (word.val >>> L) % D = z.val ∧
        (List.range L).all (fun i => left i ((word.val >>> i) % (2 * D))) = true)).card := by
    unfold massF
    rw [hwn, list_filter_length_eq_finset_card (2 ^ n)]
    congr 1
    ext word
    simp [Bool.and_eq_true, beq_iff_eq, D, and_assoc]
  by_cases hr : rightOk w right s.val z.val = true
  · simp only [hr, ↓reduceIte, hcard]
    congr 1
    ext word
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq, Fin.ext_iff]
    constructor
    · rintro ⟨hall, hs, hz⟩
      refine ⟨hs, hz, ?_⟩
      rw [List.all_eq_true] at hall ⊢
      intro i hi
      have hlt : i < L := List.mem_range.mp hi
      have h' := hall i (List.mem_range.mpr (by omega))
      simp only [hlt, ↓reduceIte] at h'
      rw [patAt_left w t word.val i hlt] at h'
      exact h'
    · rintro ⟨hs, hz, hleft⟩
      refine ⟨?_, hs, hz⟩
      rw [List.all_eq_true] at hleft ⊢
      intro site hsite
      have hsn : site < n := List.mem_range.mp hsite
      by_cases hlt : site < L
      · simp only [hlt, ↓reduceIte]
        rw [patAt_left w t word.val site hlt]
        exact hleft site (List.mem_range.mpr hlt)
      · simp only [hlt, ↓reduceIte]
        have hjs : site - L < w := by omega
        have heq : site = L + (site - L) := by omega
        rw [heq, patAt_right w t word.val (site - L) hjs]
        rw [Nat.add_sub_cancel_left, hs, hz]
        unfold rightOk at hr
        rw [List.all_eq_true] at hr
        exact hr (site - L) (List.mem_range.mpr hjs)
  · simp only [hr, Bool.false_eq_true, ↓reduceIte]
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro word hmem
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq, Fin.ext_iff] at hmem
    obtain ⟨hall, hs, hz⟩ := hmem
    apply hr
    unfold rightOk
    rw [List.all_eq_true] at hall ⊢
    intro j hj
    have hjw : j < w := List.mem_range.mp hj
    have h' := hall (L + j) (List.mem_range.mpr (by omega))
    have hge : ¬ (L + j < L) := by omega
    simp only [hge, ↓reduceIte, Nat.add_sub_cancel_left] at h'
    rw [patAt_right w t word.val j hjw, hs, hz] at h'
    exact h'

private theorem mass_le_two_pow (w t : Nat) (rows : Rows) (s z : Nat) :
    massF w rows (w + t) s z ≤ 2 ^ t := by
  unfold massF
  rw [list_filter_length_eq_finset_card]
  have hcard : Fintype.card (Fin (2 ^ t)) = 2 ^ t := Fintype.card_fin _
  rw [← hcard]
  let S := (Finset.univ : Finset (Fin (2 ^ (w + (w + t))))).filter (fun bits =>
    (bits.val % 2 ^ w == s && (bits.val >>> (w + t)) % 2 ^ w == z &&
      (List.range (w + t)).all (fun i => rows i ((bits.val >>> i) % (2 * 2 ^ w)))) = true)
  have hpow : 2 ^ (w + (w + t)) = 2 ^ (w + t) * 2 ^ w := by
    rw [Nat.add_comm w (w + t), pow_add]
  have hinj : Set.InjOn (fun bits : Fin (2 ^ (w + (w + t))) =>
      (⟨(bits.val / 2 ^ w) % 2 ^ t, Nat.mod_lt _ (by positivity)⟩ : Fin (2 ^ t))) S := by
    intro x hx y hy hxy
    simp only [Finset.mem_coe, S, Finset.mem_filter, Finset.mem_univ, true_and, Bool.and_eq_true, beq_iff_eq] at hx hy
    have hmid : (x.val / 2 ^ w) % 2 ^ t = (y.val / 2 ^ w) % 2 ^ t := congrArg Fin.val hxy
    have hxs : x.val % 2 ^ w = y.val % 2 ^ w := hx.1.1.trans hy.1.1.symm
    have hxz : x.val >>> (w + t) = y.val >>> (w + t) := by
      have h1 : x.val >>> (w + t) < 2 ^ w := by
        rw [Nat.shiftRight_eq_div_pow]
        exact Nat.div_lt_of_lt_mul (hpow ▸ x.isLt)
      have h2 : y.val >>> (w + t) < 2 ^ w := by
        rw [Nat.shiftRight_eq_div_pow]
        exact Nat.div_lt_of_lt_mul (hpow ▸ y.isLt)
      rw [← Nat.mod_eq_of_lt h1, ← Nat.mod_eq_of_lt h2]
      exact hx.1.2.trans hy.1.2.symm
    rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow] at hxz
    apply Fin.ext
    have hdx : x.val = 2 ^ w * (x.val / 2 ^ w) + x.val % 2 ^ w := (Nat.div_add_mod x.val (2 ^ w)).symm
    have hdy : y.val = 2 ^ w * (y.val / 2 ^ w) + y.val % 2 ^ w := (Nat.div_add_mod y.val (2 ^ w)).symm
    have hdx2 : x.val / 2 ^ w = 2 ^ t * (x.val / 2 ^ w / 2 ^ t) + (x.val / 2 ^ w) % 2 ^ t :=
      (Nat.div_add_mod (x.val / 2 ^ w) (2 ^ t)).symm
    have hdy2 : y.val / 2 ^ w = 2 ^ t * (y.val / 2 ^ w / 2 ^ t) + (y.val / 2 ^ w) % 2 ^ t :=
      (Nat.div_add_mod (y.val / 2 ^ w) (2 ^ t)).symm
    rw [Nat.div_div_eq_div_mul, ← pow_add] at hdx2 hdy2
    rw [hdx, hdy, hdx2, hdy2, hxs, hmid, hxz]
  have hle := Finset.card_le_card_of_injOn
    (f := fun bits : Fin (2 ^ (w + (w + t))) =>
      (⟨(bits.val / 2 ^ w) % 2 ^ t, Nat.mod_lt _ (by positivity)⟩ : Fin (2 ^ t)))
    (fun _ _ => Finset.mem_univ _) hinj
  exact hle.trans (by simp)

private theorem upper_le_lower_pow8 (w t m : Nat) (hw : 0 < w) :
    let D := 2 ^ w
    let C := if m = 0 then 2 ^ t else min (2 ^ t) m
    let lower := 2 ^ ((D / 2) * Nat.log2 C)
    let upper := C ^ (2 * D)
    upper ≤ lower ^ 8 := by
  intro D C lower upper
  have hC1 : 1 ≤ C := by
    dsimp [C]
    split_ifs with hm
    · exact Nat.one_le_pow _ _ (by decide)
    · exact le_min (Nat.one_le_pow _ _ (by decide)) (by omega)
  have hCbound : C ≤ 2 ^ (2 * Nat.log2 C) := by
    by_cases h1 : C = 1
    · rw [h1]; decide
    · have hge2 : 2 ≤ C := by omega
      have hlog : 1 ≤ Nat.log2 C := (Nat.le_log2 (by omega)).mpr (by simpa using hge2)
      have hlt : C < 2 ^ (Nat.log2 C + 1) := by
        by_contra hle
        have hge : 2 ^ (Nat.log2 C + 1) ≤ C := by omega
        have := (Nat.le_log2 (by omega)).mpr hge
        omega
      have hexp : Nat.log2 C + 1 ≤ 2 * Nat.log2 C := by omega
      exact (Nat.le_of_lt hlt).trans (Nat.pow_le_pow_right (by decide) hexp)
  have hDeven : 2 * (D / 2) = D := by
    dsimp [D]
    have : 2 ^ w = 2 * 2 ^ (w - 1) := by rw [← pow_succ', Nat.sub_add_cancel hw]
    omega
  have hpow : lower ^ 8 = (2 ^ (2 * Nat.log2 C)) ^ (2 * D) := by
    dsimp [lower]
    rw [← pow_mul, ← pow_mul]
    congr 1
    have : (D / 2) * Nat.log2 C * 8 = 2 * Nat.log2 C * (2 * (2 * (D / 2))) := by ring
    rw [this, hDeven]
  rw [hpow]
  exact Nat.pow_le_pow_left hCbound (2 * D)

private theorem upper_protocol (w t m : Nat) :
    let D := 2 ^ w
    let C := if m = 0 then 2 ^ t else min (2 ^ t) m
    let upper := C ^ (2 * D)
    ∃ (encode : Rows → Fin upper) (read : Fin upper → Rows → Nat),
      ∀ p q : Rows, goodF w t p → read (encode p) q = countF w t m p q := by
  intro D C upper
  have hCpos : 0 < C := by
    dsimp [C]
    split_ifs with hm
    · positivity
    · exact lt_min (by positivity) (by omega)
  have hcard : Fintype.card ((Fin D → Fin C) × (Fin D → Fin C)) = upper := by
    rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    dsimp [upper]
    rw [← pow_add, two_mul]
  let e : ((Fin D → Fin C) × (Fin D → Fin C)) ≃ Fin upper := Fintype.equivFinOfCardEq hcard
  let useExact : Bool := decide (m = 0 ∨ 2 ^ t ≤ m)
  have hCeq : if useExact = true then C = 2 ^ t else C = m ∧ 0 < m := by
    dsimp [useExact, C]
    by_cases hm : m = 0
    · simp [hm]
    · by_cases hle : 2 ^ t ≤ m
      · simp [hm, hle]
      · have hlt : m < 2 ^ t := by omega
        simp [hm, hle, Nat.min_eq_right (le_of_lt hlt)]
        omega
  classical
  let encode : Rows → Fin upper := fun p =>
    if h : goodF w t p then
      let a := Classical.choose h
      let b := Classical.choose (Classical.choose_spec h)
      if hEx : useExact = true then
        e (fun i => ⟨(a i - 1) % C, Nat.mod_lt _ hCpos⟩,
           fun j => ⟨(b j - 1) % C, Nat.mod_lt _ hCpos⟩)
      else
        e (fun i => ⟨a i % C, Nat.mod_lt _ hCpos⟩,
           fun j => ⟨b j % C, Nat.mod_lt _ hCpos⟩)
    else
      e (fun _ => ⟨0, hCpos⟩, fun _ => ⟨0, hCpos⟩)
  let read : Fin upper → Rows → Nat := fun code q =>
    let ab := e.symm code
    (∑ s : Fin D, ∑ z : Fin D,
      if rightOk w q s.val z.val then
        if useExact = true then ((ab.1 s).val + 1) * ((ab.2 z).val + 1)
        else (ab.1 s).val * (ab.2 z).val
      else 0) % m
  refine ⟨encode, read, fun p q hp => ?_⟩
  have hspec := Classical.choose_spec (Classical.choose_spec hp)
  set a := Classical.choose hp
  set b := Classical.choose (Classical.choose_spec hp)
  obtain ⟨haPos, hbPos, hmass⟩ := hspec
  have habLe : ∀ s z : Fin D, a s * b z ≤ 2 ^ t := fun s z => by
    rw [← hmass s z]; exact mass_le_two_pow w t p s.val z.val
  have h0D : 0 < D := by positivity
  have haLe : ∀ s : Fin D, a s ≤ 2 ^ t := fun s =>
    (Nat.le_mul_of_pos_right (a s) (hbPos ⟨0, h0D⟩)).trans (habLe s ⟨0, h0D⟩)
  have hbLe : ∀ z : Fin D, b z ≤ 2 ^ t := fun z =>
    (Nat.le_mul_of_pos_left (b z) (haPos ⟨0, h0D⟩)).trans (habLe ⟨0, h0D⟩ z)
  unfold countF
  rw [rawCount_eq_sum_mass w t p q]
  by_cases hEx : useExact = true
  · have hC2t : C = 2 ^ t := by simpa [hEx] using hCeq
    have henc : e.symm (encode p) =
        (fun i => ⟨(a i - 1) % C, Nat.mod_lt _ hCpos⟩,
         fun j => ⟨(b j - 1) % C, Nat.mod_lt _ hCpos⟩) := by
      dsimp only [encode]
      simp only [hp, hEx, ↓reduceDIte, Equiv.symm_apply_apply]
      rfl
    dsimp only [read]
    rw [henc]
    simp only [hEx, ↓reduceIte]
    congr 1
    apply Finset.sum_congr rfl; intro s _
    apply Finset.sum_congr rfl; intro z _
    split_ifs
    · have ha1 : (a s - 1) % C + 1 = a s := by
        have h1 : 0 < a s := haPos s
        have h2 : a s ≤ 2 ^ t := haLe s
        rw [hC2t, Nat.mod_eq_of_lt (by omega)]
        omega
      have hb1 : (b z - 1) % C + 1 = b z := by
        have h1 : 0 < b z := hbPos z
        have h2 : b z ≤ 2 ^ t := hbLe z
        rw [hC2t, Nat.mod_eq_of_lt (by omega)]
        omega
      rw [ha1, hb1, hmass s z]
    · rfl
  · have hCm : C = m := (by simpa [hEx] using hCeq : C = m ∧ 0 < m).1
    have hExf : useExact = false := by cases h : useExact; rfl; exact False.elim (hEx h)
    have henc : e.symm (encode p) =
        (fun i => ⟨a i % C, Nat.mod_lt _ hCpos⟩,
         fun j => ⟨b j % C, Nat.mod_lt _ hCpos⟩) := by
      dsimp only [encode]
      simp only [hp, hExf, Bool.false_eq_true, ↓reduceDIte, Equiv.symm_apply_apply]
      rfl
    dsimp only [read]
    rw [henc]
    simp only [hExf, Bool.false_eq_true, ↓reduceIte]
    rw [Finset.sum_nat_mod]
    conv_rhs => rw [Finset.sum_nat_mod]
    congr 1
    apply Finset.sum_congr rfl; intro s _
    rw [Finset.sum_nat_mod]
    conv_rhs => rw [Finset.sum_nat_mod]
    congr 1
    apply Finset.sum_congr rfl; intro z _
    split_ifs
    · rw [hCm, hmass s z, ← Nat.mul_mod]
    · rfl

private def copyRow (w : Nat) : Nat → Bool :=
  fun pat => (pat % 2) == ((pat / 2 ^ w) % 2)

private def consCopy (w : Nat) (rows : Rows) : Rows :=
  fun site pat => if site = 0 then copyRow w pat else rows (site - 1) pat

private def rotR (w s : Nat) : Nat :=
  s / 2 + (s % 2) * 2 ^ (w - 1)

private theorem mod_mul_split (x a b : Nat) : x % (a * b) = x % a + a * (x / a % b) := by
  by_cases ha : a = 0
  · subst ha; simp
  · by_cases hb : b = 0
    · subst hb; simp [Nat.mod_add_div]
    · have h1 : x = a * b * (x / a / b) + (x % a + a * (x / a % b)) := by
        have hxa := (Nat.div_add_mod x a).symm
        have hxb := (Nat.div_add_mod (x / a) b).symm
        calc x = a * (x / a) + x % a := hxa
        _ = a * (b * (x / a / b) + x / a % b) + x % a := by rw [← hxb]
        _ = a * b * (x / a / b) + (x % a + a * (x / a % b)) := by ring
      have hlt : x % a + a * (x / a % b) < a * b := by
        have hma : x % a < a := Nat.mod_lt x (by omega)
        have hmb : x / a % b < b := Nat.mod_lt (x / a) (by omega)
        have hle : a * (x / a % b + 1) ≤ a * b := Nat.mul_le_mul_left a (by omega)
        have hmul : a * (x / a % b + 1) = a * (x / a % b) + a := by ring
        omega
      conv_lhs => rw [h1]
      rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]

private theorem rotR_lt (w s : Nat) (hw : 0 < w) (hs : s < 2 ^ w) : rotR w s < 2 ^ w := by
  unfold rotR
  have h2 : 2 ^ w = 2 * 2 ^ (w - 1) := by rw [← pow_succ', Nat.sub_add_cancel hw]
  have h01 : s % 2 = 0 ∨ s % 2 = 1 := by omega
  rcases h01 with h | h <;> rw [h] <;> omega

private theorem mass_consCopy (w h s z : Nat) (hw : 0 < w) (hs : s < 2 ^ w) (rows : Rows) :
    massF w (consCopy w rows) (h + 1) s z = massF w rows h (rotR w s) z := by
  have h2w : 2 ^ w = 2 * 2 ^ (w - 1) := by rw [← pow_succ', Nat.sub_add_cancel hw]
  unfold massF
  rw [list_filter_length_eq_finset_card, list_filter_length_eq_finset_card]
  have hpow : 2 ^ (w + (h + 1)) = 2 * 2 ^ (w + h) := by
    rw [show w + (h + 1) = (w + h) + 1 by omega, pow_succ']
  refine Finset.card_bij
    (fun (x : Fin (2 ^ (w + (h + 1)))) _ => (⟨x.val / 2, by have := x.isLt; omega⟩ : Fin (2 ^ (w + h))))
    ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Bool.and_eq_true, beq_iff_eq] at hx ⊢
    obtain ⟨⟨hmod, htail⟩, hall⟩ := hx
    rw [List.all_eq_true] at hall
    have h0 : copyRow w (x.val % (2 * 2 ^ w)) = true := by
      have := hall 0 (List.mem_range.mpr (by omega))
      simpa [consCopy] using this
    unfold copyRow at h0
    simp only [beq_iff_eq] at h0
    have hxmod2 : x.val % 2 = s % 2 := by
      have : (x.val % 2 ^ w) % 2 = s % 2 := congrArg (· % 2) hmod
      have hdiv2 : 2 ∣ 2 ^ w := ⟨2 ^ (w - 1), h2w⟩
      rwa [Nat.mod_mod_of_dvd x.val hdiv2] at this
    have hlow : (x.val / 2) % 2 ^ (w - 1) = s / 2 := by
      have h1 := mod_mul_split x.val 2 (2 ^ (w - 1))
      rw [h2w] at hmod
      rw [h1, hxmod2] at hmod
      omega
    have hhi : ((x.val / 2) / 2 ^ (w - 1)) % 2 = s % 2 := by
      have hdiv2w : 2 ∣ 2 * 2 ^ w := ⟨2 ^ w, rfl⟩
      rw [Nat.mod_mod_of_dvd x.val hdiv2w, hxmod2] at h0
      have hsub : (x.val % (2 * 2 ^ w)) / 2 ^ w = (x.val / 2 ^ w) % 2 := by
        rw [Nat.mul_comm 2 (2 ^ w), Nat.mod_mul_right_div_self]
      rw [hsub, Nat.mod_mod_of_dvd _ (dvd_refl 2)] at h0
      rw [h2w, ← Nat.div_div_eq_div_mul] at h0
      exact h0.symm
    have hrot : (x.val / 2) % 2 ^ w = rotR w s := by
      rw [h2w, Nat.mul_comm 2 (2 ^ (w - 1)), mod_mul_split, hlow, hhi]
      unfold rotR
      ring
    refine ⟨⟨hrot, ?_⟩, ?_⟩
    · rw [Nat.shiftRight_eq_div_pow] at htail ⊢
      rw [pow_succ', ← Nat.div_div_eq_div_mul] at htail
      exact htail
    · rw [List.all_eq_true]
      intro i hi
      have hi' : i < h := List.mem_range.mp hi
      have hstep := hall (i + 1) (List.mem_range.mpr (by omega))
      simp only [consCopy, Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel] at hstep
      rw [Nat.shiftRight_eq_div_pow] at hstep ⊢
      rw [pow_succ', ← Nat.div_div_eq_div_mul] at hstep
      exact hstep
  · intro x1 hx1 x2 hx2 hdiv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Bool.and_eq_true, beq_iff_eq] at hx1 hx2
    have hq : x1.val / 2 = x2.val / 2 := congrArg Fin.val hdiv
    have hdiv2 : 2 ∣ 2 ^ w := ⟨2 ^ (w - 1), h2w⟩
    have hr1 : x1.val % 2 = s % 2 := by
      have := congrArg (· % 2) hx1.1.1; rwa [Nat.mod_mod_of_dvd _ hdiv2] at this
    have hr2 : x2.val % 2 = s % 2 := by
      have := congrArg (· % 2) hx2.1.1; rwa [Nat.mod_mod_of_dvd _ hdiv2] at this
    apply Fin.ext; omega
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Bool.and_eq_true, beq_iff_eq] at hy
    obtain ⟨⟨hymod, hytail⟩, hyall⟩ := hy
    rw [List.all_eq_true] at hyall
    let xval := s % 2 + 2 * y.val
    have hxlt : xval < 2 ^ (w + (h + 1)) := by
      dsimp [xval]; have := y.isLt; omega
    refine ⟨⟨xval, hxlt⟩, ?_, Fin.ext (by dsimp [xval]; omega)⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Bool.and_eq_true, beq_iff_eq]
    have hydiv : y.val / 2 ^ (w - 1) % 2 = s % 2 ∧ y.val % 2 ^ (w - 1) = s / 2 := by
      rw [h2w, Nat.mul_comm 2 (2 ^ (w - 1)), mod_mul_split] at hymod
      unfold rotR at hymod
      have h1 : y.val % 2 ^ (w - 1) < 2 ^ (w - 1) := Nat.mod_lt _ (by positivity)
      have h2 : s / 2 < 2 ^ (w - 1) := by omega
      constructor
      · have hq := congrArg (· / 2 ^ (w - 1)) hymod
        rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt h1, Nat.zero_add,
          Nat.mul_comm (s % 2), Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt h2, Nat.zero_add] at hq
        exact hq
      · have hr := congrArg (· % 2 ^ (w - 1)) hymod
        rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h1,
          Nat.mul_comm (s % 2), Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h2] at hr
        exact hr
    have hxmod : xval % 2 ^ w = s := by
      rw [h2w, mod_mul_split]
      have h1 : xval % 2 = s % 2 := by dsimp [xval]; omega
      have h2 : xval / 2 = y.val := by dsimp [xval]; omega
      rw [h1, h2, hydiv.2]; omega
    have hxtail : (xval >>> (h + 1)) % 2 ^ w = z := by
      rw [Nat.shiftRight_eq_div_pow, pow_succ', ← Nat.div_div_eq_div_mul]
      have h2 : xval / 2 = y.val := by dsimp [xval]; omega
      rw [h2, ← Nat.shiftRight_eq_div_pow]
      exact hytail
    refine ⟨⟨hxmod, hxtail⟩, ?_⟩
    rw [List.all_eq_true]
    intro i hi
    have hi' : i < h + 1 := List.mem_range.mp hi
    cases i with
    | zero =>
      simp only [consCopy, ↓reduceIte, Nat.shiftRight_zero, copyRow, beq_iff_eq]
      have hdiv2w : 2 ∣ 2 * 2 ^ w := ⟨2 ^ w, rfl⟩
      rw [Nat.mod_mod_of_dvd xval hdiv2w]
      have h1 : xval % 2 = s % 2 := by dsimp [xval]; omega
      have hsub : (xval % (2 * 2 ^ w)) / 2 ^ w = (xval / 2 ^ w) % 2 := by
        rw [Nat.mul_comm 2 (2 ^ w), Nat.mod_mul_right_div_self]
      rw [h1, hsub, Nat.mod_mod_of_dvd _ (dvd_refl 2), h2w, ← Nat.div_div_eq_div_mul]
      have h2 : xval / 2 = y.val := by dsimp [xval]; omega
      rw [h2, hydiv.1]
    | succ i' =>
      simp only [consCopy, Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
      rw [Nat.shiftRight_eq_div_pow, pow_succ', ← Nat.div_div_eq_div_mul]
      have h2 : xval / 2 = y.val := by dsimp [xval]; omega
      rw [h2, ← Nat.shiftRight_eq_div_pow]
      exact hyall i' (List.mem_range.mpr (by omega))

private def padCopy (w : Nat) : Nat → Rows → Rows
  | 0, rows => rows
  | d + 1, rows => consCopy w (padCopy w d rows)

private theorem mass_padCopy (w : Nat) (hw : 0 < w) (rows : Rows) :
    ∀ (d h s z : Nat), s < 2 ^ w →
      massF w (padCopy w d rows) (h + d) s z = massF w rows h ((rotR w)^[d] s) z := by
  intro d
  induction d with
  | zero => intro h s z _; simp [padCopy]
  | succ d ih =>
    intro h s z hs
    rw [padCopy, show h + (d + 1) = (h + d) + 1 by omega, mass_consCopy w (h + d) s z hw hs,
      ih h (rotR w s) z (rotR_lt w s hw hs), Function.iterate_succ_apply]

private theorem rotR_iter_lt (w : Nat) (hw : 0 < w) :
    ∀ (d s : Nat), s < 2 ^ w → (rotR w)^[d] s < 2 ^ w := by
  intro d
  induction d with
  | zero => intro s hs; simpa using hs
  | succ d ih =>
    intro s hs
    rw [Function.iterate_succ_apply]
    exact ih (rotR w s) (rotR_lt w s hw hs)

private def table513 (w : Nat) (flags : Nat → Nat → Bool) : Rows :=
  let D := 2 ^ w
  fun site pattern =>
    let old := pattern % 2
    let newBit := (pattern / D) % 2
    decide (site < w) || (old == newBit) ||
      ((old == 1) == flags (site - w) ((pattern % D) / 2))

private def undoF (w : Nat) (v : Nat → Nat) (j : Nat) : Nat :=
  let H := 2 ^ w / 2
  let x := v (j / 2)
  let y := v (j / 2 + H)
  if j % 2 = 0 then (if x < y then x else x - y)
  else (if x < y then y - x else y)

private theorem undoF_congr (w : Nat) (v1 v2 : Nat → Nat)
    (h : ∀ z < 2 ^ w, v1 z = v2 z) :
    ∀ j < 2 ^ w, undoF w v1 j = undoF w v2 j := by
  intro j hj
  unfold undoF
  dsimp only
  have h1 : j / 2 < 2 ^ w := by omega
  have h2 : j / 2 + 2 ^ w / 2 < 2 ^ w := by omega
  rw [h _ h1, h _ h2]

private theorem back_congr (w : Nat) (v1 v2 : Nat → Nat)
    (h : ∀ z < 2 ^ w, v1 z = v2 z) :
    ∀ (steps j : Nat), j < 2 ^ w →
      Nat.rec (motive := fun _ => Nat → Nat) v1 (fun _ prev => undoF w prev) steps j =
      Nat.rec (motive := fun _ => Nat → Nat) v2 (fun _ prev => undoF w prev) steps j := by
  intro steps
  induction steps with
  | zero => exact h
  | succ steps ih =>
    intro j hj
    exact undoF_congr w _ _ ih j hj

private def rightFor (w : Nat) (T : Fin (2 ^ w) → Bool) : Rows :=
  let D := 2 ^ w
  fun j pat =>
    if j = 0 then decide ((pat / D) % 2 = 0) && T ⟨pat % D, Nat.mod_lt _ (by positivity)⟩
    else decide ((pat / D) % 2 = 0)

private theorem rightOk_rightFor (w : Nat) (hw : 0 < w) (T : Fin (2 ^ w) → Bool)
    (s z : Fin (2 ^ w)) :
    rightOk w (rightFor w T) s.val z.val = (decide (s.val = 0) && T z) := by
  let D := 2 ^ w
  have hbit : ∀ j < w, ((((z.val + s.val * D) >>> j) % (2 * D)) / D) % 2 = (s.val.testBit j).toNat := by
    intro j hj
    have h1 : ((((z.val + s.val * D) >>> j) % (2 * D)) / D) % 2 =
        ((((z.val + s.val * D) >>> j) % (2 * D)).testBit w).toNat := by
      rw [Nat.testBit_eq_decide_div_mod_eq]
      have h01 : (((z.val + s.val * D) >>> j) % (2 * D) / D) % 2 < 2 := Nat.mod_lt _ (by decide)
      dsimp [D]
      interval_cases (((z.val + s.val * D) >>> j) % (2 * 2 ^ w) / 2 ^ w) % 2 <;> decide
    rw [h1]
    congr 1
    have h2 : 2 * D = 2 ^ (w + 1) := by dsimp [D]; rw [pow_succ']
    rw [h2, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
    simp only [Nat.lt_add_one, decide_true, Bool.true_and]
    rw [testBit_add_mul_two_pow z.val s.val w (j + w) z.isLt]
    have hge : ¬ (j + w < w) := by omega
    simp only [hge, ↓reduceIte, Nat.add_sub_cancel]
  apply Bool.eq_iff_iff.mpr
  unfold rightOk
  rw [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · intro hall
    have h0 := hall 0 (List.mem_range.mpr hw)
    simp only [rightFor, ↓reduceIte, Nat.shiftRight_zero, Bool.and_eq_true, decide_eq_true_eq] at h0
    have hzmod : (z.val + s.val * D) % (2 * D) % D = z.val := by
      have hdvd : D ∣ 2 * D := ⟨2, by ring⟩
      rw [Nat.mod_mod_of_dvd _ hdvd, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt z.isLt]
    have hT : T z = true := by
      have hfin : (⟨(z.val + s.val * D) % (2 * D) % D, Nat.mod_lt _ (by positivity)⟩ : Fin D) = z :=
        Fin.ext hzmod
      rw [hfin] at h0
      exact h0.2
    have hs0 : s.val = 0 := by
      apply Nat.eq_of_testBit_eq
      intro j
      rw [Nat.zero_testBit]
      by_cases hj : j < w
      · have hj' := hall j (List.mem_range.mpr hj)
        have htb : (s.val.testBit j).toNat = 0 := by
          rw [← hbit j hj]
          by_cases hj0 : j = 0
          · subst hj0; simpa using h0.1
          · simp only [rightFor, hj0, ↓reduceIte, decide_eq_true_eq] at hj'; exact hj'
        cases h : s.val.testBit j
        · rfl
        · rw [h] at htb; simp at htb
      · exact Nat.testBit_lt_two_pow (s.isLt.trans_le (Nat.pow_le_pow_right (by decide) (by omega)))
    exact ⟨hs0, hT⟩
  · rintro ⟨hs0, hT⟩
    intro j hj
    have hjw : j < w := List.mem_range.mp hj
    have hzero : ((((z.val + s.val * D) >>> j) % (2 * D)) / D) % 2 = 0 := by
      rw [hbit j hjw, hs0, Nat.zero_testBit]; rfl
    by_cases hj0 : j = 0
    · subst hj0
      simp only [rightFor, ↓reduceIte, Nat.shiftRight_zero, Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨by simpa using hzero, ?_⟩
      have hzmod : (z.val + s.val * D) % (2 * D) % D = z.val := by
        have hdvd : D ∣ 2 * D := ⟨2, by ring⟩
        rw [Nat.mod_mod_of_dvd _ hdvd, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt z.isLt]
      have hfin : (⟨(z.val + s.val * D) % (2 * D) % D, Nat.mod_lt _ (by positivity)⟩ : Fin D) = z :=
        Fin.ext hzmod
      rw [hfin]; exact hT
    · simp only [rightFor, hj0, ↓reduceIte, decide_eq_true_eq]
      exact hzero

private theorem count_rightFor (w t m : Nat) (hw : 0 < w) (left : Rows) (T : Fin (2 ^ w) → Bool) :
    countF w t m left (rightFor w T) =
      (∑ z : Fin (2 ^ w), if T z then massF w left (w + t) 0 z.val else 0) % m := by
  unfold countF
  rw [rawCount_eq_sum_mass w t left (rightFor w T)]
  congr 1
  have h0D : 0 < 2 ^ w := by positivity
  rw [Finset.sum_eq_single (⟨0, h0D⟩ : Fin (2 ^ w))]
  · apply Finset.sum_congr rfl
    intro z _
    rw [rightOk_rightFor w hw T ⟨0, h0D⟩ z]
    simp
  · intro s _ hs
    apply Finset.sum_eq_zero
    intro z _
    rw [rightOk_rightFor w hw T s z]
    have hne : s.val ≠ 0 := fun h => hs (Fin.ext h)
    simp [hne]
  · intro h; exact False.elim (h (Finset.mem_univ _))

private theorem mod_eq_imp_eq_of_bounds (x y m : Nat)
    (hx1 : 1 ≤ x) (hy1 : 1 ≤ y) (hxm : m = 0 ∨ x ≤ m) (hym : m = 0 ∨ y ≤ m)
    (heq : x % m = y % m) : x = y := by
  rcases hxm with rfl | hxm
  · simpa using heq
  · have hym' : y ≤ m := by rcases hym with rfl | h; omega; exact h
    by_cases hxl : x < m
    · by_cases hyl : y < m
      · rw [Nat.mod_eq_of_lt hxl, Nat.mod_eq_of_lt hyl] at heq; exact heq
      · have hy : y = m := by omega
        rw [hy, Nat.mod_self, Nat.mod_eq_of_lt hxl] at heq; omega
    · have hx : x = m := by omega
      by_cases hyl : y < m
      · rw [hx, Nat.mod_self, Nat.mod_eq_of_lt hyl] at heq; omega
      · omega

private def liftFlags {r H : Nat} (f : Fin r → Fin H → Bool) : Nat → Nat → Bool :=
  fun i u => if hi : i < r then if hu : u < H then f ⟨i, hi⟩ ⟨u, hu⟩ else false else false

private def leftOf {w t r : Nat} (f : Fin r → Fin (2 ^ w / 2) → Bool) : Rows :=
  padCopy w (t - r) (table513 w (liftFlags f))

private theorem family_props (w t m r : Nat) (hw : 0 < w) (hrt : r ≤ t)
    (hm : m = 0 ∨ 2 ^ r ≤ m) :
    let D := 2 ^ w
    let H := D / 2
    (∀ f : Fin r → Fin H → Bool, goodF w t (leftOf (w := w) (t := t) f)) ∧
    ∀ f1 f2 : Fin r → Fin H → Bool, f1 ≠ f2 →
      ∃ z : Fin D, massF w (leftOf (w := w) (t := t) f1) (w + t) 0 z.val % m ≠
                   massF w (leftOf (w := w) (t := t) f2) (w + t) 0 z.val % m := by
  intro D H
  have hmass_eq : ∀ (f : Fin r → Fin H → Bool) (s z : Fin D),
      massF w (leftOf (w := w) (t := t) f) (w + t) s.val z.val =
        massF w (table513 w (liftFlags f)) (w + r) 0 z.val ∧
      1 ≤ massF w (table513 w (liftFlags f)) (w + r) 0 z.val ∧
      massF w (table513 w (liftFlags f)) (w + r) 0 z.val ≤ 2 ^ r := by
    intro f s z
    have h513 := PEqualNP.Outside.L_lib_513 w r hw (liftFlags f)
    have hL : w + t = (w + r) + (t - r) := by omega
    rw [leftOf, hL, mass_padCopy w hw (table513 w (liftFlags f)) (t - r) (w + r) s.val z.val s.isLt]
    exact h513.1 ⟨(rotR w)^[t - r] s.val, rotR_iter_lt w hw (t - r) s.val s.isLt⟩ z
  constructor
  · intro f
    refine ⟨fun _ => 1, fun z => massF w (table513 w (liftFlags f)) (w + r) 0 z.val,
      fun _ => Nat.zero_lt_one, fun z => (hmass_eq f ⟨0, by positivity⟩ z).2.1, fun s z => ?_⟩
    rw [one_mul]
    exact (hmass_eq f s z).1
  · intro f1 f2 hne
    by_contra hall
    push Not at hall
    have heq_last : ∀ z < D,
        massF w (table513 w (liftFlags f1)) (w + r) 0 z =
        massF w (table513 w (liftFlags f2)) (w + r) 0 z := by
      intro z hz
      let zf : Fin D := ⟨z, hz⟩
      have h1 := hmass_eq f1 ⟨0, by positivity⟩ zf
      have h2 := hmass_eq f2 ⟨0, by positivity⟩ zf
      have hmod := hall zf
      rw [h1.1, h2.1] at hmod
      exact mod_eq_imp_eq_of_bounds _ _ m h1.2.1 h2.2.1
        (hm.imp id (fun h => h1.2.2.trans h))
        (hm.imp id (fun h => h2.2.2.trans h)) hmod
    have h513_1 := PEqualNP.Outside.L_lib_513 w r hw (liftFlags f1)
    have h513_2 := PEqualNP.Outside.L_lib_513 w r hw (liftFlags f2)
    apply hne
    funext i u
    have hb1 := h513_1.2.2 i u
    have hb2 := h513_2.2.2 i u
    have hD2 : 2 * H = D := by
      dsimp [H, D]
      have : 2 ^ w = 2 * 2 ^ (w - 1) := by rw [← pow_succ', Nat.sub_add_cancel hw]
      omega
    have hu1 : u.val < D := by have := u.isLt; omega
    have hu2 : u.val + H < D := by have := u.isLt; omega
    have hc1 := back_congr w _ _ heq_last (r - 1 - i.val) u.val hu1
    have hc2 := back_congr w _ _ heq_last (r - 1 - i.val) (u.val + H) hu2
    have hlf : liftFlags f1 i.val u.val = liftFlags f2 i.val u.val := by
      rw [← hb1, ← hb2]
      exact congrArg₂ Nat.blt hc2 hc1
    simpa [liftFlags, i.isLt, u.isLt] using hlf

private theorem random_subset_distinguishes {D : Nat} (m : Nat) (v1 v2 : Fin D → Nat)
    (z0 : Fin D) (hdiff : v1 z0 % m ≠ v2 z0 % m) :
    2 ^ D ≤ 2 * ((Finset.univ : Finset (Fin D → Bool)).filter (fun T =>
      (∑ z : Fin D, if T z then v1 z else 0) % m ≠ (∑ z : Fin D, if T z then v2 z else 0) % m)).card := by
  let flip : (Fin D → Bool) → (Fin D → Bool) := fun T z => if z = z0 then !T z else T z
  have hflip_invol : ∀ T, flip (flip T) = T := by
    intro T; funext z; dsimp [flip]; split_ifs <;> simp
  let A := (Finset.univ : Finset (Fin D → Bool)).filter (fun T =>
    (∑ z : Fin D, if T z then v1 z else 0) % m ≠ (∑ z : Fin D, if T z then v2 z else 0) % m)
  have hcover : ∀ T : Fin D → Bool, T ∈ A ∨ flip T ∈ A := by
    intro T
    by_cases hT : T ∈ A
    · exact Or.inl hT
    · right
      simp only [A, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hT ⊢
      intro hF
      have hsplit : ∀ (v : Fin D → Nat) (U : Fin D → Bool),
          ∑ z : Fin D, (if U z then v z else 0) =
            (if U z0 then v z0 else 0) + ∑ z ∈ Finset.univ.erase z0, (if U z then v z else 0) := by
        intro v U
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ z0)]
      have hrest : ∀ v : Fin D → Nat,
          ∑ z ∈ Finset.univ.erase z0, (if flip T z then v z else 0) =
          ∑ z ∈ Finset.univ.erase z0, (if T z then v z else 0) := by
        intro v
        apply Finset.sum_congr rfl
        intro z hz
        have hne : z ≠ z0 := (Finset.mem_erase.mp hz).1
        simp [flip, hne]
      rw [hsplit v1 T, hsplit v2 T] at hT
      rw [hsplit v1 (flip T), hsplit v2 (flip T), hrest v1, hrest v2] at hF
      set R1 := ∑ z ∈ Finset.univ.erase z0, if T z then v1 z else 0
      set R2 := ∑ z ∈ Finset.univ.erase z0, if T z then v2 z else 0
      have hadd_mod_cancel : ∀ a b c d : Nat, a % m = b % m → (c + a) % m = (d + b) % m → c % m = d % m := by
        intro a b c d hab hcd
        by_cases hm0 : m = 0
        · subst hm0; simp at hab hcd ⊢; omega
        · have h2 : (c % m + b % m) % m = (d % m + b % m) % m := by
            calc (c % m + b % m) % m = (c % m + a % m) % m := by rw [hab]
            _ = (c + a) % m := (Nat.add_mod c a m).symm
            _ = (d + b) % m := hcd
            _ = (d % m + b % m) % m := Nat.add_mod d b m
          have hc : c % m < m := Nat.mod_lt _ (by omega)
          have hd : d % m < m := Nat.mod_lt _ (by omega)
          have hb : b % m < m := Nat.mod_lt _ (by omega)
          set x := c % m; set y := d % m; set z := b % m
          have hmod : ∀ u : Nat, u < 2 * m → u % m = if u < m then u else u - m := fun u hu => by
            split_ifs with hlt
            · exact Nat.mod_eq_of_lt hlt
            · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
          rw [hmod (x + z) (by omega), hmod (y + z) (by omega)] at h2
          split_ifs at h2 <;> omega
      cases hTz : T z0
      · simp only [flip, ↓reduceIte, hTz, Bool.not_false, Bool.false_eq_true, zero_add] at hT hF
        exact hdiff (hadd_mod_cancel R1 R2 (v1 z0) (v2 z0) hT hF)
      · simp only [flip, ↓reduceIte, hTz, Bool.not_true, Bool.false_eq_true, zero_add] at hT hF
        exact hdiff (hadd_mod_cancel R1 R2 (v1 z0) (v2 z0) hF hT)
  have hunion : (Finset.univ : Finset (Fin D → Bool)) ⊆ A ∪ A.image flip := by
    intro T _
    rcases hcover T with h | h
    · exact Finset.mem_union_left _ h
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨flip T, h, hflip_invol T⟩)
  have hle := (Finset.card_le_card hunion).trans (Finset.card_union_le A (A.image flip))
  have himg : (A.image flip).card ≤ A.card := Finset.card_image_le
  have huniv : (Finset.univ : Finset (Fin D → Bool)).card = 2 ^ D := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  change 2 ^ D ≤ 2 * A.card
  omega

private def dec11 (vals : Fin 11 → Nat) : Nat :=
  match (List.finRange 11).find? (fun k =>
      6 ≤ ((List.finRange 11).filter (fun j => vals j == vals k)).length) with
  | some k => vals k
  | none => 0

private theorem dec11_eq_of_majority (vals : Fin 11 → Nat) (target : Nat)
    (hmaj : 6 ≤ ((Finset.univ : Finset (Fin 11)).filter (fun j => vals j = target)).card) :
    dec11 vals = target := by
  have hlen : ∀ v : Nat, ((List.finRange 11).filter (fun j => vals j == v)).length =
      ((Finset.univ : Finset (Fin 11)).filter (fun j => vals j = v)).card := by
    intro v
    rw [← List.toFinset_card_of_nodup ((List.nodup_finRange 11).filter _)]
    congr 1; ext j; simp [beq_iff_eq]
  have hne : ((Finset.univ : Finset (Fin 11)).filter (fun j => vals j = target)).Nonempty :=
    Finset.card_pos.mp (by omega)
  obtain ⟨k0, hk0⟩ := hne
  have hk0val : vals k0 = target := (Finset.mem_filter.mp hk0).2
  have hex : ∃ k ∈ List.finRange 11,
      decide (6 ≤ ((List.finRange 11).filter (fun j => vals j == vals k)).length) = true := by
    refine ⟨k0, List.mem_finRange k0, ?_⟩
    rw [decide_eq_true_eq, hlen, hk0val]
    exact hmaj
  unfold dec11
  cases hfind : (List.finRange 11).find? (fun k =>
      6 ≤ ((List.finRange 11).filter (fun j => vals j == vals k)).length) with
  | none =>
    obtain ⟨k, hkmem, hkpred⟩ := hex
    have := List.find?_eq_none.mp hfind k hkmem
    rw [hkpred] at this; exact False.elim (this rfl)
  | some k =>
    have hkpred := List.find?_some hfind
    rw [decide_eq_true_eq, hlen] at hkpred
    by_contra hneq
    have hdisj : Disjoint
        ((Finset.univ : Finset (Fin 11)).filter (fun j => vals j = vals k))
        ((Finset.univ : Finset (Fin 11)).filter (fun j => vals j = target)) := by
      rw [Finset.disjoint_filter]
      intro j _ h1 h2
      exact hneq (h1.symm.trans h2)
    have hsum := Finset.card_union_of_disjoint hdisj
    have hle : (((Finset.univ : Finset (Fin 11)).filter (fun j => vals j = vals k)) ∪
        ((Finset.univ : Finset (Fin 11)).filter (fun j => vals j = target))).card ≤ 11 :=
      (Finset.card_le_univ _).trans (by simp)
    omega

private theorem binom11_ineq (a b : Nat) (h2 : 2 * b ≤ a) (hpos : 0 < a + b) :
    8 * (462 * b ^ 6 * a ^ 5 + 330 * b ^ 7 * a ^ 4 + 165 * b ^ 8 * a ^ 3 +
         55 * b ^ 9 * a ^ 2 + 11 * b ^ 10 * a + b ^ 11) < (a + b) ^ 11 := by
  let u := a - 2 * b
  have ha : a = 2 * b + u := by omega
  rw [ha]
  have hid : (2 * b + u + b) ^ 11 =
      8 * (462 * b ^ 6 * (2 * b + u) ^ 5 + 330 * b ^ 7 * (2 * b + u) ^ 4 +
           165 * b ^ 8 * (2 * b + u) ^ 3 + 55 * b ^ 9 * (2 * b + u) ^ 2 +
           11 * b ^ 10 * (2 * b + u) + b ^ 11) +
      (4131 * b ^ 11 + 251691 * u * b ^ 10 + 715165 * u ^ 2 * b ^ 9 +
       912285 * u ^ 3 * b ^ 8 + 682110 * u ^ 4 * b ^ 7 + 333102 * u ^ 5 * b ^ 6 +
       112266 * u ^ 6 * b ^ 5 + 26730 * u ^ 7 * b ^ 4 + 4455 * u ^ 8 * b ^ 3 +
       495 * u ^ 9 * b ^ 2 + 33 * u ^ 10 * b + u ^ 11) := by ring
  rw [hid]
  have hrem : 0 < 4131 * b ^ 11 + u ^ 11 := by
    by_cases hb0 : b = 0
    · have hu : 0 < u := by omega
      have : 0 < u ^ 11 := pow_pos hu 11
      omega
    · have hb : 0 < b := by omega
      have : 0 < b ^ 11 := pow_pos hb 11
      omega
  omega

private theorem amp11_err_bound {R : Nat} (hR : 0 < R) (P : Fin R → Bool)
    (hgood : 2 * R ≤ 3 * ((Finset.univ : Finset (Fin R)).filter (fun c => P c = true)).card) :
    8 * ((Finset.univ : Finset (Fin 11 → Fin R)).filter (fun cs =>
      6 ≤ ((Finset.univ : Finset (Fin 11)).filter (fun k => P (cs k) = false)).card)).card < R ^ 11 := by
  let a := ((Finset.univ : Finset (Fin R)).filter (fun c => P c = true)).card
  let b := ((Finset.univ : Finset (Fin R)).filter (fun c => P c = false)).card
  have hab : a + b = R := by
    have hdisj : Disjoint
        ((Finset.univ : Finset (Fin R)).filter (fun c => P c = true))
        ((Finset.univ : Finset (Fin R)).filter (fun c => P c = false)) := by
      rw [Finset.disjoint_filter]; intro c _ h1 h2; rw [h1] at h2; exact Bool.noConfusion h2
    have hunion :
        ((Finset.univ : Finset (Fin R)).filter (fun c => P c = true)) ∪
        ((Finset.univ : Finset (Fin R)).filter (fun c => P c = false)) = Finset.univ := by
      ext c; simp
    have h := Finset.card_union_of_disjoint hdisj
    rw [hunion, Finset.card_univ, Fintype.card_fin] at h
    exact h.symm
  have h2ba : 2 * b ≤ a := by omega
  let errSet (cs : Fin 11 → Fin R) : Finset (Fin 11) :=
    (Finset.univ : Finset (Fin 11)).filter (fun k => P (cs k) = false)
  have hfib := Finset.card_eq_sum_card_fiberwise
    (f := errSet)
    (s := (Finset.univ : Finset (Fin 11 → Fin R)).filter (fun cs => 6 ≤ (errSet cs).card))
    (t := (Finset.univ : Finset (Finset (Fin 11))).filter (fun I => 6 ≤ I.card))
    (fun cs hcs => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hcs).2⟩)
  have hfiber_card : ∀ I : Finset (Fin 11),
      ((Finset.univ : Finset (Fin 11 → Fin R)).filter (fun cs => 6 ≤ (errSet cs).card) |>.filter
        (fun cs => errSet cs = I)).card =
      if 6 ≤ I.card then b ^ I.card * a ^ (11 - I.card) else 0 := by
    intro I
    by_cases hI : 6 ≤ I.card
    · simp only [hI, ↓reduceIte]
      have hset : ((Finset.univ : Finset (Fin 11 → Fin R)).filter (fun cs => 6 ≤ (errSet cs).card)).filter
            (fun cs => errSet cs = I) =
          Fintype.piFinset (fun k : Fin 11 =>
            if k ∈ I then (Finset.univ : Finset (Fin R)).filter (fun c => P c = false)
            else (Finset.univ : Finset (Fin R)).filter (fun c => P c = true)) := by
        ext cs
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
        constructor
        · rintro ⟨_, hEq⟩ k
          by_cases hk : k ∈ I
          · simp only [hk, ↓reduceIte, Finset.mem_filter, Finset.mem_univ, true_and]
            rw [← hEq] at hk; exact (Finset.mem_filter.mp hk).2
          · simp only [hk, ↓reduceIte, Finset.mem_filter, Finset.mem_univ, true_and]
            rw [← hEq] at hk
            simp only [errSet, Finset.mem_filter, Finset.mem_univ, true_and] at hk
            cases h : P (cs k); exact False.elim (hk h); rfl
        · intro hpi
          have hEq : errSet cs = I := by
            ext k
            simp only [errSet, Finset.mem_filter, Finset.mem_univ, true_and]
            have hk := hpi k
            by_cases hmem : k ∈ I
            · simp only [hmem, ↓reduceIte, Finset.mem_filter, Finset.mem_univ, true_and] at hk
              simp [hmem, hk]
            · simp only [hmem, ↓reduceIte, Finset.mem_filter, Finset.mem_univ, true_and] at hk
              simp [hmem, hk]
          exact ⟨hEq.symm ▸ hI, hEq⟩
      rw [hset, Fintype.card_piFinset]
      have hprod : ∏ k : Fin 11, (if k ∈ I then b else a) = b ^ I.card * a ^ (11 - I.card) := by
        rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
        have h1 : (Finset.univ.filter (fun k : Fin 11 => k ∈ I)).card = I.card := by
          congr 1; ext k; simp
        have h2 : (Finset.univ.filter (fun k : Fin 11 => k ∉ I)).card = 11 - I.card := by
          have hdisj : Disjoint (Finset.univ.filter (fun k : Fin 11 => k ∈ I))
              (Finset.univ.filter (fun k : Fin 11 => k ∉ I)) := by
            rw [Finset.disjoint_filter]; intro k _ h1 h2; exact h2 h1
          have hunion : Finset.univ.filter (fun k : Fin 11 => k ∈ I) ∪
              Finset.univ.filter (fun k : Fin 11 => k ∉ I) = Finset.univ := by
            ext k; simp [em]
          have hc := Finset.card_union_of_disjoint hdisj
          rw [hunion, Finset.card_univ, Fintype.card_fin, h1] at hc
          omega
        rw [h1, h2]
      rw [← hprod]
      apply Finset.prod_congr rfl
      intro k _
      split_ifs <;> rfl
    · simp only [hI, ↓reduceIte, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro cs hcs
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hcs
      rw [hcs.2] at hcs
      exact hI hcs.1
  have hsum_eq :
      ((Finset.univ : Finset (Fin 11 → Fin R)).filter (fun cs => 6 ≤ (errSet cs).card)).card =
      462 * b ^ 6 * a ^ 5 + 330 * b ^ 7 * a ^ 4 + 165 * b ^ 8 * a ^ 3 +
      55 * b ^ 9 * a ^ 2 + 11 * b ^ 10 * a + b ^ 11 := by
    rw [hfib]
    have hrewrite :
        ∑ I ∈ (Finset.univ : Finset (Finset (Fin 11))).filter (fun I => 6 ≤ I.card),
          (((Finset.univ : Finset (Fin 11 → Fin R)).filter (fun cs => 6 ≤ (errSet cs).card)).filter
            (fun cs => errSet cs = I)).card =
        ∑ I ∈ (Finset.univ : Finset (Finset (Fin 11))).filter (fun I => 6 ≤ I.card),
          b ^ I.card * a ^ (11 - I.card) := by
      apply Finset.sum_congr rfl
      intro I hI
      rw [hfiber_card I]
      simp only [(Finset.mem_filter.mp hI).2, ↓reduceIte]
    rw [hrewrite]
    have hgroup := Finset.sum_fiberwise_of_maps_to
      (s := (Finset.univ : Finset (Finset (Fin 11))).filter (fun I => 6 ≤ I.card))
      (t := Finset.Icc 6 11)
      (g := fun I : Finset (Fin 11) => I.card)
      (f := fun I : Finset (Fin 11) => b ^ I.card * a ^ (11 - I.card))
      (fun I hI => Finset.mem_Icc.mpr ⟨(Finset.mem_filter.mp hI).2, (Finset.card_le_univ I).trans (by simp)⟩)
    rw [← hgroup]
    have hterm : ∀ k ∈ Finset.Icc 6 11,
        ∑ I ∈ ((Finset.univ : Finset (Finset (Fin 11))).filter (fun I => 6 ≤ I.card)).filter (fun I => I.card = k),
          b ^ I.card * a ^ (11 - I.card) =
        Nat.choose 11 k * b ^ k * a ^ (11 - k) := by
      intro k hk
      have hk6 : 6 ≤ k := (Finset.mem_Icc.mp hk).1
      have hfilt : ((Finset.univ : Finset (Finset (Fin 11))).filter (fun I => 6 ≤ I.card)).filter (fun I => I.card = k) =
          Finset.powersetCard k (Finset.univ : Finset (Fin 11)) := by
        ext I
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_powersetCard, Finset.subset_univ]
        constructor
        · exact fun h => h.2
        · intro h; exact ⟨h ▸ hk6, h⟩
      rw [hfilt]
      have hcongr : ∑ I ∈ Finset.powersetCard k (Finset.univ : Finset (Fin 11)), b ^ I.card * a ^ (11 - I.card) =
          ∑ _I ∈ Finset.powersetCard k (Finset.univ : Finset (Fin 11)), (b ^ k * a ^ (11 - k)) := by
        apply Finset.sum_congr rfl
        intro I hI
        rw [(Finset.mem_powersetCard.mp hI).2]
      rw [hcongr, Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      ring
    rw [Finset.sum_congr rfl hterm]
    have hIcc : Finset.Icc 6 11 = {6, 7, 8, 9, 10, 11} := by decide
    rw [hIcc]
    simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Finset.sum_singleton,
      Nat.reduceEqDiff, or_self, not_false_eq_true]
    have hc6 : Nat.choose 11 6 = 462 := by decide
    have hc7 : Nat.choose 11 7 = 330 := by decide
    have hc8 : Nat.choose 11 8 = 165 := by decide
    have hc9 : Nat.choose 11 9 = 55 := by decide
    have hc10 : Nat.choose 11 10 = 11 := by decide
    have hc11 : Nat.choose 11 11 = 1 := by decide
    rw [hc6, hc7, hc8, hc9, hc10, hc11]
    ring
  rw [hsum_eq, ← hab]
  exact binom11_ineq a b h2ba (by omega)

private theorem det_lower_bound (w t m : Nat) (hw : 0 < w)
    (S : Nat) (send : Rows → Fin S) (answer : Fin S → Rows → Nat)
    (hcorr : ∀ left right : Rows, goodF w t left → answer (send left) right = countF w t m left right) :
    let D := 2 ^ w
    let C := if m = 0 then 2 ^ t else min (2 ^ t) m
    2 ^ ((D / 2) * Nat.log2 C) ≤ S := by
  intro D C
  let r := Nat.log2 C
  by_cases hr0 : r = 0
  · change 2 ^ ((D / 2) * r) ≤ S
    rw [hr0, Nat.mul_zero, pow_zero]
    exact Nat.pos_of_ne_zero (fun h0 => Fin.elim0 (h0 ▸ send (fun _ _ => true)))
  · have hCpos : 0 < C := by
      dsimp [C]; split_ifs with hm; positivity; exact lt_min (by positivity) (by omega)
    have h2rC : 2 ^ r ≤ C := (Nat.le_log2 (by omega)).mp le_rfl
    have hrt : r ≤ t := by
      have h2t : 2 ^ r ≤ 2 ^ t := by
        refine h2rC.trans ?_
        dsimp [C]; split_ifs; exact le_rfl; exact min_le_left _ _
      exact (Nat.pow_le_pow_iff_right (by decide)).mp h2t
    have hm : m = 0 ∨ 2 ^ r ≤ m := by
      by_cases hm0 : m = 0
      · exact Or.inl hm0
      · right
        refine h2rC.trans ?_
        dsimp [C]; simp only [hm0, ↓reduceIte]; exact min_le_right _ _
    obtain ⟨hgood, hdist⟩ := family_props w t m r hw hrt hm
    have hinj : Function.Injective (fun f : Fin r → Fin (D / 2) → Bool => send (leftOf (w := w) (t := t) f)) := by
      intro f1 f2 heq
      dsimp only at heq
      by_contra hne
      obtain ⟨z0, hz0⟩ := hdist f1 f2 hne
      let T : Fin D → Bool := fun z => decide (z = z0)
      have hc1 := hcorr (leftOf (w := w) (t := t) f1) (rightFor w T) (hgood f1)
      have hc2 := hcorr (leftOf (w := w) (t := t) f2) (rightFor w T) (hgood f2)
      rw [heq] at hc1
      have hceq : countF w t m (leftOf (w := w) (t := t) f1) (rightFor w T) =
                  countF w t m (leftOf (w := w) (t := t) f2) (rightFor w T) := hc1.symm.trans hc2
      rw [count_rightFor w t m hw, count_rightFor w t m hw] at hceq
      have hsum : ∀ rows : Rows, (∑ z : Fin D, if T z then massF w rows (w + t) 0 z.val else 0) =
          massF w rows (w + t) 0 z0.val := by
        intro rows
        rw [Finset.sum_eq_single z0]
        · simp [T]
        · intro z _ hne'; simp [T, hne']
        · intro h; exact False.elim (h (Finset.mem_univ _))
      rw [hsum, hsum] at hceq
      exact hz0 hceq
    have hcard := Fintype.card_le_of_injective _ hinj
    rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Fintype.card_fin, Fintype.card_fin,
      ← pow_mul] at hcard
    exact hcard

private theorem rand_lower_bound (w t m : Nat) (hw : 0 < w)
    (S R : Nat) (hR : 0 < R)
    (put : Fin R → Rows → Fin S) (get : Fin R → Fin S → Rows → Nat)
    (hcorr : ∀ x y : Rows, goodF w t x →
      2 * R ≤ 3 * ((List.finRange R).filter (fun coin => get coin (put coin x) y == countF w t m x y)).length) :
    let D := 2 ^ w
    let C := if m = 0 then 2 ^ t else min (2 ^ t) m
    2 ^ ((D / 2) * Nat.log2 C) ≤ 2 * S ^ 11 := by
  intro D C
  let r := Nat.log2 C
  by_cases hr0 : r = 0
  · change 2 ^ ((D / 2) * r) ≤ 2 * S ^ 11
    rw [hr0, Nat.mul_zero, pow_zero]
    have hS : 0 < S := Nat.pos_of_ne_zero (fun h0 => Fin.elim0 (h0 ▸ put ⟨0, hR⟩ (fun _ _ => true)))
    have : 1 ≤ S ^ 11 := Nat.one_le_pow _ _ hS
    omega
  · have hCpos : 0 < C := by
      dsimp [C]; split_ifs with hm; positivity; exact lt_min (by positivity) (by omega)
    have h2rC : 2 ^ r ≤ C := (Nat.le_log2 (by omega)).mp le_rfl
    have hrt : r ≤ t := by
      have h2t : 2 ^ r ≤ 2 ^ t := by
        refine h2rC.trans ?_
        dsimp [C]; split_ifs; exact le_rfl; exact min_le_left _ _
      exact (Nat.pow_le_pow_iff_right (by decide)).mp h2t
    have hm : m = 0 ∨ 2 ^ r ≤ m := by
      by_cases hm0 : m = 0
      · exact Or.inl hm0
      · right
        refine h2rC.trans ?_
        dsimp [C]; simp only [hm0, ↓reduceIte]; exact min_le_right _ _
    obtain ⟨hgood, hdist⟩ := family_props w t m r hw hrt hm
    let F := Fin r → Fin (D / 2) → Bool
    let Sub := Fin D → Bool
    let Coins := Fin 11 → Fin R
    let dec (cs : Coins) (msgs : Fin 11 → Fin S) (y : Rows) : Nat :=
      dec11 (fun k => get (cs k) (msgs k) y)
    let isErr (cs : Coins) (f : F) (T : Sub) : Bool :=
      decide (dec cs (fun k => put (cs k) (leftOf (w := w) (t := t) f)) (rightFor w T) ≠
        countF w t m (leftOf (w := w) (t := t) f) (rightFor w T))
    have herr_each : ∀ (f : F) (T : Sub),
        8 * ((Finset.univ : Finset Coins).filter (fun cs => isErr cs f T = true)).card < R ^ 11 := by
      intro f T
      let x := leftOf (w := w) (t := t) f
      let y := rightFor w T
      let P : Fin R → Bool := fun coin => get coin (put coin x) y == countF w t m x y
      have hP : 2 * R ≤ 3 * ((Finset.univ : Finset (Fin R)).filter (fun c => P c = true)).card := by
        have h := hcorr x y (hgood f)
        have hlen : ((List.finRange R).filter (fun coin => P coin)).length =
            ((Finset.univ : Finset (Fin R)).filter (fun c => P c = true)).card := by
          rw [← List.toFinset_card_of_nodup ((List.nodup_finRange R).filter _)]
          congr 1; ext c; simp
        rw [← hlen]; exact h
      have hamp := amp11_err_bound hR P hP
      have hsub : ((Finset.univ : Finset Coins).filter (fun cs => isErr cs f T = true)) ⊆
          ((Finset.univ : Finset Coins).filter (fun cs =>
            6 ≤ ((Finset.univ : Finset (Fin 11)).filter (fun k => P (cs k) = false)).card)) := by
        intro cs hcs
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, isErr, decide_eq_true_eq] at hcs ⊢
        by_contra hlt
        have hcompl :
            ((Finset.univ : Finset (Fin 11)).filter (fun k => P (cs k) = true)).card +
            ((Finset.univ : Finset (Fin 11)).filter (fun k => P (cs k) = false)).card = 11 := by
          have hdisj : Disjoint
              ((Finset.univ : Finset (Fin 11)).filter (fun k => P (cs k) = true))
              ((Finset.univ : Finset (Fin 11)).filter (fun k => P (cs k) = false)) := by
            rw [Finset.disjoint_filter]; intro k _ h1 h2; rw [h1] at h2; exact Bool.noConfusion h2
          have hunion :
              ((Finset.univ : Finset (Fin 11)).filter (fun k => P (cs k) = true)) ∪
              ((Finset.univ : Finset (Fin 11)).filter (fun k => P (cs k) = false)) = Finset.univ := by
            ext k; simp
          have hc := Finset.card_union_of_disjoint hdisj
          rw [hunion, Finset.card_univ, Fintype.card_fin] at hc; exact hc.symm
        have hmaj : 6 ≤ ((Finset.univ : Finset (Fin 11)).filter (fun k =>
            get (cs k) (put (cs k) x) y = countF w t m x y)).card := by
          have hfeq : ((Finset.univ : Finset (Fin 11)).filter (fun k => P (cs k) = true)) =
              ((Finset.univ : Finset (Fin 11)).filter (fun k => get (cs k) (put (cs k) x) y = countF w t m x y)) := by
            ext k; simp [P, beq_iff_eq]
          rw [← hfeq]; omega
        exact hcs (dec11_eq_of_majority _ _ hmaj)
      exact (Nat.mul_le_mul_left 8 (Finset.card_le_card hsub)).trans_lt hamp
    have hFcard : Fintype.card F = 2 ^ ((D / 2) * r) := by
      dsimp [F]
      rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Fintype.card_fin, ← pow_mul]
    have hSubcard : Fintype.card Sub = 2 ^ D := by
      dsimp [Sub]
      rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    have hCoinscard : Fintype.card Coins = R ^ 11 := by
      dsimp [Coins]
      rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    have hsum_strict :
        8 * ∑ cs : Coins, ∑ f : F, ((Finset.univ : Finset Sub).filter (fun T => isErr cs f T = true)).card <
        R ^ 11 * (Fintype.card F * Fintype.card Sub) := by
      have hswap :
          ∑ cs : Coins, ∑ f : F, ((Finset.univ : Finset Sub).filter (fun T => isErr cs f T = true)).card =
          ∑ f : F, ∑ T : Sub, ((Finset.univ : Finset Coins).filter (fun cs => isErr cs f T = true)).card := by
        simp only [Finset.card_filter]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro f _
        rw [Finset.sum_comm]
      rw [hswap, Finset.mul_sum]
      have hneF : (Finset.univ : Finset F).Nonempty := ⟨fun _ _ => false, Finset.mem_univ _⟩
      have hneSub : (Finset.univ : Finset Sub).Nonempty := ⟨fun _ => false, Finset.mem_univ _⟩
      have hlt1 : ∑ f : F, 8 * ∑ T : Sub, ((Finset.univ : Finset Coins).filter (fun cs => isErr cs f T = true)).card <
          ∑ _f : F, (Fintype.card Sub * R ^ 11) := by
        apply Finset.sum_lt_sum_of_nonempty hneF
        intro f _
        rw [Finset.mul_sum]
        have hlt2 : ∑ T : Sub, 8 * ((Finset.univ : Finset Coins).filter (fun cs => isErr cs f T = true)).card <
            ∑ _T : Sub, R ^ 11 :=
          Finset.sum_lt_sum_of_nonempty hneSub (fun T _ => herr_each f T)
        simpa [Finset.sum_const, smul_eq_mul] using hlt2
      simpa [Finset.sum_const, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using hlt1
    have hex_coin : ∃ cs : Coins,
        8 * ∑ f : F, ((Finset.univ : Finset Sub).filter (fun T => isErr cs f T = true)).card <
        Fintype.card F * Fintype.card Sub := by
      by_contra hall
      push Not at hall
      have hge : ∑ _cs : Coins, (Fintype.card F * Fintype.card Sub) ≤
          ∑ cs : Coins, 8 * ∑ f : F, ((Finset.univ : Finset Sub).filter (fun T => isErr cs f T = true)).card :=
        Finset.sum_le_sum (fun cs _ => hall cs)
      rw [Finset.sum_const, Finset.card_univ, hCoinscard, smul_eq_mul, ← Finset.mul_sum] at hge
      omega
    obtain ⟨cs0, hcs0⟩ := hex_coin
    let errCnt (f : F) : Nat := ((Finset.univ : Finset Sub).filter (fun T => isErr cs0 f T = true)).card
    let GoodF : Finset F := Finset.univ.filter (fun f => 4 * errCnt f < 2 ^ D)
    let BadF : Finset F := Finset.univ.filter (fun f => 2 ^ D ≤ 4 * errCnt f)
    have hGB : GoodF.card + BadF.card = Fintype.card F := by
      have hdisj : Disjoint GoodF BadF := by
        rw [Finset.disjoint_filter]; intro f _ h1 h2; omega
      have hunion : GoodF ∪ BadF = Finset.univ := by
        ext f; simp only [GoodF, BadF, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
        exact lt_or_ge _ _
      have hc := Finset.card_union_of_disjoint hdisj
      rw [hunion, Finset.card_univ] at hc; exact hc.symm
    have hBad : 2 * BadF.card < Fintype.card F := by
      have h1 : BadF.card * (2 * 2 ^ D) ≤ 8 * ∑ f ∈ BadF, errCnt f := by
        rw [Finset.mul_sum, ← smul_eq_mul, ← Finset.sum_const]
        apply Finset.sum_le_sum
        intro f hf
        have hge : 2 ^ D ≤ 4 * errCnt f := (Finset.mem_filter.mp hf).2
        omega
      have h2 : 8 * ∑ f ∈ BadF, errCnt f ≤ 8 * ∑ f : F, errCnt f :=
        Nat.mul_le_mul_left 8 (Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _))
      have h3 : BadF.card * (2 * 2 ^ D) < Fintype.card F * 2 ^ D := by
        rw [hSubcard] at hcs0
        exact (h1.trans h2).trans_lt hcs0
      have h2Dpos : 0 < 2 ^ D := by positivity
      have h4 : (2 * BadF.card) * 2 ^ D < Fintype.card F * 2 ^ D := by
        have : (2 * BadF.card) * 2 ^ D = BadF.card * (2 * 2 ^ D) := by ring
        rw [this]; exact h3
      exact Nat.lt_of_mul_lt_mul_right h4
    have hGoodHalf : Fintype.card F ≤ 2 * GoodF.card := by omega
    have hinj : Set.InjOn (fun f : F => (fun k : Fin 11 => put (cs0 k) (leftOf (w := w) (t := t) f))) GoodF := by
      intro f1 hf1 f2 hf2 hmsg
      dsimp only at hmsg
      by_contra hne
      obtain ⟨z0, hz0⟩ := hdist f1 f2 hne
      have hsub := random_subset_distinguishes m
        (fun z => massF w (leftOf (w := w) (t := t) f1) (w + t) 0 z.val)
        (fun z => massF w (leftOf (w := w) (t := t) f2) (w + t) 0 z.val) z0 hz0
      have hinc :
          ((Finset.univ : Finset Sub).filter (fun T =>
            (∑ z : Fin D, if T z then massF w (leftOf (w := w) (t := t) f1) (w + t) 0 z.val else 0) % m ≠
            (∑ z : Fin D, if T z then massF w (leftOf (w := w) (t := t) f2) (w + t) 0 z.val else 0) % m)) ⊆
          ((Finset.univ : Finset Sub).filter (fun T => isErr cs0 f1 T = true)) ∪
          ((Finset.univ : Finset Sub).filter (fun T => isErr cs0 f2 T = true)) := by
        intro T hT
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, isErr, decide_eq_true_eq] at hT ⊢
        rw [← count_rightFor w t m hw (leftOf (w := w) (t := t) f1) T,
            ← count_rightFor w t m hw (leftOf (w := w) (t := t) f2) T] at hT
        by_cases h1 : dec cs0 (fun k => put (cs0 k) (leftOf (w := w) (t := t) f1)) (rightFor w T) ≠
            countF w t m (leftOf (w := w) (t := t) f1) (rightFor w T)
        · exact Or.inl h1
        · push Not at h1
          right
          intro h2
          rw [← hmsg] at h2
          exact hT (h1.symm.trans h2)
      have hcard_le := (Finset.card_le_card hinc).trans (Finset.card_union_le _ _)
      have hle1 : 4 * errCnt f1 < 2 ^ D := (Finset.mem_filter.mp hf1).2
      have hle2 : 4 * errCnt f2 < 2 ^ D := (Finset.mem_filter.mp hf2).2
      dsimp only [errCnt, D, Sub] at hle1 hle2 hcard_le
      omega
    have hGoodLe : GoodF.card ≤ S ^ 11 := by
      have h := Finset.card_le_card_of_injOn
        (f := fun f : F => (fun k : Fin 11 => put (cs0 k) (leftOf (w := w) (t := t) f)))
        (fun _ _ => Finset.mem_univ _) hinj
      simpa [Finset.card_univ, Fintype.card_fun, Fintype.card_fin] using h
    rw [← hFcard]
    omega

private theorem solve_526 : ∀ (w t m : Nat), 0 < w →
    let D := 2^w
    let Rows := Nat → Nat → Bool
    let mass := fun (rows : Rows) (h seed tail : Nat) =>
      ((List.range (2^(w+h))).filter (fun bits =>
        bits % D == seed && (bits >>> h) % D == tail &&
        (List.range h).all (fun i => rows i ((bits >>> i) % (2*D))))).length
    let L := w+t
    let n := L+w
    let good := fun (tables : Rows) =>
      ∃ a b : Fin D → Nat, (∀ i, 0 < a i) ∧ (∀ j, 0 < b j) ∧
        ∀ s z : Fin D, mass tables L s.val z.val = a s * b z
    let count := fun (left right : Rows) =>
      ((List.range (2^n)).filter (fun word => (List.range n).all (fun site =>
        let pat := (List.range (w+1)).foldl (fun (acc bit : Nat) =>
          acc ||| ((word.testBit ((site+bit)%n)).toNat <<< bit)) 0
        if site < L then left site pat else right (site-L) pat))).length % m
    let C := if m = 0 then 2^t else min (2^t) m
    let lower := 2^((D/2)*Nat.log2 C)
    let upper := C^(2*D)
    upper ≤ lower^8 ∧
    (∃ (encode : Rows → Fin upper) (read : Fin upper → Rows → Nat),
      ∀ p q : Rows, good p → read (encode p) q = count p q) ∧
    (∀ (S : Nat) (send : Rows → Fin S) (answer : Fin S → Rows → Nat),
      (∀ left right : Rows, good left → answer (send left) right = count left right) →
      lower ≤ S) ∧
    ∀ (S R : Nat), 0 < R →
      ∀ (put : Fin R → Rows → Fin S) (get : Fin R → Fin S → Rows → Nat),
        (∀ x y : Rows, good x →
          2*R ≤ 3*((List.finRange R).filter (fun coin =>
            get coin (put coin x) y == count x y)).length) →
        lower ≤ 2*S^11 := by
  intro w t m hw D Rows mass L n good count C lower upper
  exact ⟨upper_le_lower_pow8 w t m hw,
    upper_protocol w t m,
    det_lower_bound w t m hw,
    rand_lower_bound w t m hw⟩

end PEqualNP.Outside.L_lib_526_aux

theorem PEqualNP.Outside.L_lib_526 : ∀ (w t m : Nat), 0 < w →
  let D := 2^w
  let Rows := Nat → Nat → Bool
  let mass := fun (rows : Rows) (h seed tail : Nat) =>
    ((List.range (2^(w+h))).filter (fun bits =>
      bits % D == seed && (bits >>> h) % D == tail &&
      (List.range h).all (fun i => rows i ((bits >>> i) % (2*D))))).length
  let L := w+t
  let n := L+w
  let good := fun (tables : Rows) =>
    ∃ a b : Fin D → Nat, (∀ i, 0 < a i) ∧ (∀ j, 0 < b j) ∧
      ∀ s z : Fin D, mass tables L s.val z.val = a s * b z
  let count := fun (left right : Rows) =>
    ((List.range (2^n)).filter (fun word => (List.range n).all (fun site =>
      let pat := (List.range (w+1)).foldl (fun (acc bit : Nat) =>
        acc ||| ((word.testBit ((site+bit)%n)).toNat <<< bit)) 0
      if site < L then left site pat else right (site-L) pat))).length % m
  let C := if m = 0 then 2^t else min (2^t) m
  let lower := 2^((D/2)*Nat.log2 C)
  let upper := C^(2*D)
  upper ≤ lower^8 ∧
  (∃ (encode : Rows → Fin upper) (read : Fin upper → Rows → Nat),
    ∀ p q : Rows, good p → read (encode p) q = count p q) ∧
  (∀ (S : Nat) (send : Rows → Fin S) (answer : Fin S → Rows → Nat),
    (∀ left right : Rows, good left → answer (send left) right = count left right) →
    lower ≤ S) ∧
  ∀ (S R : Nat), 0 < R →
    ∀ (put : Fin R → Rows → Fin S) (get : Fin R → Fin S → Rows → Nat),
      (∀ x y : Rows, good x →
        2*R ≤ 3*((List.finRange R).filter (fun coin =>
          get coin (put coin x) y == count x y)).length) →
      lower ≤ 2*S^11 :=
  PEqualNP.Outside.L_lib_526_aux.solve_526
