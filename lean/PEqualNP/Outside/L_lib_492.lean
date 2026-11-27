import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_492_aux

open MvPolynomial PEqualNP.ProofComplexity

private theorem zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  fin_cases a <;> decide

private theorem zmod2_poly_add_self {n : ℕ} (p : MvPolynomial (Fin n) (ZMod 2)) : p + p = 0 := by
  rw [← two_smul (ZMod 2) p, show (2 : ZMod 2) = 0 from rfl, zero_smul]

private theorem zmod2_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

private theorem pcDerivable_sum {n D : ℕ} {ι : Type*}
    (F : Set (MvPolynomial (Fin n) (ZMod 2))) (s : Finset ι)
    (f : ι → MvPolynomial (Fin n) (ZMod 2))
    (hf : ∀ i ∈ s, PCDerivable F D (f i)) :
    PCDerivable F D (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa using PCDerivable.zero (F := F) (B := D)
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact PCDerivable.add (hf i (Finset.mem_insert_self i s))
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

private theorem pcDerivable_monomial_mul {n D : ℕ}
    (F : Set (MvPolynomial (Fin n) (ZMod 2)))
    (q : MvPolynomial (Fin n) (ZMod 2)) (hq : PCDerivable F D q) :
    ∀ (m : ℕ) (e : Fin n →₀ ℕ), (e.sum fun _ k => k) = m → m + q.totalDegree ≤ D →
      PCDerivable F D (monomial e 1 * q) := by
  classical
  intro m
  induction m with
  | zero =>
    intro e he _
    have he0 : e = 0 := by
      ext i
      by_contra hi
      have hpos : 0 < e i := Nat.pos_of_ne_zero hi
      have hmem : i ∈ e.support := Finsupp.mem_support_iff.2 hi
      have hle : e i ≤ e.sum (fun _ k => k) := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hmem
      omega
    rw [he0, show (monomial (0 : Fin n →₀ ℕ) (1 : ZMod 2)) = 1 from rfl, one_mul]
    exact hq
  | succ m ih =>
    intro e he hdeg
    have hne : e.support.Nonempty := by
      by_contra hempty
      rw [Finset.not_nonempty_iff_eq_empty] at hempty
      have hsum0 : (e.sum fun _ k => k) = 0 := by
        simp [Finsupp.sum, hempty]
      omega
    obtain ⟨j, hj⟩ := hne
    have hej : 1 ≤ e j := Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 hj)
    set e' := e - Finsupp.single j 1 with he'_def
    have he_eq : e = e' + Finsupp.single j 1 := by
      ext i
      simp only [he'_def, Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
      split_ifs with h
      · subst h; omega
      · omega
    have hsum' : (e'.sum fun _ k => k) = m := by
      have h1 : (e.sum fun _ k => k) = (e'.sum fun _ k => k) + 1 := by
        rw [he_eq, Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
          Finsupp.sum_single_index rfl]
      omega
    have hrec : PCDerivable F D (monomial e' 1 * q) := ih e' hsum' (by omega)
    have hmul_eq : monomial e (1 : ZMod 2) * q = X j * (monomial e' 1 * q) := by
      rw [← mul_assoc, X, monomial_mul_monomial, mul_one, add_comm, ← he_eq]
    rw [hmul_eq]
    refine PCDerivable.mulX j hrec ?_
    have hd1 : (X j * (monomial e' (1 : ZMod 2) * q)).totalDegree ≤
        (X j : MvPolynomial (Fin n) (ZMod 2)).totalDegree + (monomial e' 1 * q).totalDegree :=
      totalDegree_mul _ _
    have hd2 : (monomial e' (1 : ZMod 2) * q).totalDegree ≤
        (monomial e' (1 : ZMod 2)).totalDegree + q.totalDegree :=
      totalDegree_mul _ _
    have hdX : (X j : MvPolynomial (Fin n) (ZMod 2)).totalDegree ≤ 1 := by
      rw [totalDegree_X]
    have hdM : (monomial e' (1 : ZMod 2)).totalDegree ≤ m := by
      rw [totalDegree_monomial e' (one_ne_zero : (1 : ZMod 2) ≠ 0), hsum']
    omega

private theorem pcDerivable_mul {n D : ℕ}
    (F : Set (MvPolynomial (Fin n) (ZMod 2)))
    (r q : MvPolynomial (Fin n) (ZMod 2))
    (hq : PCDerivable F D q) (hdeg : r.totalDegree + q.totalDegree ≤ D) :
    PCDerivable F D (r * q) := by
  classical
  have hr_eq : r = ∑ e ∈ r.support, monomial e (1 : ZMod 2) := by
    conv_lhs => rw [r.as_sum]
    apply Finset.sum_congr rfl
    intro e he
    have hc : r.coeff e ≠ 0 := mem_support_iff.1 he
    rcases zmod2_eq_zero_or_one (r.coeff e) with h0 | h1
    · exact absurd h0 hc
    · rw [h1]
  rw [hr_eq, Finset.sum_mul]
  apply pcDerivable_sum
  intro e he
  have hle : (e.sum fun _ k => k) ≤ r.totalDegree :=
    Finset.le_sup (f := fun s : Fin n →₀ ℕ => s.sum fun _ k => k) he
  exact pcDerivable_monomial_mul F q hq (e.sum fun _ k => k) e rfl (by omega)

private noncomputable def mlin {n : ℕ} (a : Fin n →₀ ℕ) : Fin n →₀ ℕ :=
  Finsupp.mapRange (fun k => min k 1) (by simp) a

private theorem mlin_apply {n : ℕ} (a : Fin n →₀ ℕ) (i : Fin n) :
    mlin a i = min (a i) 1 := by
  simp [mlin]

private theorem boolDerivable_monomial {n D : ℕ}
    (F : Set (MvPolynomial (Fin n) (ZMod 2)))
    (hB : ∀ i : Fin n, X i * X i + X i ∈ F) :
    ∀ (m : ℕ) (a : Fin n →₀ ℕ), (a.sum fun _ e => e) = m → m ≤ D →
      PCDerivable F D (monomial a 1 + monomial (mlin a) 1) := by
  classical
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro a ha hm
    by_cases hall : ∀ i, a i ≤ 1
    · have hml : mlin a = a := by
        ext i; rw [mlin_apply]; have := hall i; omega
      rw [hml, zmod2_poly_add_self]
      exact PCDerivable.zero
    · simp only [not_forall, not_le] at hall
      obtain ⟨i, hi⟩ := hall
      set b := a - Finsupp.single i 2 with hb_def
      have ha_eq : a = b + Finsupp.single i 2 := by
        ext j
        simp only [hb_def, Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
        split_ifs with h
        · subst h; omega
        · omega
      set a' := b + Finsupp.single i 1 with ha'_def
      have hsum_single : ∀ (c : Fin n →₀ ℕ) (k : ℕ),
          ((c + Finsupp.single i k).sum fun _ e => e) = (c.sum fun _ e => e) + k := by
        intro c k
        rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
          Finsupp.sum_single_index rfl]
      have hml_eq : mlin a' = mlin a := by
        ext j
        simp only [mlin_apply, ha_eq, ha'_def, Finsupp.add_apply, Finsupp.single_apply]
        split_ifs <;> omega
      have hma : m = (b.sum fun _ e => e) + 2 := by rw [← ha, ha_eq, hsum_single]
      have hma' : (a'.sum fun _ e => e) = (b.sum fun _ e => e) + 1 := by rw [ha'_def, hsum_single]
      have hstep : PCDerivable F D (monomial a 1 + monomial a' 1) := by
        have hid : monomial a (1 : ZMod 2) + monomial a' 1 =
            monomial b 1 * (X i * X i + X i) := by
          rw [mul_add, X, monomial_mul_monomial, monomial_mul_monomial, monomial_mul_monomial,
            ← Finsupp.single_add, ha_eq, ha'_def, one_mul, one_mul]
        rw [hid]
        have hdeg_ax : (X i * X i + X i : MvPolynomial (Fin n) (ZMod 2)).totalDegree ≤ 2 := by
          refine (totalDegree_add _ _).trans (max_le ?_ ?_)
          · refine (totalDegree_mul _ _).trans ?_
            rw [totalDegree_X]
          · rw [totalDegree_X]; omega
        have hax : PCDerivable F D (X i * X i + X i) :=
          PCDerivable.ax (hB i) (by omega)
        exact pcDerivable_monomial_mul F _ hax (b.sum fun _ e => e) b rfl (by omega)
      have hrest := ih ((b.sum fun _ e => e) + 1) (by omega) a' hma' (by omega)
      rw [hml_eq] at hrest
      have hcomb := PCDerivable.add hstep hrest
      have hcancel : monomial a (1 : ZMod 2) + monomial a' 1 + (monomial a' 1 + monomial (mlin a) 1) =
          monomial a 1 + monomial (mlin a) 1 := by
        rw [add_assoc, ← add_assoc (monomial a' 1), zmod2_poly_add_self, zero_add]
      rwa [hcancel] at hcomb

private theorem eval_mlin_eq {n : ℕ} (x : Fin n → ZMod 2) (a : Fin n →₀ ℕ) :
    eval x (monomial (mlin a) (1 : ZMod 2)) = eval x (monomial a (1 : ZMod 2)) := by
  simp only [eval_monomial, map_one, one_mul]
  rw [Finsupp.prod, Finsupp.prod]
  have hsupp : (mlin a).support = a.support := by
    ext i
    simp only [Finsupp.mem_support_iff, mlin_apply]
    omega
  rw [hsupp]
  apply Finset.prod_congr rfl
  intro i hi
  rw [mlin_apply]
  have hpos : 1 ≤ a i := Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 hi)
  have hmin : min (a i) 1 = 1 := Nat.min_eq_right hpos
  rw [hmin, pow_one]
  rcases zmod2_eq_zero_or_one (x i) with h0 | h1
  · rw [h0, zero_pow (by omega)]
  · rw [h1, one_pow]

private theorem vanish_derivable {n D : ℕ}
    (F : Set (MvPolynomial (Fin n) (ZMod 2)))
    (hB : ∀ i : Fin n, X i * X i + X i ∈ F)
    (q : MvPolynomial (Fin n) (ZMod 2))
    (hdeg : q.totalDegree ≤ D)
    (h0 : ∀ x : Fin n → ZMod 2, eval x q = 0) :
    PCDerivable F D q := by
  classical
  let qml : MvPolynomial (Fin n) (ZMod 2) := ∑ a ∈ q.support, monomial (mlin a) 1
  have hdiff : PCDerivable F D (q + qml) := by
    have hq_eq : q = ∑ a ∈ q.support, monomial a (1 : ZMod 2) := by
      conv_lhs => rw [q.as_sum]
      apply Finset.sum_congr rfl
      intro a ha
      have hc : q.coeff a ≠ 0 := mem_support_iff.1 ha
      rcases zmod2_eq_zero_or_one (q.coeff a) with h0c | h1c
      · exact absurd h0c hc
      · rw [h1c]
    have hsum_eq : q + qml = ∑ a ∈ q.support, (monomial a 1 + monomial (mlin a) 1) := by
      conv_lhs => rw [hq_eq]
      dsimp only [qml]
      rw [← Finset.sum_add_distrib]
    rw [hsum_eq]
    apply pcDerivable_sum
    intro a ha
    have hle : (a.sum fun _ e => e) ≤ q.totalDegree :=
      Finset.le_sup (f := fun s : Fin n →₀ ℕ => s.sum fun _ e => e) ha
    exact boolDerivable_monomial F hB (a.sum fun _ e => e) a rfl (by omega)
  have hqml_eval : ∀ x : Fin n → ZMod 2, eval x qml = 0 := by
    intro x
    have hq_eq : q = ∑ a ∈ q.support, monomial a (1 : ZMod 2) := by
      conv_lhs => rw [q.as_sum]
      apply Finset.sum_congr rfl
      intro a ha
      have hc : q.coeff a ≠ 0 := mem_support_iff.1 ha
      rcases zmod2_eq_zero_or_one (q.coeff a) with h0c | h1c
      · exact absurd h0c hc
      · rw [h1c]
    have heq : eval x qml = eval x q := by
      conv_rhs => rw [hq_eq]
      dsimp only [qml]
      rw [map_sum, map_sum]
      apply Finset.sum_congr rfl
      intro a _
      exact eval_mlin_eq x a
    rw [heq, h0 x]
  have hqml_zero : qml = 0 := by
    refine MvPolynomial.eq_zero_of_eval_eq_zero (Fin n) (ZMod 2) qml hqml_eval ?_
    rw [mem_restrictDegree]
    intro c hc i
    have hmem : qml.coeff c ≠ 0 := mem_support_iff.1 hc
    have hex : ∃ a ∈ q.support, (monomial (mlin a) (1 : ZMod 2)).coeff c ≠ 0 := by
      by_contra hall
      push_neg at hall
      apply hmem
      dsimp only [qml]
      rw [coeff_sum]
      exact Finset.sum_eq_zero hall
    obtain ⟨a, _, ha⟩ := hex
    rw [coeff_monomial] at ha
    split_ifs at ha with hca
    · rw [← hca, mlin_apply]
      have hcard : Fintype.card (ZMod 2) = 2 := ZMod.card 2
      omega
    · exact absurd rfl ha
  rw [hqml_zero, add_zero] at hdiff
  exact hdiff

private theorem totalDegree_prod_le {n : ℕ} {ι : Type*} (s : Finset ι)
    (f : ι → MvPolynomial (Fin n) (ZMod 2)) :
    (∏ i ∈ s, f i).totalDegree ≤ ∑ i ∈ s, (f i).totalDegree := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact (totalDegree_mul _ _).trans (Nat.add_le_add_left ih _)

private theorem totalDegree_sum_le {n : ℕ} {ι : Type*} (s : Finset ι) (B : ℕ)
    (f : ι → MvPolynomial (Fin n) (ZMod 2)) (hf : ∀ i ∈ s, (f i).totalDegree ≤ B) :
    (∑ i ∈ s, f i).totalDegree ≤ B := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (totalDegree_add _ _).trans (max_le (hf i (Finset.mem_insert_self i s))
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))))

private noncomputable def indPoly {n : ℕ} (a : Fin n → ZMod 2) : MvPolynomial (Fin n) (ZMod 2) :=
  ∏ i : Fin n, (X i + C (a i) + 1)

private theorem totalDegree_indPoly {n : ℕ} (a : Fin n → ZMod 2) :
    (indPoly a).totalDegree ≤ n := by
  dsimp only [indPoly]
  refine (totalDegree_prod_le _ _).trans ?_
  have hterm : ∑ i : Fin n, (X i + C (a i) + 1 : MvPolynomial (Fin n) (ZMod 2)).totalDegree ≤
      ∑ _i : Fin n, (1 : ℕ) := by
    apply Finset.sum_le_sum
    intro i _
    have h1 : (X i + C (a i) + 1 : MvPolynomial (Fin n) (ZMod 2)).totalDegree ≤
        max (X i + C (a i) : MvPolynomial (Fin n) (ZMod 2)).totalDegree
          (1 : MvPolynomial (Fin n) (ZMod 2)).totalDegree := totalDegree_add _ _
    have h2 : (X i + C (a i) : MvPolynomial (Fin n) (ZMod 2)).totalDegree ≤
        max (X i : MvPolynomial (Fin n) (ZMod 2)).totalDegree
          (C (a i) : MvPolynomial (Fin n) (ZMod 2)).totalDegree := totalDegree_add _ _
    rw [totalDegree_one] at h1
    rw [totalDegree_X, totalDegree_C] at h2
    omega
  simpa using hterm

private theorem eval_indPoly {n : ℕ} (a b : Fin n → ZMod 2) :
    eval b (indPoly a) = if b = a then 1 else 0 := by
  dsimp only [indPoly]
  rw [map_prod]
  by_cases hba : b = a
  · subst hba
    rw [if_pos rfl]
    apply Finset.prod_eq_one
    intro i _
    simp only [map_add, eval_X, eval_C, map_one, zmod2_add_self, zero_add]
  · rw [if_neg hba]
    have hex : ∃ i : Fin n, b i ≠ a i := by
      by_contra hall
      push_neg at hall
      exact hba (funext hall)
    obtain ⟨i₀, hi₀⟩ := hex
    apply Finset.prod_eq_zero (Finset.mem_univ i₀)
    simp only [map_add, eval_X, eval_C, map_one]
    rcases zmod2_eq_zero_or_one (b i₀) with hb0 | hb1 <;>
      rcases zmod2_eq_zero_or_one (a i₀) with ha0 | ha1
    · exact absurd (hb0.trans ha0.symm) hi₀
    · rw [hb0, ha1]; decide
    · rw [hb1, ha0]; decide
    · exact absurd (hb1.trans ha1.symm) hi₀

private theorem main_core (n w : ℕ) (G : Set (MvPolynomial (Fin n) (ZMod 2)))
    (p : MvPolynomial (Fin n) (ZMod 2))
    (hw : ∀ g ∈ G, MvPolynomial.totalDegree g ≤ w) :
    let P := MvPolynomial (Fin n) (ZMod 2)
    let B := {q : P | ∃ i : Fin n, q = MvPolynomial.X i * MvPolynomial.X i + MvPolynomial.X i}
    (∀ a : Fin n → ZMod 2, (∀ g ∈ G, MvPolynomial.eval a g = 0) → MvPolynomial.eval a p = 0) ↔
      PEqualNP.ProofComplexity.PCDerivable (B ∪ G) (max p.totalDegree (n + w)) p := by
  classical
  intro P B
  set D := max p.totalDegree (n + w)
  have hB : ∀ i : Fin n, X i * X i + X i ∈ B ∪ G := fun i => Or.inl ⟨i, rfl⟩
  constructor
  · intro hsem
    have hind_deriv : ∀ a : Fin n → ZMod 2, eval a p = 1 → PCDerivable (B ∪ G) D (indPoly a) := by
      intro a hap
      have hex : ∃ g ∈ G, eval a g ≠ 0 := by
        by_contra hall
        push_neg at hall
        have hp0 := hsem a hall
        rw [hap] at hp0
        exact one_ne_zero hp0
      obtain ⟨g, hgG, hga_ne⟩ := hex
      have hga : eval a g = 1 := by
        rcases zmod2_eq_zero_or_one (eval a g) with h0 | h1
        · exact absurd h0 hga_ne
        · exact h1
      have hgw : g.totalDegree ≤ w := hw g hgG
      have hdg : PCDerivable (B ∪ G) D g := PCDerivable.ax (Or.inr hgG) (by omega)
      have hind_deg : (indPoly a).totalDegree ≤ n := totalDegree_indPoly a
      have hmul : PCDerivable (B ∪ G) D (indPoly a * g) :=
        pcDerivable_mul (B ∪ G) (indPoly a) g hdg (by omega)
      have hdiff_deg : (indPoly a * g + indPoly a).totalDegree ≤ D := by
        have h1 := totalDegree_add (indPoly a * g) (indPoly a)
        have h2 := totalDegree_mul (indPoly a) g
        omega
      have hdiff_eval : ∀ b : Fin n → ZMod 2, eval b (indPoly a * g + indPoly a) = 0 := by
        intro b
        rw [map_add, map_mul, eval_indPoly]
        by_cases hba : b = a
        · subst hba
          rw [if_pos rfl, hga, one_mul]
          exact zmod2_add_self 1
        · rw [if_neg hba, zero_mul, add_zero]
      have hdiff : PCDerivable (B ∪ G) D (indPoly a * g + indPoly a) :=
        vanish_derivable (B ∪ G) hB (indPoly a * g + indPoly a) hdiff_deg hdiff_eval
      have hsum := PCDerivable.add hmul hdiff
      have hcancel : indPoly a * g + (indPoly a * g + indPoly a) = indPoly a := by
        rw [← add_assoc, zmod2_poly_add_self, zero_add]
      rwa [hcancel] at hsum
    let S : Finset (Fin n → ZMod 2) := Finset.univ.filter (fun a => eval a p = 1)
    let r : P := ∑ a ∈ S, indPoly a
    have hr_deriv : PCDerivable (B ∪ G) D r := by
      apply pcDerivable_sum
      intro a ha
      exact hind_deriv a (Finset.mem_filter.1 ha).2
    have hr_deg : r.totalDegree ≤ n := by
      dsimp only [r]
      exact totalDegree_sum_le S n indPoly (fun a _ => totalDegree_indPoly a)
    have hpr_deg : (p + r).totalDegree ≤ D := by
      have h1 := totalDegree_add p r
      omega
    have hpr_eval : ∀ b : Fin n → ZMod 2, eval b (p + r) = 0 := by
      intro b
      rw [map_add]
      have hr_b : eval b r = eval b p := by
        dsimp only [r]
        rw [map_sum]
        have heq : ∑ a ∈ S, eval b (indPoly a) = ∑ a ∈ S, (if b = a then (1 : ZMod 2) else 0) := by
          apply Finset.sum_congr rfl
          intro a _
          exact eval_indPoly a b
        rw [heq]
        by_cases hbS : b ∈ S
        · rw [← Finset.add_sum_erase _ _ hbS, if_pos rfl]
          have hrest : ∑ a ∈ S.erase b, (if b = a then (1 : ZMod 2) else 0) = 0 := by
            apply Finset.sum_eq_zero
            intro a ha
            exact if_neg (Ne.symm (Finset.ne_of_mem_erase ha))
          rw [hrest, add_zero]
          exact (Finset.mem_filter.1 hbS).2.symm
        · have hzero : ∑ a ∈ S, (if b = a then (1 : ZMod 2) else 0) = 0 := by
            apply Finset.sum_eq_zero
            intro a ha
            have hne : b ≠ a := fun h => hbS (h ▸ ha)
            exact if_neg hne
          rw [hzero]
          have hne1 : eval b p ≠ 1 := fun h => hbS (Finset.mem_filter.2 ⟨Finset.mem_univ b, h⟩)
          rcases zmod2_eq_zero_or_one (eval b p) with h0 | h1
          · exact h0.symm
          · exact absurd h1 hne1
      rw [hr_b, zmod2_add_self]
    have hpr_deriv : PCDerivable (B ∪ G) D (p + r) :=
      vanish_derivable (B ∪ G) hB (p + r) hpr_deg hpr_eval
    have hcomb := PCDerivable.add hpr_deriv hr_deriv
    have hcancel : p + r + r = p := by
      rw [add_assoc, zmod2_poly_add_self, add_zero]
    rwa [hcancel] at hcomb
  · intro hderiv a hGa
    have hsound : ∀ q : P, PCDerivable (B ∪ G) D q → eval a q = 0 := by
      intro q hq
      induction hq with
      | ax hp _ =>
        rcases hp with ⟨i, rfl⟩ | hgG
        · simp only [map_add, map_mul, eval_X]
          rcases zmod2_eq_zero_or_one (a i) with h0 | h1
          · rw [h0]; decide
          · rw [h1]; decide
        · exact hGa _ hgG
      | zero => exact map_zero _
      | add _ _ ih1 ih2 => rw [map_add, ih1, ih2, add_zero]
      | mulX j _ _ ih => rw [map_mul, ih, mul_zero]
    exact hsound p hderiv

end PEqualNP.Outside.L_lib_492_aux

theorem PEqualNP.Outside.L_lib_492 : (∀ (n w : ℕ), let P := MvPolynomial (Fin n) (ZMod 2)
  let B := {q : P | ∃ i : Fin n, q = MvPolynomial.X i * MvPolynomial.X i + MvPolynomial.X i}
  ∀ (G : Set P) (p : P), (∀ g ∈ G, MvPolynomial.totalDegree g ≤ w) →
    ((∀ a : Fin n → ZMod 2, (∀ g ∈ G, MvPolynomial.eval a g = 0) → MvPolynomial.eval a p = 0) ↔
      PEqualNP.ProofComplexity.PCDerivable (B ∪ G) (max p.totalDegree (n + w)) p)) := by
  intro n w P B G p hw
  exact PEqualNP.Outside.L_lib_492_aux.main_core n w G p hw
