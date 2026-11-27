import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_648_aux

private def orePsi (q d c : ℕ) : ℕ :=
  let a := c / (q - 1)
  let b := c % (q - 1)
  q ^ (d - a) - b * q ^ (d - a - 1)

private lemma orePsi_eq_mul (q d c : ℕ) (hq : 2 ≤ q) (hc : c < d * (q - 1)) :
    orePsi q d c = (q - c % (q - 1)) * q ^ (d - c / (q - 1) - 1) := by
  unfold orePsi
  dsimp only
  have hq1 : 0 < q - 1 := by omega
  have ha_lt : c / (q - 1) < d := Nat.div_lt_of_lt_mul (by rwa [mul_comm])
  have hsub : d - c / (q - 1) = (d - c / (q - 1) - 1) + 1 := by omega
  have h1 : q ^ (d - c / (q - 1)) = q * q ^ (d - c / (q - 1) - 1) := by
    conv_lhs => rw [hsub, pow_succ]
    ring
  rw [h1, ← Nat.sub_mul]

private lemma orePsi_top (q d : ℕ) (hq : 2 ≤ q) :
    orePsi q d (d * (q - 1)) = 1 := by
  unfold orePsi
  dsimp only
  have hq1 : 0 < q - 1 := by omega
  rw [Nat.mul_div_cancel _ hq1, Nat.mul_mod_left, Nat.sub_self, pow_zero, zero_mul, Nat.sub_zero]

private lemma orePsi_anti (q d c1 c2 : ℕ) (hq : 2 ≤ q) (hle : c1 ≤ c2) (hc2 : c2 ≤ d * (q - 1)) :
    orePsi q d c2 ≤ orePsi q d c1 := by
  have hstep : ∀ c, c + 1 ≤ d * (q - 1) → orePsi q d (c + 1) ≤ orePsi q d c := by
    intro c hc
    have hq1 : 0 < q - 1 := by omega
    have hlt : c < d * (q - 1) := by omega
    rw [orePsi_eq_mul q d c hq hlt]
    by_cases htop : c + 1 = d * (q - 1)
    · rw [htop, orePsi_top q d hq]
      have hmod_lt : c % (q - 1) < q - 1 := Nat.mod_lt c hq1
      have hpos1 : 1 ≤ q - c % (q - 1) := by omega
      have hpos2 : 1 ≤ q ^ (d - c / (q - 1) - 1) := Nat.one_le_pow _ _ (by omega)
      calc
        1 = 1 * 1 := rfl
        _ ≤ (q - c % (q - 1)) * q ^ (d - c / (q - 1) - 1) := Nat.mul_le_mul hpos1 hpos2
    · have hlt1 : c + 1 < d * (q - 1) := by omega
      rw [orePsi_eq_mul q d (c + 1) hq hlt1]
      set a := c / (q - 1)
      set b := c % (q - 1)
      have hdiv_mod : c = a * (q - 1) + b := by
        have := Nat.div_add_mod c (q - 1)
        rw [mul_comm (q - 1)] at this
        exact this.symm
      have hb_lt : b < q - 1 := Nat.mod_lt c hq1
      by_cases hwrap : b + 1 < q - 1
      · have hdiv1 : (c + 1) / (q - 1) = a := by
          rw [hdiv_mod, add_assoc, mul_comm a (q - 1), Nat.mul_add_div hq1,
            Nat.div_eq_of_lt hwrap, add_zero]
        have hmod1 : (c + 1) % (q - 1) = b + 1 := by
          rw [hdiv_mod, add_assoc, mul_comm a (q - 1), Nat.mul_add_mod, Nat.mod_eq_of_lt hwrap]
        rw [hdiv1, hmod1]
        exact Nat.mul_le_mul_right _ (by omega)
      · have hb_eq : b + 1 = q - 1 := by omega
        have hc1_eq : c + 1 = (a + 1) * (q - 1) := by
          rw [hdiv_mod, add_assoc, hb_eq]; ring
        have hdiv1 : (c + 1) / (q - 1) = a + 1 := by
          rw [hc1_eq, Nat.mul_div_cancel _ hq1]
        have hmod1 : (c + 1) % (q - 1) = 0 := by
          rw [hc1_eq, Nat.mul_mod_left]
        rw [hdiv1, hmod1, Nat.sub_zero]
        have ha1_lt : a + 1 < d := Nat.lt_of_mul_lt_mul_right (by rwa [← hc1_eq])
        have hsub : d - a - 1 = (d - (a + 1) - 1) + 1 := by omega
        rw [hsub, pow_succ]
        have hqb : 1 ≤ q - b := by omega
        calc
          q * q ^ (d - (a + 1) - 1) = 1 * (q ^ (d - (a + 1) - 1) * q) := by ring
          _ ≤ (q - b) * (q ^ (d - (a + 1) - 1) * q) := Nat.mul_le_mul_right _ hqb
  have hind : ∀ t : ℕ, c1 + t ≤ d * (q - 1) → orePsi q d (c1 + t) ≤ orePsi q d c1 := by
    intro t
    induction t with
    | zero => intro _; simp
    | succ t ih =>
      intro ht
      exact le_trans (hstep (c1 + t) (by omega)) (ih (by omega))
  have h := hind (c2 - c1) (by omega)
  rwa [Nat.add_sub_of_le hle] at h

private lemma orePsi_step (q k c e : ℕ) (hq : 2 ≤ q) (he : e ≤ q - 1)
    (hec : e ≤ c) (hc : c ≤ (k + 1) * (q - 1)) :
    orePsi q (k + 1) c ≤ (q - e) * orePsi q k (min (c - e) (k * (q - 1))) := by
  have hq1 : 0 < q - 1 := by omega
  by_cases hcase : k * (q - 1) ≤ c - e
  · rw [min_eq_right hcase, orePsi_top q k hq, mul_one]
    by_cases htop : c = (k + 1) * (q - 1)
    · rw [htop, orePsi_top q (k + 1) hq]
      omega
    · have hlt : c < (k + 1) * (q - 1) := by omega
      rw [orePsi_eq_mul q (k + 1) c hq hlt]
      have hge : k * (q - 1) ≤ c := by omega
      have hdiv : c / (q - 1) = k := by
        have h1 : k ≤ c / (q - 1) := (Nat.le_div_iff_mul_le hq1).mpr hge
        have h2 : c / (q - 1) < k + 1 := Nat.div_lt_of_lt_mul (by rwa [mul_comm])
        omega
      have hmod : c % (q - 1) = c - k * (q - 1) := by
        have := Nat.div_add_mod c (q - 1)
        rw [hdiv] at this
        have hmul : (q - 1) * k = k * (q - 1) := mul_comm _ _
        omega
      rw [hdiv, hmod]
      have hsub0 : k + 1 - k - 1 = 0 := by omega
      rw [hsub0, pow_zero, mul_one]
      omega
  · have hlt' : c - e < k * (q - 1) := by omega
    rw [min_eq_left (le_of_lt hlt'), orePsi_eq_mul q k (c - e) hq hlt']
    have hlt : c < (k + 1) * (q - 1) := by
      have hmul : (k + 1) * (q - 1) = k * (q - 1) + (q - 1) := by ring
      omega
    rw [orePsi_eq_mul q (k + 1) c hq hlt]
    set c' := c - e
    set a' := c' / (q - 1)
    set b' := c' % (q - 1)
    have hc_eq : c = c' + e := by omega
    have hc'_eq : c' = a' * (q - 1) + b' := by
      have := Nat.div_add_mod c' (q - 1)
      rw [mul_comm (q - 1)] at this
      exact this.symm
    have hb'_lt : b' < q - 1 := Nat.mod_lt c' hq1
    have ha'_lt : a' < k := Nat.div_lt_of_lt_mul (by rwa [mul_comm])
    by_cases hwrap : b' + e < q - 1
    · have hdiv : c / (q - 1) = a' := by
        rw [hc_eq, hc'_eq, add_assoc, mul_comm a' (q - 1), Nat.mul_add_div hq1,
          Nat.div_eq_of_lt hwrap, add_zero]
      have hmod : c % (q - 1) = b' + e := by
        rw [hc_eq, hc'_eq, add_assoc, mul_comm a' (q - 1), Nat.mul_add_mod, Nat.mod_eq_of_lt hwrap]
      rw [hdiv, hmod]
      have hexp : k + 1 - a' - 1 = (k - a' - 1) + 1 := by omega
      rw [hexp, pow_succ]
      have hmul_le : (q - (b' + e)) * q ≤ (q - e) * (q - b') := by
        zify [show b' + e ≤ q by omega, show e ≤ q by omega, show b' ≤ q by omega]
        nlinarith
      calc
        (q - (b' + e)) * (q ^ (k - a' - 1) * q)
            = ((q - (b' + e)) * q) * q ^ (k - a' - 1) := by ring
        _ ≤ ((q - e) * (q - b')) * q ^ (k - a' - 1) := Nat.mul_le_mul_right _ hmul_le
        _ = (q - e) * ((q - b') * q ^ (k - a' - 1)) := by ring
    · set r := b' + e - (q - 1)
      have hr_lt : r < q - 1 := by omega
      have hbe : b' + e = (q - 1) + r := by omega
      have hc_split : c = (a' + 1) * (q - 1) + r := by
        rw [hc_eq, hc'_eq, add_assoc, hbe]; ring
      have hdiv : c / (q - 1) = a' + 1 := by
        rw [hc_split, mul_comm (a' + 1) (q - 1), Nat.mul_add_div hq1,
          Nat.div_eq_of_lt hr_lt, add_zero]
      have hmod : c % (q - 1) = r := by
        rw [hc_split, mul_comm (a' + 1) (q - 1), Nat.mul_add_mod, Nat.mod_eq_of_lt hr_lt]
      rw [hdiv, hmod]
      have hexp : k + 1 - (a' + 1) - 1 = k - a' - 1 := by omega
      rw [hexp]
      have hmul_le : q - r ≤ (q - e) * (q - b') := by
        zify [show r ≤ q by omega, show e ≤ q by omega, show b' ≤ q by omega]
        have hr_z : (r : ℤ) = (b' : ℤ) + (e : ℤ) - ((q : ℤ) - 1) := by omega
        rw [hr_z]
        have h1 : (0 : ℤ) ≤ (q : ℤ) - 1 - (e : ℤ) := by omega
        have h2 : (0 : ℤ) ≤ (q : ℤ) - 1 - (b' : ℤ) := by omega
        nlinarith
      calc
        (q - r) * q ^ (k - a' - 1) ≤ ((q - e) * (q - b')) * q ^ (k - a' - 1) :=
          Nat.mul_le_mul_right _ hmul_le
        _ = (q - e) * ((q - b') * q ^ (k - a' - 1)) := by ring

private lemma pow_reduce_ff {E : Type} [Field E] [Fintype E] (a : E) (e : ℕ) :
    let q := Fintype.card E
    let e' := if e = 0 then 0 else (e - 1) % (q - 1) + 1
    a ^ e' = a ^ e := by
  intro q e'
  by_cases he : e = 0
  · subst he; simp [e']
  · have hq : 2 ≤ q := Fintype.one_lt_card
    have hq1 : 0 < q - 1 := by omega
    dsimp only [e']
    rw [if_neg he]
    set r := (e - 1) % (q - 1)
    set m := (e - 1) / (q - 1)
    have he_eq : e = r + 1 + m * (q - 1) := by
      have hdm : m * (q - 1) + r = e - 1 := by
        dsimp only [m, r]
        rw [mul_comm]
        exact Nat.div_add_mod (e - 1) (q - 1)
      omega
    have hpow_q : a ^ q = a := FiniteField.pow_card a
    rw [he_eq]
    clear he_eq
    induction m with
    | zero => simp
    | succ m ih =>
      have hm1 : (m + 1) * (q - 1) = m * (q - 1) + (q - 1) := by ring
      have hstep : r + 1 + (m + 1) * (q - 1) = (r + 1 + m * (q - 1) - 1) + q := by omega
      have hstep2 : r + 1 + m * (q - 1) = (r + 1 + m * (q - 1) - 1) + 1 := by omega
      conv_rhs => rw [hstep, pow_add, hpow_q, ← pow_succ, ← hstep2]
      exact ih

private noncomputable def reduceExp (q : ℕ) (e : ℕ) : ℕ :=
  if e = 0 then 0 else (e - 1) % (q - 1) + 1

private lemma reduceExp_le (q e : ℕ) (hq : 2 ≤ q) : reduceExp q e ≤ e := by
  unfold reduceExp
  by_cases he : e = 0
  · simp [he]
  · rw [if_neg he]
    have := Nat.mod_le (e - 1) (q - 1)
    omega

private lemma reduceExp_lt (q e : ℕ) (hq : 2 ≤ q) : reduceExp q e ≤ q - 1 := by
  unfold reduceExp
  by_cases he : e = 0
  · simp [he]
  · rw [if_neg he]
    have hq1 : 0 < q - 1 := by omega
    have := Nat.mod_lt (e - 1) hq1
    omega

private noncomputable def reduceMon {d : ℕ} (q : ℕ) (m : Fin d →₀ ℕ) : Fin d →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun j => reduceExp q (m j))

private lemma reduceMon_apply {d : ℕ} (q : ℕ) (m : Fin d →₀ ℕ) (j : Fin d) :
    reduceMon q m j = reduceExp q (m j) := by
  simp [reduceMon]

private lemma totalDegree_sum_le {E : Type} [CommSemiring E] {σ ι : Type}
    (s : Finset ι) (f : ι → MvPolynomial σ E) (N : ℕ) (h : ∀ i ∈ s, (f i).totalDegree ≤ N) :
    (∑ i ∈ s, f i).totalDegree ≤ N := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact le_trans (MvPolynomial.totalDegree_add _ _)
      (max_le (h a (Finset.mem_insert_self a s))
        (ih (fun i hi => h i (Finset.mem_insert_of_mem hi))))

private lemma totalDegree_prod_le {E : Type} [CommSemiring E] {σ ι : Type}
    (s : Finset ι) (f : ι → MvPolynomial σ E) :
    (∏ i ∈ s, f i).totalDegree ≤ ∑ i ∈ s, (f i).totalDegree := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact le_trans (MvPolynomial.totalDegree_mul _ _) (Nat.add_le_add_left ih _)

private noncomputable def reducePoly {E : Type} [Field E] [Fintype E] {d : ℕ}
    (F : MvPolynomial (Fin d) E) : MvPolynomial (Fin d) E :=
  ∑ m ∈ F.support, MvPolynomial.monomial (reduceMon (Fintype.card E) m) (F.coeff m)

private lemma eval_reducePoly {E : Type} [Field E] [Fintype E] {d : ℕ}
    (F : MvPolynomial (Fin d) E) (x : Fin d → E) :
    MvPolynomial.eval x (reducePoly F) = MvPolynomial.eval x F := by
  unfold reducePoly
  rw [map_sum]
  conv_rhs => rw [MvPolynomial.as_sum F, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.eval_monomial, MvPolynomial.eval_monomial]
  congr 1
  rw [Finsupp.prod_fintype _ _ (fun _ => by simp), Finsupp.prod_fintype _ _ (fun _ => by simp)]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [reduceMon_apply]
  exact pow_reduce_ff (x j) (m j)

private lemma reducePoly_deg_le {E : Type} [Field E] [Fintype E] {d : ℕ}
    (F : MvPolynomial (Fin d) E) :
    (reducePoly F).totalDegree ≤ F.totalDegree := by
  have hq : 2 ≤ Fintype.card E := Fintype.one_lt_card
  unfold reducePoly
  refine totalDegree_sum_le F.support _ F.totalDegree fun m hm => ?_
  refine le_trans (MvPolynomial.totalDegree_monomial_le (reduceMon (Fintype.card E) m) (F.coeff m)) ?_
  have hsum_le : (reduceMon (Fintype.card E) m).sum (fun _ e => e) ≤ m.sum (fun _ e => e) := by
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Finsupp.sum_fintype _ _ (fun _ => rfl)]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [reduceMon_apply]
    exact reduceExp_le (Fintype.card E) (m j) hq
  exact le_trans hsum_le (MvPolynomial.le_totalDegree hm)

private lemma reducePoly_var_le {E : Type} [Field E] [Fintype E] {d : ℕ}
    (F : MvPolynomial (Fin d) E) :
    ∀ m ∈ (reducePoly F).support, ∀ j : Fin d, m j ≤ Fintype.card E - 1 := by
  have hq : 2 ≤ Fintype.card E := Fintype.one_lt_card
  intro m hm j
  unfold reducePoly at hm
  have hcoeff : (∑ m' ∈ F.support,
      MvPolynomial.monomial (reduceMon (Fintype.card E) m') (F.coeff m')).coeff m ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hm
  rw [MvPolynomial.coeff_sum] at hcoeff
  have hex : ∃ m' ∈ F.support,
      (MvPolynomial.monomial (reduceMon (Fintype.card E) m') (F.coeff m')).coeff m ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact hcoeff (Finset.sum_eq_zero hall)
  rcases hex with ⟨m', _, hne⟩
  rw [MvPolynomial.coeff_monomial] at hne
  by_cases hEq : reduceMon (Fintype.card E) m' = m
  · rw [← hEq, reduceMon_apply]
    exact reduceExp_lt (Fintype.card E) (m' j) hq
  · rw [if_neg hEq] at hne
    exact absurd rfl hne

private lemma ore_reduced_bound {E : Type} [Field E] [Fintype E] [DecidableEq E] :
    ∀ (d : ℕ) (G : MvPolynomial (Fin d) E),
      G ≠ 0 →
      (∀ m ∈ G.support, ∀ j : Fin d, m j ≤ Fintype.card E - 1) →
      ∀ c : ℕ, G.totalDegree ≤ c → c ≤ d * (Fintype.card E - 1) →
      orePsi (Fintype.card E) d c ≤
        (Finset.univ.filter (fun x : Fin d → E => MvPolynomial.eval x G ≠ 0)).card := by
  classical
  have hq : 2 ≤ Fintype.card E := Fintype.one_lt_card
  intro d
  induction d with
  | zero =>
    intro G hG0 _ c _ hc
    have hc0 : c = 0 := by omega
    subst hc0
    have hpsi : orePsi (Fintype.card E) 0 0 = 1 := by
      unfold orePsi; simp
    rw [hpsi]
    have hGeq : G = MvPolynomial.C (MvPolynomial.eval Fin.elim0 G) := by
      ext m
      have hm0 : m = 0 := by ext i; exact Fin.elim0 i
      subst hm0
      rw [MvPolynomial.coeff_C, if_pos rfl, MvPolynomial.eval_eq']
      have hsupp : G.support = {0} := by
        ext m'
        have hm'0 : m' = 0 := by ext i; exact Fin.elim0 i
        subst hm'0
        simp only [Finset.mem_singleton, iff_true, MvPolynomial.mem_support_iff]
        intro h0
        apply hG0
        ext m''
        have hm''0 : m'' = 0 := by ext i; exact Fin.elim0 i
        subst hm''0
        simpa using h0
      rw [hsupp, Finset.sum_singleton]
      simp
    have hev_ne : MvPolynomial.eval Fin.elim0 G ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hGeq
      exact hG0 hGeq
    have hmem : (Fin.elim0 : Fin 0 → E) ∈
        Finset.univ.filter (fun x : Fin 0 → E => MvPolynomial.eval x G ≠ 0) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hev_ne⟩
    exact Finset.card_pos.mpr ⟨Fin.elim0, hmem⟩
  | succ k ih =>
    intro G hG0 hvar c hdeg hc
    let P : Polynomial (MvPolynomial (Fin k) E) := MvPolynomial.finSuccEquiv E k G
    have hP0 : P ≠ 0 := by
      intro h0
      exact hG0 ((MvPolynomial.finSuccEquiv E k).injective (by simpa [P] using h0))
    set e := P.natDegree
    let L : MvPolynomial (Fin k) E := P.leadingCoeff
    have hL0 : L ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hP0
    have hL_coeff : ∀ m' : Fin k →₀ ℕ,
        L.coeff m' = G.coeff (Finsupp.cons e m') := by
      intro m'
      dsimp only [L, P]
      rw [Polynomial.leadingCoeff, MvPolynomial.finSuccEquiv_coeff_coeff]
    have he_le : e ≤ Fintype.card E - 1 := by
      have hex : ∃ m' ∈ L.support, True := by
        obtain ⟨m', hm'⟩ := MvPolynomial.support_nonempty.mpr hL0
        exact ⟨m', hm', trivial⟩
      rcases hex with ⟨m', hm', _⟩
      have hne : G.coeff (Finsupp.cons e m') ≠ 0 := by
        rw [← hL_coeff m']
        exact MvPolynomial.mem_support_iff.mp hm'
      have hmemG : Finsupp.cons e m' ∈ G.support := MvPolynomial.mem_support_iff.mpr hne
      have h0 := hvar (Finsupp.cons e m') hmemG 0
      simpa using h0
    have hLvar : ∀ m' ∈ L.support, ∀ j : Fin k, m' j ≤ Fintype.card E - 1 := by
      intro m' hm' j
      have hmemG : Finsupp.cons e m' ∈ G.support := by
        rw [MvPolynomial.mem_support_iff, ← hL_coeff m']
        exact MvPolynomial.mem_support_iff.mp hm'
      have hj := hvar (Finsupp.cons e m') hmemG j.succ
      simpa using hj
    have hLdeg_add : L.totalDegree + e ≤ G.totalDegree := by
      rw [MvPolynomial.totalDegree]
      by_cases hLs : L.support = ∅
      · exact absurd (MvPolynomial.support_eq_empty.mp hLs) hL0
      · have hne : L.support.Nonempty := Finset.nonempty_iff_ne_empty.mpr hLs
        obtain ⟨m', hm', hmax⟩ := Finset.exists_max_image L.support (fun m => m.sum fun _ n => n) hne
        have hsup : L.support.sup (fun m => m.sum fun _ n => n) = m'.sum (fun _ n => n) := by
          apply le_antisymm
          · rw [Finset.sup_le_iff]; exact hmax
          · exact Finset.le_sup (f := fun m : Fin k →₀ ℕ => m.sum fun _ n => n) hm'
        rw [hsup]
        have hmemG : Finsupp.cons e m' ∈ G.support := by
          rw [MvPolynomial.mem_support_iff, ← hL_coeff m']
          exact MvPolynomial.mem_support_iff.mp hm'
        have hleG := MvPolynomial.le_totalDegree hmemG
        have hcons_sum : (Finsupp.cons e m').sum (fun _ n => n) = e + m'.sum (fun _ n => n) := by
          rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Finsupp.sum_fintype _ _ (fun _ => rfl),
            Fin.sum_univ_succ]
          simp
        omega
    have he_le_c : e ≤ c := by omega
    have hLdeg_var : L.totalDegree ≤ k * (Fintype.card E - 1) := by
      rw [MvPolynomial.totalDegree, Finset.sup_le_iff]
      intro m' hm'
      rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
      calc
        ∑ j : Fin k, m' j ≤ ∑ _j : Fin k, (Fintype.card E - 1) :=
          Finset.sum_le_sum fun j _ => hLvar m' hm' j
        _ = k * (Fintype.card E - 1) := by simp
    set c' := min (c - e) (k * (Fintype.card E - 1))
    have hLdeg_c' : L.totalDegree ≤ c' := le_min (by omega) hLdeg_var
    have hih := ih L hL0 hLvar c' hLdeg_c' (min_le_right _ _)
    let goodL : Finset (Fin k → E) := Finset.univ.filter (fun y => MvPolynomial.eval y L ≠ 0)
    let goodG : Finset (Fin (k + 1) → E) := Finset.univ.filter (fun x => MvPolynomial.eval x G ≠ 0)
    have hfiber : ∀ y ∈ goodL,
        Fintype.card E - e ≤
          (Finset.univ.filter (fun t : E => MvPolynomial.eval (Fin.cons t y) G ≠ 0)).card := by
      intro y hy
      have hyL : MvPolynomial.eval y L ≠ 0 := (Finset.mem_filter.mp hy).2
      let Py : Polynomial E := P.map (MvPolynomial.eval y)
      have hPy_coeff : ∀ i, Py.coeff i = MvPolynomial.eval y (P.coeff i) :=
        fun i => Polynomial.coeff_map (MvPolynomial.eval y) i
      have hPy_e : Py.coeff e ≠ 0 := by
        rw [hPy_coeff e]; exact hyL
      have hPy_ne : Py ≠ 0 := fun h0 => hPy_e (by rw [h0]; simp)
      have hPy_deg : Py.natDegree ≤ e := Polynomial.natDegree_map_le
      have hPy_eval : ∀ t : E, Py.eval t = MvPolynomial.eval (Fin.cons t y) G := by
        intro t
        have h := MvPolynomial.eval_eq_eval_mv_eval' (s := y) (y := t) (f := G)
        simpa [Py, P, Polynomial.eval_map] using h.symm
      let rootsS : Finset E := Finset.univ.filter (fun t : E => Py.eval t = 0)
      have hroots_le : rootsS.card ≤ e := by
        have hsub : rootsS.val ⊆ Py.roots := by
          intro t ht
          have h0 : Py.eval t = 0 := (Finset.mem_filter.mp ht).2
          exact (Polynomial.mem_roots hPy_ne).mpr h0
        have hc1 : rootsS.card ≤ Py.roots.card := Multiset.card_le_card (Multiset.le_iff_subset rootsS.nodup |>.mpr hsub)
        exact le_trans hc1 (le_trans (Polynomial.card_roots' Py) hPy_deg)
      have hcomp :
          rootsS.card + (Finset.univ.filter (fun t : E => MvPolynomial.eval (Fin.cons t y) G ≠ 0)).card =
            Fintype.card E := by
        have hdisj : Disjoint rootsS
            (Finset.univ.filter (fun t : E => MvPolynomial.eval (Fin.cons t y) G ≠ 0)) := by
          rw [Finset.disjoint_left]
          intro t h1 h2
          have a1 := (Finset.mem_filter.mp h1).2
          have a2 := (Finset.mem_filter.mp h2).2
          rw [hPy_eval] at a1
          exact a2 a1
        have hunion : rootsS ∪
            (Finset.univ.filter (fun t : E => MvPolynomial.eval (Fin.cons t y) G ≠ 0)) = Finset.univ := by
          ext t
          simp only [rootsS, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
            hPy_eval, iff_true]
          exact eq_or_ne _ 0
        rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ]
      omega
    have hcard_mul : (Fintype.card E - e) * goodL.card ≤ goodG.card := by
      let pairs : Finset ((Fin k → E) × E) :=
        goodL.sigma (fun y => Finset.univ.filter (fun t : E => MvPolynomial.eval (Fin.cons t y) G ≠ 0))
          |>.map ⟨fun p => (p.1, p.2), fun a b h => by cases a; cases b; cases h; rfl⟩
      have hpairs_le : (Fintype.card E - e) * goodL.card ≤ pairs.card := by
        dsimp only [pairs]
        rw [Finset.card_map, Finset.card_sigma]
        calc
          (Fintype.card E - e) * goodL.card = ∑ _y ∈ goodL, (Fintype.card E - e) := by
            rw [Finset.sum_const, smul_eq_mul, mul_comm]
          _ ≤ ∑ y ∈ goodL, (Finset.univ.filter (fun t : E => MvPolynomial.eval (Fin.cons t y) G ≠ 0)).card :=
            Finset.sum_le_sum hfiber
      have hmap_le : pairs.card ≤ goodG.card := by
        refine Finset.card_le_card_of_injOn (fun p => Fin.cons p.2 p.1) ?_ ?_
        · intro p hp
          dsimp only [pairs] at hp
          rcases Finset.mem_map.mp hp with ⟨⟨y, t⟩, hsig, rfl⟩
          have ht := (Finset.mem_sigma.mp hsig).2
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp ht).2⟩
        · intro p1 _ p2 _ hEq
          have ht : p1.2 = p2.2 := by
            have := congrFun hEq 0
            simpa using this
          have hy : p1.1 = p2.1 := by
            funext j
            have := congrFun hEq j.succ
            simpa using this
          exact Prod.ext hy ht
      exact le_trans hpairs_le hmap_le
    calc
      orePsi (Fintype.card E) (k + 1) c
          ≤ (Fintype.card E - e) * orePsi (Fintype.card E) k c' :=
            orePsi_step (Fintype.card E) k c e hq he_le he_le_c hc
      _ ≤ (Fintype.card E - e) * goodL.card := Nat.mul_le_mul_left _ hih
      _ ≤ goodG.card := hcard_mul

private lemma det_poly_of_pencil {E : Type} [Field E] {d n : ℕ}
    (M : Matrix (Fin n) (Fin n) E)
    (P : (Fin d → E) →ₗ[E] Matrix (Fin n) (Fin n) E) :
    ∃ f : MvPolynomial (Fin d) E,
      f.totalDegree ≤ M.rank ∧
      ∀ x : Fin d → E, MvPolynomial.eval x f = ((1 : Matrix (Fin n) (Fin n) E) + P x * M).det := by
  classical
  let A : Matrix (Fin n) (Fin n) (MvPolynomial (Fin d) E) := fun u v =>
    (1 : Matrix (Fin n) (Fin n) (MvPolynomial (Fin d) E)) u v +
      ∑ k : Fin d, MvPolynomial.X k * MvPolynomial.C ((P (Pi.single k 1) * M) u v)
  refine ⟨A.det, ?_, ?_⟩
  · let K : Submodule E (Fin n → E) := LinearMap.ker M.mulVecLin
    obtain ⟨W, hKW⟩ := Submodule.exists_isCompl K
    have hsum_rk : Module.finrank E (LinearMap.range M.mulVecLin) + Module.finrank E K = n := by
      have h := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
      simpa [Module.finrank_pi] using h
    have hKW_dim : Module.finrank E K + Module.finrank E W = n := by
      have h := Submodule.finrank_add_eq_of_isCompl hKW
      simpa [Module.finrank_pi] using h
    set r := M.rank
    have hWdim : Module.finrank E W = r := by
      have : r = Module.finrank E (LinearMap.range M.mulVecLin) := rfl
      omega
    have hKdim : Module.finrank E K = n - r := by
      have : r = Module.finrank E (LinearMap.range M.mulVecLin) := rfl
      omega
    have hr_le : r ≤ n := by omega
    let bW : Module.Basis (Fin r) E W :=
      (Module.finBasis E W).reindex (finCongr hWdim)
    let bK : Module.Basis (Fin (n - r)) E K :=
      (Module.finBasis E K).reindex (finCongr hKdim)
    let eWK : (W × K) ≃ₗ[E] (Fin n → E) := Submodule.prodEquivOfIsCompl W K hKW.symm
    let bSum : Module.Basis (Fin r ⊕ Fin (n - r)) E (Fin n → E) :=
      (bW.prod bK).map eWK
    let idxEquiv : Fin r ⊕ Fin (n - r) ≃ Fin n :=
      (finSumFinEquiv).trans (finCongr (by omega))
    let b : Module.Basis (Fin n) E (Fin n → E) := bSum.reindex idxEquiv
    have hb_ker : ∀ j : Fin n, r ≤ j.val → M.mulVec (b j) = 0 := by
      intro j hj
      let jK : Fin (n - r) := ⟨j.val - r, by have := j.isLt; omega⟩
      have hidx : idxEquiv (Sum.inr jK) = j := by
        apply Fin.ext
        simp only [idxEquiv, Equiv.trans_apply, finSumFinEquiv_apply_right, finCongr_apply,
          Fin.val_cast, Fin.val_natAdd, jK]
        omega
      have hbj : b j = (bK jK).1 := by
        rw [← hidx]
        dsimp only [b, bSum]
        rw [Module.Basis.reindex_apply, Equiv.symm_apply_apply]
        simp only [Module.Basis.map_apply, Module.Basis.prod_apply, LinearMap.coe_inl, LinearMap.coe_inr,
          eWK, Submodule.prodEquivOfIsCompl]
        change (W.subtype.coprod K.subtype) (0, bK jK) = (bK jK).1
        simp
      rw [hbj]
      exact LinearMap.mem_ker.mp (bK jK).2
    let φ : (Fin n → E) ≃ₗ[E] (Fin n → E) := b.equivFun.symm
    let U : Matrix (Fin n) (Fin n) E := LinearMap.toMatrix' φ.toLinearMap
    let Uinv : Matrix (Fin n) (Fin n) E := LinearMap.toMatrix' φ.symm.toLinearMap
    have hUUinv : Uinv * U = 1 := by
      dsimp only [Uinv, U]
      rw [← LinearMap.toMatrix'_comp]
      have hcomp : φ.symm.toLinearMap.comp φ.toLinearMap = LinearMap.id := by
        ext v; simp
      rw [hcomp, LinearMap.toMatrix'_id]
    have hUcol : ∀ j : Fin n, U.mulVec (Pi.single j 1) = b j := by
      intro j
      dsimp only [U, φ]
      rw [LinearMap.toMatrix'_mulVec]
      change b.equivFun.symm (Pi.single j 1) = b j
      rw [Module.Basis.equivFun_symm_apply]
      simp [Pi.single_apply]
    have hMU_zero : ∀ u v : Fin n, r ≤ v.val → (M * U) u v = 0 := by
      intro u v hv
      have h1 : (M * U).mulVec (Pi.single v 1) u = (M * U) u v := by
        simp [Matrix.mulVec_single]
      rw [← h1, ← Matrix.mulVec_mulVec, hUcol v, hb_ker v hv]
      rfl
    let UC : Matrix (Fin n) (Fin n) (MvPolynomial (Fin d) E) := U.map MvPolynomial.C
    let UinvC : Matrix (Fin n) (Fin n) (MvPolynomial (Fin d) E) := Uinv.map MvPolynomial.C
    have hUinvC_mul : UinvC * UC = 1 := by
      dsimp only [UinvC, UC]
      rw [← Matrix.map_mul, hUUinv, Matrix.map_one MvPolynomial.C (map_zero _) (map_one _)]
    let B : Matrix (Fin n) (Fin n) (MvPolynomial (Fin d) E) := UinvC * A * UC
    have hBdet : B.det = A.det := by
      dsimp only [B]
      rw [Matrix.det_mul, Matrix.det_mul, mul_assoc UinvC.det A.det UC.det, mul_comm A.det UC.det,
        ← mul_assoc, ← Matrix.det_mul, hUinvC_mul, Matrix.det_one, one_mul]
    have hBentry : ∀ u v : Fin n,
        B u v = (1 : Matrix (Fin n) (Fin n) (MvPolynomial (Fin d) E)) u v +
          ∑ k : Fin d, MvPolynomial.X k * MvPolynomial.C ((Uinv * P (Pi.single k 1) * M * U) u v) := by
      intro u v
      have hA_eq : A = 1 + ∑ k : Fin d, (MvPolynomial.X k : MvPolynomial (Fin d) E) • (P (Pi.single k 1) * M).map MvPolynomial.C := by
        ext i j
        simp only [A, Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
      have hB_eq : B = 1 + ∑ k : Fin d, (MvPolynomial.X k : MvPolynomial (Fin d) E) • (Uinv * P (Pi.single k 1) * M * U).map MvPolynomial.C := by
        dsimp only [B]
        rw [hA_eq, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hUinvC_mul,
          Matrix.mul_sum, Matrix.sum_mul]
        congr 1
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Matrix.mul_smul, Matrix.smul_mul]
        congr 1
        dsimp only [UinvC, UC]
        rw [← Matrix.map_mul, ← Matrix.map_mul]
        congr 1
        simp only [Matrix.mul_assoc]
      rw [hB_eq]
      simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
    have hBdeg_hi : ∀ u v : Fin n, r ≤ v.val → (B u v).totalDegree = 0 := by
      intro u v hv
      rw [hBentry u v]
      have hzero : ∀ k : Fin d, (Uinv * P (Pi.single k 1) * M * U) u v = 0 := by
        intro k
        have hassoc : Uinv * P (Pi.single k 1) * M * U = (Uinv * P (Pi.single k 1)) * (M * U) := by
          rw [Matrix.mul_assoc]
        rw [hassoc, Matrix.mul_apply]
        refine Finset.sum_eq_zero fun w _ => ?_
        rw [hMU_zero w v hv, mul_zero]
      have hsum0 : (∑ k : Fin d, MvPolynomial.X k * MvPolynomial.C ((Uinv * P (Pi.single k 1) * M * U) u v)) = 0 := by
        refine Finset.sum_eq_zero fun k _ => ?_
        rw [hzero k, map_zero, mul_zero]
      rw [hsum0, add_zero]
      by_cases huv : u = v
      · subst huv; simp [Matrix.one_apply]
      · simp [Matrix.one_apply, huv]
    have hBdeg_lo : ∀ u v : Fin n, (B u v).totalDegree ≤ 1 := by
      intro u v
      rw [hBentry u v]
      refine le_trans (MvPolynomial.totalDegree_add _ _) (max_le ?_ ?_)
      · by_cases huv : u = v
        · subst huv; simp [Matrix.one_apply]
        · simp [Matrix.one_apply, huv]
      · refine totalDegree_sum_le Finset.univ _ 1 fun k _ => ?_
        refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
        simp [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_C]
    rw [← hBdet, Matrix.det_apply']
    refine totalDegree_sum_le Finset.univ _ r fun σ _ => ?_
    have hsign_le : (((Equiv.Perm.sign σ : ℤ) : MvPolynomial (Fin d) E) * ∏ i : Fin n, B (σ i) i).totalDegree ≤
        (∏ i : Fin n, B (σ i) i).totalDegree := by
      refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
      have hcast : ((Equiv.Perm.sign σ : ℤ) : MvPolynomial (Fin d) E) =
          MvPolynomial.C ((Equiv.Perm.sign σ : ℤ) : E) := by simp
      rw [hcast, MvPolynomial.totalDegree_C, zero_add]
    refine le_trans hsign_le ?_
    refine le_trans (totalDegree_prod_le Finset.univ _) ?_
    have hsplit : (∑ i : Fin n, (B (σ i) i).totalDegree) =
        ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < r), (B (σ i) i).totalDegree := by
      rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ) (p := fun i : Fin n => i.val < r)]
      have hzero : ∑ i ∈ Finset.univ.filter (fun i : Fin n => ¬ i.val < r), (B (σ i) i).totalDegree = 0 :=
        Finset.sum_eq_zero fun i hi => hBdeg_hi (σ i) i (by have := (Finset.mem_filter.mp hi).2; omega)
      rw [hzero, add_zero]
    rw [hsplit]
    have hcard_lt : (Finset.univ.filter (fun i : Fin n => i.val < r)).card = r := by
      have heq : Finset.univ.filter (fun i : Fin n => i.val < r) =
          (Finset.range r).attach.image (fun t => (⟨t.1, by have := Finset.mem_range.mp t.2; omega⟩ : Fin n)) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
          Finset.mem_attach, Subtype.exists, Finset.mem_range]
        constructor
        · intro hi; exact ⟨i.val, hi, Fin.ext rfl⟩
        · rintro ⟨a, ha, rfl⟩; exact ha
      rw [heq, Finset.card_image_of_injective]
      · simp
      · intro a b hab; apply Subtype.ext; exact congrArg Fin.val hab
    calc
      ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < r), (B (σ i) i).totalDegree
          ≤ ∑ _i ∈ Finset.univ.filter (fun i : Fin n => i.val < r), 1 :=
            Finset.sum_le_sum fun i _ => hBdeg_lo (σ i) i
      _ = r := by simp [hcard_lt]
  · intro x
    rw [RingHom.map_det (MvPolynomial.eval x) A]
    congr 1
    ext u v
    rw [RingHom.mapMatrix_apply, Matrix.map_apply]
    simp only [A, map_add, map_sum, map_mul, MvPolynomial.eval_X, MvPolynomial.eval_C,
      Matrix.add_apply]
    have h1 : MvPolynomial.eval x ((1 : Matrix (Fin n) (Fin n) (MvPolynomial (Fin d) E)) u v) =
        (1 : Matrix (Fin n) (Fin n) E) u v := by
      by_cases huv : u = v
      · subst huv; simp
      · simp [huv]
    rw [h1]
    congr 1
    have hx_eq : x = ∑ k : Fin d, x k • Pi.single k (1 : E) := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply]
    conv_rhs => rw [hx_eq, map_sum]
    rw [Finset.sum_mul, Matrix.sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]

end PEqualNP.Outside.L_lib_648_aux

theorem PEqualNP.Outside.L_lib_648 : (∀ (E : Type) [Field E] [Fintype E] (d n l : ℕ),
  let q := Fintype.card E
  let Mat := Matrix (Fin n) (Fin n) E
  ∀ (M : Fin l → Mat) (P : Fin l → ((Fin d → E) →ₗ[E] Mat)),
    let c := min (∑ i : Fin l, (M i).rank) (d*(q-1))
    let a := c/(q-1)
    let b := c % (q-1)
    let good := @Finset.filter (Fin d → E)
      (fun x => ∀ i : Fin l, ((1 : Mat) + P i x * M i).det ≠ 0)
      (fun _ => Classical.propDecidable _) Finset.univ
    q^(d-a) - b*q^(d-a-1) ≤ good.card) := by
  classical
  intro E _ _ d n l q Mat M P c a b good
  have hq : 2 ≤ q := Fintype.one_lt_card
  have hf_ex : ∀ i : Fin l, ∃ f : MvPolynomial (Fin d) E,
      f.totalDegree ≤ (M i).rank ∧
      ∀ x : Fin d → E, MvPolynomial.eval x f = ((1 : Mat) + P i x * M i).det :=
    fun i => PEqualNP.Outside.L_lib_648_aux.det_poly_of_pencil (M i) (P i)
  let f : Fin l → MvPolynomial (Fin d) E := fun i => Classical.choose (hf_ex i)
  have hf_deg : ∀ i : Fin l, (f i).totalDegree ≤ (M i).rank :=
    fun i => (Classical.choose_spec (hf_ex i)).1
  have hf_eval : ∀ i : Fin l, ∀ x : Fin d → E,
      MvPolynomial.eval x (f i) = ((1 : Mat) + P i x * M i).det :=
    fun i => (Classical.choose_spec (hf_ex i)).2
  let F : MvPolynomial (Fin d) E := ∏ i : Fin l, f i
  have hF_eval : ∀ x : Fin d → E,
      MvPolynomial.eval x F = ∏ i : Fin l, ((1 : Mat) + P i x * M i).det := by
    intro x
    dsimp only [F]
    rw [map_prod]
    exact Finset.prod_congr rfl fun i _ => hf_eval i x
  have hF_deg : F.totalDegree ≤ ∑ i : Fin l, (M i).rank := by
    dsimp only [F]
    exact le_trans (PEqualNP.Outside.L_lib_648_aux.totalDegree_prod_le Finset.univ f)
      (Finset.sum_le_sum fun i _ => hf_deg i)
  let G : MvPolynomial (Fin d) E := PEqualNP.Outside.L_lib_648_aux.reducePoly F
  have hG_eval : ∀ x : Fin d → E, MvPolynomial.eval x G = MvPolynomial.eval x F :=
    fun x => PEqualNP.Outside.L_lib_648_aux.eval_reducePoly F x
  have hG_ne0 : G ≠ 0 := by
    intro h0
    have hev0 : MvPolynomial.eval (0 : Fin d → E) G = 0 := by rw [h0, map_zero]
    rw [hG_eval 0, hF_eval 0] at hev0
    have hprod1 : (∏ i : Fin l, ((1 : Mat) + P i 0 * M i).det) = 1 := by
      refine Finset.prod_eq_one fun i _ => ?_
      simp
    rw [hprod1] at hev0
    exact one_ne_zero hev0
  have hG_var : ∀ m ∈ G.support, ∀ j : Fin d, m j ≤ q - 1 :=
    PEqualNP.Outside.L_lib_648_aux.reducePoly_var_le F
  have hG_deg_var : G.totalDegree ≤ d * (q - 1) := by
    rw [MvPolynomial.totalDegree, Finset.sup_le_iff]
    intro m hm
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
    calc
      ∑ j : Fin d, m j ≤ ∑ _j : Fin d, (q - 1) := Finset.sum_le_sum fun j _ => hG_var m hm j
      _ = d * (q - 1) := by simp
  have hG_deg_c : G.totalDegree ≤ c :=
    le_min (le_trans (PEqualNP.Outside.L_lib_648_aux.reducePoly_deg_le F) hF_deg) hG_deg_var
  have hbound := PEqualNP.Outside.L_lib_648_aux.ore_reduced_bound d G hG_ne0 hG_var c hG_deg_c (min_le_right _ _)
  have hcard_eq : (Finset.univ.filter (fun x : Fin d → E => MvPolynomial.eval x G ≠ 0)).card = good.card := by
    apply congrArg Finset.card
    ext x
    simp only [good, Finset.mem_filter, Finset.mem_univ, true_and, hG_eval, hF_eval,
      Finset.prod_ne_zero_iff, Finset.mem_univ, true_implies]
  rw [← hcard_eq]
  exact hbound
