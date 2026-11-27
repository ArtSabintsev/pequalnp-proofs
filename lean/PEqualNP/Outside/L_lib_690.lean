import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_690_aux

private def chi (u : ZMod 2) : ℤ :=
  if u = 0 then 1 else -1

private lemma chi_add (u v : ZMod 2) : chi (u + v) = chi u * chi v := by
  revert u v; decide

private lemma chi_sub (u v : ZMod 2) : chi (u - v) = chi u * chi v := by
  revert u v; decide

private lemma sum_eq_zero_of_invol {α : Type} [Fintype α]
    (f : α → ℤ) (τ : α → α) (hinv : ∀ x, τ (τ x) = x) (hneg : ∀ x, f (τ x) = -f x) :
    (∑ x : α, f x) = 0 := by
  have h1 : (∑ x : α, f (τ x)) = ∑ x : α, f x :=
    Fintype.sum_equiv (Equiv.ofBijective τ ⟨fun a b h => by have := congrArg τ h; rwa [hinv, hinv] at this,
      fun b => ⟨τ b, hinv b⟩⟩) _ _ (fun _ => rfl)
  have h2 : (∑ x : α, f (τ x)) = - ∑ x : α, f x := by
    rw [Finset.sum_congr rfl fun x _ => hneg x, Finset.sum_neg_distrib]
  linarith

private lemma chi_dot_sum {n : ℕ} (v : Fin n → ZMod 2) :
    (∑ c : Fin n → ZMod 2, chi (∑ i : Fin n, c i * v i)) =
      if v = 0 then (2 : ℤ) ^ n else 0 := by
  by_cases hv : v = 0
  · subst hv
    rw [if_pos rfl]
    have hconst : ∀ c : Fin n → ZMod 2, chi (∑ i : Fin n, c i * (0 : Fin n → ZMod 2) i) = 1 := by
      intro c; simp [chi]
    rw [Finset.sum_congr rfl fun c _ => hconst c, Finset.sum_const, Finset.card_univ,
      Fintype.card_fun, ZMod.card, Fintype.card_fin, nsmul_eq_mul, mul_one]
    push_cast; rfl
  · rw [if_neg hv]
    have hex : ∃ i0 : Fin n, v i0 ≠ 0 := by
      by_contra hall
      push_neg at hall
      apply hv; funext i; exact hall i
    rcases hex with ⟨i0, hi0⟩
    have hi01 : v i0 = 1 := by
      generalize hv0 : v i0 = z at hi0
      fin_cases z
      · exact absurd rfl hi0
      · rfl
    let τ : (Fin n → ZMod 2) → (Fin n → ZMod 2) := fun c => Function.update c i0 (c i0 + 1)
    refine sum_eq_zero_of_invol _ τ ?_ ?_
    · intro c
      funext i
      by_cases hi : i = i0
      · subst hi
        simp only [τ, Function.update_self]
        generalize c i = z; revert z; decide
      · simp [τ, Function.update, hi]
    · intro c
      have hdot : (∑ i : Fin n, τ c i * v i) = (∑ i : Fin n, c i * v i) + 1 := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i0),
          ← Finset.add_sum_erase _ _ (Finset.mem_univ i0)]
        have hrest : (∑ i ∈ Finset.univ.erase i0, τ c i * v i) =
            ∑ i ∈ Finset.univ.erase i0, c i * v i := by
          refine Finset.sum_congr rfl fun i hi => ?_
          have hne : i ≠ i0 := (Finset.mem_erase.mp hi).1
          simp [τ, Function.update, hne]
        rw [hrest]
        simp only [τ, Function.update_self, hi01]
        ring
      rw [hdot, chi_add]
      have hchi1 : chi 1 = -1 := by decide
      rw [hchi1]; ring

private lemma neg_masks_card_le {r : ℕ} (hr : 0 < r) (t : Fin r → ZMod 2) :
    (Finset.univ.filter (fun mask : Fin r → ZMod 2 => (∑ i : Fin r, mask i * t i) ≠ 0)).card ≤
      2 ^ (r - 1) := by
  by_cases ht : t = 0
  · subst ht
    have hemp : Finset.univ.filter (fun mask : Fin r → ZMod 2 => (∑ i : Fin r, mask i * (0 : Fin r → ZMod 2) i) ≠ 0) = ∅ := by
      ext mask; simp
    rw [hemp]; simp
  · have hsum := chi_dot_sum t
    rw [if_neg ht] at hsum
    let Pos := Finset.univ.filter (fun mask : Fin r → ZMod 2 => (∑ i : Fin r, mask i * t i) = 0)
    let Neg := Finset.univ.filter (fun mask : Fin r → ZMod 2 => (∑ i : Fin r, mask i * t i) ≠ 0)
    have hsplit : (∑ mask : Fin r → ZMod 2, chi (∑ i : Fin r, mask i * t i)) =
        (Pos.card : ℤ) - (Neg.card : ℤ) := by
      rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
        (p := fun mask : Fin r → ZMod 2 => (∑ i : Fin r, mask i * t i) = 0)]
      have hp : (∑ mask ∈ Pos, chi (∑ i : Fin r, mask i * t i)) = (Pos.card : ℤ) := by
        have hc : ∀ mask ∈ Pos, chi (∑ i : Fin r, mask i * t i) = 1 := by
          intro mask hm; rw [(Finset.mem_filter.mp hm).2]; decide
        rw [Finset.sum_congr rfl hc, Finset.sum_const, nsmul_eq_mul, mul_one]
      have hn : (∑ mask ∈ Neg, chi (∑ i : Fin r, mask i * t i)) = - (Neg.card : ℤ) := by
        have hc : ∀ mask ∈ Neg, chi (∑ i : Fin r, mask i * t i) = -1 := by
          intro mask hm; unfold chi; rw [if_neg (Finset.mem_filter.mp hm).2]
        rw [Finset.sum_congr rfl hc, Finset.sum_const, nsmul_eq_mul]; ring
      change (∑ mask ∈ Pos, chi (∑ i : Fin r, mask i * t i)) +
          (∑ mask ∈ Neg, chi (∑ i : Fin r, mask i * t i)) = (Pos.card : ℤ) - (Neg.card : ℤ)
      rw [hp, hn]; ring
    have htot : Pos.card + Neg.card = 2 ^ r := by
      have hdisj : Disjoint Pos Neg := by
        rw [Finset.disjoint_left]
        intro m h1 h2; exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
      have hunion : Pos ∪ Neg = Finset.univ := by
        ext m; simp only [Pos, Neg, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
        exact eq_or_ne _ 0
      rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ,
        Fintype.card_fun, ZMod.card, Fintype.card_fin]
    have hpow : 2 ^ r = 2 * 2 ^ (r - 1) := by
      conv_lhs => rw [show r = (r - 1) + 1 by omega, pow_succ]
      ring
    have heq_pn : Pos.card = Neg.card := by omega
    change Neg.card ≤ 2 ^ (r - 1)
    omega

private lemma poly_degree_sum_le {K : Type} [Field K] {k : ℕ} (hk : 0 < k) (c : Fin k → ZMod 2) :
    (∑ j : Fin k, if c j = 0 then (0 : Polynomial K) else Polynomial.X ^ j.val).natDegree ≤ k - 1 := by
  refine le_trans (Polynomial.natDegree_sum_le Finset.univ _) ?_
  rw [Finset.fold_max_le]
  refine ⟨Nat.zero_le _, fun j _ => ?_⟩
  dsimp only [Function.comp_apply]
  by_cases h : c j = 0
  · simp [h]
  · rw [if_neg h, Polynomial.natDegree_X_pow]
    have := j.isLt
    omega

end PEqualNP.Outside.L_lib_690_aux

theorem PEqualNP.Outside.L_lib_690 : (∀ (k s r : ℕ), 0 < k → 0 < s → 0 < r →
  let F := ZMod 2
  let K := GaloisField 2 s
  let q := 2^s
  let V := Fin k → F
  let W := Fin s → F
  let R := Fin r → F
  ∀ (atPoint : Fin q ≃ K) (coord : K ≃ₗ[F] W) (a : Fin r → V) (t : R),
    let sample := fun (x : Fin q) (y : W) (j : Fin k) =>
      ∑ i : Fin s, y i * coord (atPoint x ^ j.val) i
    let hits := ((Finset.univ : Finset (Fin q × W)).filter (fun z =>
      ∀ i : Fin r, (∑ j : Fin k, a i j * sample z.1 z.2 j) = t i)).card
    let roots := fun mask : R => ((Finset.univ : Finset (Fin q)).filter (fun x =>
      coord (∑ j : Fin k, if (∑ i : Fin r, mask i * a i j) = 0 then (0 : K) else atPoint x ^ j.val) = (0 : W))).card
    (2:ℤ)^r * (hits : ℤ) =
      (q : ℤ) * ∑ mask : R,
        (if (∑ i : Fin r, mask i*t i) = 0 then (1 : ℤ) else -1) * (roots mask : ℤ) ∧
    (LinearIndependent F a → q^2 ≤ 2^r*hits + 2^(r-1)*q*(k-1))) := by
  classical
  intro k s r hk hs hr F K q V W R atPoint coord a t sample hits roots
  have hpart1 : (2 : ℤ) ^ r * (hits : ℤ) =
      (q : ℤ) * ∑ mask : R,
        (if (∑ i : Fin r, mask i * t i) = 0 then (1 : ℤ) else -1) * (roots mask : ℤ) := by
    let res : (Fin q × W) → R := fun z i => (∑ j : Fin k, a i j * sample z.1 z.2 j) - t i
    have hhits_sum : (2 : ℤ) ^ r * (hits : ℤ) =
        ∑ z : Fin q × W, ∑ mask : R, PEqualNP.Outside.L_lib_690_aux.chi (∑ i : Fin r, mask i * res z i) := by
      have hinner : ∀ z : Fin q × W,
          (∑ mask : R, PEqualNP.Outside.L_lib_690_aux.chi (∑ i : Fin r, mask i * res z i)) =
            if (∀ i : Fin r, (∑ j : Fin k, a i j * sample z.1 z.2 j) = t i) then (2 : ℤ) ^ r else 0 := by
        intro z
        rw [PEqualNP.Outside.L_lib_690_aux.chi_dot_sum (res z)]
        refine if_congr ?_ rfl rfl
        constructor
        · intro h0 i
          have hi := congrFun h0 i
          dsimp only [res] at hi
          exact sub_eq_zero.mp hi
        · intro hall
          funext i
          dsimp only [res]
          exact sub_eq_zero.mpr (hall i)
      rw [Finset.sum_congr rfl fun z _ => hinner z, ← Finset.sum_filter, Finset.sum_const,
        nsmul_eq_mul, mul_comm]
    rw [hhits_sum, Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun mask _ => ?_
    have hsplit : ∀ z : Fin q × W,
        PEqualNP.Outside.L_lib_690_aux.chi (∑ i : Fin r, mask i * res z i) =
          PEqualNP.Outside.L_lib_690_aux.chi (∑ i : Fin r, mask i * t i) *
          PEqualNP.Outside.L_lib_690_aux.chi (∑ l : Fin s, z.2 l *
            coord (∑ j : Fin k, if (∑ i : Fin r, mask i * a i j) = 0 then (0 : K) else atPoint z.1 ^ j.val) l) := by
      intro z
      have hres_eq : (∑ i : Fin r, mask i * res z i) =
          (∑ i : Fin r, mask i * t i) -
          (∑ i : Fin r, mask i * ∑ j : Fin k, a i j * sample z.1 z.2 j) := by
        have hsub : ∀ i : Fin r, mask i * res z i =
            mask i * (∑ j : Fin k, a i j * sample z.1 z.2 j) - mask i * t i := by
          intro i; dsimp only [res]; ring
        rw [Finset.sum_congr rfl fun i _ => hsub i, Finset.sum_sub_distrib]
        generalize ∑ i : Fin r, mask i * ∑ j : Fin k, a i j * sample z.1 z.2 j = u
        generalize ∑ i : Fin r, mask i * t i = v
        revert u v; decide
      rw [hres_eq, PEqualNP.Outside.L_lib_690_aux.chi_sub]
      congr 2
      have hswap : (∑ i : Fin r, mask i * ∑ j : Fin k, a i j * sample z.1 z.2 j) =
          ∑ l : Fin s, z.2 l * ∑ j : Fin k,
            (∑ i : Fin r, mask i * a i j) * coord (atPoint z.1 ^ j.val) l := by
        calc
          (∑ i : Fin r, mask i * ∑ j : Fin k, a i j * sample z.1 z.2 j)
              = ∑ i : Fin r, ∑ j : Fin k, (mask i * a i j) * sample z.1 z.2 j := by
                refine Finset.sum_congr rfl fun i _ => ?_
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl fun j _ => by ring
          _ = ∑ j : Fin k, ∑ i : Fin r, (mask i * a i j) * sample z.1 z.2 j := Finset.sum_comm
          _ = ∑ j : Fin k, (∑ i : Fin r, mask i * a i j) * sample z.1 z.2 j := by
                refine Finset.sum_congr rfl fun j _ => (Finset.sum_mul _ _ _).symm
          _ = ∑ j : Fin k, ∑ l : Fin s, z.2 l * ((∑ i : Fin r, mask i * a i j) * coord (atPoint z.1 ^ j.val) l) := by
                refine Finset.sum_congr rfl fun j _ => ?_
                dsimp only [sample]
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl fun l _ => by ring
          _ = ∑ l : Fin s, ∑ j : Fin k, z.2 l * ((∑ i : Fin r, mask i * a i j) * coord (atPoint z.1 ^ j.val) l) :=
                Finset.sum_comm
          _ = ∑ l : Fin s, z.2 l * ∑ j : Fin k, (∑ i : Fin r, mask i * a i j) * coord (atPoint z.1 ^ j.val) l := by
                refine Finset.sum_congr rfl fun l _ => (Finset.mul_sum _ _ _).symm
      rw [hswap]
      refine Finset.sum_congr rfl fun l _ => ?_
      congr 1
      rw [map_sum, Finset.sum_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hc : (∑ i : Fin r, mask i * a i j) = 0
      · rw [if_pos hc, hc, zero_mul, map_zero]; rfl
      · have hc1 : (∑ i : Fin r, mask i * a i j) = 1 := by
          generalize (∑ i : Fin r, mask i * a i j) = u at hc
          fin_cases u
          · exact absurd rfl hc
          · rfl
        rw [if_neg hc, hc1, one_mul]
    rw [Finset.sum_congr rfl fun z _ => hsplit z, ← Finset.mul_sum]
    have hxy : (∑ z : Fin q × W, PEqualNP.Outside.L_lib_690_aux.chi (∑ l : Fin s, z.2 l *
        coord (∑ j : Fin k, if (∑ i : Fin r, mask i * a i j) = 0 then (0 : K) else atPoint z.1 ^ j.val) l)) =
        (q : ℤ) * (roots mask : ℤ) := by
      rw [Fintype.sum_prod_type]
      have hinner : ∀ x : Fin q,
          (∑ y : W, PEqualNP.Outside.L_lib_690_aux.chi (∑ l : Fin s, y l *
            coord (∑ j : Fin k, if (∑ i : Fin r, mask i * a i j) = 0 then (0 : K) else atPoint x ^ j.val) l)) =
          if coord (∑ j : Fin k, if (∑ i : Fin r, mask i * a i j) = 0 then (0 : K) else atPoint x ^ j.val) = (0 : W)
          then (q : ℤ) else 0 := by
        intro x
        rw [PEqualNP.Outside.L_lib_690_aux.chi_dot_sum]
        dsimp only [q]
        push_cast
        rfl
      rw [Finset.sum_congr rfl fun x _ => hinner x, ← Finset.sum_filter, Finset.sum_const,
        nsmul_eq_mul, mul_comm]
    rw [hxy]
    unfold PEqualNP.Outside.L_lib_690_aux.chi
    ring
  refine ⟨hpart1, ?_⟩
  intro hli
  have hroots0 : roots 0 = q := by
    dsimp only [roots]
    have huniv : Finset.univ.filter (fun x : Fin q =>
        coord (∑ j : Fin k, if (∑ i : Fin r, (0 : R) i * a i j) = 0 then (0 : K) else atPoint x ^ j.val) = (0 : W)) =
        Finset.univ := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      have hsum0 : (∑ j : Fin k, if (∑ i : Fin r, (0 : R) i * a i j) = 0 then (0 : K) else atPoint x ^ j.val) = 0 := by
        have hzero : ∀ i : Fin r, (0 : R) i = 0 := fun _ => rfl
        refine Finset.sum_eq_zero fun j _ => ?_
        simp only [hzero, zero_mul, Finset.sum_const_zero, ↓reduceIte]
      rw [hsum0, map_zero]
    rw [huniv, Finset.card_univ, Fintype.card_fin]
  have hroots_nz : ∀ mask : R, mask ≠ 0 → roots mask ≤ k - 1 := by
    intro mask hmask
    let c : Fin k → ZMod 2 := fun j => ∑ i : Fin r, mask i * a i j
    have hc_ne : c ≠ 0 := by
      intro hc0
      have hlin : ∑ i : Fin r, mask i • a i = 0 := by
        funext j
        rw [Finset.sum_apply]
        have hj : (∑ i : Fin r, mask i * a i j) = 0 := congrFun hc0 j
        change (∑ i : Fin r, mask i * a i j) = 0
        exact hj
      have hzero := (Fintype.linearIndependent_iff.mp hli) mask hlin
      apply hmask
      funext i
      exact hzero i
    let P : Polynomial K := ∑ j : Fin k, if c j = 0 then (0 : Polynomial K) else Polynomial.X ^ j.val
    have hP_ne : P ≠ 0 := by
      have hex : ∃ j0 : Fin k, c j0 ≠ 0 := by
        by_contra hall
        push_neg at hall
        apply hc_ne; funext j; exact hall j
      rcases hex with ⟨j0, hj0⟩
      intro hP0
      have hcoeff : P.coeff j0.val = 0 := by rw [hP0]; simp
      dsimp only [P] at hcoeff
      have hcoeff2 : (∑ j : Fin k, (if c j = 0 then (0 : Polynomial K) else Polynomial.X ^ j.val).coeff j0.val) = 0 := by
        have hlin_c := map_sum (Polynomial.lcoeff K j0.val) (fun j : Fin k => if c j = 0 then (0 : Polynomial K) else Polynomial.X ^ j.val) Finset.univ
        simpa only [Polynomial.lcoeff_apply, hcoeff] using hlin_c.symm
      have hsingle : (∑ j : Fin k, (if c j = 0 then (0 : Polynomial K) else Polynomial.X ^ j.val).coeff j0.val) = 1 := by
        rw [Finset.sum_eq_single j0]
        · rw [if_neg hj0, Polynomial.coeff_X_pow_self]
        · intro j _ hjj0
          by_cases hcj : c j = 0
          · rw [if_pos hcj, Polynomial.coeff_zero]
          · rw [if_neg hcj, Polynomial.coeff_X_pow]
            have hvne : j.val ≠ j0.val := fun hv => hjj0 (Fin.ext hv)
            rw [if_neg hvne.symm]
        · intro h; exact absurd (Finset.mem_univ j0) h
      rw [hsingle] at hcoeff2
      exact one_ne_zero hcoeff2
    have hP_deg : P.natDegree ≤ k - 1 := PEqualNP.Outside.L_lib_690_aux.poly_degree_sum_le hk c
    have hP_eval : ∀ x : Fin q,
        P.eval (atPoint x) = ∑ j : Fin k, if c j = 0 then (0 : K) else atPoint x ^ j.val := by
      intro x
      dsimp only [P]
      have hev := map_sum (Polynomial.evalRingHom (atPoint x)) (fun j : Fin k => if c j = 0 then (0 : Polynomial K) else Polynomial.X ^ j.val) Finset.univ
      simp only [Polynomial.coe_evalRingHom] at hev
      rw [hev]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hcj : c j = 0
      · simp [hcj]
      · simp [hcj]
    let S := Finset.univ.filter (fun x : Fin q =>
      coord (∑ j : Fin k, if c j = 0 then (0 : K) else atPoint x ^ j.val) = (0 : W))
    have himg_sub : (S.image atPoint).val ⊆ P.roots := by
      intro y hy
      rcases Finset.mem_image.mp (Finset.mem_val.mp hy) with ⟨x, hx, rfl⟩
      have hcoord0 := (Finset.mem_filter.mp hx).2
      have hval0 : (∑ j : Fin k, if c j = 0 then (0 : K) else atPoint x ^ j.val) = 0 :=
        coord.injective (by rw [hcoord0, map_zero])
      exact (Polynomial.mem_roots hP_ne).mpr (by rw [Polynomial.IsRoot.def, hP_eval x, hval0])
    have hle1 : S.card = (S.image atPoint).card :=
      (Finset.card_image_of_injective S atPoint.injective).symm
    have hle2 : (S.image atPoint).card ≤ P.roots.card :=
      Multiset.card_le_card ((Multiset.le_iff_subset (S.image atPoint).nodup).mpr himg_sub)
    exact le_trans (le_trans (le_of_eq hle1) hle2) (le_trans (Polynomial.card_roots' P) hP_deg)
  let Neg := Finset.univ.filter (fun mask : R => (∑ i : Fin r, mask i * t i) ≠ 0)
  have hNeg_card : Neg.card ≤ 2 ^ (r - 1) := PEqualNP.Outside.L_lib_690_aux.neg_masks_card_le hr t
  have hsum_ge : (q : ℤ) - (2 : ℤ) ^ (r - 1) * ((k - 1 : ℕ) : ℤ) ≤
      ∑ mask : R, (if (∑ i : Fin r, mask i * t i) = 0 then (1 : ℤ) else -1) * (roots mask : ℤ) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : R))]
    have h0term : (if (∑ i : Fin r, (0 : R) i * t i) = 0 then (1 : ℤ) else -1) * (roots 0 : ℤ) = (q : ℤ) := by
      have hzero : ∀ i : Fin r, (0 : R) i = 0 := fun _ => rfl
      simp [hzero, hroots0]
    rw [h0term]
    have hrest_ge :
        - ((2 : ℤ) ^ (r - 1) * ((k - 1 : ℕ) : ℤ)) ≤
        ∑ mask ∈ Finset.univ.erase (0 : R),
          (if (∑ i : Fin r, mask i * t i) = 0 then (1 : ℤ) else -1) * (roots mask : ℤ) := by
      have hterm_ge : ∀ mask ∈ Finset.univ.erase (0 : R),
          (if mask ∈ Neg then - ((k - 1 : ℕ) : ℤ) else 0) ≤
          (if (∑ i : Fin r, mask i * t i) = 0 then (1 : ℤ) else -1) * (roots mask : ℤ) := by
        intro mask hmask
        have hnz : mask ≠ 0 := (Finset.mem_erase.mp hmask).1
        by_cases hmN : mask ∈ Neg
        · have hne : (∑ i : Fin r, mask i * t i) ≠ 0 := (Finset.mem_filter.mp hmN).2
          rw [if_pos hmN, if_neg hne]
          have hle : (roots mask : ℤ) ≤ ((k - 1 : ℕ) : ℤ) := by exact_mod_cast hroots_nz mask hnz
          linarith
        · have heq0 : (∑ i : Fin r, mask i * t i) = 0 := by
            by_contra hne
            exact hmN (Finset.mem_filter.mpr ⟨Finset.mem_univ mask, hne⟩)
          rw [if_neg hmN, if_pos heq0, one_mul]
          exact Nat.cast_nonneg _
      have hsub : Neg ⊆ Finset.univ.erase (0 : R) := by
        intro mask hm
        refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ mask⟩
        intro h0; subst h0
        have hne := (Finset.mem_filter.mp hm).2
        have hzero : ∀ i : Fin r, (0 : R) i = 0 := fun _ => rfl
        simp [hzero] at hne
      have hsum_neg : (∑ mask ∈ Finset.univ.erase (0 : R), if mask ∈ Neg then - ((k - 1 : ℕ) : ℤ) else 0) =
          - ((Neg.card : ℤ) * ((k - 1 : ℕ) : ℤ)) := by
        rw [← Finset.sum_filter]
        have hflt : (Finset.univ.erase (0 : R)).filter (fun mask => mask ∈ Neg) = Neg := by
          ext mask
          simp only [Finset.mem_filter]
          constructor
          · exact fun h => h.2
          · intro h; exact ⟨hsub h, h⟩
        rw [hflt, Finset.sum_const, nsmul_eq_mul]; ring
      have hle_neg : - ((2 : ℤ) ^ (r - 1) * ((k - 1 : ℕ) : ℤ)) ≤ - ((Neg.card : ℤ) * ((k - 1 : ℕ) : ℤ)) := by
        have hc : (Neg.card : ℤ) ≤ (2 : ℤ) ^ (r - 1) := by exact_mod_cast hNeg_card
        have hk0 : (0 : ℤ) ≤ ((k - 1 : ℕ) : ℤ) := Nat.cast_nonneg _
        nlinarith
      exact le_trans hle_neg (by rw [← hsum_neg]; exact Finset.sum_le_sum hterm_ge)
    linarith
  have hq_nn : (0 : ℤ) ≤ (q : ℤ) := Nat.cast_nonneg _
  have hmul_ge : (q : ℤ) * ((q : ℤ) - (2 : ℤ) ^ (r - 1) * ((k - 1 : ℕ) : ℤ)) ≤
      (2 : ℤ) ^ r * (hits : ℤ) := by
    rw [hpart1]
    exact mul_le_mul_of_nonneg_left hsum_ge hq_nn
  have hz_ineq : (q : ℤ) ^ 2 ≤ (2 : ℤ) ^ r * (hits : ℤ) + (2 : ℤ) ^ (r - 1) * (q : ℤ) * ((k - 1 : ℕ) : ℤ) := by
    linarith
  exact_mod_cast hz_ineq
