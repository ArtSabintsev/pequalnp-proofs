import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_436_aux

private theorem sum_superset_alt {n : ℕ} (T : Finset (Fin n)) :
    ∑ S : Finset (Fin n), (if T ⊆ S then (-1 : ℤ) ^ (n - S.card) else 0) =
      if T = Finset.univ then 1 else 0 := by
  classical
  by_cases hT : T = Finset.univ
  · subst hT
    rw [if_pos rfl, ← Finset.add_sum_erase _ _ (Finset.mem_univ (Finset.univ : Finset (Fin n)))]
    have hself : (if (Finset.univ : Finset (Fin n)) ⊆ Finset.univ then
        (-1 : ℤ) ^ (n - (Finset.univ : Finset (Fin n)).card) else 0) = 1 := by
      simp
    have hrest : ∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).erase Finset.univ,
        (if (Finset.univ : Finset (Fin n)) ⊆ S then (-1 : ℤ) ^ (n - S.card) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro S hS
      have hne : S ≠ Finset.univ := Finset.ne_of_mem_erase hS
      have hnot : ¬ ((Finset.univ : Finset (Fin n)) ⊆ S) := fun hsub =>
        hne (Finset.eq_univ_of_forall fun x => hsub (Finset.mem_univ x))
      exact if_neg hnot
    rw [hself, hrest, add_zero]
  · rw [if_neg hT]
    have hex : ∃ c : Fin n, c ∉ T := by
      by_contra hall
      push_neg at hall
      exact hT (Finset.eq_univ_of_forall hall)
    obtain ⟨c, hc⟩ := hex
    let A : Finset (Finset (Fin n)) := Finset.univ.filter (fun S => c ∉ S)
    let B : Finset (Finset (Fin n)) := Finset.univ.filter (fun S => c ∈ S)
    have hdisj : Disjoint A B := by
      rw [Finset.disjoint_left]
      intro S hSA hSB
      exact (Finset.mem_filter.1 hSA).2 (Finset.mem_filter.1 hSB).2
    have hunion : (Finset.univ : Finset (Finset (Fin n))) = A ∪ B := by
      ext S
      simp only [A, B, Finset.mem_univ, Finset.mem_union, Finset.mem_filter, true_and, true_iff]
      tauto
    have hB_img : B = A.image (insert c) := by
      ext S
      simp only [A, B, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · intro hS
        exact ⟨S.erase c, Finset.notMem_erase c S, Finset.insert_erase hS⟩
      · rintro ⟨R, _, rfl⟩
        exact Finset.mem_insert_self c R
    have hinj : Set.InjOn (insert c) (A : Set (Finset (Fin n))) := by
      intro R1 hR1 R2 hR2 heq
      have h1 : c ∉ R1 := (Finset.mem_filter.1 hR1).2
      have h2 : c ∉ R2 := (Finset.mem_filter.1 hR2).2
      have := congrArg (fun X => X.erase c) heq
      simpa [Finset.erase_insert h1, Finset.erase_insert h2] using this
    rw [hunion, Finset.sum_union hdisj, hB_img, Finset.sum_image hinj, ← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro S hS
    have hcS : c ∉ S := (Finset.mem_filter.1 hS).2
    have hsub_iff : T ⊆ insert c S ↔ T ⊆ S := by
      constructor
      · intro h x hx
        rcases Finset.mem_insert.1 (h hx) with rfl | hxS
        · exact absurd hx hc
        · exact hxS
      · intro h x hx
        exact Finset.mem_insert_of_mem (h hx)
    have hcard_lt : S.card < n := by
      have hss : S ⊂ Finset.univ := Finset.ssubset_iff_subset_ne.2
        ⟨Finset.subset_univ S, fun h => hcS (h ▸ Finset.mem_univ c)⟩
      simpa using Finset.card_lt_card hss
    have hcard_ins : (insert c S).card = S.card + 1 := Finset.card_insert_of_notMem hcS
    by_cases hTS : T ⊆ S
    · rw [if_pos hTS, if_pos (hsub_iff.2 hTS), hcard_ins,
        show n - S.card = (n - (S.card + 1)) + 1 by omega, pow_succ]
      ring
    · rw [if_neg hTS, if_neg (fun h => hTS (hsub_iff.1 h)), add_zero]

private theorem prod_row_sum_eq {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (S : Finset (Fin n)) :
    (∏ i : Fin n, ∑ j ∈ S, M i j) =
      ∑ f : Fin n → Fin n, if Finset.univ.image f ⊆ S then ∏ i : Fin n, M i (f i) else 0 := by
  classical
  have hrow : ∀ i : Fin n, ∑ j ∈ S, M i j = ∑ j : Fin n, if j ∈ S then M i j else 0 := by
    intro i
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  simp_rw [hrow]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro f _
  have hiff : (∀ i : Fin n, f i ∈ S) ↔ Finset.univ.image f ⊆ S := by
    simp [Finset.subset_iff]
  by_cases h : ∀ i : Fin n, f i ∈ S
  · rw [if_pos (hiff.1 h)]
    apply Finset.prod_congr rfl
    intro i _
    exact if_pos (h i)
  · rw [if_neg (fun h' => h (hiff.2 h'))]
    obtain ⟨i₀, hi₀⟩ := not_forall.1 h
    exact Finset.prod_eq_zero (Finset.mem_univ i₀) (if_neg hi₀)

private theorem ryser_core (n : ℕ) (M : Matrix (Fin n) (Fin n) ℤ) :
    M.permanent = ∑ S : Finset (Fin n), (-1 : ℤ) ^ (n - S.card) *
      ∏ i : Fin n, ∑ j ∈ S, M i j := by
  classical
  have hrhs : ∑ S : Finset (Fin n), (-1 : ℤ) ^ (n - S.card) * (∏ i : Fin n, ∑ j ∈ S, M i j) =
      ∑ f : Fin n → Fin n,
        (if Finset.univ.image f = Finset.univ then 1 else 0) * (∏ i : Fin n, M i (f i)) := by
    have h1 : ∀ S : Finset (Fin n),
        (-1 : ℤ) ^ (n - S.card) * (∏ i : Fin n, ∑ j ∈ S, M i j) =
        ∑ f : Fin n → Fin n,
          (if Finset.univ.image f ⊆ S then (-1 : ℤ) ^ (n - S.card) else 0) *
            (∏ i : Fin n, M i (f i)) := by
      intro S
      rw [prod_row_sum_eq, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro f _
      split_ifs <;> ring
    simp_rw [h1]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro f _
    rw [← Finset.sum_mul, sum_superset_alt]
  rw [hrhs]
  have hfilt : ∑ f : Fin n → Fin n,
      (if Finset.univ.image f = Finset.univ then (1 : ℤ) else 0) * (∏ i : Fin n, M i (f i)) =
      ∑ f ∈ Finset.univ.filter (fun f : Fin n → Fin n => Function.Bijective f),
        ∏ i : Fin n, M i (f i) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro f _
    have hiff : Finset.univ.image f = Finset.univ ↔ Function.Bijective f := by
      have hbij_iff : Function.Bijective f ↔ Function.Surjective f :=
        ⟨fun h => h.2, fun h => ⟨Finite.injective_iff_surjective.2 h, h⟩⟩
      rw [hbij_iff]
      constructor
      · intro h y
        have hy : y ∈ Finset.univ.image f := by rw [h]; exact Finset.mem_univ y
        obtain ⟨x, _, hx⟩ := Finset.mem_image.1 hy
        exact ⟨x, hx⟩
      · intro h
        apply Finset.eq_univ_of_forall
        intro y
        obtain ⟨x, hx⟩ := h y
        exact Finset.mem_image.2 ⟨x, Finset.mem_univ x, hx⟩
    by_cases hf : Function.Bijective f
    · rw [if_pos (hiff.2 hf), if_pos hf, one_mul]
    · rw [if_neg (fun h => hf (hiff.1 h)), if_neg hf, zero_mul]
  rw [hfilt]
  have hperm_inv : M.permanent = ∑ σ : Equiv.Perm (Fin n), ∏ i : Fin n, M i (σ i) := by
    dsimp only [Matrix.permanent]
    exact Fintype.sum_equiv (Equiv.inv (Equiv.Perm (Fin n)))
      (fun σ : Equiv.Perm (Fin n) => ∏ i : Fin n, M (σ i) i)
      (fun σ : Equiv.Perm (Fin n) => ∏ i : Fin n, M i (σ i))
      (fun σ => Fintype.prod_equiv σ (fun i => M (σ i) i) (fun j => M j (σ⁻¹ j))
        (fun i => by simp))
  rw [hperm_inv]
  refine Finset.sum_nbij (fun σ : Equiv.Perm (Fin n) => (σ : Fin n → Fin n)) ?_ ?_ ?_ ?_
  · intro σ _
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, σ.bijective⟩
  · intro σ1 _ σ2 _ h
    exact DFunLike.coe_injective h
  · intro f hf
    have hbij : Function.Bijective f := (Finset.mem_filter.1 hf).2
    refine ⟨Equiv.ofBijective f hbij, Finset.mem_univ _, ?_⟩
    rfl
  · intro σ _
    rfl

end PEqualNP.Outside.L_lib_436_aux

theorem PEqualNP.Outside.L_lib_436 : (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℤ),
  M.permanent = ∑ S : Finset (Fin n), (-1 : ℤ)^(n-S.card) *
    ∏ i : Fin n, ∑ j ∈ S, M i j) := by
  exact PEqualNP.Outside.L_lib_436_aux.ryser_core
