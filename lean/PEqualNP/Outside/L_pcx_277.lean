import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_277_aux

private lemma exists_partition {α : Type} [DecidableEq α] {m : ℕ}
    (U : Finset α) (g : α → ℕ) (S : Finset (Fin m)) (hsum : (∑ H ∈ U, g H) = S.card) :
    ∃ B : α → Finset (Fin m),
      (∀ H ∈ U, (B H).card = g H) ∧
      (∀ H ∈ U, B H ⊆ S) ∧
      (∀ H1 ∈ U, ∀ H2 ∈ U, H1 ≠ H2 → Disjoint (B H1) (B H2)) ∧
      U.biUnion B = S := by
  induction U using Finset.induction generalizing S with
  | empty =>
    simp only [Finset.sum_empty] at hsum
    have hS : S = ∅ := Finset.card_eq_zero.mp hsum.symm
    refine ⟨fun _ => ∅, ?_, ?_, ?_, ?_⟩ <;> simp [hS]
  | insert H U' hHnot ih =>
    rw [Finset.sum_insert hHnot] at hsum
    have hle : g H ≤ S.card := by omega
    obtain ⟨BH, hBH_sub, hBH_card⟩ := Finset.exists_subset_card_eq hle
    have hrest_card : (∑ H' ∈ U', g H') = (S \ BH).card := by
      rw [Finset.card_sdiff_of_subset hBH_sub, hBH_card]
      omega
    obtain ⟨B', hcard', hsub', hdisj', hunion'⟩ := ih (S \ BH) hrest_card
    refine ⟨fun x => if x = H then BH else B' x, ?_, ?_, ?_, ?_⟩
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx'
      · simp [hBH_card]
      · have hne : x ≠ H := fun h => hHnot (h ▸ hx')
        simp [hne, hcard' x hx']
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx'
      · simp [hBH_sub]
      · have hne : x ≠ H := fun h => hHnot (h ▸ hx')
        simp only [hne, ↓reduceIte]
        exact Finset.Subset.trans (hsub' x hx') Finset.sdiff_subset
    · intro x1 hx1 x2 hx2 hne
      rcases Finset.mem_insert.mp hx1 with rfl | hx1' <;>
      rcases Finset.mem_insert.mp hx2 with rfl | hx2'
      · exact absurd rfl hne
      · have hne2 : x2 ≠ x1 := hne.symm
        simp only [↓reduceIte, hne2]
        exact Disjoint.mono_right (hsub' x2 hx2') Finset.disjoint_sdiff
      · simp only [hne, ↓reduceIte]
        exact Disjoint.mono_left (hsub' x1 hx1') Finset.sdiff_disjoint
      · have h1 : x1 ≠ H := fun h => hHnot (h ▸ hx1')
        have h2 : x2 ≠ H := fun h => hHnot (h ▸ hx2')
        simp only [h1, h2, ↓reduceIte]
        exact hdisj' x1 hx1' x2 hx2' hne
    · rw [Finset.biUnion_insert]
      simp only [↓reduceIte]
      have hbi : U'.biUnion (fun x => if x = H then BH else B' x) = U'.biUnion B' := by
        refine Finset.biUnion_congr rfl fun x hx => ?_
        have hne : x ≠ H := fun h => hHnot (h ▸ hx)
        simp [hne]
      rw [hbi, hunion', Finset.union_sdiff_of_subset hBH_sub]

private lemma exists_min_unsat {hiddenCount : ℕ}
    (S : Finset (PEqualNP.ProofComplexity.Clause (Fin hiddenCount)))
    (hunsat : ¬ ∃ z : Fin hiddenCount → Bool, PEqualNP.ProofComplexity.Satisfies z (↑S : Set _)) :
    ∃ U : Finset (PEqualNP.ProofComplexity.Clause (Fin hiddenCount)),
      U ⊆ S ∧
      (¬ ∃ z : Fin hiddenCount → Bool, PEqualNP.ProofComplexity.Satisfies z (↑U : Set _)) ∧
      (∀ H ∈ U, ∃ z : Fin hiddenCount → Bool, PEqualNP.ProofComplexity.Satisfies z (↑(U.erase H) : Set _)) := by
  induction hcard : S.card using Nat.strong_induction_on generalizing S with
  | ind n ih =>
    by_cases hmin : ∀ H ∈ S, ∃ z : Fin hiddenCount → Bool,
        PEqualNP.ProofComplexity.Satisfies z (↑(S.erase H) : Set _)
    · exact ⟨S, Finset.Subset.refl S, hunsat, hmin⟩
    · push_neg at hmin
      rcases hmin with ⟨H, hHS, hunsat'⟩
      have hlt : (S.erase H).card < n := by
        rw [← hcard]
        exact Finset.card_erase_lt_of_mem hHS
      obtain ⟨U, hUsub, hUunsat, hUmin⟩ := ih (S.erase H).card hlt (S.erase H) (fun ⟨z, hz⟩ => hunsat' z hz) rfl
      exact ⟨U, Finset.Subset.trans hUsub (Finset.erase_subset H S), hUunsat, hUmin⟩

private def hidPart {n m hiddenCount : ℕ}
    (C : PEqualNP.ProofComplexity.Clause (Sum (Fin m × Fin n) (Fin hiddenCount))) :
    PEqualNP.ProofComplexity.Clause (Fin hiddenCount) :=
  C.biUnion (fun lit => match lit with
    | (Sum.inr h, b) => {(h, b)}
    | (Sum.inl _, _) => ∅)

private lemma mem_hidPart {n m hiddenCount : ℕ}
    (C : PEqualNP.ProofComplexity.Clause (Sum (Fin m × Fin n) (Fin hiddenCount)))
    (l : PEqualNP.ProofComplexity.Literal (Fin hiddenCount)) :
    l ∈ hidPart C ↔ (Sum.inr l.1, l.2) ∈ C := by
  unfold hidPart
  simp only [Finset.mem_biUnion]
  constructor
  · rintro ⟨⟨v, b⟩, hvC, hl⟩
    cases v with
    | inl r => simp at hl
    | inr h =>
      simp only [Finset.mem_singleton] at hl
      cases l with
      | mk lh lb =>
        cases hl
        exact hvC
  · intro hC
    exact ⟨(Sum.inr l.1, l.2), hC, by simp⟩

private def posRawPart {n m hiddenCount : ℕ}
    (C : PEqualNP.ProofComplexity.Clause (Sum (Fin m × Fin n) (Fin hiddenCount))) :
    Finset (Fin m × Fin n) :=
  C.biUnion (fun lit => match lit with
    | (Sum.inl r, true) => {r}
    | _ => ∅)

private lemma mem_posRawPart {n m hiddenCount : ℕ}
    (C : PEqualNP.ProofComplexity.Clause (Sum (Fin m × Fin n) (Fin hiddenCount)))
    (r : Fin m × Fin n) :
    r ∈ posRawPart C ↔ (Sum.inl r, true) ∈ C := by
  unfold posRawPart
  simp only [Finset.mem_biUnion]
  constructor
  · rintro ⟨⟨v, b⟩, hvC, hr⟩
    cases v with
    | inl r' =>
      cases b with
      | false => simp at hr
      | true =>
        simp only [Finset.mem_singleton] at hr
        subst hr
        exact hvC
    | inr h => simp at hr
  · intro hC
    exact ⟨(Sum.inl r, true), hC, by simp⟩

private lemma card_hidPart_add_posRawPart_le {n m hiddenCount : ℕ}
    (C : PEqualNP.ProofComplexity.Clause (Sum (Fin m × Fin n) (Fin hiddenCount))) :
    (hidPart C).card + (posRawPart C).card ≤ C.card := by
  let A : PEqualNP.ProofComplexity.Clause (Sum (Fin m × Fin n) (Fin hiddenCount)) :=
    (hidPart C).image (fun l => (Sum.inr l.1, l.2))
  let B : PEqualNP.ProofComplexity.Clause (Sum (Fin m × Fin n) (Fin hiddenCount)) :=
    (posRawPart C).image (fun r => (Sum.inl r, true))
  have hAcard : A.card = (hidPart C).card := by
    apply Finset.card_image_of_injective
    intro a b hab
    cases a; cases b; cases hab; rfl
  have hBcard : B.card = (posRawPart C).card := by
    apply Finset.card_image_of_injective
    intro a b hab
    cases hab; rfl
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro lit hA hB
    rcases Finset.mem_image.mp hA with ⟨l, _, rfl⟩
    rcases Finset.mem_image.mp hB with ⟨r, _, hEq⟩
    cases hEq
  have hsub : A ∪ B ⊆ C := by
    intro lit hlit
    rcases Finset.mem_union.mp hlit with hA | hB
    · rcases Finset.mem_image.mp hA with ⟨l, hl, rfl⟩
      exact (mem_hidPart C l).mp hl
    · rcases Finset.mem_image.mp hB with ⟨r, hr, rfl⟩
      exact (mem_posRawPart C r).mp hr
  calc
    (hidPart C).card + (posRawPart C).card = A.card + B.card := by rw [hAcard, hBcard]
    _ = (A ∪ B).card := (Finset.card_union_of_disjoint hdisj).symm
    _ ≤ C.card := Finset.card_le_card hsub

private def xOf {n m : ℕ} (f : Fin m → Fin n) : (Fin m × Fin n) → Bool :=
  fun p => decide (p.2 ≠ f p.1)

private def rawSat {n m hiddenCount : ℕ} (x : (Fin m × Fin n) → Bool)
    (C : PEqualNP.ProofComplexity.Clause (Sum (Fin m × Fin n) (Fin hiddenCount))) : Prop :=
  ∃ r : Fin m × Fin n, ∃ b : Bool, (Sum.inl r, b) ∈ C ∧ x r = b

private def survives {n m hiddenCount : ℕ} (f : Fin m → Fin n)
    (C : PEqualNP.ProofComplexity.Clause (Sum (Fin m × Fin n) (Fin hiddenCount))) : Prop :=
  ¬ rawSat (xOf f) C

private lemma surv_card_mul_pow_le {n m hiddenCount : ℕ}
    (C : PEqualNP.ProofComplexity.Clause (Sum (Fin m × Fin n) (Fin hiddenCount))) :
    let Pblocks : Finset (Fin m) := (posRawPart C).image Prod.fst
    let Surv : Finset (Fin m → Fin n) := by
      classical
      exact Finset.univ.filter (fun f => survives f C)
    Surv.card * n ^ Pblocks.card ≤ n ^ m := by
  classical
  intro Pblocks Surv
  have hdet : ∀ j ∈ Pblocks, ∃ i : Fin n, ∀ f ∈ Surv, f j = i := by
    intro j hj
    rcases Finset.mem_image.mp hj with ⟨⟨j', i⟩, hmem, hjEq⟩
    dsimp only at hjEq
    subst hjEq
    refine ⟨i, fun f hf => ?_⟩
    have hsurv : survives f C := (Finset.mem_filter.mp hf).2
    have hlit : (Sum.inl (j', i), true) ∈ C := (mem_posRawPart C (j', i)).mp hmem
    by_contra hne
    apply hsurv
    refine ⟨(j', i), true, hlit, ?_⟩
    dsimp only [xOf]
    rw [decide_eq_true_eq]
    exact fun h => hne h.symm
  let Rem : Finset (Fin m) := Finset.univ \ Pblocks
  let res : Surv → (Rem → Fin n) := fun f j => f.1 j.1
  have hinj : Function.Injective res := by
    intro f1 f2 hEq
    apply Subtype.ext
    funext j
    by_cases hj : j ∈ Pblocks
    · obtain ⟨i, hi⟩ := hdet j hj
      rw [hi f1.1 f1.2, hi f2.1 f2.2]
    · have hjRem : j ∈ Rem := Finset.mem_sdiff.mpr ⟨Finset.mem_univ j, hj⟩
      exact congrFun hEq ⟨j, hjRem⟩
  have hcard_le : Surv.card ≤ n ^ Rem.card := by
    calc
      Surv.card = Fintype.card Surv := (Fintype.card_coe Surv).symm
      _ ≤ Fintype.card (Rem → Fin n) := Fintype.card_le_of_injective res hinj
      _ = n ^ Rem.card := by rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe]
  have hadd : Rem.card + Pblocks.card = m := by
    have h1 : Rem.card + Pblocks.card = (Rem ∪ Pblocks).card :=
      (Finset.card_union_of_disjoint Finset.sdiff_disjoint).symm
    have h2 : Rem ∪ Pblocks = Finset.univ := Finset.sdiff_union_of_subset (Finset.subset_univ Pblocks)
    rw [h1, h2, Finset.card_univ, Fintype.card_fin]
  calc
    Surv.card * n ^ Pblocks.card ≤ n ^ Rem.card * n ^ Pblocks.card := Nat.mul_le_mul_right _ hcard_le
    _ = n ^ (Rem.card + Pblocks.card) := (pow_add n Rem.card Pblocks.card).symm
    _ = n ^ m := by rw [hadd]

private lemma exists_le_of_sum_le_mul {α : Type} [Fintype α] [Nonempty α]
    (val : α → ℕ) (K : ℕ) (hsum : (∑ a : α, val a) ≤ Fintype.card α * K) :
    ∃ a : α, val a ≤ K := by
  by_contra hall
  push_neg at hall
  have hgt : Fintype.card α * K < ∑ a : α, val a := by
    have h1 : ∑ _a : α, K < ∑ a : α, val a :=
      Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun a _ => hall a)
    simpa [Finset.sum_const, nsmul_eq_mul] using h1
  omega

end PEqualNP.Outside.L_pcx_277_aux

theorem PEqualNP.Outside.L_pcx_277 : (∀ (n m hiddenCount W K : ℕ), 0 < n → 0 < m → ∀ price : ℕ → ℕ, (∀ lo hi, lo ≤ hi → price lo ≤ price hi) →
  let Raw := Fin m × Fin n
  let Cl := PEqualNP.ProofComplexity.Clause (Sum Raw (Fin hiddenCount))
  let Hidden := PEqualNP.ProofComplexity.Clause (Fin hiddenCount)
  let enc := fun F : Finset Cl => ∀ x : Raw → Bool,
    (∃ j : Fin m, ∀ i : Fin n, x (j,i) = true) ↔
      ∃ z : Fin hiddenCount → Bool, PEqualNP.ProofComplexity.Satisfies (Sum.elim x z) (↑F : Set _)
  let consistent := fun U : Finset Hidden =>
    ∃ z : Fin hiddenCount → Bool, PEqualNP.ProofComplexity.Satisfies z (↑U : Set _)
  (∃ F : Finset Cl, enc F ∧ (∀ C ∈ F, C.card ≤ W) ∧
    (∑ C ∈ F, price C.card) ≤ K) ↔
  ∃ (U : Finset Hidden) (g : Hidden → ℕ),
    ¬ consistent U ∧ (∀ H ∈ U, consistent (U.erase H)) ∧
    (∑ H ∈ U, g H) = m ∧ (∀ H ∈ U, H.card + g H ≤ W) ∧
    (∑ H ∈ U, n^(g H) * price (H.card + g H)) ≤ K) := by
  classical
  intro n m hiddenCount W K hn hm price hmono Raw Cl Hidden enc consistent
  constructor
  · rintro ⟨F, henc, hW, hK⟩
    have hSunsat : ∀ f : Fin m → Fin n,
        let Sf : Finset Hidden :=
          (F.filter (fun C => PEqualNP.Outside.L_pcx_277_aux.survives f C)).image
            PEqualNP.Outside.L_pcx_277_aux.hidPart
        ¬ consistent Sf := by
      intro f Sf hcons
      rcases hcons with ⟨z, hz⟩
      have hsatF : PEqualNP.ProofComplexity.Satisfies (Sum.elim (PEqualNP.Outside.L_pcx_277_aux.xOf f) z) (↑F : Set _) := by
        intro C hCF
        by_cases hsurv : PEqualNP.Outside.L_pcx_277_aux.survives f C
        · have hmem : PEqualNP.Outside.L_pcx_277_aux.hidPart C ∈ Sf :=
            Finset.mem_image.mpr ⟨C, Finset.mem_filter.mpr ⟨hCF, hsurv⟩, rfl⟩
          rcases hz (PEqualNP.Outside.L_pcx_277_aux.hidPart C) hmem with ⟨l, hlH, hzl⟩
          exact ⟨(Sum.inr l.1, l.2), (PEqualNP.Outside.L_pcx_277_aux.mem_hidPart C l).mp hlH, hzl⟩
        · unfold PEqualNP.Outside.L_pcx_277_aux.survives at hsurv
          push_neg at hsurv
          rcases hsurv with ⟨r, b, hlit, hxr⟩
          exact ⟨(Sum.inl r, b), hlit, hxr⟩
      have hpos : ∃ j : Fin m, ∀ i : Fin n, PEqualNP.Outside.L_pcx_277_aux.xOf f (j, i) = true :=
        (henc (PEqualNP.Outside.L_pcx_277_aux.xOf f)).mpr ⟨z, hsatF⟩
      rcases hpos with ⟨j, hj⟩
      have hfj := hj (f j)
      dsimp only [PEqualNP.Outside.L_pcx_277_aux.xOf] at hfj
      simp at hfj
    let pickU : (Fin m → Fin n) → Finset Hidden := fun f =>
      Classical.choose (PEqualNP.Outside.L_pcx_277_aux.exists_min_unsat _ (hSunsat f))
    have hpickU_spec : ∀ f,
        pickU f ⊆ (F.filter (fun C => PEqualNP.Outside.L_pcx_277_aux.survives f C)).image
          PEqualNP.Outside.L_pcx_277_aux.hidPart ∧
        ¬ consistent (pickU f) ∧
        (∀ H ∈ pickU f, consistent ((pickU f).erase H)) :=
      fun f => Classical.choose_spec (PEqualNP.Outside.L_pcx_277_aux.exists_min_unsat _ (hSunsat f))
    have hwit_ex : ∀ (f : Fin m → Fin n) (H : Hidden), H ∈ pickU f →
        ∃ C ∈ F, PEqualNP.Outside.L_pcx_277_aux.survives f C ∧
          PEqualNP.Outside.L_pcx_277_aux.hidPart C = H := by
      intro f H hH
      have hmem := (hpickU_spec f).1 hH
      rcases Finset.mem_image.mp hmem with ⟨C, hCf, hEq⟩
      rcases Finset.mem_filter.mp hCf with ⟨hCF, hsurv⟩
      exact ⟨C, hCF, hsurv, hEq⟩
    let wit : (Fin m → Fin n) → Hidden → Cl := fun f H =>
      if hH : H ∈ pickU f then Classical.choose (hwit_ex f H hH) else ∅
    have hwit_mem : ∀ f H, H ∈ pickU f → wit f H ∈ F := by
      intro f H hH; dsimp only [wit]; rw [dif_pos hH]; exact (Classical.choose_spec (hwit_ex f H hH)).1
    have hwit_surv : ∀ f H, H ∈ pickU f → PEqualNP.Outside.L_pcx_277_aux.survives f (wit f H) := by
      intro f H hH; dsimp only [wit]; rw [dif_pos hH]; exact (Classical.choose_spec (hwit_ex f H hH)).2.1
    have hwit_hid : ∀ f H, H ∈ pickU f → PEqualNP.Outside.L_pcx_277_aux.hidPart (wit f H) = H := by
      intro f H hH; dsimp only [wit]; rw [dif_pos hH]; exact (Classical.choose_spec (hwit_ex f H hH)).2.2
    have howner_ex : ∀ (f : Fin m → Fin n) (j : Fin m),
        ∃ H ∈ pickU f, (j, f j) ∈ PEqualNP.Outside.L_pcx_277_aux.posRawPart (wit f H) := by
      intro f j
      let x' : Raw → Bool := fun p => if p.1 = j then true else PEqualNP.Outside.L_pcx_277_aux.xOf f p
      have hx'_sat : ∃ z : Fin hiddenCount → Bool,
          PEqualNP.ProofComplexity.Satisfies (Sum.elim x' z) (↑F : Set _) := by
        apply (henc x').mp
        refine ⟨j, fun i => ?_⟩
        simp [x']
      rcases hx'_sat with ⟨z, hz⟩
      have hexH : ∃ H ∈ pickU f, ¬ PEqualNP.ProofComplexity.ClauseSat z H := by
        by_contra hall
        push_neg at hall
        exact (hpickU_spec f).2.1 ⟨z, hall⟩
      rcases hexH with ⟨H, hH, hnotH⟩
      refine ⟨H, hH, ?_⟩
      have hsatC := hz (wit f H) (hwit_mem f H hH)
      rcases hsatC with ⟨⟨v, b⟩, hlit, hval⟩
      cases v with
      | inr h =>
        exfalso
        apply hnotH
        refine ⟨(h, b), ?_, hval⟩
        rw [← hwit_hid f H hH]
        exact (PEqualNP.Outside.L_pcx_277_aux.mem_hidPart (wit f H) (h, b)).mpr hlit
      | inl r =>
        have hsurv := hwit_surv f H hH
        have hne_raw : PEqualNP.Outside.L_pcx_277_aux.xOf f r ≠ b := by
          intro hEq
          exact hsurv ⟨r, b, hlit, hEq⟩
        dsimp only [Sum.elim, x'] at hval
        by_cases hr1 : r.1 = j
        · simp only [hr1, ↓reduceIte] at hval
          have hb : b = true := hval.symm
          subst hb
          have hxf : PEqualNP.Outside.L_pcx_277_aux.xOf f r = false := by
            cases hxr : PEqualNP.Outside.L_pcx_277_aux.xOf f r
            · rfl
            · exact absurd hxr hne_raw
          dsimp only [PEqualNP.Outside.L_pcx_277_aux.xOf] at hxf
          have hr2 : r.2 = f r.1 := by
            by_contra hne2
            have : decide (r.2 ≠ f r.1) = true := decide_eq_true hne2
            rw [this] at hxf; cases hxf
          have hr_eq : r = (j, f j) := Prod.ext hr1 (by rw [hr2, hr1])
          rw [hr_eq] at hlit
          exact (PEqualNP.Outside.L_pcx_277_aux.mem_posRawPart (wit f H) (j, f j)).mpr hlit
        · simp only [hr1, ↓reduceIte] at hval
          exact absurd hval hne_raw
    let owner : (Fin m → Fin n) → Fin m → Hidden := fun f j =>
      Classical.choose (howner_ex f j)
    have howner_mem : ∀ f j, owner f j ∈ pickU f :=
      fun f j => (Classical.choose_spec (howner_ex f j)).1
    have howner_pos : ∀ f j,
        (j, f j) ∈ PEqualNP.Outside.L_pcx_277_aux.posRawPart (wit f (owner f j)) :=
      fun f j => (Classical.choose_spec (howner_ex f j)).2
    let gOf : (Fin m → Fin n) → Hidden → ℕ := fun f H =>
      (Finset.univ.filter (fun j : Fin m => owner f j = H)).card
    have hg_sum : ∀ f, (∑ H ∈ pickU f, gOf f H) = m := by
      intro f
      have hfib := Finset.sum_fiberwise_of_maps_to
        (s := (Finset.univ : Finset (Fin m))) (t := pickU f) (g := owner f)
        (fun j _ => howner_mem f j) (fun _ => (1 : ℕ))
      simpa [gOf] using hfib
    have hg_le_pos : ∀ f H, H ∈ pickU f →
        gOf f H ≤ (PEqualNP.Outside.L_pcx_277_aux.posRawPart (wit f H)).card := by
      intro f H _hH
      let J : Finset (Fin m) := Finset.univ.filter (fun j : Fin m => owner f j = H)
      have hsub : J.image (fun j => (j, f j)) ⊆ PEqualNP.Outside.L_pcx_277_aux.posRawPart (wit f H) := by
        intro r hr
        rcases Finset.mem_image.mp hr with ⟨j, hj, rfl⟩
        have ho : owner f j = H := (Finset.mem_filter.mp hj).2
        have hp := howner_pos f j
        rwa [ho] at hp
      have hinj : Function.Injective (fun j : Fin m => (j, f j)) :=
        fun j1 j2 h => congrArg Prod.fst h
      calc
        gOf f H = (J.image (fun j => (j, f j))).card := (Finset.card_image_of_injective J hinj).symm
        _ ≤ (PEqualNP.Outside.L_pcx_277_aux.posRawPart (wit f H)).card := Finset.card_le_card hsub
    have hg_le_pblk : ∀ f H, H ∈ pickU f →
        gOf f H ≤ ((PEqualNP.Outside.L_pcx_277_aux.posRawPart (wit f H)).image Prod.fst).card := by
      intro f H _hH
      let J : Finset (Fin m) := Finset.univ.filter (fun j : Fin m => owner f j = H)
      have hsub : J ⊆ (PEqualNP.Outside.L_pcx_277_aux.posRawPart (wit f H)).image Prod.fst := by
        intro j hj
        have ho : owner f j = H := (Finset.mem_filter.mp hj).2
        have hp := howner_pos f j
        rw [ho] at hp
        exact Finset.mem_image.mpr ⟨(j, f j), hp, rfl⟩
      exact Finset.card_le_card hsub
    have hcard_le_wit : ∀ f H, H ∈ pickU f → H.card + gOf f H ≤ (wit f H).card := by
      intro f H hH
      calc
        H.card + gOf f H = (PEqualNP.Outside.L_pcx_277_aux.hidPart (wit f H)).card + gOf f H := by
          rw [hwit_hid f H hH]
        _ ≤ (PEqualNP.Outside.L_pcx_277_aux.hidPart (wit f H)).card +
            (PEqualNP.Outside.L_pcx_277_aux.posRawPart (wit f H)).card :=
          Nat.add_le_add_left (hg_le_pos f H hH) _
        _ ≤ (wit f H).card := PEqualNP.Outside.L_pcx_277_aux.card_hidPart_add_posRawPart_le (wit f H)
    have havg : (∑ f : Fin m → Fin n, ∑ H ∈ pickU f, n ^ (gOf f H) * price (H.card + gOf f H)) ≤
        Fintype.card (Fin m → Fin n) * K := by
      have hstep1 : ∀ f : Fin m → Fin n,
          (∑ H ∈ pickU f, n ^ (gOf f H) * price (H.card + gOf f H)) ≤
          ∑ C ∈ F.filter (fun C => PEqualNP.Outside.L_pcx_277_aux.survives f C),
            n ^ ((PEqualNP.Outside.L_pcx_277_aux.posRawPart C).image Prod.fst).card * price C.card := by
        intro f
        have hterm : (∑ H ∈ pickU f, n ^ (gOf f H) * price (H.card + gOf f H)) ≤
            ∑ H ∈ pickU f,
              n ^ ((PEqualNP.Outside.L_pcx_277_aux.posRawPart (wit f H)).image Prod.fst).card *
                price (wit f H).card := by
          refine Finset.sum_le_sum fun H hH => ?_
          exact Nat.mul_le_mul
            (Nat.pow_le_pow_right hn (hg_le_pblk f H hH))
            (hmono _ _ (hcard_le_wit f H hH))
        have hinj : Set.InjOn (wit f) (↑(pickU f) : Set Hidden) := by
          intro H1 hH1 H2 hH2 hEq
          rw [← hwit_hid f H1 hH1, hEq, hwit_hid f H2 hH2]
        have hsub : (pickU f).image (wit f) ⊆ F.filter (fun C => PEqualNP.Outside.L_pcx_277_aux.survives f C) := by
          intro C hC
          rcases Finset.mem_image.mp hC with ⟨H, hH, rfl⟩
          exact Finset.mem_filter.mpr ⟨hwit_mem f H hH, hwit_surv f H hH⟩
        calc
          (∑ H ∈ pickU f, n ^ (gOf f H) * price (H.card + gOf f H))
              ≤ ∑ H ∈ pickU f,
                  n ^ ((PEqualNP.Outside.L_pcx_277_aux.posRawPart (wit f H)).image Prod.fst).card *
                    price (wit f H).card := hterm
          _ = ∑ C ∈ (pickU f).image (wit f),
                  n ^ ((PEqualNP.Outside.L_pcx_277_aux.posRawPart C).image Prod.fst).card *
                    price C.card :=
                (Finset.sum_image (f := fun C =>
                  n ^ ((PEqualNP.Outside.L_pcx_277_aux.posRawPart C).image Prod.fst).card *
                    price C.card) hinj).symm
          _ ≤ ∑ C ∈ F.filter (fun C => PEqualNP.Outside.L_pcx_277_aux.survives f C),
                  n ^ ((PEqualNP.Outside.L_pcx_277_aux.posRawPart C).image Prod.fst).card *
                    price C.card := Finset.sum_le_sum_of_subset hsub
      have hswap :
          (∑ f : Fin m → Fin n, ∑ C ∈ F.filter (fun C => PEqualNP.Outside.L_pcx_277_aux.survives f C),
            n ^ ((PEqualNP.Outside.L_pcx_277_aux.posRawPart C).image Prod.fst).card * price C.card) =
          ∑ C ∈ F,
            ((Finset.univ.filter (fun f : Fin m → Fin n => PEqualNP.Outside.L_pcx_277_aux.survives f C)).card *
              n ^ ((PEqualNP.Outside.L_pcx_277_aux.posRawPart C).image Prod.fst).card) * price C.card := by
        have h1 : ∀ f : Fin m → Fin n,
            (∑ C ∈ F.filter (fun C => PEqualNP.Outside.L_pcx_277_aux.survives f C),
              n ^ ((PEqualNP.Outside.L_pcx_277_aux.posRawPart C).image Prod.fst).card * price C.card) =
            ∑ C ∈ F, if PEqualNP.Outside.L_pcx_277_aux.survives f C then
              n ^ ((PEqualNP.Outside.L_pcx_277_aux.posRawPart C).image Prod.fst).card * price C.card else 0 :=
          fun f => Finset.sum_filter _ _
        rw [Finset.sum_congr rfl fun f _ => h1 f, Finset.sum_comm]
        refine Finset.sum_congr rfl fun C _ => ?_
        rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_assoc]
      have hcard_fn : Fintype.card (Fin m → Fin n) = n ^ m := by
        rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
      calc
        (∑ f : Fin m → Fin n, ∑ H ∈ pickU f, n ^ (gOf f H) * price (H.card + gOf f H))
            ≤ ∑ f : Fin m → Fin n, ∑ C ∈ F.filter (fun C => PEqualNP.Outside.L_pcx_277_aux.survives f C),
                n ^ ((PEqualNP.Outside.L_pcx_277_aux.posRawPart C).image Prod.fst).card * price C.card :=
              Finset.sum_le_sum fun f _ => hstep1 f
        _ = ∑ C ∈ F,
              ((Finset.univ.filter (fun f : Fin m → Fin n => PEqualNP.Outside.L_pcx_277_aux.survives f C)).card *
                n ^ ((PEqualNP.Outside.L_pcx_277_aux.posRawPart C).image Prod.fst).card) * price C.card := hswap
        _ ≤ ∑ C ∈ F, n ^ m * price C.card := by
              refine Finset.sum_le_sum fun C _ => ?_
              exact Nat.mul_le_mul_right _ (PEqualNP.Outside.L_pcx_277_aux.surv_card_mul_pow_le C)
        _ = n ^ m * (∑ C ∈ F, price C.card) := (Finset.mul_sum _ _ _).symm
        _ ≤ n ^ m * K := Nat.mul_le_mul_left _ hK
        _ = Fintype.card (Fin m → Fin n) * K := by rw [hcard_fn]
    have hnonemp : Nonempty (Fin m → Fin n) := ⟨fun _ => ⟨0, hn⟩⟩
    obtain ⟨f0, hf0⟩ := PEqualNP.Outside.L_pcx_277_aux.exists_le_of_sum_le_mul
      (fun f => ∑ H ∈ pickU f, n ^ (gOf f H) * price (H.card + gOf f H)) K havg
    refine ⟨pickU f0, gOf f0, (hpickU_spec f0).2.1, (hpickU_spec f0).2.2, hg_sum f0, ?_, hf0⟩
    intro H hH
    exact le_trans (hcard_le_wit f0 H hH) (hW (wit f0 H) (hwit_mem f0 H hH))
  · rintro ⟨U, g, hunsat, hmin, hsum_g, hW, hK⟩
    have hsum_univ : (∑ H ∈ U, g H) = (Finset.univ : Finset (Fin m)).card := by
      rw [hsum_g, Finset.card_univ, Fintype.card_fin]
    obtain ⟨B, hBcard, _, _, hBunion⟩ :=
      PEqualNP.Outside.L_pcx_277_aux.exists_partition U g (Finset.univ : Finset (Fin m)) hsum_univ
    let expClause : (H : Hidden) → (B H → Fin n) → Cl := fun H t =>
      H.image (fun l : Fin hiddenCount × Bool => ((Sum.inr l.1 : Sum Raw (Fin hiddenCount)), l.2)) ∪
        (B H).attach.image (fun j => ((Sum.inl (j.1, t j) : Sum Raw (Fin hiddenCount)), true))
    have hexp_card : ∀ H ∈ U, ∀ t : B H → Fin n, (expClause H t).card = H.card + g H := by
      intro H hH t
      dsimp only [expClause]
      have hdisj : Disjoint
          (H.image (fun l : Fin hiddenCount × Bool => ((Sum.inr l.1 : Sum Raw (Fin hiddenCount)), l.2)))
          ((B H).attach.image (fun j => ((Sum.inl (j.1, t j) : Sum Raw (Fin hiddenCount)), true))) := by
        rw [Finset.disjoint_left]
        intro lit h1 h2
        rcases Finset.mem_image.mp h1 with ⟨l, _, rfl⟩
        rcases Finset.mem_image.mp h2 with ⟨j, _, hEq⟩
        cases hEq
      rw [Finset.card_union_of_disjoint hdisj]
      have hc1 : (H.image (fun l : Fin hiddenCount × Bool =>
          ((Sum.inr l.1 : Sum Raw (Fin hiddenCount)), l.2))).card = H.card := by
        apply Finset.card_image_of_injective
        intro a b hab; cases a; cases b; cases hab; rfl
      have hc2 : ((B H).attach.image (fun j =>
          ((Sum.inl (j.1, t j) : Sum Raw (Fin hiddenCount)), true))).card = g H := by
        rw [Finset.card_image_of_injective]
        · rw [Finset.card_attach, hBcard H hH]
        · intro j1 j2 hj
          simp only [Prod.mk.injEq, Sum.inl.injEq] at hj
          exact Subtype.ext (congrArg Prod.fst hj.1)
      rw [hc1, hc2]
    let blockCl : Hidden → Finset Cl := fun H =>
      Finset.univ.image (fun t : B H → Fin n => expClause H t)
    let F : Finset Cl := U.biUnion blockCl
    refine ⟨F, ?_, ?_, ?_⟩
    · intro x
      constructor
      · rintro ⟨j0, hj0⟩
        have hj0_mem : j0 ∈ U.biUnion B := by rw [hBunion]; exact Finset.mem_univ j0
        rcases Finset.mem_biUnion.mp hj0_mem with ⟨H0, hH0, hj0B⟩
        obtain ⟨z, hz⟩ := hmin H0 hH0
        refine ⟨z, ?_⟩
        intro C hCF
        rcases Finset.mem_biUnion.mp hCF with ⟨H, hH, hCB⟩
        rcases Finset.mem_image.mp hCB with ⟨t, _, rfl⟩
        by_cases hEq : H = H0
        · subst hEq
          refine ⟨(Sum.inl (j0, t ⟨j0, hj0B⟩), true), ?_, hj0 (t ⟨j0, hj0B⟩)⟩
          apply Finset.mem_union_right
          exact Finset.mem_image.mpr ⟨⟨j0, hj0B⟩, Finset.mem_attach _ _, rfl⟩
        · have hmemE : H ∈ U.erase H0 := Finset.mem_erase.mpr ⟨hEq, hH⟩
          rcases hz H hmemE with ⟨l, hlH, hzl⟩
          refine ⟨(Sum.inr l.1, l.2), ?_, hzl⟩
          apply Finset.mem_union_left
          exact Finset.mem_image.mpr ⟨l, hlH, rfl⟩
      · rintro ⟨z, hz⟩
        by_contra hall
        push_neg at hall
        have hexF : ∀ j : Fin m, ∃ i : Fin n, x (j, i) = false := by
          intro j
          rcases hall j with ⟨i, hi⟩
          refine ⟨i, ?_⟩
          cases hxi : x (j, i)
          · rfl
          · exact absurd hxi hi
        let f : Fin m → Fin n := fun j => Classical.choose (hexF j)
        have hf : ∀ j, x (j, f j) = false := fun j => Classical.choose_spec (hexF j)
        apply hunsat
        refine ⟨z, fun H hH => ?_⟩
        let t : B H → Fin n := fun j => f j.1
        have hCF : expClause H t ∈ F :=
          Finset.mem_biUnion.mpr ⟨H, hH, Finset.mem_image.mpr ⟨t, Finset.mem_univ t, rfl⟩⟩
        rcases hz (expClause H t) hCF with ⟨lit, hlit, hval⟩
        rcases Finset.mem_union.mp hlit with h1 | h2
        · rcases Finset.mem_image.mp h1 with ⟨l, hlH, rfl⟩
          exact ⟨l, hlH, hval⟩
        · rcases Finset.mem_image.mp h2 with ⟨j, _, rfl⟩
          dsimp only [Sum.elim, t] at hval
          rw [hf j.1] at hval
          cases hval
    · intro C hCF
      rcases Finset.mem_biUnion.mp hCF with ⟨H, hH, hCB⟩
      rcases Finset.mem_image.mp hCB with ⟨t, _, rfl⟩
      rw [hexp_card H hH t]
      exact hW H hH
    · have hbi_le : ∀ T : Finset Hidden,
          (∑ C ∈ T.biUnion blockCl, price C.card) ≤ ∑ H ∈ T, ∑ C ∈ blockCl H, price C.card := by
        intro T
        induction T using Finset.induction with
        | empty => simp
        | insert H T' hnot ih =>
          rw [Finset.biUnion_insert, Finset.sum_insert hnot]
          have hun : (∑ C ∈ blockCl H ∪ T'.biUnion blockCl, price C.card) ≤
              (∑ C ∈ blockCl H, price C.card) + (∑ C ∈ T'.biUnion blockCl, price C.card) := by
            have := Finset.sum_union_inter (s₁ := blockCl H) (s₂ := T'.biUnion blockCl) (f := fun C => price C.card)
            omega
          omega
      calc
        (∑ C ∈ F, price C.card) ≤ ∑ H ∈ U, ∑ C ∈ blockCl H, price C.card := hbi_le U
        _ ≤ ∑ H ∈ U, n ^ g H * price (H.card + g H) := by
          refine Finset.sum_le_sum fun H hH => ?_
          have hconst : ∀ C ∈ blockCl H, price C.card = price (H.card + g H) := by
            intro C hCB
            rcases Finset.mem_image.mp hCB with ⟨t, _, rfl⟩
            rw [hexp_card H hH t]
          rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul]
          have hbc : (blockCl H).card ≤ n ^ g H := by
            calc
              (blockCl H).card ≤ (Finset.univ : Finset (B H → Fin n)).card := Finset.card_image_le
              _ = n ^ g H := by
                rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_coe, hBcard H hH]
          exact Nat.mul_le_mul_right _ hbc
        _ ≤ K := hK
