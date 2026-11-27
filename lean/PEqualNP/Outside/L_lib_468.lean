import PEqualNP.Defs

theorem PEqualNP.Outside.L_lib_468 : ∀ (n k : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
  let E : Finset (Fin n × Fin n) := Finset.univ.filter (fun p => p.1 < p.2 ∧ G.Adj p.1 p.2)
  let star : Fin n → Finset (Fin n × Fin n) := fun v =>
    E.filter (fun p => p.1 = v ∨ p.2 = v)
  (∃ T : Finset (Fin n), T.card ≤ k ∧ G.IsVertexCover (↑T)) ↔
    ∃ F : Finset (Finset (Fin n × Fin n)), F ⊆ Finset.univ.image star ∧
      F.card ≤ k ∧ ∀ e ∈ E, ∃ A ∈ F, e ∈ A := by
  intro n k G _ E star
  constructor
  · rintro ⟨T, hTcard, hTcov⟩
    refine ⟨T.image star, ?_, le_trans Finset.card_image_le hTcard, ?_⟩
    · intro A hA
      rcases Finset.mem_image.mp hA with ⟨v, _, rfl⟩
      exact Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩
    · intro e he
      have hadj : G.Adj e.1 e.2 := (Finset.mem_filter.mp he).2.2
      have hcov := hTcov hadj
      rcases hcov with h1 | h2
      · refine ⟨star e.1, Finset.mem_image.mpr ⟨e.1, h1, rfl⟩, ?_⟩
        exact Finset.mem_filter.mpr ⟨he, Or.inl rfl⟩
      · refine ⟨star e.2, Finset.mem_image.mpr ⟨e.2, h2, rfl⟩, ?_⟩
        exact Finset.mem_filter.mpr ⟨he, Or.inr rfl⟩
  · rintro ⟨F, hFsub, hFcard, hFcov⟩
    classical
    have hex : ∀ A : {A // A ∈ F}, ∃ v : Fin n, star v = A.val := by
      intro A
      rcases Finset.mem_image.mp (hFsub A.property) with ⟨v, _, hv⟩
      exact ⟨v, hv⟩
    let pick : {A // A ∈ F} → Fin n := fun A => Classical.choose (hex A)
    have hpick : ∀ A : {A // A ∈ F}, star (pick A) = A.val :=
      fun A => Classical.choose_spec (hex A)
    let T : Finset (Fin n) := F.attach.image pick
    refine ⟨T, ?_, ?_⟩
    · calc T.card ≤ F.attach.card := Finset.card_image_le
        _ = F.card := Finset.card_attach
        _ ≤ k := hFcard
    · intro u v huv
      rcases lt_or_gt_of_ne (G.ne_of_adj huv) with hlt | hgt
      · have he : (u, v) ∈ E := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt, huv⟩
        rcases hFcov (u, v) he with ⟨A, hAF, heA⟩
        have heS : (u, v) ∈ star (pick ⟨A, hAF⟩) := by rwa [hpick ⟨A, hAF⟩]
        have hmemT : pick ⟨A, hAF⟩ ∈ T :=
          Finset.mem_image.mpr ⟨⟨A, hAF⟩, Finset.mem_attach F ⟨A, hAF⟩, rfl⟩
        rcases (Finset.mem_filter.mp heS).2 with hu | hv
        · dsimp only at hu; left; exact Finset.mem_coe.mpr (hu ▸ hmemT)
        · dsimp only at hv; right; exact Finset.mem_coe.mpr (hv ▸ hmemT)
      · have he : (v, u) ∈ E := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgt, huv.symm⟩
        rcases hFcov (v, u) he with ⟨A, hAF, heA⟩
        have heS : (v, u) ∈ star (pick ⟨A, hAF⟩) := by rwa [hpick ⟨A, hAF⟩]
        have hmemT : pick ⟨A, hAF⟩ ∈ T :=
          Finset.mem_image.mpr ⟨⟨A, hAF⟩, Finset.mem_attach F ⟨A, hAF⟩, rfl⟩
        rcases (Finset.mem_filter.mp heS).2 with hv | hu
        · dsimp only at hv; right; exact Finset.mem_coe.mpr (hv ▸ hmemT)
        · dsimp only at hu; left; exact Finset.mem_coe.mpr (hu ▸ hmemT)
