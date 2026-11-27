import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_669_aux

abbrev W (n : ℕ) := Fin n → Bool
abbrev Lit (n : ℕ) := Fin n × Bool
abbrev F (n : ℕ) := Finset (Lit n × Lit n)

def satFn (n : ℕ) (A : F n) (word : W n) : Bool :=
  decide (∀ c ∈ A, word c.1.1 ≠ c.1.2 ∨ word c.2.1 ≠ c.2.2)

def massFn (n : ℕ) (A : F n) : ℕ :=
  (Finset.univ.filter (fun x : W n => satFn n A x = true)).card

def isTaut {n : ℕ} (cl : Lit n × Lit n) : Prop :=
  cl.1.1 = cl.2.1 ∧ cl.1.2 ≠ cl.2.2

instance {n : ℕ} (cl : Lit n × Lit n) : Decidable (isTaut cl) :=
  inferInstanceAs (Decidable (cl.1.1 = cl.2.1 ∧ cl.1.2 ≠ cl.2.2))

def stripTaut {n : ℕ} (A : F n) : F n :=
  A.filter (fun cl => ¬ isTaut cl)

theorem satFn_stripTaut {n : ℕ} (A : F n) (x : W n) :
    satFn n (stripTaut A) x = satFn n A x := by
  unfold satFn stripTaut
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, Finset.mem_filter]
  constructor
  · intro h cl hcl
    by_cases ht : isTaut cl
    · rcases ht with ⟨hv, hb⟩
      rw [← hv]
      cases hx : x cl.1.1 <;> cases h1 : cl.1.2 <;> cases h2 : cl.2.2 <;> simp_all
    · exact h cl ⟨hcl, ht⟩
  · intro h cl hcl
    exact h cl hcl.1

theorem massFn_stripTaut {n : ℕ} (A : F n) :
    massFn n (stripTaut A) = massFn n A := by
  unfold massFn
  congr 1
  ext x
  simp [satFn_stripTaut]

theorem massFn_mono {n : ℕ} {P A : F n} (hsub : P ⊆ A) :
    massFn n A ≤ massFn n P := by
  unfold massFn
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, satFn, decide_eq_true_eq] at hx ⊢
  intro cl hcl
  exact hx cl (hsub hcl)

def clVars {n : ℕ} (cl : Lit n × Lit n) : Finset (Fin n) :=
  {cl.1.1, cl.2.1}

def isPacking {n : ℕ} (P : F n) : Prop :=
  (∀ cl ∈ P, ¬ isTaut cl) ∧
  (∀ cl1 ∈ P, ∀ cl2 ∈ P, cl1 ≠ cl2 → Disjoint (clVars cl1) (clVars cl2))

theorem packing_step {n : ℕ} (cl : Lit n × Lit n) (Q : F n)
    (hnt : ¬ isTaut cl)
    (hdisj : ∀ cl' ∈ Q, Disjoint (clVars cl) (clVars cl')) :
    massFn n (insert cl Q) * 4 ≤ 3 * massFn n Q := by
  classical
  let U : Finset (Fin n) := clVars cl
  let goodU : Finset (U → Bool) :=
    Finset.univ.filter (fun y =>
      y ⟨cl.1.1, by simp [U, clVars]⟩ ≠ cl.1.2 ∨ y ⟨cl.2.1, by simp [U, clVars]⟩ ≠ cl.2.2)
  let Uc := {i : Fin n // i ∉ U}
  let goodUc : Finset (Uc → Bool) :=
    Finset.univ.filter (fun z =>
      ∀ cl' ∈ Q,
        (∃ h1 : cl'.1.1 ∉ U, z ⟨cl'.1.1, h1⟩ ≠ cl'.1.2) ∨
        (∃ h2 : cl'.2.1 ∉ U, z ⟨cl'.2.1, h2⟩ ≠ cl'.2.2))
  let splitEquiv : W n ≃ (U → Bool) × (Uc → Bool) :=
    { toFun := fun x => (fun i => x i.1, fun j => x j.1)
      invFun := fun p i => if h : i ∈ U then p.1 ⟨i, h⟩ else p.2 ⟨i, h⟩
      left_inv := fun x => by
        funext i
        by_cases h : i ∈ U <;> simp [h]
      right_inv := fun p => by
        ext i
        · simp [i.2]
        · simp [i.2] }
  have hQ_iff : ∀ x : W n, satFn n Q x = true ↔ (splitEquiv x).2 ∈ goodUc := by
    intro x
    simp only [satFn, decide_eq_true_eq, goodUc, Finset.mem_filter, Finset.mem_univ, true_and,
      splitEquiv, Equiv.coe_fn_mk]
    constructor
    · intro hx cl' hcl'
      have hd := hdisj cl' hcl'
      have h1 : cl'.1.1 ∉ U := Finset.disjoint_right.mp hd (by simp [clVars])
      have h2 : cl'.2.1 ∉ U := Finset.disjoint_right.mp hd (by simp [clVars])
      rcases hx cl' hcl' with h | h
      · exact Or.inl ⟨h1, h⟩
      · exact Or.inr ⟨h2, h⟩
    · intro hx cl' hcl'
      rcases hx cl' hcl' with ⟨_, h⟩ | ⟨_, h⟩
      · exact Or.inl h
      · exact Or.inr h
  have hcl_iff : ∀ x : W n,
      (x cl.1.1 ≠ cl.1.2 ∨ x cl.2.1 ≠ cl.2.2) ↔ (splitEquiv x).1 ∈ goodU := by
    intro x
    simp [goodU, splitEquiv]
  have hcard_ins : massFn n (insert cl Q) = goodU.card * goodUc.card := by
    unfold massFn
    rw [← Finset.card_product]
    refine Finset.card_bij (fun x _ => splitEquiv x) ?_ ?_ ?_
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      have hx' : (x cl.1.1 ≠ cl.1.2 ∨ x cl.2.1 ≠ cl.2.2) ∧ satFn n Q x = true := by
        simp only [satFn, decide_eq_true_eq, Finset.mem_insert] at hx ⊢
        exact ⟨hx cl (Or.inl rfl), fun cl' hcl' => hx cl' (Or.inr hcl')⟩
      exact Finset.mem_product.mpr ⟨(hcl_iff x).mp hx'.1, (hQ_iff x).mp hx'.2⟩
    · intro a _ b _ h
      exact splitEquiv.injective h
    · intro p hp
      rcases Finset.mem_product.mp hp with ⟨hp1, hp2⟩
      refine ⟨splitEquiv.symm p, ?_, splitEquiv.apply_symm_apply p⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have h1 : splitEquiv.symm p cl.1.1 ≠ cl.1.2 ∨ splitEquiv.symm p cl.2.1 ≠ cl.2.2 := by
        rw [hcl_iff, splitEquiv.apply_symm_apply]
        exact hp1
      have h2 : satFn n Q (splitEquiv.symm p) = true := by
        rw [hQ_iff, splitEquiv.apply_symm_apply]
        exact hp2
      simp only [satFn, decide_eq_true_eq, Finset.mem_insert] at h2 ⊢
      rintro cl' (rfl | hcl')
      · exact h1
      · exact h2 cl' hcl'
  have hcard_Q : massFn n Q = (Finset.univ : Finset (U → Bool)).card * goodUc.card := by
    unfold massFn
    rw [← Finset.card_product]
    refine Finset.card_bij (fun x _ => splitEquiv x) ?_ ?_ ?_
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      exact Finset.mem_product.mpr ⟨Finset.mem_univ _, (hQ_iff x).mp hx⟩
    · intro a _ b _ h
      exact splitEquiv.injective h
    · intro p hp
      rcases Finset.mem_product.mp hp with ⟨_, hp2⟩
      refine ⟨splitEquiv.symm p, ?_, splitEquiv.apply_symm_apply p⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hQ_iff, splitEquiv.apply_symm_apply]
      exact hp2
  have hbad : ∃ y0 : U → Bool, y0 ∉ goodU := by
    refine ⟨fun i => if i.1 = cl.1.1 then cl.1.2 else cl.2.2, ?_⟩
    simp only [goodU, Finset.mem_filter, Finset.mem_univ, true_and, not_or, not_ne_iff]
    refine ⟨by simp, ?_⟩
    by_cases hv : cl.2.1 = cl.1.1
    · simp only [hv, ↓reduceIte]
      by_contra hne
      exact hnt ⟨hv.symm, hne⟩
    · simp [hv]
  obtain ⟨y0, hy0⟩ := hbad
  have hlt : goodU.card < (Finset.univ : Finset (U → Bool)).card := by
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨Finset.subset_univ _, ?_⟩
    intro heq
    exact hy0 (heq ▸ Finset.mem_univ y0)
  have hcard_all : (Finset.univ : Finset (U → Bool)).card = 2 ^ U.card := by
    simp
  have hU_cases : U.card = 1 ∨ U.card = 2 := by
    by_cases hv : cl.1.1 = cl.2.1
    · left
      simp [U, clVars, hv]
    · right
      exact Finset.card_pair hv
  have h43 : goodU.card * 4 ≤ 3 * (Finset.univ : Finset (U → Bool)).card := by
    rw [hcard_all] at hlt ⊢
    rcases hU_cases with h1 | h2
    · rw [h1] at hlt ⊢; omega
    · rw [h2] at hlt ⊢; omega
  rw [hcard_ins, hcard_Q]
  calc goodU.card * goodUc.card * 4 = (goodU.card * 4) * goodUc.card := by ring
    _ ≤ (3 * (Finset.univ : Finset (U → Bool)).card) * goodUc.card := Nat.mul_le_mul_right _ h43
    _ = 3 * ((Finset.univ : Finset (U → Bool)).card * goodUc.card) := by ring

theorem packing_bound {n : ℕ} (P : F n) (hP : isPacking P) :
    massFn n P * 4 ^ P.card ≤ 3 ^ P.card * 2 ^ n := by
  classical
  induction P using Finset.induction_on with
  | empty =>
    have hm : massFn n ∅ = 2 ^ n := by
      unfold massFn satFn
      simp
    simp [hm]
  | @insert cl Q hcl ih =>
    have hQ : isPacking Q := by
      refine ⟨fun c hc => hP.1 c (Finset.mem_insert_of_mem hc), ?_⟩
      intro c1 hc1 c2 hc2 hne
      exact hP.2 c1 (Finset.mem_insert_of_mem hc1) c2 (Finset.mem_insert_of_mem hc2) hne
    have ihQ := ih hQ
    have hnt : ¬ isTaut cl := hP.1 cl (Finset.mem_insert_self cl Q)
    have hdisj : ∀ cl' ∈ Q, Disjoint (clVars cl) (clVars cl') := by
      intro cl' hcl'
      have hne : cl ≠ cl' := fun h => hcl (h ▸ hcl')
      exact hP.2 cl (Finset.mem_insert_self cl Q) cl' (Finset.mem_insert_of_mem hcl') hne
    have hstep := packing_step cl Q hnt hdisj
    rw [Finset.card_insert_of_notMem hcl, pow_succ, pow_succ]
    calc massFn n (insert cl Q) * (4 ^ Q.card * 4)
        = (massFn n (insert cl Q) * 4) * 4 ^ Q.card := by ring
      _ ≤ (3 * massFn n Q) * 4 ^ Q.card := Nat.mul_le_mul_right _ hstep
      _ = 3 * (massFn n Q * 4 ^ Q.card) := by ring
      _ ≤ 3 * (3 ^ Q.card * 2 ^ n) := Nat.mul_le_mul_left _ ihQ
      _ = 3 ^ Q.card * 3 * 2 ^ n := by ring

theorem exists_cover_of_large_mass {p q n : ℕ} (hp : 0 < p) (A : F n)
    (hlarge : p * 2 ^ n < 2 * q * massFn n A) :
    let c := 6 * (1 + Nat.clog 2 ((q + p - 1) / p))
    ∃ C : Finset (Fin n), C.card ≤ c ∧
      ∀ cl ∈ stripTaut A, cl.1.1 ∈ C ∨ cl.2.1 ∈ C := by
  classical
  dsimp only
  let t := 1 + Nat.clog 2 ((q + p - 1) / p)
  let c := 6 * t
  let A' := stripTaut A
  let packs := A'.powerset.filter (fun P => isPacking P)
  have hempty : (∅ : F n) ∈ packs := by
    simp [packs, isPacking]
  obtain ⟨P, hPmem, hPmax⟩ := Finset.exists_max_image packs Finset.card ⟨∅, hempty⟩
  have hPsub : P ⊆ A' := Finset.mem_powerset.mp (Finset.mem_filter.mp hPmem).1
  have hPpack : isPacking P := (Finset.mem_filter.mp hPmem).2
  have hP_lt : P.card < 3 * t := by
    by_contra hge
    have hle : 3 * t ≤ P.card := by omega
    obtain ⟨Q, hQP, hQcard⟩ := Finset.exists_subset_card_eq hle
    have hQpack : isPacking Q :=
      ⟨fun cl hcl => hPpack.1 cl (hQP hcl),
       fun c1 hc1 c2 hc2 hne => hPpack.2 c1 (hQP hc1) c2 (hQP hc2) hne⟩
    have hQsubA : Q ⊆ A' := hQP.trans hPsub
    have hm_le : massFn n A ≤ massFn n Q := by
      rw [← massFn_stripTaut A]
      exact massFn_mono hQsubA
    have hpb := packing_bound Q hQpack
    rw [hQcard] at hpb
    have hmass_pb : massFn n A * 4 ^ (3 * t) ≤ 3 ^ (3 * t) * 2 ^ n :=
      (Nat.mul_le_mul_right _ hm_le).trans hpb
    have hq_le_div : q ≤ p * ((q + p - 1) / p) := by
      have hdm := Nat.div_add_mod (q + p - 1) p
      have hmod : (q + p - 1) % p < p := Nat.mod_lt _ hp
      omega
    have hdiv_le : (q + p - 1) / p ≤ 2 ^ Nat.clog 2 ((q + p - 1) / p) :=
      Nat.le_pow_clog (by norm_num) _
    have h2q_le : 2 * q ≤ p * 2 ^ t := by
      have h1 : q ≤ p * 2 ^ Nat.clog 2 ((q + p - 1) / p) :=
        hq_le_div.trans (Nat.mul_le_mul_left p hdiv_le)
      have hpow : 2 ^ t = 2 * 2 ^ Nat.clog 2 ((q + p - 1) / p) := by
        dsimp only [t]
        rw [pow_add, pow_one]
      rw [hpow]
      nlinarith
    have h54_lt : 2 ^ t * 3 ^ (3 * t) < 4 ^ (3 * t) := by
      have h1 : 2 ^ t * 3 ^ (3 * t) = 54 ^ t := by
        rw [pow_mul, ← mul_pow]
        norm_num
      have h2 : 4 ^ (3 * t) = 64 ^ t := by
        rw [pow_mul]
        norm_num
      rw [h1, h2]
      exact Nat.pow_lt_pow_left (by norm_num) (by dsimp only [t]; omega)
    have hcontra : 2 * q * massFn n A * 4 ^ (3 * t) < p * 2 ^ n * 4 ^ (3 * t) := by
      calc 2 * q * massFn n A * 4 ^ (3 * t)
          = (2 * q) * (massFn n A * 4 ^ (3 * t)) := by ring
        _ ≤ (2 * q) * (3 ^ (3 * t) * 2 ^ n) := Nat.mul_le_mul_left _ hmass_pb
        _ ≤ (p * 2 ^ t) * (3 ^ (3 * t) * 2 ^ n) := Nat.mul_le_mul_right _ h2q_le
        _ = (p * 2 ^ n) * (2 ^ t * 3 ^ (3 * t)) := by ring
        _ < (p * 2 ^ n) * 4 ^ (3 * t) := Nat.mul_lt_mul_of_pos_left h54_lt (by positivity)
    have h4pos : 0 < 4 ^ (3 * t) := by positivity
    have hlt2 : 2 * q * massFn n A < p * 2 ^ n :=
      Nat.lt_of_mul_lt_mul_right hcontra
    omega
  let C : Finset (Fin n) := P.biUnion clVars
  refine ⟨C, ?_, ?_⟩
  · have hC_le : C.card ≤ ∑ cl ∈ P, (clVars cl).card := Finset.card_biUnion_le
    have hterm : ∑ cl ∈ P, (clVars cl).card ≤ ∑ _cl ∈ P, 2 := by
      refine Finset.sum_le_sum (fun cl _ => ?_)
      exact Finset.card_le_two
    have hsum2 : (∑ _cl ∈ P, 2) = P.card * 2 := by simp
    have hC2 : C.card ≤ 2 * P.card := by omega
    omega
  · intro cl hcl
    by_contra hnot
    push Not at hnot
    have hdisj : ∀ cl' ∈ P, Disjoint (clVars cl) (clVars cl') := by
      intro cl' hcl'
      rw [Finset.disjoint_left]
      intro v hv hv'
      have hvC : v ∈ C := Finset.mem_biUnion.mpr ⟨cl', hcl', hv'⟩
      simp only [clVars, Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl
      · exact hnot.1 hvC
      · exact hnot.2 hvC
    have hcl_notP : cl ∉ P := by
      intro hmem
      exact hnot.1 (Finset.mem_biUnion.mpr ⟨cl, hmem, by simp [clVars]⟩)
    have hins_pack : isPacking (insert cl P) := by
      refine ⟨?_, ?_⟩
      · intro c hc
        rcases Finset.mem_insert.mp hc with rfl | hcP
        · exact (Finset.mem_filter.mp hcl).2
        · exact hPpack.1 c hcP
      · intro c1 hc1 c2 hc2 hne
        rcases Finset.mem_insert.mp hc1 with rfl | hc1P <;>
        rcases Finset.mem_insert.mp hc2 with rfl | hc2P
        · exact absurd rfl hne
        · exact hdisj c2 hc2P
        · exact (hdisj c1 hc1P).symm
        · exact hPpack.2 c1 hc1P c2 hc2P hne
    have hins_mem : insert cl P ∈ packs := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ?_, hins_pack⟩
      intro c hc
      rcases Finset.mem_insert.mp hc with rfl | hcP
      · exact hcl
      · exact hPsub hcP
    have hle := hPmax (insert cl P) hins_mem
    rw [Finset.card_insert_of_notMem hcl_notP] at hle
    omega

theorem card_filter_fixed {n : ℕ} (S : Finset (Fin n)) (val : Fin n → Bool) :
    (Finset.univ.filter (fun x : W n => ∀ i ∈ S, x i = val i)).card = 2 ^ (n - S.card) := by
  classical
  let Sc := {i : Fin n // i ∉ S}
  have hbij : (Finset.univ.filter (fun x : W n => ∀ i ∈ S, x i = val i)).card =
      Fintype.card (Sc → Bool) := by
    rw [← Finset.card_univ]
    refine Finset.card_bij (fun x _ j => x j.1) ?_ ?_ ?_
    · intro _ _; exact Finset.mem_univ _
    · intro a ha b hb heq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      funext i
      by_cases hi : i ∈ S
      · rw [ha i hi, hb i hi]
      · exact congrFun heq ⟨i, hi⟩
    · intro y _
      refine ⟨fun i => if h : i ∈ S then val i else y ⟨i, h⟩, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        intro i hi; simp [hi]
      · funext j; simp [j.2]
  rw [hbij, Fintype.card_fun, Fintype.card_bool]
  congr 1
  have hSc : Fintype.card Sc = (Finset.univ \ S).card := by
    rw [Fintype.card_subtype]
    congr 1
    ext i
    simp
  rw [hSc, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]

def forbLits {n : ℕ} (A' : F n) (C : Finset (Fin n)) (σ : C → Bool) : Finset (Lit n) :=
  Finset.univ.filter (fun l : Lit n => l.1 ∉ C ∧
    ∃ cl ∈ A',
      (∃ h1 : cl.1.1 ∈ C, σ ⟨cl.1.1, h1⟩ = cl.1.2 ∧ cl.2 = l) ∨
      (∃ h2 : cl.2.1 ∈ C, σ ⟨cl.2.1, h2⟩ = cl.2.2 ∧ cl.1 = l))

def forcedVars {n : ℕ} (A' : F n) (C : Finset (Fin n)) (σ : C → Bool) : Finset (Fin n) :=
  (forbLits A' C σ).image Prod.fst

def survives {n : ℕ} (A' : F n) (C : Finset (Fin n)) (σ : C → Bool) : Prop :=
  (∀ cl ∈ A', ∀ (h1 : cl.1.1 ∈ C) (h2 : cl.2.1 ∈ C),
      σ ⟨cl.1.1, h1⟩ ≠ cl.1.2 ∨ σ ⟨cl.2.1, h2⟩ ≠ cl.2.2) ∧
  (∀ v : Fin n, ¬ ((v, true) ∈ forbLits A' C σ ∧ (v, false) ∈ forbLits A' C σ))

instance {n : ℕ} (A' : F n) (C : Finset (Fin n)) (σ : C → Bool) :
    Decidable (survives A' C σ) := by
  unfold survives
  infer_instance

def fiberExp {n : ℕ} (A' : F n) (C : Finset (Fin n)) (σ : C → Bool) : ℕ :=
  C.card + (forcedVars A' C σ).card

theorem forcedVars_disjoint {n : ℕ} (A' : F n) (C : Finset (Fin n)) (σ : C → Bool) :
    Disjoint C (forcedVars A' C σ) := by
  rw [Finset.disjoint_right]
  intro v hv hvC
  rcases Finset.mem_image.mp hv with ⟨l, hl, rfl⟩
  exact (Finset.mem_filter.mp hl).2.1 hvC

theorem fiberExp_le {n : ℕ} (A' : F n) (C : Finset (Fin n)) (σ : C → Bool) :
    fiberExp A' C σ ≤ n := by
  unfold fiberExp
  rw [← Finset.card_union_of_disjoint (forcedVars_disjoint A' C σ)]
  calc (C ∪ forcedVars A' C σ).card ≤ (Finset.univ : Finset (Fin n)).card :=
        Finset.card_le_card (Finset.subset_univ _)
    _ = n := by simp

theorem fiber_card_eq {n : ℕ} (A : F n) (C : Finset (Fin n))
    (hcov : ∀ cl ∈ stripTaut A, cl.1.1 ∈ C ∨ cl.2.1 ∈ C) (σ : C → Bool) :
    (Finset.univ.filter (fun x : W n => (∀ i : C, x i.1 = σ i) ∧ satFn n A x = true)).card =
      if survives (stripTaut A) C σ then 2 ^ (n - fiberExp (stripTaut A) C σ) else 0 := by
  classical
  let A' := stripTaut A
  have hsat : ∀ x : W n, satFn n A x = true ↔ ∀ cl ∈ A', x cl.1.1 ≠ cl.1.2 ∨ x cl.2.1 ≠ cl.2.2 := by
    intro x
    rw [← satFn_stripTaut]
    simp [satFn, A']
  split_ifs with hsurv
  · let Fσ : Finset (Fin n) := C ∪ forcedVars A' C σ
    let val : Fin n → Bool := fun i =>
      if h : i ∈ C then σ ⟨i, h⟩
      else if (i, true) ∈ forbLits A' C σ then false else true
    have hset : Finset.univ.filter (fun x : W n => (∀ i : C, x i.1 = σ i) ∧ satFn n A x = true) =
        Finset.univ.filter (fun x : W n => ∀ i ∈ Fσ, x i = val i) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hsat]
      constructor
      · rintro ⟨hσ, hA'⟩ i hi
        rcases Finset.mem_union.mp hi with hiC | hiF
        · simp only [val, hiC, ↓reduceDIte]
          exact hσ ⟨i, hiC⟩
        · have hi_notC : i ∉ C := Finset.disjoint_right.mp (forcedVars_disjoint A' C σ) hiF
          simp only [val, hi_notC, ↓reduceDIte]
          rcases Finset.mem_image.mp hiF with ⟨l, hl, rfl⟩
          have hl_forb : ∀ b : Bool, (l.1, b) ∈ forbLits A' C σ → x l.1 ≠ b := by
            intro b hb
            rcases (Finset.mem_filter.mp hb).2.2 with ⟨cl, hcl, hcase⟩
            rcases hcase with ⟨h1, hσ1, hcl2⟩ | ⟨h2, hσ2, hcl1⟩
            · have hx1 : x cl.1.1 = cl.1.2 := (hσ ⟨cl.1.1, h1⟩).trans hσ1
              rcases hA' cl hcl with h | h
              · exact absurd hx1 h
              · rw [hcl2] at h; exact h
            · have hx2 : x cl.2.1 = cl.2.2 := (hσ ⟨cl.2.1, h2⟩).trans hσ2
              rcases hA' cl hcl with h | h
              · rw [hcl1] at h; exact h
              · exact absurd hx2 h
          by_cases ht : (l.1, true) ∈ forbLits A' C σ
          · simp only [ht, ↓reduceIte]
            have hne := hl_forb true ht
            cases hx : x l.1 <;> simp_all
          · simp only [ht, ↓reduceIte]
            have hf : (l.1, false) ∈ forbLits A' C σ := by
              cases hb : l.2
              · have hl' : (l.1, false) = l := Prod.ext rfl hb.symm
                rw [hl']; exact hl
              · have hl' : (l.1, true) = l := Prod.ext rfl hb.symm
                exact absurd (hl'.symm ▸ hl) ht
            have hne := hl_forb false hf
            cases hx : x l.1 <;> simp_all
      · intro hfix
        have hσ : ∀ i : C, x i.1 = σ i := by
          intro i
          have h := hfix i.1 (Finset.mem_union_left _ i.2)
          simpa [val, i.2] using h
        refine ⟨hσ, ?_⟩
        intro cl hcl
        by_cases h1 : cl.1.1 ∈ C
        · by_cases h2 : cl.2.1 ∈ C
          · rw [hσ ⟨cl.1.1, h1⟩, hσ ⟨cl.2.1, h2⟩]
            exact hsurv.1 cl hcl h1 h2
          · by_cases htrig : σ ⟨cl.1.1, h1⟩ = cl.1.2
            · right
              have hmem : cl.2 ∈ forbLits A' C σ :=
                Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2, ⟨cl, hcl, Or.inl ⟨h1, htrig, rfl⟩⟩⟩
              have hvF : cl.2.1 ∈ Fσ :=
                Finset.mem_union_right _ (Finset.mem_image.mpr ⟨cl.2, hmem, rfl⟩)
              have hx2 := hfix cl.2.1 hvF
              simp only [val, h2, ↓reduceDIte] at hx2
              cases hb : cl.2.2
              · have hnf : (cl.2.1, false) ∈ forbLits A' C σ := by
                  have : (cl.2.1, false) = cl.2 := Prod.ext rfl hb.symm
                  rwa [this]
                have hnt : (cl.2.1, true) ∉ forbLits A' C σ := fun ht => hsurv.2 cl.2.1 ⟨ht, hnf⟩
                simp only [hnt, ↓reduceIte] at hx2
                rw [hx2]; decide
              · have hnt : (cl.2.1, true) ∈ forbLits A' C σ := by
                  have : (cl.2.1, true) = cl.2 := Prod.ext rfl hb.symm
                  rwa [this]
                simp only [hnt, ↓reduceIte] at hx2
                rw [hx2]; decide
            · left
              rw [hσ ⟨cl.1.1, h1⟩]
              exact htrig
        · have h2 : cl.2.1 ∈ C := (hcov cl hcl).resolve_left h1
          by_cases htrig : σ ⟨cl.2.1, h2⟩ = cl.2.2
          · left
            have hmem : cl.1 ∈ forbLits A' C σ :=
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1, ⟨cl, hcl, Or.inr ⟨h2, htrig, rfl⟩⟩⟩
            have hvF : cl.1.1 ∈ Fσ :=
              Finset.mem_union_right _ (Finset.mem_image.mpr ⟨cl.1, hmem, rfl⟩)
            have hx1 := hfix cl.1.1 hvF
            simp only [val, h1, ↓reduceDIte] at hx1
            cases hb : cl.1.2
            · have hnf : (cl.1.1, false) ∈ forbLits A' C σ := by
                have : (cl.1.1, false) = cl.1 := Prod.ext rfl hb.symm
                rwa [this]
              have hnt : (cl.1.1, true) ∉ forbLits A' C σ := fun ht => hsurv.2 cl.1.1 ⟨ht, hnf⟩
              simp only [hnt, ↓reduceIte] at hx1
              rw [hx1]; decide
            · have hnt : (cl.1.1, true) ∈ forbLits A' C σ := by
                have : (cl.1.1, true) = cl.1 := Prod.ext rfl hb.symm
                rwa [this]
              simp only [hnt, ↓reduceIte] at hx1
              rw [hx1]; decide
          · right
            rw [hσ ⟨cl.2.1, h2⟩]
            exact htrig
    rw [hset, card_filter_fixed]
    congr 2
    dsimp only [Fσ, fiberExp]
    exact Finset.card_union_of_disjoint (forcedVars_disjoint A' C σ)
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro x _ hx
    rcases hx with ⟨hσ, hA⟩
    have hA' := (hsat x).mp hA
    apply hsurv
    refine ⟨?_, ?_⟩
    · intro cl hcl h1 h2
      rw [← hσ ⟨cl.1.1, h1⟩, ← hσ ⟨cl.2.1, h2⟩]
      exact hA' cl hcl
    · intro v ⟨ht, hf⟩
      have hforb : ∀ b : Bool, (v, b) ∈ forbLits A' C σ → x v ≠ b := by
        intro b hb
        rcases (Finset.mem_filter.mp hb).2.2 with ⟨cl, hcl, hcase⟩
        rcases hcase with ⟨h1, hσ1, hcl2⟩ | ⟨h2, hσ2, hcl1⟩
        · have hx1 : x cl.1.1 = cl.1.2 := (hσ ⟨cl.1.1, h1⟩).trans hσ1
          rcases hA' cl hcl with h | h
          · exact absurd hx1 h
          · rw [hcl2] at h; exact h
        · have hx2 : x cl.2.1 = cl.2.2 := (hσ ⟨cl.2.1, h2⟩).trans hσ2
          rcases hA' cl hcl with h | h
          · rw [hcl1] at h; exact h
          · exact absurd hx2 h
      have h1 := hforb true ht
      have h2 := hforb false hf
      cases hx : x v <;> simp_all

theorem mass_eq_sum_surviving {n : ℕ} (A : F n) (C : Finset (Fin n))
    (hcov : ∀ cl ∈ stripTaut A, cl.1.1 ∈ C ∨ cl.2.1 ∈ C) :
    let A' := stripTaut A
    massFn n A = ∑ σ ∈ Finset.univ.filter (fun σ : C → Bool => survives A' C σ),
      2 ^ (n - fiberExp A' C σ) := by
  classical
  dsimp only
  let A' := stripTaut A
  have hpart : massFn n A =
      ∑ σ : C → Bool,
        (Finset.univ.filter (fun x : W n => (∀ i : C, x i.1 = σ i) ∧ satFn n A x = true)).card := by
    unfold massFn
    rw [Finset.card_eq_sum_ones, ← Finset.sum_fiberwise_of_maps_to
      (g := fun (x : W n) (i : C) => x i.1) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    rw [← Finset.card_eq_sum_ones, Finset.filter_filter]
    congr 1
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨fun i => congrFun h2 i, h1⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h2, funext h1⟩
  rw [hpart]
  have hrew : (∑ σ : C → Bool,
      (Finset.univ.filter (fun x : W n => (∀ i : C, x i.1 = σ i) ∧ satFn n A x = true)).card) =
      ∑ σ : C → Bool, if survives A' C σ then 2 ^ (n - fiberExp A' C σ) else 0 :=
    Finset.sum_congr rfl (fun σ _ => fiber_card_eq A C hcov σ)
  rw [hrew, Finset.sum_ite, Finset.sum_const_zero, add_zero]

theorem exists_gap_from {α : Type*} (S : Finset α) (e : α → ℕ) (n D : ℕ)
    (hle : ∀ σ ∈ S, e σ ≤ n) :
    ∀ (m cur : ℕ), cur ≤ n → (S.filter (fun σ => cur < e σ)).card ≤ m →
      ∃ E : ℕ, E ≤ cur + m * D ∧ E ≤ n ∧ ∀ σ ∈ S, e σ ≤ E ∨ E + D < e σ := by
  intro m
  induction m with
  | zero =>
    intro cur hcur hcard
    refine ⟨cur, by omega, hcur, ?_⟩
    intro σ hσ
    left
    by_contra hgt
    have hmem : σ ∈ S.filter (fun σ => cur < e σ) :=
      Finset.mem_filter.mpr ⟨hσ, by omega⟩
    have hpos : 0 < (S.filter (fun σ => cur < e σ)).card := Finset.card_pos.mpr ⟨σ, hmem⟩
    omega
  | succ m ih =>
    intro cur hcur hcard
    let band := S.filter (fun σ => cur < e σ ∧ e σ ≤ cur + D)
    by_cases hband : band.Nonempty
    · obtain ⟨σ0, hσ0⟩ := hband
      have hσ0S : σ0 ∈ S := (Finset.mem_filter.mp hσ0).1
      have hσ0_gt : cur < e σ0 := (Finset.mem_filter.mp hσ0).2.1
      have hσ0_le : e σ0 ≤ cur + D := (Finset.mem_filter.mp hσ0).2.2
      have hsub : S.filter (fun σ => e σ0 < e σ) ⊂ S.filter (fun σ => cur < e σ) := by
        rw [Finset.ssubset_iff_subset_ne]
        refine ⟨?_, ?_⟩
        · intro σ hσ
          simp only [Finset.mem_filter] at hσ ⊢
          exact ⟨hσ.1, by omega⟩
        · intro heq
          have hmem : σ0 ∈ S.filter (fun σ => cur < e σ) :=
            Finset.mem_filter.mpr ⟨hσ0S, hσ0_gt⟩
          rw [← heq] at hmem
          have := (Finset.mem_filter.mp hmem).2
          omega
      have hlt_card : (S.filter (fun σ => e σ0 < e σ)).card < (S.filter (fun σ => cur < e σ)).card :=
        Finset.card_lt_card hsub
      obtain ⟨E, hE1, hE2, hE3⟩ := ih (e σ0) (hle σ0 hσ0S) (by omega)
      refine ⟨E, ?_, hE2, hE3⟩
      calc E ≤ e σ0 + m * D := hE1
        _ ≤ (cur + D) + m * D := by omega
        _ = cur + (m + 1) * D := by ring
    · refine ⟨cur, by omega, hcur, ?_⟩
      intro σ hσ
      by_cases hgt : cur < e σ
      · right
        by_contra hleD
        have hmem : σ ∈ band := Finset.mem_filter.mpr ⟨hσ, hgt, by omega⟩
        exact hband ⟨σ, hmem⟩
      · left
        omega

theorem exists_gap_threshold {α : Type*} (S : Finset α) (e : α → ℕ) (n D : ℕ)
    (hle : ∀ σ ∈ S, e σ ≤ n) :
    ∃ E : ℕ, E ≤ S.card * D ∧ E ≤ n ∧ ∀ σ ∈ S, e σ ≤ E ∨ E + D < e σ := by
  have h := exists_gap_from S e n D hle S.card 0 (Nat.zero_le n)
    (Finset.card_le_card (Finset.filter_subset _ _))
  simpa using h

theorem gap_split_bounds {p q n c : ℕ} (_hp : 0 < p) (_hpq : p ≤ q) (A : F n)
    (C : Finset (Fin n)) (hC : C.card ≤ c)
    (hcov : ∀ cl ∈ stripTaut A, cl.1.1 ∈ C ∨ cl.2.1 ∈ C) :
    let D := Nat.clog 2 q + c + 1
    let H := 2 ^ c * D
    let A' := stripTaut A
    let Ssurv := Finset.univ.filter (fun σ : C → Bool => survives A' C σ)
    ∃ E : ℕ, E ≤ H ∧ E ≤ n ∧
      (let Mpre := ∑ σ ∈ Ssurv.filter (fun σ => fiberExp A' C σ ≤ E), 2 ^ (n - fiberExp A' C σ)
       let Mtail := ∑ σ ∈ Ssurv.filter (fun σ => E < fiberExp A' C σ), 2 ^ (n - fiberExp A' C σ)
       massFn n A = Mpre + Mtail ∧
       (∃ U : ℕ, Mpre * 2 ^ E = U * 2 ^ n) ∧
       4 * q * Mtail * 2 ^ E ≤ 2 ^ n) := by
  classical
  dsimp only
  let D := Nat.clog 2 q + c + 1
  let H := 2 ^ c * D
  let A' := stripTaut A
  let Ssurv := Finset.univ.filter (fun σ : C → Bool => survives A' C σ)
  have hS_card : Ssurv.card ≤ 2 ^ c := by
    calc Ssurv.card ≤ (Finset.univ : Finset (C → Bool)).card :=
          Finset.card_le_card (Finset.subset_univ _)
      _ = 2 ^ C.card := by simp
      _ ≤ 2 ^ c := Nat.pow_le_pow_right (by omega) hC
  obtain ⟨E, hE1, hE2, hEgap⟩ := exists_gap_threshold Ssurv (fiberExp A' C) n D
    (fun σ _ => fiberExp_le A' C σ)
  have hE_le_H : E ≤ H := hE1.trans (Nat.mul_le_mul_right D hS_card)
  refine ⟨E, hE_le_H, hE2, ?_, ?_, ?_⟩
  · change massFn n A =
      (∑ σ ∈ Ssurv.filter (fun σ => fiberExp A' C σ ≤ E), 2 ^ (n - fiberExp A' C σ)) +
      (∑ σ ∈ Ssurv.filter (fun σ => E < fiberExp A' C σ), 2 ^ (n - fiberExp A' C σ))
    rw [mass_eq_sum_surviving A C hcov]
    have hpart := (Finset.sum_filter_add_sum_filter_not (s := Ssurv)
      (p := fun σ => fiberExp A' C σ ≤ E)
      (f := fun σ => 2 ^ (n - fiberExp A' C σ))).symm
    rw [hpart]
    congr 1
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext σ
    simp only [Finset.mem_filter]
    constructor <;> intro ⟨h1, h2⟩ <;> exact ⟨h1, by omega⟩
  · refine ⟨∑ σ ∈ Ssurv.filter (fun σ => fiberExp A' C σ ≤ E), 2 ^ (E - fiberExp A' C σ), ?_⟩
    change (∑ σ ∈ Ssurv.filter (fun σ => fiberExp A' C σ ≤ E), 2 ^ (n - fiberExp A' C σ)) * 2 ^ E = _
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun σ hσ => ?_)
    have hleE : fiberExp A' C σ ≤ E := (Finset.mem_filter.mp hσ).2
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  · have hq_le : q ≤ 2 ^ Nat.clog 2 q := Nat.le_pow_clog (by norm_num) q
    have h4q_le : 4 * q * 2 ^ c ≤ 2 ^ (D + 1) := by
      have hpow : 2 ^ (D + 1) = 4 * 2 ^ Nat.clog 2 q * 2 ^ c := by
        dsimp only [D]
        have : Nat.clog 2 q + c + 1 + 1 = 2 + Nat.clog 2 q + c := by omega
        rw [this, pow_add, pow_add]
        norm_num
      rw [hpow]
      nlinarith
    have htail_bound :
        (∑ σ ∈ Ssurv.filter (fun σ => E < fiberExp A' C σ), 2 ^ (n - fiberExp A' C σ)) *
          2 ^ (E + D + 1) ≤ 2 ^ c * 2 ^ n := by
      rw [Finset.sum_mul]
      have hterm : ∀ σ ∈ Ssurv.filter (fun σ => E < fiberExp A' C σ),
          2 ^ (n - fiberExp A' C σ) * 2 ^ (E + D + 1) ≤ 2 ^ n := by
        intro σ hσ
        have hσS : σ ∈ Ssurv := (Finset.mem_filter.mp hσ).1
        have hgtE : E < fiberExp A' C σ := (Finset.mem_filter.mp hσ).2
        have hgtED : E + D < fiberExp A' C σ := (hEgap σ hσS).resolve_left (by omega)
        have hlen : fiberExp A' C σ ≤ n := fiberExp_le A' C σ
        rw [← pow_add]
        exact Nat.pow_le_pow_right (by omega) (by omega)
      calc (∑ σ ∈ Ssurv.filter (fun σ => E < fiberExp A' C σ),
              2 ^ (n - fiberExp A' C σ) * 2 ^ (E + D + 1))
          ≤ ∑ _σ ∈ Ssurv.filter (fun σ => E < fiberExp A' C σ), 2 ^ n := Finset.sum_le_sum hterm
        _ = (Ssurv.filter (fun σ => E < fiberExp A' C σ)).card * 2 ^ n := by simp
        _ ≤ Ssurv.card * 2 ^ n := Nat.mul_le_mul_right _ (Finset.card_le_card (Finset.filter_subset _ _))
        _ ≤ 2 ^ c * 2 ^ n := Nat.mul_le_mul_right _ hS_card
    have hbig :
        (4 * q * (∑ σ ∈ Ssurv.filter (fun σ => E < fiberExp A' C σ), 2 ^ (n - fiberExp A' C σ)) * 2 ^ E) *
          2 ^ (D + 1) ≤ 2 ^ n * 2 ^ (D + 1) := by
      calc (4 * q * (∑ σ ∈ Ssurv.filter (fun σ => E < fiberExp A' C σ), 2 ^ (n - fiberExp A' C σ)) * 2 ^ E) *
              2 ^ (D + 1)
          = (4 * q) * ((∑ σ ∈ Ssurv.filter (fun σ => E < fiberExp A' C σ), 2 ^ (n - fiberExp A' C σ)) *
              (2 ^ E * 2 ^ (D + 1))) := by ring
        _ = (4 * q) * ((∑ σ ∈ Ssurv.filter (fun σ => E < fiberExp A' C σ), 2 ^ (n - fiberExp A' C σ)) *
              2 ^ (E + D + 1)) := by
              rw [← pow_add, show E + (D + 1) = E + D + 1 by omega]
        _ ≤ (4 * q) * (2 ^ c * 2 ^ n) := Nat.mul_le_mul_left _ htail_bound
        _ = (4 * q * 2 ^ c) * 2 ^ n := by ring
        _ ≤ 2 ^ (D + 1) * 2 ^ n := Nat.mul_le_mul_right _ h4q_le
        _ = 2 ^ n * 2 ^ (D + 1) := by ring
    exact Nat.le_of_mul_le_mul_right hbig (by positivity)

def outsideNbrs {n : ℕ} (A' : F n) (C : Finset (Fin n)) (u : Fin n) (b : Bool) : Finset (Fin n) :=
  Finset.univ.filter (fun v : Fin n => v ∉ C ∧
    ∃ cl ∈ A', (cl.1 = (u, b) ∧ cl.2.1 = v) ∨ (cl.2 = (u, b) ∧ cl.1.1 = v))

theorem outsideNbrs_subset_forcedVars {n : ℕ} (A' : F n) (C : Finset (Fin n))
    (σ : C → Bool) (u : Fin n) (hu : u ∈ C) (b : Bool) (hσ : σ ⟨u, hu⟩ = b) :
    outsideNbrs A' C u b ⊆ forcedVars A' C σ := by
  intro v hv
  simp only [outsideNbrs, Finset.mem_filter, Finset.mem_univ, true_and] at hv
  rcases hv with ⟨hvC, cl, hcl, hcase⟩
  rcases hcase with ⟨hcl1, hcl2v⟩ | ⟨hcl2, hcl1v⟩
  · refine Finset.mem_image.mpr ⟨cl.2, ?_, hcl2v⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcl2v.symm ▸ hvC, ⟨cl, hcl, Or.inl ?_⟩⟩
    have hu1 : cl.1.1 = u := congrArg Prod.fst hcl1
    have hb1 : cl.1.2 = b := congrArg Prod.snd hcl1
    refine ⟨hu1.symm ▸ hu, ?_, rfl⟩
    have hsub : (⟨cl.1.1, hu1.symm ▸ hu⟩ : C) = ⟨u, hu⟩ := Subtype.ext hu1
    rw [hsub, hσ, hb1]
  · refine Finset.mem_image.mpr ⟨cl.1, ?_, hcl1v⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcl1v.symm ▸ hvC, ⟨cl, hcl, Or.inr ?_⟩⟩
    have hu2 : cl.2.1 = u := congrArg Prod.fst hcl2
    have hb2 : cl.2.2 = b := congrArg Prod.snd hcl2
    refine ⟨hu2.symm ▸ hu, ?_, rfl⟩
    have hsub : (⟨cl.2.1, hu2.symm ▸ hu⟩ : C) = ⟨u, hu⟩ := Subtype.ext hu2
    rw [hsub, hσ, hb2]

theorem bool_ne_not_iff (a b : Bool) : a ≠ !b ↔ a = b := by
  cases a <;> cases b <;> decide

theorem bool_ne_iff_eq_not (a b : Bool) : a ≠ b ↔ a = !b := by
  cases a <;> cases b <;> decide

theorem main_conj1 {p q n : ℕ} (hp : 0 < p) (hpq : p ≤ q) (A : F n)
    (hge : p * 2 ^ n ≤ q * massFn n A) :
    let c := 6 * (1 + Nat.clog 2 ((q + p - 1) / p))
    let H := 2 ^ c * (Nat.clog 2 q + c + 1)
    let K := c + 2 * c * H
    ∃ (S : Finset (Fin n)) (pins : Finset (Lit n)) (B : F n),
      S.card ≤ K ∧ (∀ l ∈ pins, l.1 ∈ S) ∧
      (∀ cl ∈ B, cl.1.1 ∈ S ∧ cl.2.1 ∈ S) ∧ p * 2 ^ n ≤ q * massFn n B ∧
      ∀ z : W n, satFn n B z = true ↔ satFn n A z = true ∧ ∀ l ∈ pins, z l.1 = l.2 := by
  classical
  dsimp only
  let c := 6 * (1 + Nat.clog 2 ((q + p - 1) / p))
  let D := Nat.clog 2 q + c + 1
  let H := 2 ^ c * D
  let K := c + 2 * c * H
  let A' := stripTaut A
  have h2n_pos : 0 < 2 ^ n := by positivity
  have hlarge : p * 2 ^ n < 2 * q * massFn n A := by
    have hp2 : 0 < p * 2 ^ n := Nat.mul_pos hp h2n_pos
    nlinarith
  obtain ⟨C, hC_le, hcov⟩ := exists_cover_of_large_mass hp A hlarge
  obtain ⟨E, hE_le_H, hE_le_n, hmass_eq, ⟨U, hU⟩, htail⟩ :=
    gap_split_bounds hp hpq A C hC_le hcov
  let Ssurv := Finset.univ.filter (fun σ : C → Bool => survives A' C σ)
  let Mpre := ∑ σ ∈ Ssurv.filter (fun σ => fiberExp A' C σ ≤ E), 2 ^ (n - fiberExp A' C σ)
  let Mtail := ∑ σ ∈ Ssurv.filter (fun σ => E < fiberExp A' C σ), 2 ^ (n - fiberExp A' C σ)
  have hE_le_H' : E ≤ H := hE_le_H
  have hmass_eq' : massFn n A = Mpre + Mtail := hmass_eq
  have htail4 : 4 * (q * Mtail * 2 ^ E) ≤ 2 ^ n := by
    calc 4 * (q * Mtail * 2 ^ E) = 4 * q * Mtail * 2 ^ E := by ring
      _ ≤ 2 ^ n := htail
  have hMpre_ge : p * 2 ^ n ≤ q * Mpre := by
    by_contra hlt
    have hlt' : q * Mpre < p * 2 ^ n := by omega
    have hmul : q * U * 2 ^ n < p * 2 ^ E * 2 ^ n := by
      calc q * U * 2 ^ n = q * (U * 2 ^ n) := by ring
        _ = q * (Mpre * 2 ^ E) := by rw [← hU]
        _ = (q * Mpre) * 2 ^ E := by ring
        _ < (p * 2 ^ n) * 2 ^ E := Nat.mul_lt_mul_of_pos_right hlt' (by positivity)
        _ = p * 2 ^ E * 2 ^ n := by ring
    have hqU_lt : q * U < p * 2 ^ E := Nat.lt_of_mul_lt_mul_right hmul
    have hqU_le : q * U + 1 ≤ p * 2 ^ E := hqU_lt
    have hgap_pre : q * Mpre * 2 ^ E + 2 ^ n ≤ p * 2 ^ n * 2 ^ E := by
      calc q * Mpre * 2 ^ E + 2 ^ n = q * (Mpre * 2 ^ E) + 2 ^ n := by ring
        _ = q * (U * 2 ^ n) + 2 ^ n := by rw [hU]
        _ = (q * U + 1) * 2 ^ n := by ring
        _ ≤ (p * 2 ^ E) * 2 ^ n := Nat.mul_le_mul_right _ hqU_le
        _ = p * 2 ^ n * 2 ^ E := by ring
    have htail_lt : q * Mtail * 2 ^ E < 2 ^ n := by omega
    have htot_lt : q * massFn n A * 2 ^ E < p * 2 ^ n * 2 ^ E := by
      calc q * massFn n A * 2 ^ E = q * Mpre * 2 ^ E + q * Mtail * 2 ^ E := by
            rw [hmass_eq']; ring
        _ < q * Mpre * 2 ^ E + 2 ^ n := Nat.add_lt_add_left htail_lt _
        _ ≤ p * 2 ^ n * 2 ^ E := hgap_pre
    have htot_lt' : q * massFn n A < p * 2 ^ n := Nat.lt_of_mul_lt_mul_right htot_lt
    omega
  let pins : Finset (Lit n) :=
    (C ×ˢ (Finset.univ : Finset Bool)).filter (fun l => H < (outsideNbrs A' C l.1 (!l.2)).card)
  let Bkeep : F n :=
    A'.filter (fun cl => (cl.1.1, !cl.1.2) ∉ pins ∧ (cl.2.1, !cl.2.2) ∉ pins)
  let B : F n :=
    Bkeep ∪ pins.image (fun l => ((l.1, !l.2), (l.1, !l.2)))
  let S : Finset (Fin n) :=
    C ∪ (C ×ˢ (Finset.univ : Finset Bool)).biUnion
      (fun lb => if (outsideNbrs A' C lb.1 lb.2).card ≤ H then outsideNbrs A' C lb.1 lb.2 else ∅)
  have hS_card : S.card ≤ K := by
    have h1 : S.card ≤ C.card +
        ((C ×ˢ (Finset.univ : Finset Bool)).biUnion
          (fun lb => if (outsideNbrs A' C lb.1 lb.2).card ≤ H then outsideNbrs A' C lb.1 lb.2 else ∅)).card :=
      Finset.card_union_le _ _
    have h2 : ((C ×ˢ (Finset.univ : Finset Bool)).biUnion
          (fun lb => if (outsideNbrs A' C lb.1 lb.2).card ≤ H then outsideNbrs A' C lb.1 lb.2 else ∅)).card ≤
        ∑ lb ∈ C ×ˢ (Finset.univ : Finset Bool),
          (if (outsideNbrs A' C lb.1 lb.2).card ≤ H then outsideNbrs A' C lb.1 lb.2 else ∅).card :=
      Finset.card_biUnion_le
    have h3 : (∑ lb ∈ C ×ˢ (Finset.univ : Finset Bool),
          (if (outsideNbrs A' C lb.1 lb.2).card ≤ H then outsideNbrs A' C lb.1 lb.2 else ∅).card) ≤
        ∑ _lb ∈ C ×ˢ (Finset.univ : Finset Bool), H := by
      refine Finset.sum_le_sum (fun lb _ => ?_)
      split_ifs with hleH
      · exact hleH
      · simp
    have h4 : (∑ _lb ∈ C ×ˢ (Finset.univ : Finset Bool), H) = 2 * C.card * H := by
      simp only [Finset.sum_const, Finset.card_product, Finset.card_univ, Fintype.card_bool,
        smul_eq_mul]
      ring
    have h5 : 2 * C.card * H ≤ 2 * c * H :=
      Nat.mul_le_mul_right H (Nat.mul_le_mul_left 2 hC_le)
    dsimp only [K]
    omega
  have hpins_in_S : ∀ l ∈ pins, l.1 ∈ S := by
    intro l hl
    have hlC : l.1 ∈ C := (Finset.mem_product.mp (Finset.mem_filter.mp hl).1).1
    exact Finset.mem_union_left _ hlC
  have hB_in_S : ∀ cl ∈ B, cl.1.1 ∈ S ∧ cl.2.1 ∈ S := by
    intro cl hcl
    rcases Finset.mem_union.mp hcl with hkeep | hpin
    · simp only [Bkeep, Finset.mem_filter] at hkeep
      rcases hkeep with ⟨hclA', hnp1, hnp2⟩
      by_cases h1 : cl.1.1 ∈ C
      · by_cases h2 : cl.2.1 ∈ C
        · exact ⟨Finset.mem_union_left _ h1, Finset.mem_union_left _ h2⟩
        · refine ⟨Finset.mem_union_left _ h1, Finset.mem_union_right _ ?_⟩
          have hleH : (outsideNbrs A' C cl.1.1 cl.1.2).card ≤ H := by
            by_contra hgt
            apply hnp1
            refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨h1, Finset.mem_univ _⟩, ?_⟩
            simpa using (show H < (outsideNbrs A' C cl.1.1 cl.1.2).card by omega)
          refine Finset.mem_biUnion.mpr ⟨(cl.1.1, cl.1.2), Finset.mem_product.mpr ⟨h1, Finset.mem_univ _⟩, ?_⟩
          dsimp only
          simp only [hleH, ↓reduceIte]
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2, cl, hclA', Or.inl ⟨rfl, rfl⟩⟩
      · have h2 : cl.2.1 ∈ C := (hcov cl hclA').resolve_left h1
        refine ⟨Finset.mem_union_right _ ?_, Finset.mem_union_left _ h2⟩
        have hleH : (outsideNbrs A' C cl.2.1 cl.2.2).card ≤ H := by
          by_contra hgt
          apply hnp2
          refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨h2, Finset.mem_univ _⟩, ?_⟩
          simpa using (show H < (outsideNbrs A' C cl.2.1 cl.2.2).card by omega)
        refine Finset.mem_biUnion.mpr ⟨(cl.2.1, cl.2.2), Finset.mem_product.mpr ⟨h2, Finset.mem_univ _⟩, ?_⟩
        dsimp only
        simp only [hleH, ↓reduceIte]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1, cl, hclA', Or.inr ⟨rfl, rfl⟩⟩
    · rcases Finset.mem_image.mp hpin with ⟨l, hl, rfl⟩
      exact ⟨hpins_in_S l hl, hpins_in_S l hl⟩
  have hsat_iff : ∀ z : W n, satFn n B z = true ↔ satFn n A z = true ∧ ∀ l ∈ pins, z l.1 = l.2 := by
    intro z
    rw [← satFn_stripTaut A z]
    simp only [satFn, decide_eq_true_eq]
    constructor
    · intro hB
      have hpins_z : ∀ l ∈ pins, z l.1 = l.2 := by
        intro l hl
        have hclB : ((l.1, !l.2), (l.1, !l.2)) ∈ B :=
          Finset.mem_union_right _ (Finset.mem_image.mpr ⟨l, hl, rfl⟩)
        have hz := hB _ hclB
        have hne : z l.1 ≠ !l.2 := by rcases hz with h | h <;> exact h
        exact (bool_ne_not_iff (z l.1) l.2).mp hne
      refine ⟨?_, hpins_z⟩
      intro cl hcl
      by_cases h1 : (cl.1.1, !cl.1.2) ∈ pins
      · left
        have hz : z cl.1.1 = !cl.1.2 := hpins_z _ h1
        exact (bool_ne_iff_eq_not (z cl.1.1) cl.1.2).mpr hz
      · by_cases h2 : (cl.2.1, !cl.2.2) ∈ pins
        · right
          have hz : z cl.2.1 = !cl.2.2 := hpins_z _ h2
          exact (bool_ne_iff_eq_not (z cl.2.1) cl.2.2).mpr hz
        · exact hB cl (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hcl, h1, h2⟩))
    · rintro ⟨hA', hpins_z⟩ cl hcl
      rcases Finset.mem_union.mp hcl with hkeep | hpin
      · exact hA' cl (Finset.mem_filter.mp hkeep).1
      · rcases Finset.mem_image.mp hpin with ⟨l, hl, rfl⟩
        left
        exact (bool_ne_not_iff (z l.1) l.2).mpr (hpins_z l hl)
  have hmassB_ge : Mpre ≤ massFn n B := by
    let Sgood := Ssurv.filter (fun σ => fiberExp A' C σ ≤ E)
    have hMpre_cards : Mpre = ∑ σ ∈ Sgood,
        (Finset.univ.filter (fun x : W n => (∀ i : C, x i.1 = σ i) ∧ satFn n A x = true)).card := by
      refine Finset.sum_congr rfl (fun σ hσ => ?_)
      have hsurv : survives (stripTaut A) C σ := (Finset.mem_filter.mp (Finset.mem_filter.mp hσ).1).2
      rw [fiber_card_eq A C hcov σ]
      simp only [hsurv, ↓reduceIte]
      rfl
    rw [hMpre_cards]
    have hsub : Sgood.biUnion (fun σ =>
        Finset.univ.filter (fun x : W n => (∀ i : C, x i.1 = σ i) ∧ satFn n A x = true)) ⊆
        Finset.univ.filter (fun x : W n => satFn n B x = true) := by
      intro x hx
      rcases Finset.mem_biUnion.mp hx with ⟨σ, hσ, hxσ⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hxσ ⊢
      rw [hsat_iff]
      refine ⟨hxσ.2, ?_⟩
      intro l hl
      have hlC : l.1 ∈ C := (Finset.mem_product.mp (Finset.mem_filter.mp hl).1).1
      have hheavy : H < (outsideNbrs A' C l.1 (!l.2)).card := (Finset.mem_filter.mp hl).2
      have hleE : fiberExp A' C σ ≤ E := (Finset.mem_filter.mp hσ).2
      rw [hxσ.1 ⟨l.1, hlC⟩]
      by_contra hne
      have hσ_eq : σ ⟨l.1, hlC⟩ = !l.2 := (bool_ne_iff_eq_not _ _).mp hne
      have hsub_fv := outsideNbrs_subset_forcedVars A' C σ l.1 hlC (!l.2) hσ_eq
      have hcard_le : (outsideNbrs A' C l.1 (!l.2)).card ≤ (forcedVars A' C σ).card :=
        Finset.card_le_card hsub_fv
      have hfexp : (forcedVars A' C σ).card ≤ fiberExp A' C σ := Nat.le_add_left _ _
      omega
    have hdisj : Set.PairwiseDisjoint (Sgood : Set (C → Bool)) (fun σ =>
        Finset.univ.filter (fun x : W n => (∀ i : C, x i.1 = σ i) ∧ satFn n A x = true)) := by
      intro σ1 _ σ2 _ hne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx1 hx2
      apply hne
      funext i
      rw [← hx1.1 i, hx2.1 i]
    rw [← Finset.card_biUnion hdisj]
    exact Finset.card_le_card hsub
  have hmassB_pq : p * 2 ^ n ≤ q * massFn n B :=
    hMpre_ge.trans (Nat.mul_le_mul_left q hmassB_ge)
  exact ⟨S, pins, B, hS_card, hpins_in_S, hB_in_S, hmassB_pq, hsat_iff⟩

theorem main_conj2 {p q n : ℕ} (hp : 0 < p) (hpq : p ≤ q) (A : F n)
    (hlt : q * massFn n A < p * 2 ^ n) :
    let c := 6 * (1 + Nat.clog 2 ((q + p - 1) / p))
    let H := 2 ^ c * (Nat.clog 2 q + c + 1)
    q * massFn n A * 2 ^ (H + 1) + 2 ^ n ≤ p * 2 ^ n * 2 ^ (H + 1) := by
  classical
  dsimp only
  let c := 6 * (1 + Nat.clog 2 ((q + p - 1) / p))
  let D := Nat.clog 2 q + c + 1
  let H := 2 ^ c * D
  let A' := stripTaut A
  by_cases hsmall : 2 * q * massFn n A ≤ p * 2 ^ n
  · have h1 : q * massFn n A * 2 ^ (H + 1) ≤ p * 2 ^ n * 2 ^ H := by
      calc q * massFn n A * 2 ^ (H + 1) = (2 * q * massFn n A) * 2 ^ H := by
            rw [pow_succ]; ring
        _ ≤ (p * 2 ^ n) * 2 ^ H := Nat.mul_le_mul_right _ hsmall
    have h2 : 2 ^ n ≤ p * 2 ^ n * 2 ^ H := by
      have h1le : 1 ≤ p * 2 ^ H := Nat.mul_pos hp (by positivity)
      calc 2 ^ n = 2 ^ n * 1 := (mul_one _).symm
        _ ≤ 2 ^ n * (p * 2 ^ H) := Nat.mul_le_mul_left _ h1le
        _ = p * 2 ^ n * 2 ^ H := by ring
    calc q * massFn n A * 2 ^ (H + 1) + 2 ^ n
        ≤ p * 2 ^ n * 2 ^ H + p * 2 ^ n * 2 ^ H := Nat.add_le_add h1 h2
      _ = p * 2 ^ n * 2 ^ (H + 1) := by rw [pow_succ]; ring
  · have hlarge : p * 2 ^ n < 2 * q * massFn n A := by omega
    obtain ⟨C, hC_le, hcov⟩ := exists_cover_of_large_mass hp A hlarge
    obtain ⟨E, hE_le_H, hE_le_n, hmass_eq, ⟨U, hU⟩, htail⟩ :=
      gap_split_bounds hp hpq A C hC_le hcov
    let Ssurv := Finset.univ.filter (fun σ : C → Bool => survives A' C σ)
    let Mpre := ∑ σ ∈ Ssurv.filter (fun σ => fiberExp A' C σ ≤ E), 2 ^ (n - fiberExp A' C σ)
    let Mtail := ∑ σ ∈ Ssurv.filter (fun σ => E < fiberExp A' C σ), 2 ^ (n - fiberExp A' C σ)
    have hE_le_H' : E ≤ H := hE_le_H
    have hmass_eq' : massFn n A = Mpre + Mtail := hmass_eq
    have htail4 : 4 * (q * Mtail * 2 ^ E) ≤ 2 ^ n := by
      calc 4 * (q * Mtail * 2 ^ E) = 4 * q * Mtail * 2 ^ E := by ring
        _ ≤ 2 ^ n := htail
    have hMpre_lt : q * Mpre < p * 2 ^ n := by
      have hle : Mpre ≤ massFn n A := by omega
      have hqle : q * Mpre ≤ q * massFn n A := Nat.mul_le_mul_left q hle
      omega
    have hmul : q * U * 2 ^ n < p * 2 ^ E * 2 ^ n := by
      calc q * U * 2 ^ n = q * (U * 2 ^ n) := by ring
        _ = q * (Mpre * 2 ^ E) := by rw [← hU]
        _ = (q * Mpre) * 2 ^ E := by ring
        _ < (p * 2 ^ n) * 2 ^ E := Nat.mul_lt_mul_of_pos_right hMpre_lt (by positivity)
        _ = p * 2 ^ E * 2 ^ n := by ring
    have hqU_lt : q * U < p * 2 ^ E := Nat.lt_of_mul_lt_mul_right hmul
    have hqU_le : q * U + 1 ≤ p * 2 ^ E := hqU_lt
    have hgap_pre : q * Mpre * 2 ^ E + 2 ^ n ≤ p * 2 ^ n * 2 ^ E := by
      calc q * Mpre * 2 ^ E + 2 ^ n = q * (Mpre * 2 ^ E) + 2 ^ n := by ring
        _ = q * (U * 2 ^ n) + 2 ^ n := by rw [hU]
        _ = (q * U + 1) * 2 ^ n := by ring
        _ ≤ (p * 2 ^ E) * 2 ^ n := Nat.mul_le_mul_right _ hqU_le
        _ = p * 2 ^ n * 2 ^ E := by ring
    have htail2 : 2 * q * Mtail * 2 ^ E ≤ 2 ^ n := by
      calc 2 * q * Mtail * 2 ^ E = 2 * (q * Mtail * 2 ^ E) := by ring
        _ ≤ 2 ^ n := by omega
    have hE_gap : q * massFn n A * 2 ^ (E + 1) + 2 ^ n ≤ p * 2 ^ n * 2 ^ (E + 1) := by
      calc q * massFn n A * 2 ^ (E + 1) + 2 ^ n
          = 2 * (q * Mpre * 2 ^ E) + (2 * q * Mtail * 2 ^ E) + 2 ^ n := by
            rw [hmass_eq', pow_succ]; ring
        _ ≤ 2 * (q * Mpre * 2 ^ E) + 2 ^ n + 2 ^ n := by omega
        _ = 2 * (q * Mpre * 2 ^ E + 2 ^ n) := by ring
        _ ≤ 2 * (p * 2 ^ n * 2 ^ E) := Nat.mul_le_mul_left 2 hgap_pre
        _ = p * 2 ^ n * 2 ^ (E + 1) := by rw [pow_succ]; ring
    have hpow_diff : 1 ≤ 2 ^ (H - E) := Nat.one_le_pow _ _ (by omega)
    have hpow_split : 2 ^ (H + 1) = 2 ^ (E + 1) * 2 ^ (H - E) := by
      rw [← pow_add]
      congr 1
      omega
    calc q * massFn n A * 2 ^ (H + 1) + 2 ^ n
        ≤ q * massFn n A * 2 ^ (H + 1) + 2 ^ n * 2 ^ (H - E) :=
          Nat.add_le_add_left (Nat.le_mul_of_pos_right _ hpow_diff) _
      _ = (q * massFn n A * 2 ^ (E + 1) + 2 ^ n) * 2 ^ (H - E) := by
          rw [hpow_split]; ring
      _ ≤ (p * 2 ^ n * 2 ^ (E + 1)) * 2 ^ (H - E) := Nat.mul_le_mul_right _ hE_gap
      _ = p * 2 ^ n * 2 ^ (H + 1) := by rw [hpow_split]; ring

theorem main : (let W := fun width : ℕ => Fin width → Bool
let Lit := fun width : ℕ => Fin width × Bool
let F := fun width : ℕ => Finset (Lit width × Lit width)
let sat := fun (len : ℕ) (A : F len) (word : W len) => decide (∀ c ∈ A,
  word c.1.1 ≠ c.1.2 ∨ word c.2.1 ≠ c.2.2)
let mass := fun (len : ℕ) (A : F len) =>
  (Finset.univ.filter (fun x : W len => sat len A x = true)).card
∀ p q : ℕ, 0 < p → p ≤ q →
  let c := 6 * (1 + Nat.clog 2 ((q + p - 1) / p))
  let H := 2 ^ c * (Nat.clog 2 q + c + 1)
  let K := c + 2 * c * H
  ∀ (n : ℕ) (A : F n),
    (p * 2 ^ n ≤ q * mass n A →
      ∃ (S : Finset (Fin n)) (pins : Finset (Lit n)) (B : F n),
        S.card ≤ K ∧ (∀ l ∈ pins, l.1 ∈ S) ∧
        (∀ cl ∈ B, cl.1.1 ∈ S ∧ cl.2.1 ∈ S) ∧ p * 2 ^ n ≤ q * mass n B ∧
        ∀ z : W n, sat n B z = true ↔ sat n A z = true ∧ ∀ l ∈ pins, z l.1 = l.2) ∧
    (q * mass n A < p * 2 ^ n →
      q * mass n A * 2 ^ (H + 1) + 2 ^ n ≤ p * 2 ^ n * 2 ^ (H + 1))) := by
  dsimp only
  intro p q hp hpq n A
  exact ⟨main_conj1 hp hpq A, main_conj2 hp hpq A⟩

end PEqualNP.Outside.L_lib_669_aux

theorem PEqualNP.Outside.L_lib_669 : (let W := fun width : ℕ => Fin width → Bool
let Lit := fun width : ℕ => Fin width × Bool
let F := fun width : ℕ => Finset (Lit width × Lit width)
let sat := fun (len : ℕ) (A : F len) (word : W len) => decide (∀ c ∈ A,
  word c.1.1 ≠ c.1.2 ∨ word c.2.1 ≠ c.2.2)
let mass := fun (len : ℕ) (A : F len) =>
  (Finset.univ.filter (fun x : W len => sat len A x = true)).card
∀ p q : ℕ, 0 < p → p ≤ q →
  let c := 6 * (1 + Nat.clog 2 ((q + p - 1) / p))
  let H := 2 ^ c * (Nat.clog 2 q + c + 1)
  let K := c + 2 * c * H
  ∀ (n : ℕ) (A : F n),
    (p * 2 ^ n ≤ q * mass n A →
      ∃ (S : Finset (Fin n)) (pins : Finset (Lit n)) (B : F n),
        S.card ≤ K ∧ (∀ l ∈ pins, l.1 ∈ S) ∧
        (∀ cl ∈ B, cl.1.1 ∈ S ∧ cl.2.1 ∈ S) ∧ p * 2 ^ n ≤ q * mass n B ∧
        ∀ z : W n, sat n B z = true ↔ sat n A z = true ∧ ∀ l ∈ pins, z l.1 = l.2) ∧
    (q * mass n A < p * 2 ^ n →
      q * mass n A * 2 ^ (H + 1) + 2 ^ n ≤ p * 2 ^ n * 2 ^ (H + 1))) :=
  PEqualNP.Outside.L_lib_669_aux.main
