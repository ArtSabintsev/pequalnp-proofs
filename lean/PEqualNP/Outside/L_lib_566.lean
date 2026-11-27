import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_566_aux

private def upMove (d : ℕ) (A B : Finset ℕ) : Prop :=
  B.card ≤ d ∧ ∃ i : ℕ, 0 < i ∧ i ∉ A ∧ B = insert i A ∧ (i = 1 ∨ i - 1 ∈ A)

private def stepMove (d : ℕ) (U V : Finset ℕ) : Prop :=
  upMove d U V ∨ upMove d V U

private def reachSet (d : ℕ) (S : Finset ℕ) : Prop :=
  Relation.ReflTransGen (stepMove d) ∅ S

private def extSet (d t : ℕ) : Finset ℕ :=
  (Finset.range t).image (fun j => 2 ^ d - 2 ^ (d - (j + 1)))

private def leftPred (S : Finset ℕ) (x : ℕ) : ℕ :=
  (S.filter (fun y => y < x)).sup id

private inductive Clearable (d : ℕ) : Finset ℕ → Prop
  | empty : Clearable d ∅
  | step (S : Finset ℕ) (x : ℕ) :
      S.card ≤ d → (∀ y ∈ S, 0 < y) → x ∈ S →
      x - leftPred S x ≤ 2 ^ (d - S.card) →
      Clearable d (S.erase x) →
      Clearable d S

private lemma leftPred_lt {S : Finset ℕ} {x : ℕ} (hx : 0 < x) : leftPred S x < x := by
  unfold leftPred
  by_cases hemp : (S.filter (fun y => y < x)) = ∅
  · rw [hemp, Finset.sup_empty]
    exact hx
  · have hne : (S.filter (fun y => y < x)).Nonempty := Finset.nonempty_iff_ne_empty.mpr hemp
    have hlt : (S.filter (fun y => y < x)).sup id < x := by
      rw [Finset.sup_lt_iff hx]
      intro y hy
      exact (Finset.mem_filter.mp hy).2
    exact hlt

private lemma leftPred_mem_or_zero (S : Finset ℕ) (x : ℕ) :
    leftPred S x = 0 ∨ leftPred S x ∈ S := by
  unfold leftPred
  by_cases hemp : (S.filter (fun y => y < x)) = ∅
  · left
    rw [hemp, Finset.sup_empty]
    rfl
  · right
    have hne : (S.filter (fun y => y < x)).Nonempty := Finset.nonempty_iff_ne_empty.mpr hemp
    rcases Finset.exists_mem_eq_sup _ hne id with ⟨m, hm, hsup⟩
    rw [hsup]
    exact (Finset.mem_filter.mp hm).1

private lemma le_leftPred {S : Finset ℕ} {x y : ℕ} (hy : y ∈ S) (hxy : y < x) :
    y ≤ leftPred S x := by
  unfold leftPred
  exact Finset.le_sup (f := id) (Finset.mem_filter.mpr ⟨hy, hxy⟩)

private lemma leftPred_le_of_subset {A B : Finset ℕ} (hAB : A ⊆ B) (x : ℕ) :
    leftPred A x ≤ leftPred B x := by
  unfold leftPred
  exact Finset.sup_mono (Finset.filter_subset_filter _ hAB)

private lemma leftPred_erase_ne {S : Finset ℕ} {x y : ℕ} (hne : x ≠ leftPred S y)
    (hy : 0 < y) : leftPred (S.erase x) y = leftPred S y := by
  apply le_antisymm
  · exact leftPred_le_of_subset (Finset.erase_subset x S) y
  · rcases leftPred_mem_or_zero S y with h0 | hmem
    · rw [h0]
      exact Nat.zero_le _
    · exact le_leftPred (Finset.mem_erase.mpr ⟨Ne.symm hne, hmem⟩) (leftPred_lt hy)

private lemma leftPred_erase_eq {S : Finset ℕ} {x y : ℕ} (heq : x = leftPred S y)
    (hx : 0 < x) (hy : 0 < y) : leftPred (S.erase x) y = leftPred S x := by
  have hxy : x < y := by
    rw [heq]
    exact leftPred_lt hy
  apply le_antisymm
  · unfold leftPred
    rw [Finset.sup_le_iff]
    intro z hz
    have hzm : z ∈ S.erase x := (Finset.mem_filter.mp hz).1
    have hzy : z < y := (Finset.mem_filter.mp hz).2
    have hzx_ne : z ≠ x := (Finset.mem_erase.mp hzm).1
    have hzS : z ∈ S := (Finset.mem_erase.mp hzm).2
    have hle : z ≤ x := by
      rw [heq]
      exact le_leftPred hzS hzy
    have hzx : z < x := lt_of_le_of_ne hle hzx_ne
    exact Finset.le_sup (f := id) (Finset.mem_filter.mpr ⟨hzS, hzx⟩)
  · rcases leftPred_mem_or_zero S x with h0 | hmem
    · rw [h0]
      exact Nat.zero_le _
    · have hlt_x : leftPred S x < x := leftPred_lt hx
      have hne : leftPred S x ≠ x := Nat.ne_of_lt hlt_x
      exact le_leftPred (Finset.mem_erase.mpr ⟨hne, hmem⟩) (lt_trans hlt_x hxy)

private lemma gap_erase_le {S : Finset ℕ} {x y k : ℕ}
    (hpos : ∀ z ∈ S, 0 < z) (hxS : x ∈ S) (hyS : y ∈ S)
    (hgx : x - leftPred S x ≤ 2 ^ k) (hgy : y - leftPred S y ≤ 2 ^ k) :
    y - leftPred (S.erase x) y ≤ 2 ^ (k + 1) := by
  have hx : 0 < x := hpos x hxS
  have hy : 0 < y := hpos y hyS
  by_cases hne : x = leftPred S y
  · rw [leftPred_erase_eq hne hx hy]
    have hxy : x < y := hne ▸ leftPred_lt hy
    have hpx : leftPred S x < x := leftPred_lt hx
    rw [← hne] at hgy
    rw [pow_succ]
    omega
  · rw [leftPred_erase_ne hne hy, pow_succ]
    omega

private lemma clearable_erase {d : ℕ} {S : Finset ℕ} (hC : Clearable d S) :
    ∀ {x : ℕ}, x ∈ S → x - leftPred S x ≤ 2 ^ (d - S.card) → Clearable d (S.erase x) := by
  induction hC with
  | empty =>
    intro x hx
    exact False.elim (Finset.notMem_empty x hx)
  | step S y hcard hpos hyS hgy hCy ih =>
    intro x hxS hgx
    by_cases hxy : x = y
    · subst hxy
      exact hCy
    · have hy_erx : y ∈ S.erase x := Finset.mem_erase.mpr ⟨Ne.symm hxy, hyS⟩
      have hx_ery : x ∈ S.erase y := Finset.mem_erase.mpr ⟨hxy, hxS⟩
      have hcard_erx : (S.erase x).card = S.card - 1 := Finset.card_erase_of_mem hxS
      have hcard_ery : (S.erase y).card = S.card - 1 := Finset.card_erase_of_mem hyS
      have hSpos : 0 < S.card := Finset.card_pos.mpr ⟨x, hxS⟩
      have hdiff_x : d - (S.erase x).card = (d - S.card) + 1 := by omega
      have hdiff_y : d - (S.erase y).card = (d - S.card) + 1 := by omega
      have hgap_y : y - leftPred (S.erase x) y ≤ 2 ^ (d - (S.erase x).card) := by
        rw [hdiff_x]
        exact gap_erase_le hpos hxS hyS hgx hgy
      have hgap_x : x - leftPred (S.erase y) x ≤ 2 ^ (d - (S.erase y).card) := by
        rw [hdiff_y]
        exact gap_erase_le hpos hyS hxS hgy hgx
      have hboth : Clearable d ((S.erase y).erase x) := ih hx_ery hgap_x
      rw [Finset.erase_right_comm] at hboth
      exact Clearable.step (S.erase x) y (by omega)
        (fun z hz => hpos z (Finset.mem_of_mem_erase hz)) hy_erx hgap_y hboth

private lemma clearable_card_le {d : ℕ} {S : Finset ℕ} (hC : Clearable d S) : S.card ≤ d := by
  cases hC with
  | empty => exact Nat.zero_le d
  | step _ _ hcard _ _ _ _ => exact hcard

private lemma clearable_pos {d : ℕ} {S : Finset ℕ} (hC : Clearable d S) :
    ∀ y ∈ S, 0 < y := by
  cases hC with
  | empty =>
    intro y hy
    exact False.elim (Finset.notMem_empty y hy)
  | step _ _ _ hpos _ _ _ => exact hpos

private lemma reach_clearable {d : ℕ} {S : Finset ℕ} (hR : reachSet d S) : Clearable d S := by
  unfold reachSet at hR
  induction hR with
  | refl => exact Clearable.empty
  | @tail B C _ hstep ih =>
    rcases hstep with ⟨hBcard, i, hipos, hiA, rfl, hprev⟩ | ⟨hAcard, i, hipos, hiB, hAeq, hprev⟩
    · have hi_mem : i ∈ insert i B := Finset.mem_insert_self i B
      have hpos_B : ∀ y ∈ insert i B, 0 < y := by
        intro y hy
        rcases Finset.mem_insert.mp hy with rfl | hyA
        · exact hipos
        · exact clearable_pos ih y hyA
      have hgap1 : i - leftPred (insert i B) i ≤ 1 := by
        rcases hprev with rfl | hpre
        · have h0 : leftPred (insert 1 B) 1 = 0 := by
            have := leftPred_lt (S := insert 1 B) (x := 1) (by omega)
            omega
          omega
        · have hle : i - 1 ≤ leftPred (insert i B) i :=
            le_leftPred (Finset.mem_insert_of_mem hpre) (by omega)
          omega
      have hgap : i - leftPred (insert i B) i ≤ 2 ^ (d - (insert i B).card) :=
        le_trans hgap1 (Nat.one_le_pow _ 2 (by omega))
      have herase : (insert i B).erase i = B := Finset.erase_insert hiA
      exact Clearable.step (insert i B) i hBcard hpos_B hi_mem hgap (by rwa [herase])
    · subst hAeq
      have hi_mem : i ∈ insert i C := Finset.mem_insert_self i C
      have hgap1 : i - leftPred (insert i C) i ≤ 1 := by
        rcases hprev with rfl | hpre
        · have h0 : leftPred (insert 1 C) 1 = 0 := by
            have := leftPred_lt (S := insert 1 C) (x := 1) (by omega)
            omega
          omega
        · have hle : i - 1 ≤ leftPred (insert i C) i :=
            le_leftPred (Finset.mem_insert_of_mem hpre) (by omega)
          omega
      have hgap : i - leftPred (insert i C) i ≤ 2 ^ (d - (insert i C).card) :=
        le_trans hgap1 (Nat.one_le_pow _ 2 (by omega))
      have hclear := clearable_erase ih hi_mem hgap
      rwa [Finset.erase_insert hiB] at hclear

private lemma extSet_succ (d t : ℕ) :
    extSet d (t + 1) = insert (2 ^ d - 2 ^ (d - (t + 1))) (extSet d t) := by
  unfold extSet
  rw [Finset.range_add_one, Finset.image_insert]

private lemma extSet_lt_next {d t : ℕ} (ht : t < d) :
    ∀ y ∈ extSet d t, y < 2 ^ d - 2 ^ (d - (t + 1)) := by
  intro y hy
  rcases Finset.mem_image.mp hy with ⟨j, hj, rfl⟩
  have hjt : j < t := Finset.mem_range.mp hj
  have h1 : d - (t + 1) < d - (j + 1) := by omega
  have h2 : 2 ^ (d - (t + 1)) < 2 ^ (d - (j + 1)) :=
    Nat.pow_lt_pow_right (by omega) h1
  have h3 : 2 ^ (d - (j + 1)) ≤ 2 ^ d :=
    Nat.pow_le_pow_right (by omega) (by omega)
  omega

private lemma extSet_card {d t : ℕ} (ht : t ≤ d) : (extSet d t).card = t := by
  induction t with
  | zero => simp [extSet]
  | succ t ih =>
    rw [extSet_succ]
    have hnot : 2 ^ d - 2 ^ (d - (t + 1)) ∉ extSet d t := by
      intro hmem
      exact Nat.lt_irrefl _ (extSet_lt_next (by omega) _ hmem)
    rw [Finset.card_insert_of_notMem hnot, ih (by omega)]

private lemma extSet_sup {d t : ℕ} (ht : t ≤ d) : (extSet d t).sup id = 2 ^ d - 2 ^ (d - t) := by
  induction t with
  | zero => simp [extSet]
  | succ t ih =>
    rw [extSet_succ, Finset.sup_insert, ih (by omega)]
    have h1 : d - (t + 1) ≤ d - t := by omega
    have h2 : 2 ^ (d - (t + 1)) ≤ 2 ^ (d - t) := Nat.pow_le_pow_right (by omega) h1
    have h3 : 2 ^ d - 2 ^ (d - t) ≤ 2 ^ d - 2 ^ (d - (t + 1)) := by omega
    exact max_eq_left h3

private lemma clearable_sup_bound {d : ℕ} {S : Finset ℕ} (hC : Clearable d S) :
    S.sup id ≤ 2 ^ d - 2 ^ (d - S.card) ∧
      (S.sup id = 2 ^ d - 2 ^ (d - S.card) ↔ S = extSet d S.card) := by
  induction hC with
  | empty =>
    simp [extSet]
  | step S x hcard hpos hxS hgx hCer ih =>
    set t := S.card
    have htpos : 0 < t := Finset.card_pos.mpr ⟨x, hxS⟩
    have hcard_er : (S.erase x).card = t - 1 := Finset.card_erase_of_mem hxS
    rw [hcard_er] at ih
    have hpow_step : 2 ^ (d - (t - 1)) = 2 * 2 ^ (d - t) := by
      have hexp : d - (t - 1) = (d - t) + 1 := by omega
      rw [hexp, pow_succ, Nat.mul_comm]
    have hpow_le : 2 ^ (d - (t - 1)) ≤ 2 ^ d := Nat.pow_le_pow_right (by omega) (by omega)
    have hpow_pos : 0 < 2 ^ (d - t) := Nat.pow_pos (by omega)
    have hS_ins : insert x (S.erase x) = S := Finset.insert_erase hxS
    have hsup_eq : S.sup id = max x ((S.erase x).sup id) := by
      conv_lhs => rw [← hS_ins]
      rw [Finset.sup_insert]
      rfl
    have hbound : S.sup id ≤ 2 ^ d - 2 ^ (d - t) := by
      rw [hsup_eq]
      by_cases hle : x ≤ (S.erase x).sup id
      · rw [max_eq_right hle]
        omega
      · push Not at hle
        rw [max_eq_left (le_of_lt hle)]
        have hpred : leftPred S x = (S.erase x).sup id := by
          unfold leftPred
          congr 1
          ext y
          simp only [Finset.mem_filter, Finset.mem_erase]
          constructor
          · rintro ⟨hyS, hyx⟩
            exact ⟨Nat.ne_of_lt hyx, hyS⟩
          · rintro ⟨hyx, hyS⟩
            have hyle : y ≤ (S.erase x).sup id :=
              Finset.le_sup (f := id) (Finset.mem_erase.mpr ⟨hyx, hyS⟩)
            exact ⟨hyS, lt_of_le_of_lt hyle hle⟩
        rw [hpred] at hgx
        omega
    refine ⟨hbound, ?_⟩
    constructor
    · intro heq
      rw [hsup_eq] at heq
      have hgt : (S.erase x).sup id < x := by
        by_contra hnot
        push Not at hnot
        rw [max_eq_right hnot] at heq
        omega
      rw [max_eq_left (le_of_lt hgt)] at heq
      have hpred : leftPred S x = (S.erase x).sup id := by
        unfold leftPred
        congr 1
        ext y
        simp only [Finset.mem_filter, Finset.mem_erase]
        constructor
        · rintro ⟨hyS, hyx⟩
          exact ⟨Nat.ne_of_lt hyx, hyS⟩
        · rintro ⟨hyx, hyS⟩
          have hyle : y ≤ (S.erase x).sup id :=
            Finset.le_sup (f := id) (Finset.mem_erase.mpr ⟨hyx, hyS⟩)
          exact ⟨hyS, lt_of_le_of_lt hyle hgt⟩
      rw [hpred] at hgx
      have her_eq : (S.erase x).sup id = 2 ^ d - 2 ^ (d - (t - 1)) := by omega
      have hSer : S.erase x = extSet d (t - 1) := ih.2.mp her_eq
      rw [← hS_ins, hSer, heq]
      have ht_eq : t = (t - 1) + 1 := by omega
      conv_rhs => rw [ht_eq]
      rw [extSet_succ, ← ht_eq]
    · intro hEq
      rw [hEq]
      exact extSet_sup hcard

private lemma stepMove_symm {d : ℕ} {U V : Finset ℕ} (h : stepMove d U V) : stepMove d V U := by
  rcases h with h1 | h2
  · exact Or.inr h1
  · exact Or.inl h2

private lemma rtg_symm {d : ℕ} {U V : Finset ℕ}
    (h : Relation.ReflTransGen (stepMove d) U V) :
    Relation.ReflTransGen (stepMove d) V U := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
    exact Relation.ReflTransGen.head (stepMove_symm hstep) ih

private lemma stepMove_insert_above {d : ℕ} {U V : Finset ℕ} {z : ℕ}
    (hstep : stepMove d U V) (hU : ∀ y ∈ U, y < z) (hV : ∀ y ∈ V, y < z)
    (hUcard : U.card + 1 ≤ d) (hVcard : V.card + 1 ≤ d) :
    stepMove d (insert z U) (insert z V) := by
  have hzU : z ∉ U := fun h => Nat.lt_irrefl z (hU z h)
  have hzV : z ∉ V := fun h => Nat.lt_irrefl z (hV z h)
  rcases hstep with ⟨_, i, hipos, hiU, hVeq, hprev⟩ | ⟨_, i, hipos, hiV, hUeq, hprev⟩
  · left
    have hiz : i ≠ z := by
      have : i ∈ V := hVeq ▸ Finset.mem_insert_self i U
      exact Nat.ne_of_lt (hV i this)
    refine ⟨by rw [Finset.card_insert_of_notMem hzV]; exact hVcard, i, hipos, ?_, ?_, ?_⟩
    · simp [Finset.mem_insert, hiz, hiU]
    · rw [hVeq, Finset.insert_comm]
    · rcases hprev with rfl | hpre
      · exact Or.inl rfl
      · exact Or.inr (Finset.mem_insert_of_mem hpre)
  · right
    have hiz : i ≠ z := by
      have : i ∈ U := hUeq ▸ Finset.mem_insert_self i V
      exact Nat.ne_of_lt (hU i this)
    refine ⟨by rw [Finset.card_insert_of_notMem hzU]; exact hUcard, i, hipos, ?_, ?_, ?_⟩
    · simp [Finset.mem_insert, hiz, hiV]
    · rw [hUeq, Finset.insert_comm]
    · rcases hprev with rfl | hpre
      · exact Or.inl rfl
      · exact Or.inr (Finset.mem_insert_of_mem hpre)

private lemma bennett_bridge (d : ℕ) :
    ∀ (k : ℕ), 1 ≤ k →
    ∀ (A : Finset ℕ) (base m : ℕ),
      (∀ y ∈ A, y ≤ base) →
      (base = 0 ∨ base ∈ A) →
      A.card + k ≤ d →
      1 ≤ m → m ≤ 2 ^ (k - 1) →
      ∃ seq : List (Finset ℕ),
        seq.head? = some A ∧
        seq.getLast? = some (insert (base + m) A) ∧
        (∀ S ∈ seq, S.card ≤ A.card + k ∧ ∀ y ∈ S, y ≤ base + m) ∧
        seq.IsChain (stepMove d) := by
  intro k
  induction k with
  | zero =>
    intro hk
    omega
  | succ k ih =>
    intro _ A base m hA_le hbase hcard hm1 hm_le
    by_cases hk0 : k = 0
    · subst hk0
      have hm_eq : m = 1 := by simp at hm_le; omega
      subst hm_eq
      have hnot : base + 1 ∉ A := fun h => by have := hA_le (base + 1) h; omega
      have hup : upMove d A (insert (base + 1) A) := by
        refine ⟨by rw [Finset.card_insert_of_notMem hnot]; omega, base + 1, by omega, hnot, rfl, ?_⟩
        rcases hbase with rfl | hmem
        · exact Or.inl rfl
        · exact Or.inr (by simpa using hmem)
      refine ⟨[A, insert (base + 1) A], rfl, rfl, ?_, ?_⟩
      · intro S hS
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hS
        rcases hS with rfl | rfl
        · exact ⟨by omega, fun y hy => le_trans (hA_le y hy) (by omega)⟩
        · refine ⟨le_of_eq (Finset.card_insert_of_notMem hnot), ?_⟩
          intro y hy
          rcases Finset.mem_insert.mp hy with rfl | hyA
          · exact le_rfl
          · exact le_trans (hA_le y hyA) (by omega)
      · simp [List.isChain_cons_cons, stepMove, hup]
    · have hk1 : 1 ≤ k := by omega
      by_cases hsmall : m ≤ 2 ^ (k - 1)
      · rcases ih hk1 A base m hA_le hbase (by omega) hm1 hsmall with
          ⟨seq, hhead, hlast, hbound, hchain⟩
        refine ⟨seq, hhead, hlast, ?_, hchain⟩
        intro S hS
        exact ⟨le_trans (hbound S hS).1 (by omega), (hbound S hS).2⟩
      · set mid := base + 2 ^ (k - 1)
        set rem := m - 2 ^ (k - 1)
        have hpow_k : 2 ^ k = 2 * 2 ^ (k - 1) := by
          conv_lhs => rw [← Nat.sub_add_cancel hk1]
          rw [pow_succ, Nat.mul_comm]
        have hrem1 : 1 ≤ rem := by omega
        have hrem_le : rem ≤ 2 ^ (k - 1) := by simp at hm_le; omega
        have hmid_not : mid ∉ A := by
          intro h
          have := hA_le mid h
          have : 0 < 2 ^ (k - 1) := Nat.pow_pos (by omega)
          omega
        rcases ih hk1 A base (2 ^ (k - 1)) hA_le hbase (by omega)
          (Nat.one_le_pow _ 2 (by omega)) le_rfl with
          ⟨seq1, hhead1, hlast1, hbound1, hchain1⟩
        have hAmid_le : ∀ y ∈ insert mid A, y ≤ mid := by
          intro y hy
          rcases Finset.mem_insert.mp hy with rfl | hyA
          · exact le_rfl
          · exact le_trans (hA_le y hyA) (by omega)
        have hAmid_card : (insert mid A).card + k ≤ d := by
          rw [Finset.card_insert_of_notMem hmid_not]
          omega
        rcases ih hk1 (insert mid A) mid rem hAmid_le (Or.inr (Finset.mem_insert_self mid A))
          hAmid_card hrem1 hrem_le with
          ⟨seq2, hhead2, hlast2, hbound2, hchain2⟩
        have hmid_add : mid + rem = base + m := by omega
        rw [hmid_add] at hlast2 hbound2
        let seq3 := seq1.reverse.map (fun S => insert (base + m) S)
        have hseq1_ne : seq1 ≠ [] := by
          intro h; rw [h] at hhead1; simp at hhead1
        have hseq2_ne : seq2 ≠ [] := by
          intro h; rw [h] at hhead2; simp at hhead2
        have hhead3 : seq3.head? = some (insert (base + m) (insert mid A)) := by
          simp only [seq3, List.head?_map, List.head?_reverse, hlast1, Option.map_some]
          rfl
        have hlast3 : seq3.getLast? = some (insert (base + m) A) := by
          simp only [seq3, List.getLast?_map, List.getLast?_reverse, hhead1, Option.map_some]
        have hchain3 : seq3.IsChain (stepMove d) := by
          have hrev : seq1.reverse.IsChain (stepMove d) := by
            rw [List.isChain_reverse]
            exact hchain1.imp (fun _ _ h => stepMove_symm h)
          have hmem_all : ∀ S ∈ seq1.reverse, S.card + 1 ≤ d ∧ ∀ y ∈ S, y < base + m := by
            intro S hS
            have hS1 : S ∈ seq1 := List.mem_reverse.mp hS
            have hb := hbound1 S hS1
            refine ⟨by omega, fun y hy => lt_of_le_of_lt (hb.2 y hy) (by omega)⟩
          have hmap_chain : ∀ l : List (Finset ℕ),
              l.IsChain (stepMove d) →
              (∀ S ∈ l, S.card + 1 ≤ d ∧ ∀ y ∈ S, y < base + m) →
              (l.map (fun S => insert (base + m) S)).IsChain (stepMove d) := by
            intro l
            induction l with
            | nil => intro _ _; simp
            | cons a l ihl =>
              intro hch hma
              cases l with
              | nil => simp
              | cons b t =>
                simp only [List.map_cons, List.isChain_cons_cons] at hch ⊢
                have ha := hma a (List.mem_cons_self ..)
                have hb := hma b (List.mem_cons_of_mem a (List.mem_cons_self ..))
                exact ⟨stepMove_insert_above hch.1 ha.2 hb.2 ha.1 hb.1,
                  ihl hch.2 (fun S hS => hma S (List.mem_cons_of_mem a hS))⟩
          exact hmap_chain seq1.reverse hrev hmem_all
        have hjoin : ∀ (l1 l2 : List (Finset ℕ)) (x : Finset ℕ),
            l1.getLast? = some x → l2.head? = some x →
            l1.IsChain (stepMove d) → l2.IsChain (stepMove d) →
            ∃ l : List (Finset ℕ),
              l.head? = l1.head? ∧ l.getLast? = l2.getLast? ∧
              (∀ S ∈ l, S ∈ l1 ∨ S ∈ l2) ∧ l.IsChain (stepMove d) := by
          intro l1 l2 x hl1 hl2 hc1 hc2
          cases l2 with
          | nil => simp at hl2
          | cons y t2 =>
            simp only [List.head?_cons, Option.some.injEq] at hl2
            subst hl2
            refine ⟨l1 ++ t2, ?_, ?_, ?_, ?_⟩
            · cases l1 with
              | nil => simp at hl1
              | cons a t1 => simp
            · cases t2 with
              | nil => simpa using hl1
              | cons b t2' =>
                rw [List.getLast?_append_of_ne_nil _ (List.cons_ne_nil b t2')]
                simp
            · intro S hS
              rcases List.mem_append.mp hS with h1 | h2
              · exact Or.inl h1
              · exact Or.inr (List.mem_cons_of_mem y h2)
            · cases t2 with
              | nil => simpa using hc1
              | cons b t2' =>
                rw [List.isChain_append]
                refine ⟨hc1, (List.isChain_cons_cons.mp hc2).2, ?_⟩
                intro a ha c hc
                rw [hl1] at ha
                simp only [Option.mem_def, Option.some.injEq] at ha
                simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hc
                subst ha hc
                exact (List.isChain_cons_cons.mp hc2).1
        rcases hjoin seq1 seq2 (insert mid A) hlast1 hhead2 hchain1 hchain2 with
          ⟨seq12, hhead12, hlast12, hmem12, hchain12⟩
        rcases hjoin seq12 seq3 (insert (base + m) (insert mid A)) (hlast12.trans hlast2) hhead3 hchain12 hchain3 with
          ⟨seq123, hhead123, hlast123, hmem123, hchain123⟩
        refine ⟨seq123, hhead123.trans hhead12 |>.trans hhead1, hlast123.trans hlast3, ?_, hchain123⟩
        intro S hS
        rcases hmem123 S hS with h12 | h3
        · rcases hmem12 S h12 with h1 | h2
          · exact ⟨le_trans (hbound1 S h1).1 (by omega),
              fun y hy => le_trans ((hbound1 S h1).2 y hy) (by omega)⟩
          · have hb := hbound2 S h2
            rw [Finset.card_insert_of_notMem hmid_not] at hb
            exact ⟨by omega, hb.2⟩
        · rcases List.mem_map.mp h3 with ⟨T, hT, rfl⟩
          have hT1 : T ∈ seq1 := List.mem_reverse.mp hT
          have hb := hbound1 T hT1
          refine ⟨le_trans (Finset.card_insert_le _ T) (by omega), ?_⟩
          intro y hy
          rcases Finset.mem_insert.mp hy with rfl | hyT
          · exact le_rfl
          · exact le_trans (hb.2 y hyT) (by omega)

private lemma chain_to_rtg {α : Type*} {R : α → α → Prop} :
    ∀ {l : List α} {a b : α},
      l.head? = some a → l.getLast? = some b → l.IsChain R →
      Relation.ReflTransGen R a b := by
  intro l
  induction l with
  | nil =>
    intro a b ha _ _
    simp at ha
  | cons x t ih =>
    intro a b ha hb hc
    simp only [List.head?_cons, Option.some.injEq] at ha
    subst ha
    cases t with
    | nil =>
      simp only [List.getLast?_singleton, Option.some.injEq] at hb
      subst hb
      exact Relation.ReflTransGen.refl
    | cons y t' =>
      have hc' := List.isChain_cons_cons.mp hc
      have hb' : (y :: t').getLast? = some b := by simpa using hb
      exact Relation.ReflTransGen.head hc'.1 (ih rfl hb' hc'.2)

private lemma reach_extSet (d : ℕ) : ∀ t ≤ d, reachSet d (extSet d t) := by
  intro t
  induction t with
  | zero =>
    intro _
    simp [reachSet, extSet]
    exact Relation.ReflTransGen.refl
  | succ t ih =>
    intro ht
    have hprev := ih (by omega)
    have hk1 : 1 ≤ d - t := by omega
    have hbase_le : ∀ y ∈ extSet d t, y ≤ 2 ^ d - 2 ^ (d - t) := by
      intro y hy
      have hsup := extSet_sup (d := d) (t := t) (by omega)
      rw [← hsup]
      exact Finset.le_sup (f := id) hy
    have hbase_mem : (2 ^ d - 2 ^ (d - t) = 0) ∨ (2 ^ d - 2 ^ (d - t) ∈ extSet d t) := by
      cases t with
      | zero => left; simp
      | succ t' =>
        right
        rw [extSet_succ]
        exact Finset.mem_insert_self _ _
    have hcard : (extSet d t).card + (d - t) ≤ d := by
      rw [extSet_card (by omega)]
      omega
    have hm1 : 1 ≤ 2 ^ (d - t - 1) := Nat.one_le_pow _ 2 (by omega)
    rcases bennett_bridge d (d - t) hk1 (extSet d t) (2 ^ d - 2 ^ (d - t)) (2 ^ (d - t - 1))
      hbase_le hbase_mem hcard hm1 le_rfl with ⟨seq, hhead, hlast, _, hchain⟩
    have hstep := chain_to_rtg hhead hlast hchain
    have hadd : (2 ^ d - 2 ^ (d - t)) + 2 ^ (d - t - 1) = 2 ^ d - 2 ^ (d - (t + 1)) := by
      have hexp : d - t = (d - (t + 1)) + 1 := by omega
      have hsub : d - t - 1 = d - (t + 1) := by omega
      have hle : 2 ^ (d - t) ≤ 2 ^ d := Nat.pow_le_pow_right (by omega) (by omega)
      rw [hexp, pow_succ] at hle
      rw [hsub, hexp, pow_succ]
      omega
    rw [hadd, ← extSet_succ] at hstep
    exact Relation.ReflTransGen.trans hprev hstep

end PEqualNP.Outside.L_lib_566_aux

theorem PEqualNP.Outside.L_lib_566 : (∀ (d t : ℕ), t ≤ d →
  let up := fun A B : Finset ℕ => B.card ≤ d ∧
    ∃ i : ℕ, 0 < i ∧ i ∉ A ∧ B = insert i A ∧ (i = 1 ∨ i-1 ∈ A)
  let reach := fun S : Finset ℕ =>
    Relation.ReflTransGen (fun U V => up U V ∨ up V U) ∅ S
  let limit := 2^d - 2^(d-t)
  let extremal := (Finset.range t).image (fun j => 2^d - 2^(d-(j+1)))
  reach extremal ∧ extremal.card = t ∧ extremal.sup id = limit ∧
    ∀ S : Finset ℕ, reach S → S.card = t →
      S.sup id ≤ limit ∧ (S.sup id = limit ↔ S = extremal)) := by
  intro d t ht up reach limit extremal
  refine ⟨PEqualNP.Outside.L_lib_566_aux.reach_extSet d t ht,
    PEqualNP.Outside.L_lib_566_aux.extSet_card ht,
    PEqualNP.Outside.L_lib_566_aux.extSet_sup ht, ?_⟩
  intro S hR hScard
  have hC := PEqualNP.Outside.L_lib_566_aux.reach_clearable hR
  have hbd := PEqualNP.Outside.L_lib_566_aux.clearable_sup_bound hC
  rw [hScard] at hbd
  exact hbd
