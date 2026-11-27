import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25561_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Represents PEqualNP.NotBracket

private def offsets : Finset ℕ := {0, 1, 4, 6}

private def targets (n : ℕ) : Finset ℕ := {0, 1, n - 3, n - 5}

private def Gfun (n : ℕ) (u v : Fin n) : Bool :=
  decide ((v.val + n - u.val) % n ∈ offsets)

private def mateVal (n : ℕ) (source : Fin n) : ℕ :=
  (n + 1 - source.val) % n

private def mateFin {n : ℕ} (hn : 13 ≤ n) (i : Fin n) : Fin n :=
  ⟨(n + 1 - i.val) % n, Nat.mod_lt _ (by omega)⟩

private theorem mod_two_range {x n : ℕ} (h : x < 2 * n) :
    (x < n ∧ x % n = x) ∨ (n ≤ x ∧ x % n = x - n) := by
  by_cases hlt : x < n
  · exact Or.inl ⟨hlt, Nat.mod_eq_of_lt hlt⟩
  · refine Or.inr ⟨by omega, ?_⟩
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

private theorem mateFin_inv {n : ℕ} (hn : 13 ≤ n) (i : Fin n) :
    mateFin hn (mateFin hn i) = i := by
  ext
  simp only [mateFin]
  have hi : i.val < n := i.isLt
  rcases mod_two_range (x := n + 1 - i.val) (n := n) (by omega) with ⟨h1, hm1⟩ | ⟨h1, hm1⟩
  · rw [hm1]
    rcases mod_two_range (x := n + 1 - (n + 1 - i.val)) (n := n) (by omega) with
      ⟨h2, hm2⟩ | ⟨h2, hm2⟩ <;> rw [hm2] <;> omega
  · rw [hm1]
    rcases mod_two_range (x := n + 1 - (n + 1 - i.val - n)) (n := n) (by omega) with
      ⟨h2, hm2⟩ | ⟨h2, hm2⟩ <;> rw [hm2] <;> omega

private theorem mateFin_sum_mod {n : ℕ} (hn : 13 ≤ n) (i : Fin n) :
    (i.val + (mateFin hn i).val) % n = 1 := by
  simp only [mateFin]
  have hi : i.val < n := i.isLt
  rcases mod_two_range (x := n + 1 - i.val) (n := n) (by omega) with ⟨h1, hm1⟩ | ⟨h1, hm1⟩
  · rw [hm1]
    rcases mod_two_range (x := i.val + (n + 1 - i.val)) (n := n) (by omega) with
      ⟨h2, hm2⟩ | ⟨h2, hm2⟩ <;> rw [hm2] <;> omega
  · rw [hm1]
    rcases mod_two_range (x := i.val + (n + 1 - i.val - n)) (n := n) (by omega) with
      ⟨h2, hm2⟩ | ⟨h2, hm2⟩ <;> rw [hm2] <;> omega

private theorem mateVal_eq_iff {n : ℕ} (hn : 13 ≤ n) (i j : Fin n) :
    mateVal n i = j.val ↔ i = mateFin hn j := by
  constructor
  · intro h
    have h1 : mateFin hn i = j := Fin.ext h
    have h2 := congrArg (mateFin hn) h1
    rwa [mateFin_inv] at h2
  · intro h
    rw [h]
    have h1 := congrArg Fin.val (mateFin_inv hn j)
    simpa [mateVal, mateFin] using h1

private theorem sidon_add_eq :
    ∀ a1 ∈ offsets, ∀ b1 ∈ offsets, ∀ a2 ∈ offsets, ∀ b2 ∈ offsets,
      a1 ≠ b1 → a1 + b2 = a2 + b1 → a1 = a2 ∧ b1 = b2 := by
  decide

private theorem mod_diff_eq_imp_add_eq {n a1 b1 a2 b2 : ℕ} (hn : 13 ≤ n)
    (ha1 : a1 ∈ offsets) (hb1 : b1 ∈ offsets) (ha2 : a2 ∈ offsets) (hb2 : b2 ∈ offsets)
    (heq : (a1 + n - b1) % n = (a2 + n - b2) % n) :
    a1 + b2 = a2 + b1 := by
  have ha1' : a1 ≤ 6 := by simp [offsets] at ha1; omega
  have hb1' : b1 ≤ 6 := by simp [offsets] at hb1; omega
  have ha2' : a2 ≤ 6 := by simp [offsets] at ha2; omega
  have hb2' : b2 ≤ 6 := by simp [offsets] at hb2; omega
  rcases mod_two_range (x := a1 + n - b1) (n := n) (by omega) with ⟨h1, hm1⟩ | ⟨h1, hm1⟩ <;>
  rcases mod_two_range (x := a2 + n - b2) (n := n) (by omega) with ⟨h2, hm2⟩ | ⟨h2, hm2⟩ <;>
  rw [hm1, hm2] at heq <;> omega

private theorem mod_sub_add_cancel {n a b : ℕ} (hn : 0 < n) (ha : a < n) (hb : b < n) :
    (b + (a + n - b) % n) % n = a := by
  rcases mod_two_range (x := a + n - b) (n := n) (by omega) with ⟨h1, hm1⟩ | ⟨h1, hm1⟩
  · rw [hm1]
    rcases mod_two_range (x := b + (a + n - b)) (n := n) (by omega) with
      ⟨h2, hm2⟩ | ⟨h2, hm2⟩ <;> rw [hm2] <;> omega
  · rw [hm1]
    rcases mod_two_range (x := b + (a + n - b - n)) (n := n) (by omega) with
      ⟨h2, hm2⟩ | ⟨h2, hm2⟩ <;> rw [hm2] <;> omega

private theorem mod_add_sub_cancel {n a b : ℕ} (hn : 0 < n) (ha : a < n) (hb : b < n) :
    ((a + b) % n + n - a) % n = b := by
  rcases mod_two_range (x := a + b) (n := n) (by omega) with ⟨h1, hm1⟩ | ⟨h1, hm1⟩
  · rw [hm1]
    rcases mod_two_range (x := a + b + n - a) (n := n) (by omega) with
      ⟨h2, hm2⟩ | ⟨h2, hm2⟩ <;> rw [hm2] <;> omega
  · rw [hm1]
    rcases mod_two_range (x := a + b - n + n - a) (n := n) (by omega) with
      ⟨h2, hm2⟩ | ⟨h2, hm2⟩ <;> rw [hm2] <;> omega

private theorem mod_sub_sub_cancel {n a b : ℕ} (hn : 0 < n) (ha : a < n) (hb : b < n) :
    (a + n - (a + n - b) % n) % n = b := by
  rcases mod_two_range (x := a + n - b) (n := n) (by omega) with ⟨h1, hm1⟩ | ⟨h1, hm1⟩
  · rw [hm1]
    rcases mod_two_range (x := a + n - (a + n - b)) (n := n) (by omega) with
      ⟨h2, hm2⟩ | ⟨h2, hm2⟩ <;> rw [hm2] <;> omega
  · rw [hm1]
    rcases mod_two_range (x := a + n - (a + n - b - n)) (n := n) (by omega) with
      ⟨h2, hm2⟩ | ⟨h2, hm2⟩ <;> rw [hm2] <;> omega

private theorem mod_diff_left {n c i j : ℕ} (hc : c < n) (hi : i < n) (hj : j < n) :
    ((c + n - i) % n + n - (c + n - j) % n) % n = (j + n - i) % n := by
  rcases mod_two_range (x := c + n - i) (n := n) (by omega) with ⟨h1, hm1⟩ | ⟨h1, hm1⟩ <;>
  rcases mod_two_range (x := c + n - j) (n := n) (by omega) with ⟨h2, hm2⟩ | ⟨h2, hm2⟩ <;>
  rw [hm1, hm2] <;>
  rcases mod_two_range (x := j + n - i) (n := n) (by omega) with ⟨h3, hm3⟩ | ⟨h3, hm3⟩ <;>
  rw [hm3]
  · rcases mod_two_range (x := c + n - i + n - (c + n - j)) (n := n) (by omega) with
      ⟨_, hm⟩ | ⟨_, hm⟩ <;> rw [hm] <;> omega
  · rcases mod_two_range (x := c + n - i + n - (c + n - j)) (n := n) (by omega) with
      ⟨_, hm⟩ | ⟨_, hm⟩ <;> rw [hm] <;> omega
  · rcases mod_two_range (x := c + n - i + n - (c + n - j - n)) (n := n) (by omega) with
      ⟨_, hm⟩ | ⟨_, hm⟩ <;> rw [hm] <;> omega
  · rcases mod_two_range (x := c + n - i + n - (c + n - j - n)) (n := n) (by omega) with
      ⟨_, hm⟩ | ⟨_, hm⟩ <;> rw [hm] <;> omega
  · rcases mod_two_range (x := c + n - i - n + n - (c + n - j)) (n := n) (by omega) with
      ⟨_, hm⟩ | ⟨_, hm⟩ <;> rw [hm] <;> omega
  · rcases mod_two_range (x := c + n - i - n + n - (c + n - j)) (n := n) (by omega) with
      ⟨_, hm⟩ | ⟨_, hm⟩ <;> rw [hm] <;> omega
  · rcases mod_two_range (x := c + n - i - n + n - (c + n - j - n)) (n := n) (by omega) with
      ⟨_, hm⟩ | ⟨_, hm⟩ <;> rw [hm] <;> omega
  · rcases mod_two_range (x := c + n - i - n + n - (c + n - j - n)) (n := n) (by omega) with
      ⟨_, hm⟩ | ⟨_, hm⟩ <;> rw [hm] <;> omega

private theorem mod_diff_right {n r i j : ℕ} (hr : r < n) (hi : i < n) (hj : j < n) :
    ((i + n - r) % n + n - (j + n - r) % n) % n = (i + n - j) % n := by
  rcases mod_two_range (x := i + n - r) (n := n) (by omega) with ⟨h1, hm1⟩ | ⟨h1, hm1⟩ <;>
  rcases mod_two_range (x := j + n - r) (n := n) (by omega) with ⟨h2, hm2⟩ | ⟨h2, hm2⟩ <;>
  rw [hm1, hm2] <;>
  rcases mod_two_range (x := i + n - j) (n := n) (by omega) with ⟨h3, hm3⟩ | ⟨h3, hm3⟩ <;>
  rw [hm3]
  · rcases mod_two_range (x := i + n - r + n - (j + n - r)) (n := n) (by omega) with
      ⟨_, hm⟩ | ⟨_, hm⟩ <;> rw [hm] <;> omega
  · rcases mod_two_range (x := i + n - r + n - (j + n - r)) (n := n) (by omega) with
      ⟨_, hm⟩ | ⟨_, hm⟩ <;> rw [hm] <;> omega
  · rcases mod_two_range (x := i + n - r + n - (j + n - r - n)) (n := n) (by omega) with
      ⟨_, hm⟩ | ⟨_, hm⟩ <;> rw [hm] <;> omega
  · rcases mod_two_range (x := i + n - r + n - (j + n - r - n)) (n := n) (by omega) with
      ⟨_, hm⟩ | ⟨_, hm⟩ <;> rw [hm] <;> omega
  · rcases mod_two_range (x := i + n - r - n + n - (j + n - r)) (n := n) (by omega) with
      ⟨_, hm⟩ | ⟨_, hm⟩ <;> rw [hm] <;> omega
  · rcases mod_two_range (x := i + n - r - n + n - (j + n - r)) (n := n) (by omega) with
      ⟨_, hm⟩ | ⟨_, hm⟩ <;> rw [hm] <;> omega
  · rcases mod_two_range (x := i + n - r - n + n - (j + n - r - n)) (n := n) (by omega) with
      ⟨_, hm⟩ | ⟨_, hm⟩ <;> rw [hm] <;> omega
  · rcases mod_two_range (x := i + n - r - n + n - (j + n - r - n)) (n := n) (by omega) with
      ⟨_, hm⟩ | ⟨_, hm⟩ <;> rw [hm] <;> omega

private theorem row_filter_card {n : ℕ} (hn : 13 ≤ n) (i : Fin n) :
    (Finset.univ.filter (fun col : Fin n => Gfun n i col = true)).card = 4 := by
  let f : ℕ → Fin n := fun e => ⟨(i.val + e) % n, Nat.mod_lt _ (by omega)⟩
  have heq : Finset.univ.filter (fun col : Fin n => Gfun n i col = true) = offsets.image f := by
    ext col
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Gfun, decide_eq_true_eq,
      Finset.mem_image, f]
    constructor
    · intro h
      refine ⟨(col.val + n - i.val) % n, h, ?_⟩
      apply Fin.ext
      exact mod_sub_add_cancel (by omega) col.isLt i.isLt
    · rintro ⟨e, he, hcol⟩
      have he6 : e ≤ 6 := by simp [offsets] at he; omega
      have hval : col.val = (i.val + e) % n := (congrArg Fin.val hcol).symm
      rw [hval, mod_add_sub_cancel (by omega) i.isLt (by omega)]
      exact he
  rw [heq, Finset.card_image_of_injOn]
  · decide
  · intro e1 he1 e2 he2 h
    have h1 : e1 ≤ 6 := by simp [offsets] at he1; omega
    have h2 : e2 ≤ 6 := by simp [offsets] at he2; omega
    have hv : (i.val + e1) % n = (i.val + e2) % n := congrArg Fin.val h
    have h1' := mod_add_sub_cancel (n := n) (a := i.val) (b := e1) (by omega) i.isLt (by omega)
    have h2' := mod_add_sub_cancel (n := n) (a := i.val) (b := e2) (by omega) i.isLt (by omega)
    rw [hv] at h1'
    omega

private theorem col_filter_card {n : ℕ} (hn : 13 ≤ n) (j : Fin n) :
    (Finset.univ.filter (fun row : Fin n => Gfun n row j = true)).card = 4 := by
  let f : ℕ → Fin n := fun e => ⟨(j.val + n - e) % n, Nat.mod_lt _ (by omega)⟩
  have heq : Finset.univ.filter (fun row : Fin n => Gfun n row j = true) = offsets.image f := by
    ext row
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Gfun, decide_eq_true_eq,
      Finset.mem_image, f]
    constructor
    · intro h
      refine ⟨(j.val + n - row.val) % n, h, ?_⟩
      apply Fin.ext
      exact mod_sub_sub_cancel (by omega) j.isLt row.isLt
    · rintro ⟨e, he, hrow⟩
      have he6 : e ≤ 6 := by simp [offsets] at he; omega
      have hval : row.val = (j.val + n - e) % n := (congrArg Fin.val hrow).symm
      rw [hval, mod_sub_sub_cancel (by omega) j.isLt (by omega)]
      exact he
  rw [heq, Finset.card_image_of_injOn]
  · decide
  · intro e1 he1 e2 he2 h
    have h1 : e1 ≤ 6 := by simp [offsets] at he1; omega
    have h2 : e2 ≤ 6 := by simp [offsets] at he2; omega
    have hv : (j.val + n - e1) % n = (j.val + n - e2) % n := congrArg Fin.val h
    have h1' := mod_sub_sub_cancel (n := n) (a := j.val) (b := e1) (by omega) j.isLt (by omega)
    have h2' := mod_sub_sub_cancel (n := n) (a := j.val) (b := e2) (by omega) j.isLt (by omega)
    rw [hv] at h1'
    omega

private theorem row_inter_le_one {n : ℕ} (hn : 13 ≤ n) {i j : Fin n} (hij : i ≠ j) :
    ((Finset.univ.filter (fun col : Fin n => Gfun n i col = true)) ∩
      (Finset.univ.filter (fun col : Fin n => Gfun n j col = true))).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro c1 hc1 c2 hc2
  simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and, Gfun,
    decide_eq_true_eq] at hc1 hc2
  set a1 := (c1.val + n - i.val) % n
  set b1 := (c1.val + n - j.val) % n
  set a2 := (c2.val + n - i.val) % n
  set b2 := (c2.val + n - j.val) % n
  have hne_val : i.val ≠ j.val := fun h => hij (Fin.ext h)
  have hd1 : (a1 + n - b1) % n = (j.val + n - i.val) % n :=
    mod_diff_left c1.isLt i.isLt j.isLt
  have hd2 : (a2 + n - b2) % n = (j.val + n - i.val) % n :=
    mod_diff_left c2.isLt i.isLt j.isLt
  have hne1 : a1 ≠ b1 := by
    intro heq
    rw [heq] at hd1
    have hzero : (b1 + n - b1) % n = 0 := by
      have : b1 + n - b1 = n := by omega
      rw [this, Nat.mod_self]
    rw [hzero] at hd1
    rcases mod_two_range (x := j.val + n - i.val) (n := n) (by have := i.isLt; have := j.isLt; omega) with
      ⟨h1, hm1⟩ | ⟨h1, hm1⟩ <;> rw [hm1] at hd1 <;> have := i.isLt <;> have := j.isLt <;> omega
  have hdiff : (a1 + n - b1) % n = (a2 + n - b2) % n := hd1.trans hd2.symm
  have hadd := mod_diff_eq_imp_add_eq hn hc1.1 hc1.2 hc2.1 hc2.2 hdiff
  have ha := (sidon_add_eq a1 hc1.1 b1 hc1.2 a2 hc2.1 b2 hc2.2 hne1 hadd).1
  apply Fin.ext
  have h1 := mod_sub_add_cancel (n := n) (a := c1.val) (b := i.val) (by omega) c1.isLt i.isLt
  have h2 := mod_sub_add_cancel (n := n) (a := c2.val) (b := i.val) (by omega) c2.isLt i.isLt
  change (i.val + a1) % n = c1.val at h1
  change (i.val + a2) % n = c2.val at h2
  rw [← h1, ← h2, ha]

private theorem col_inter_le_one {n : ℕ} (hn : 13 ≤ n) {i j : Fin n} (hij : i ≠ j) :
    ((Finset.univ.filter (fun row : Fin n => Gfun n row i = true)) ∩
      (Finset.univ.filter (fun row : Fin n => Gfun n row j = true))).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro r1 hr1 r2 hr2
  simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and, Gfun,
    decide_eq_true_eq] at hr1 hr2
  set a1 := (i.val + n - r1.val) % n
  set b1 := (j.val + n - r1.val) % n
  set a2 := (i.val + n - r2.val) % n
  set b2 := (j.val + n - r2.val) % n
  have hne_val : i.val ≠ j.val := fun h => hij (Fin.ext h)
  have hd1 : (a1 + n - b1) % n = (i.val + n - j.val) % n :=
    mod_diff_right r1.isLt i.isLt j.isLt
  have hd2 : (a2 + n - b2) % n = (i.val + n - j.val) % n :=
    mod_diff_right r2.isLt i.isLt j.isLt
  have hne1 : a1 ≠ b1 := by
    intro heq
    rw [heq] at hd1
    have hzero : (b1 + n - b1) % n = 0 := by
      have : b1 + n - b1 = n := by omega
      rw [this, Nat.mod_self]
    rw [hzero] at hd1
    rcases mod_two_range (x := i.val + n - j.val) (n := n) (by have := i.isLt; have := j.isLt; omega) with
      ⟨h1, hm1⟩ | ⟨h1, hm1⟩ <;> rw [hm1] at hd1 <;> have := i.isLt <;> have := j.isLt <;> omega
  have hdiff : (a1 + n - b1) % n = (a2 + n - b2) % n := hd1.trans hd2.symm
  have hadd := mod_diff_eq_imp_add_eq hn hr1.1 hr1.2 hr2.1 hr2.2 hdiff
  have ha := (sidon_add_eq a1 hr1.1 b1 hr1.2 a2 hr2.1 b2 hr2.2 hne1 hadd).1
  apply Fin.ext
  have h1 := mod_sub_sub_cancel (n := n) (a := i.val) (b := r1.val) (by omega) i.isLt r1.isLt
  have h2 := mod_sub_sub_cancel (n := n) (a := i.val) (b := r2.val) (by omega) i.isLt r2.isLt
  change (i.val + n - a1) % n = r1.val at h1
  change (i.val + n - a2) % n = r2.val at h2
  rw [← h1, ← h2, ha]

private theorem symm_diff_card_ge_six {α : Type*} [Fintype α] [DecidableEq α]
    (p q : α → Bool)
    (hp : (Finset.univ.filter (fun x => p x = true)).card = 4)
    (hq : (Finset.univ.filter (fun x => q x = true)).card = 4)
    (hint : ((Finset.univ.filter (fun x => p x = true)) ∩
      (Finset.univ.filter (fun x => q x = true))).card ≤ 1) :
    6 ≤ (Finset.univ.filter (fun x => p x ≠ q x)).card := by
  set A := Finset.univ.filter (fun x => p x = true)
  set B := Finset.univ.filter (fun x => q x = true)
  have hsd : Finset.univ.filter (fun x => p x ≠ q x) = (A \ B) ∪ (B \ A) := by
    ext x
    simp only [A, B, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      Finset.mem_sdiff]
    cases p x <;> cases q x <;> decide
  have hdisj : Disjoint (A \ B) (B \ A) := by
    rw [Finset.disjoint_left]
    intro x h1 h2
    exact (Finset.mem_sdiff.mp h1).2 (Finset.mem_sdiff.mp h2).1
  rw [hsd, Finset.card_union_of_disjoint hdisj]
  have h1 : (A \ B).card + (A ∩ B).card = A.card := Finset.card_sdiff_add_card_inter A B
  have h2 : (B \ A).card + (B ∩ A).card = B.card := Finset.card_sdiff_add_card_inter B A
  rw [Finset.inter_comm] at h2
  omega

private theorem part1_rows {n : ℕ} (hn : 13 ≤ n) (i j : Fin n) (hij : i ≠ j) :
    6 ≤ (Finset.univ.filter (fun col => Gfun n i col ≠ Gfun n j col)).card :=
  symm_diff_card_ge_six (Gfun n i) (Gfun n j)
    (row_filter_card hn i) (row_filter_card hn j) (row_inter_le_one hn hij)

private theorem part1_cols {n : ℕ} (hn : 13 ≤ n) (i j : Fin n) (hij : i ≠ j) :
    6 ≤ (Finset.univ.filter (fun row => Gfun n row i ≠ Gfun n row j)).card :=
  symm_diff_card_ge_six (fun row => Gfun n row i) (fun row => Gfun n row j)
    (col_filter_card hn i) (col_filter_card hn j) (col_inter_le_one hn hij)

private theorem part4_not_mono {n : ℕ} (hn : 13 ≤ n) :
    ¬ ∃ accept : Finset (Fin n) → Prop,
      (∀ S T, S ⊆ T → accept S → accept T) ∧
      ∀ u v : Fin n, accept (Finset.univ.filter
        (fun lit : Fin n => lit = u ∨ mateVal n lit = v.val)) ↔ Gfun n u v = true := by
  rintro ⟨accept, hmono, hiff⟩
  let u0 : Fin n := ⟨0, by omega⟩
  let v1 : Fin n := ⟨1, by omega⟩
  let v2 : Fin n := ⟨2, by omega⟩
  have hsub : Finset.univ.filter (fun lit : Fin n => lit = u0 ∨ mateVal n lit = v1.val) ⊆
      Finset.univ.filter (fun lit : Fin n => lit = u0 ∨ mateVal n lit = v2.val) := by
    intro lit hlit
    have hlit' : lit = u0 ∨ mateVal n lit = v1.val := (Finset.mem_filter.mp hlit).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ lit, ?_⟩
    rcases hlit' with h | h
    · exact Or.inl h
    · left
      have hm : (n + 1 - lit.val) % n = 1 := by simpa [v1, mateVal] using h
      have hl : lit.val < n := lit.isLt
      rcases mod_two_range (x := n + 1 - lit.val) (n := n) (by omega) with ⟨_, h2⟩ | ⟨_, h2⟩
      · rw [h2] at hm; exact Fin.ext (show lit.val = 0 by omega)
      · rw [h2] at hm; exact Fin.ext (show lit.val = 0 by omega)
  have hg1 : Gfun n u0 v1 = true := by
    simp only [Gfun, offsets, u0, v1, decide_eq_true_eq, Finset.mem_insert, Finset.mem_singleton]
    have hm : (1 + n - 0) % n = 1 := by
      rcases mod_two_range (x := 1 + n - 0) (n := n) (by omega) with ⟨_, h⟩ | ⟨_, h⟩ <;> rw [h] <;> omega
    right; left; exact hm
  have hg2 : Gfun n u0 v2 = false := by
    simp only [Gfun, offsets, u0, v2, decide_eq_false_iff_not, Finset.mem_insert,
      Finset.mem_singleton]
    have hm : (2 + n - 0) % n = 2 := by
      rcases mod_two_range (x := 2 + n - 0) (n := n) (by omega) with ⟨_, h⟩ | ⟨_, h⟩ <;> rw [h] <;> omega
    rw [hm]; omega
  have ha1 : accept (Finset.univ.filter (fun lit : Fin n => lit = u0 ∨ mateVal n lit = v1.val)) :=
    (hiff u0 v1).mpr hg1
  have ha2 : accept (Finset.univ.filter (fun lit : Fin n => lit = u0 ∨ mateVal n lit = v2.val)) :=
    hmono _ _ hsub ha1
  have ht2 : Gfun n u0 v2 = true := (hiff u0 v2).mp ha2
  rw [hg2] at ht2
  exact Bool.false_ne_true ht2

private theorem Gfun_iff_target {n : ℕ} (hn : 13 ≤ n) (u v : Fin n) :
    Gfun n u v = true ↔ (u.val + (mateFin hn v).val) % n ∈ targets n := by
  simp only [Gfun, offsets, targets, decide_eq_true_eq, Finset.mem_insert, Finset.mem_singleton]
  have hu : u.val < n := u.isLt
  have hv : v.val < n := v.isLt
  have hv' : (mateFin hn v).val < n := (mateFin hn v).isLt
  have hsum : (v.val + (mateFin hn v).val) % n = 1 := mateFin_sum_mod hn v
  rcases mod_two_range (x := v.val + (mateFin hn v).val) (n := n) (by omega) with ⟨_, hm0⟩ | ⟨_, hm0⟩ <;>
  rw [hm0] at hsum <;>
  rcases mod_two_range (x := v.val + n - u.val) (n := n) (by omega) with ⟨_, hm1⟩ | ⟨_, hm1⟩ <;>
  rcases mod_two_range (x := u.val + (mateFin hn v).val) (n := n) (by omega) with ⟨_, hm2⟩ | ⟨_, hm2⟩ <;>
  rw [hm1, hm2] <;> omega

private def runGates (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

private theorem runGates_append (gs1 gs2 : List Gate) (w : List Bool) :
    runGates (gs1 ++ gs2) w = runGates gs2 (runGates gs1 w) :=
  List.foldl_append

private theorem runGates_length (gs : List Gate) (w : List Bool) :
    (runGates gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [runGates]
  | cons g gs ih =>
    simp only [runGates, List.foldl_cons] at ih ⊢
    rw [ih, List.length_append, List.length_cons, List.length_cons, List.length_nil]
    omega

private theorem getD_append_left_lt (w1 w2 : List Bool) (i : ℕ) (hi : i < w1.length) :
    (w1 ++ w2).getD i false = w1.getD i false := by
  rw [List.getD_eq_getElem _ _ (by rw [List.length_append]; omega),
    List.getElem_append_left hi, ← List.getD_eq_getElem _ _ hi]

private theorem getD_append_right_self (w : List Bool) (b : Bool) :
    (w ++ [b]).getD w.length false = b := by
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (le_refl _)]
  simp

private theorem runGates_getD_old (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (runGates gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (runGates gs (w ++ [_])).getD i false = w.getD i false
    rw [ih (w ++ [_]) (by simp; omega)]
    exact getD_append_left_lt w [_] i hi

private theorem runGates_map_reads_old {α : Type*} (l : List α) (f : α → Gate) (w : List Bool)
    (hold : ∀ a ∈ l, ∀ i ∈ (f a).inputs, i < w.length) :
    runGates (l.map f) w =
      w ++ l.map (fun a => (f a).op.eval ((f a).inputs.map fun i => w.getD i false)) := by
  induction l using List.reverseRecOn with
  | nil => simp [runGates]
  | append_singleton l a ih =>
    rw [List.map_append, List.map_singleton, runGates_append,
      ih (fun x hx => hold x (List.mem_append_left _ hx))]
    simp only [runGates, List.foldl_cons, List.foldl_nil, List.map_append, List.map_singleton,
      List.append_assoc]
    congr 2
    congr 1
    congr 1
    apply List.map_congr_left
    intro i hi
    exact getD_append_left_lt w _ i (hold a (List.mem_append_right _ (List.mem_singleton_self a)) i hi)

private def ReadsBackFrom (base : ℕ) (gs : List Gate) : Prop :=
  ∀ j (hj : j < gs.length), ∀ i ∈ gs[j].inputs, i < base + j

private theorem readsBack_of_readsBackFrom (raw : ℕ) (gs : List Gate) (out : ℕ)
    (h : ReadsBackFrom raw gs) :
    ReadsBack raw ⟨gs, out⟩ := by
  intro j hj i hi
  unfold gateAt at hi
  rw [List.getD_eq_getElem gs _ hj] at hi
  exact h j hj i hi

private theorem readsBackFrom_append {base : ℕ} {gs1 gs2 : List Gate}
    (h1 : ReadsBackFrom base gs1) (h2 : ReadsBackFrom (base + gs1.length) gs2) :
    ReadsBackFrom base (gs1 ++ gs2) := by
  intro j hj i hi
  by_cases hlt : j < gs1.length
  · rw [List.getElem_append_left hlt] at hi
    exact h1 j hlt i hi
  · rw [List.getElem_append_right (Nat.not_lt.mp hlt)] at hi
    have hj2 : j - gs1.length < gs2.length := by rw [List.length_append] at hj; omega
    have hlt2 := h2 (j - gs1.length) hj2 i hi
    omega

private def IsFanInTwoGates (gs : List Gate) : Prop :=
  ∀ g ∈ gs,
    g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

private def NoNotGates (gs : List Gate) : Prop :=
  ∀ g ∈ gs, g.op ≠ GateOp.not

private theorem filter_len_eq_zero {gs : List Gate} (p : Gate → Bool)
    (h : ∀ g ∈ gs, p g = false) :
    (gs.filter p).length = 0 := by
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro g hg
  simp [h g hg]

private theorem list_any_congr {α : Type*} (l : List α) {p q : α → Bool}
    (h : ∀ a ∈ l, p a = q a) : l.any p = l.any q := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.any_cons]
    rw [h a (List.mem_cons_self ..), ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

private theorem sum_count_eq_zero_of_ge {gs : List Gate} {bound w : ℕ}
    (hge : ∀ g ∈ gs, ∀ u ∈ g.inputs, bound ≤ u) (hw : w < bound) :
    (gs.map (fun g => g.inputs.count w)).sum = 0 := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    simp only [List.map_cons, List.sum_cons]
    have h1 : g.inputs.count w = 0 := by
      rw [List.count_eq_zero]
      intro hmem
      have := hge g (List.mem_cons_self ..) w hmem
      omega
    rw [h1, Nat.zero_add]
    exact ih (fun g' hg' => hge g' (List.mem_cons_of_mem _ hg'))

private def orChainAcc (base acc : ℕ) : List ℕ → List Gate × ℕ
  | [] => ([], acc)
  | w :: ws =>
    let res := orChainAcc (base + 1) base ws
    (⟨GateOp.or, [acc, w]⟩ :: res.1, res.2)

private theorem orChainAcc_length (base acc : ℕ) (ws : List ℕ) :
    (orChainAcc base acc ws).1.length = ws.length := by
  induction ws generalizing base acc with
  | nil => rfl
  | cons w ws ih => simp [orChainAcc, ih]

private theorem orChainAcc_out_lt (base acc : ℕ) (ws : List ℕ) (hacc : acc < base) :
    (orChainAcc base acc ws).2 < base + ws.length := by
  induction ws generalizing base acc with
  | nil => simpa [orChainAcc] using hacc
  | cons w ws ih =>
    simp only [orChainAcc, List.length_cons]
    have h := ih (base + 1) base (by omega)
    omega

private theorem orChainAcc_out_ge (base acc b : ℕ) (ws : List ℕ)
    (hacc : b ≤ acc) (hbase : b ≤ base) :
    b ≤ (orChainAcc base acc ws).2 := by
  induction ws generalizing base acc with
  | nil => simpa [orChainAcc] using hacc
  | cons w ws ih =>
    simp only [orChainAcc]
    exact ih (base + 1) base hbase (by omega)

private theorem orChainAcc_fanInTwo (base acc : ℕ) (ws : List ℕ) :
    IsFanInTwoGates (orChainAcc base acc ws).1 := by
  induction ws generalizing base acc with
  | nil => intro g hg; cases hg
  | cons w ws ih =>
    intro g hg
    simp only [orChainAcc, List.mem_cons] at hg
    rcases hg with rfl | hg
    · exact ⟨by simp, by simp⟩
    · exact ih (base + 1) base g hg

private theorem orChainAcc_noNot (base acc : ℕ) (ws : List ℕ) :
    NoNotGates (orChainAcc base acc ws).1 := by
  induction ws generalizing base acc with
  | nil => intro g hg; cases hg
  | cons w ws ih =>
    intro g hg
    simp only [orChainAcc, List.mem_cons] at hg
    rcases hg with rfl | hg
    · intro h; cases h
    · exact ih (base + 1) base g hg

private theorem orChainAcc_inputs_ge (base acc b : ℕ) (ws : List ℕ)
    (hacc : b ≤ acc) (hbase : b ≤ base) (hws : ∀ w ∈ ws, b ≤ w) :
    ∀ g ∈ (orChainAcc base acc ws).1, ∀ u ∈ g.inputs, b ≤ u := by
  induction ws generalizing base acc with
  | nil => intro g hg; cases hg
  | cons w ws ih =>
    intro g hg u hu
    simp only [orChainAcc, List.mem_cons] at hg
    rcases hg with rfl | hg
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl
      · exact hacc
      · exact hws u (List.mem_cons_self ..)
    · exact ih (base + 1) base hbase (by omega)
        (fun x hx => hws x (List.mem_cons_of_mem _ hx)) g hg u hu

private theorem orChainAcc_readsBack (base acc : ℕ) (ws : List ℕ)
    (hacc : acc < base) (hws : ∀ w ∈ ws, w < base) :
    ReadsBackFrom base (orChainAcc base acc ws).1 := by
  induction ws generalizing base acc with
  | nil => intro j hj; simp [orChainAcc] at hj
  | cons w ws ih =>
    intro j hj u hu
    cases j with
    | zero =>
      simp only [orChainAcc, List.getElem_cons_zero, List.mem_cons, List.not_mem_nil,
        or_false] at hu
      rcases hu with rfl | rfl
      · omega
      · have := hws u (List.mem_cons_self ..); omega
    | succ j =>
      simp only [orChainAcc, List.getElem_cons_succ] at hu
      have hj' : j < (orChainAcc (base + 1) base ws).1.length := by
        simp only [orChainAcc, List.length_cons] at hj; omega
      have h := ih (base + 1) base (by omega)
        (fun x hx => by have := hws x (List.mem_cons_of_mem _ hx); omega) j hj' u hu
      omega

private theorem orChainAcc_eval (base acc : ℕ) (ws : List ℕ) (W : List Bool)
    (hlen : W.length = base) (hacc : acc < base) (hws : ∀ w ∈ ws, w < base) :
    (runGates (orChainAcc base acc ws).1 W).getD (orChainAcc base acc ws).2 false =
      (W.getD acc false || ws.any (fun w => W.getD w false)) := by
  induction ws generalizing base acc W with
  | nil => simp [orChainAcc, runGates]
  | cons w ws ih =>
    simp only [orChainAcc]
    change (runGates (orChainAcc (base + 1) base ws).1
      (W ++ [GateOp.or.eval ([acc, w].map fun i => W.getD i false)])).getD
      (orChainAcc (base + 1) base ws).2 false = _
    have hval : GateOp.or.eval ([acc, w].map fun i => W.getD i false) =
        (W.getD acc false || W.getD w false) := by
      simp [GateOp.eval]
    rw [hval]
    set W' := W ++ [W.getD acc false || W.getD w false]
    have hlen' : W'.length = base + 1 := by simp [W', hlen]
    have hstep := ih (base + 1) base W' hlen' (by omega)
      (fun x hx => by have := hws x (List.mem_cons_of_mem _ hx); omega)
    rw [hstep]
    have hbase_val : W'.getD base false = (W.getD acc false || W.getD w false) := by
      rw [← hlen]; exact getD_append_right_self W _
    have hany : ws.any (fun x => W'.getD x false) = ws.any (fun x => W.getD x false) := by
      apply list_any_congr
      intro x hx
      have hxlt : x < W.length := by rw [hlen]; exact hws x (List.mem_cons_of_mem _ hx)
      rw [getD_append_left_lt W _ x hxlt]
    rw [hbase_val, hany]
    simp [Bool.or_assoc]

private def orChain (base : ℕ) : List ℕ → List Gate × ℕ
  | [] => ([], base)
  | w :: ws => orChainAcc base w ws

private def isF (n : ℕ) (i : Fin n) : Bool :=
  decide ((2 * i.val) % n ∈ targets n)

private theorem isF_even_iff {n : ℕ} (hn : 13 ≤ n) (heven : n % 2 = 0) (i : Fin n) :
    isF n i = true ↔ i.val = 0 ∨ i.val = n / 2 := by
  simp only [isF, targets, decide_eq_true_eq, Finset.mem_insert, Finset.mem_singleton]
  have hi : i.val < n := i.isLt
  rcases mod_two_range (x := 2 * i.val) (n := n) (by omega) with ⟨_, hm⟩ | ⟨_, hm⟩ <;>
  rw [hm] <;> omega

private theorem isF_odd_iff {n : ℕ} (hn : 13 ≤ n) (hodd : n % 2 = 1) (i : Fin n) :
    isF n i = true ↔
      i.val = 0 ∨ i.val = (n - 5) / 2 ∨ i.val = (n - 3) / 2 ∨ i.val = (n + 1) / 2 := by
  simp only [isF, targets, decide_eq_true_eq, Finset.mem_insert, Finset.mem_singleton]
  have hi : i.val < n := i.isLt
  rcases mod_two_range (x := 2 * i.val) (n := n) (by omega) with ⟨_, hm⟩ | ⟨_, hm⟩ <;>
  rw [hm] <;> omega

private theorem card_F_even {n : ℕ} (hn : 13 ≤ n) (heven : n % 2 = 0) :
    (Finset.univ.filter (fun i : Fin n => isF n i = true)).card = 2 := by
  let a0 : Fin n := ⟨0, by omega⟩
  let a1 : Fin n := ⟨n / 2, by omega⟩
  have heq : Finset.univ.filter (fun i : Fin n => isF n i = true) = {a0, a1} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, Fin.ext_iff, a0, a1]
    exact isF_even_iff hn heven i
  rw [heq, Finset.card_pair]
  intro h
  have := congrArg Fin.val h
  simp only [a0, a1] at this
  omega

private theorem card_F_odd {n : ℕ} (hn : 13 ≤ n) (hodd : n % 2 = 1) :
    (Finset.univ.filter (fun i : Fin n => isF n i = true)).card = 4 := by
  let a0 : Fin n := ⟨0, by omega⟩
  let a1 : Fin n := ⟨(n - 5) / 2, by omega⟩
  let a2 : Fin n := ⟨(n - 3) / 2, by omega⟩
  let a3 : Fin n := ⟨(n + 1) / 2, by omega⟩
  have heq : Finset.univ.filter (fun i : Fin n => isF n i = true) = {a0, a1, a2, a3} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, Fin.ext_iff, a0, a1, a2, a3]
    exact isF_odd_iff hn hodd i
  rw [heq]
  have h01 : a0 ≠ a1 := by intro h; have := congrArg Fin.val h; simp [a0, a1] at this; omega
  have h02 : a0 ≠ a2 := by intro h; have := congrArg Fin.val h; simp [a0, a2] at this; omega
  have h03 : a0 ≠ a3 := by intro h; have := congrArg Fin.val h; simp [a0, a3] at this; omega
  have h12 : a1 ≠ a2 := by intro h; have := congrArg Fin.val h; simp [a1, a2] at this; omega
  have h13 : a1 ≠ a3 := by intro h; have := congrArg Fin.val h; simp [a1, a3] at this; omega
  have h23 : a2 ≠ a3 := by intro h; have := congrArg Fin.val h; simp [a2, a3] at this; omega
  rw [Finset.card_insert_of_notMem (by simp [h01, h02, h03]),
    Finset.card_insert_of_notMem (by simp [h12, h13]),
    Finset.card_insert_of_notMem (by simp [h23]),
    Finset.card_singleton]

private theorem card_goodPairs {n : ℕ} (hn : 13 ≤ n) :
    (Finset.univ.filter (fun p : Fin n × Fin n => (p.1.val + p.2.val) % n ∈ targets n)).card =
      4 * n := by
  let f : Fin n × ℕ → Fin n × Fin n :=
    fun x => (x.1, ⟨(x.2 + n - x.1.val) % n, Nat.mod_lt _ (by omega)⟩)
  have heq : Finset.univ.filter (fun p : Fin n × Fin n => (p.1.val + p.2.val) % n ∈ targets n) =
      (Finset.univ ×ˢ targets n).image f := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Finset.mem_product,
      f]
    constructor
    · intro h
      refine ⟨(a, (a.val + b.val) % n), h, ?_⟩
      apply Prod.ext
      · rfl
      · apply Fin.ext
        exact mod_add_sub_cancel (by omega) a.isLt b.isLt
    · rintro ⟨⟨a', t⟩, ht, heq'⟩
      have hae : a' = a := congrArg Prod.fst heq'
      have hbe : (t + n - a'.val) % n = b.val := congrArg (fun p => p.2.val) heq'
      rw [hae] at hbe
      have htlt : t < n := by simp [targets] at ht; omega
      have hmod : (a.val + b.val) % n = t := by
        rw [← hbe]
        exact mod_sub_add_cancel (by omega) htlt a.isLt
      rwa [hmod]
  rw [heq, Finset.card_image_of_injOn]
  · rw [Finset.card_product, Finset.card_fin]
    have ht4 : (targets n).card = 4 := by
      unfold targets
      rw [Finset.card_insert_of_notMem (by simp; omega),
        Finset.card_insert_of_notMem (by simp; omega),
        Finset.card_insert_of_notMem (by simp; omega),
        Finset.card_singleton]
    rw [ht4]
    omega
  · rintro ⟨a1, t1⟩ h1 ⟨a2, t2⟩ h2 h
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_univ, true_and] at h1 h2
    have hae : a1 = a2 := congrArg Prod.fst h
    have hte : (t1 + n - a1.val) % n = (t2 + n - a2.val) % n := congrArg (fun p => p.2.val) h
    rw [← hae] at hte
    have ht1 : t1 < n := by simp [targets] at h1; omega
    have ht2 : t2 < n := by simp [targets] at h2; omega
    have h1' := mod_sub_add_cancel (n := n) (a := t1) (b := a1.val) (by omega) ht1 a1.isLt
    have h2' := mod_sub_add_cancel (n := n) (a := t2) (b := a1.val) (by omega) ht2 a1.isLt
    rw [hte] at h1'
    have ht12 : t1 = t2 := h1'.symm.trans h2'
    exact Prod.ext hae ht12

private theorem card_upperPairs {n : ℕ} (hn : 13 ≤ n) :
    2 * (Finset.univ.filter (fun p : Fin n × Fin n =>
      p.1.val < p.2.val ∧ (p.1.val + p.2.val) % n ∈ targets n)).card +
      (Finset.univ.filter (fun i : Fin n => isF n i = true)).card = 4 * n := by
  set Good := Finset.univ.filter (fun p : Fin n × Fin n => (p.1.val + p.2.val) % n ∈ targets n)
  set Up := Finset.univ.filter (fun p : Fin n × Fin n =>
    p.1.val < p.2.val ∧ (p.1.val + p.2.val) % n ∈ targets n)
  set Lo := Finset.univ.filter (fun p : Fin n × Fin n =>
    p.2.val < p.1.val ∧ (p.1.val + p.2.val) % n ∈ targets n)
  set Dg := Finset.univ.filter (fun p : Fin n × Fin n =>
    p.1.val = p.2.val ∧ (p.1.val + p.2.val) % n ∈ targets n)
  have hpart : Good = Up ∪ Lo ∪ Dg := by
    ext ⟨a, b⟩
    simp only [Good, Up, Lo, Dg, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · intro h
      rcases lt_trichotomy a.val b.val with hlt | heq | hgt
      · exact Or.inl (Or.inl ⟨hlt, h⟩)
      · exact Or.inr ⟨heq, h⟩
      · exact Or.inl (Or.inr ⟨hgt, h⟩)
    · rintro ((⟨_, h⟩ | ⟨_, h⟩) | ⟨_, h⟩) <;> exact h
  have hd1 : Disjoint Up Lo := by
    rw [Finset.disjoint_left]
    intro p h1 h2
    simp only [Up, Lo, Finset.mem_filter] at h1 h2
    omega
  have hd2 : Disjoint (Up ∪ Lo) Dg := by
    rw [Finset.disjoint_left]
    intro p h1 h2
    simp only [Up, Lo, Dg, Finset.mem_union, Finset.mem_filter] at h1 h2
    omega
  have hlo : Lo.card = Up.card := by
    have hsw : Lo = Up.image Prod.swap := by
      ext ⟨a, b⟩
      simp only [Lo, Up, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
        Prod.exists, Prod.swap_prod_mk, Prod.mk.injEq]
      constructor
      · intro ⟨hlt, ht⟩
        exact ⟨b, a, ⟨hlt, by rwa [Nat.add_comm]⟩, rfl, rfl⟩
      · rintro ⟨x, y, ⟨hlt, ht⟩, rfl, rfl⟩
        exact ⟨hlt, by rwa [Nat.add_comm]⟩
    rw [hsw, Finset.card_image_of_injective _ Prod.swap_injective]
  have hdg : Dg.card = (Finset.univ.filter (fun i : Fin n => isF n i = true)).card := by
    have him : Dg = (Finset.univ.filter (fun i : Fin n => isF n i = true)).image (fun i => (i, i)) := by
      ext ⟨a, b⟩
      simp only [Dg, isF, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
        Prod.mk.injEq, decide_eq_true_eq]
      constructor
      · intro ⟨heq, ht⟩
        have hab : a = b := Fin.ext heq
        subst hab
        exact ⟨a, by rwa [Nat.two_mul], rfl, rfl⟩
      · rintro ⟨x, hx, rfl, rfl⟩
        exact ⟨rfl, by rwa [← Nat.two_mul]⟩
    rw [him, Finset.card_image_of_injective _ (fun x y h => congrArg Prod.fst h)]
  have hgood : Good.card = 4 * n := card_goodPairs hn
  rw [hpart, Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1, hlo, hdg] at hgood
  omega

private def th2OddGates (n base : ℕ) : List Gate :=
  let sa := 2 * n + 0
  let sb := 2 * n + (n - 5) / 2
  let sc := 2 * n + (n - 3) / 2
  let sd := 2 * n + (n + 1) / 2
  [ ⟨GateOp.or, [sa, sb]⟩,
    ⟨GateOp.or, [sc, sd]⟩,
    ⟨GateOp.and, [base, base + 1]⟩,
    ⟨GateOp.or, [sa, sc]⟩,
    ⟨GateOp.or, [sb, sd]⟩,
    ⟨GateOp.and, [base + 3, base + 4]⟩,
    ⟨GateOp.or, [base + 2, base + 5]⟩ ]

private theorem th2OddGates_eval (n base : ℕ) (hn : 13 ≤ n) (hbase : 3 * n ≤ base)
    (W : List Bool) (hlen : W.length = base) :
    (runGates (th2OddGates n base) W).getD (base + 6) false =
      (((W.getD (2 * n + 0) false || W.getD (2 * n + (n - 5) / 2) false) &&
        (W.getD (2 * n + (n - 3) / 2) false || W.getD (2 * n + (n + 1) / 2) false)) ||
       ((W.getD (2 * n + 0) false || W.getD (2 * n + (n - 3) / 2) false) &&
        (W.getD (2 * n + (n - 5) / 2) false || W.getD (2 * n + (n + 1) / 2) false))) := by
  set sa := 2 * n + 0
  set sb := 2 * n + (n - 5) / 2
  set sc := 2 * n + (n - 3) / 2
  set sd := 2 * n + (n + 1) / 2
  have hsa : sa < W.length := by omega
  have hsb : sb < W.length := by omega
  have hsc : sc < W.length := by omega
  have hsd : sd < W.length := by omega
  unfold th2OddGates runGates
  simp only [List.foldl_cons, List.foldl_nil, GateOp.eval, List.map_cons, List.map_nil,
    List.any_cons, List.any_nil, List.all_cons, List.all_nil, id_eq, Bool.or_false, Bool.and_true]
  set va := W.getD sa false
  set vb := W.getD sb false
  set vc := W.getD sc false
  set vd := W.getD sd false
  set W1 := W ++ [va || vb]
  have hW1_len : W1.length = base + 1 := by simp [W1, hlen]
  have hW1_sa : W1.getD sa false = va := getD_append_left_lt W _ sa hsa
  have hW1_sb : W1.getD sb false = vb := getD_append_left_lt W _ sb hsb
  have hW1_sc : W1.getD sc false = vc := getD_append_left_lt W _ sc hsc
  have hW1_sd : W1.getD sd false = vd := getD_append_left_lt W _ sd hsd
  have hW1_0 : W1.getD base false = (va || vb) := by rw [← hlen]; exact getD_append_right_self W _
  rw [hW1_sc, hW1_sd]
  set W2 := W1 ++ [vc || vd]
  have hW2_len : W2.length = base + 2 := by simp [W2, hW1_len]
  have hW2_sa : W2.getD sa false = va := by rw [getD_append_left_lt W1 _ sa (by omega), hW1_sa]
  have hW2_sb : W2.getD sb false = vb := by rw [getD_append_left_lt W1 _ sb (by omega), hW1_sb]
  have hW2_sc : W2.getD sc false = vc := by rw [getD_append_left_lt W1 _ sc (by omega), hW1_sc]
  have hW2_sd : W2.getD sd false = vd := by rw [getD_append_left_lt W1 _ sd (by omega), hW1_sd]
  have hW2_0 : W2.getD base false = (va || vb) := by
    rw [getD_append_left_lt W1 _ base (by omega), hW1_0]
  have hW2_1 : W2.getD (base + 1) false = (vc || vd) := by
    rw [← hW1_len]; exact getD_append_right_self W1 _
  rw [hW2_0, hW2_1]
  set W3 := W2 ++ [(va || vb) && (vc || vd)]
  have hW3_len : W3.length = base + 3 := by simp [W3, hW2_len]
  have hW3_sa : W3.getD sa false = va := by rw [getD_append_left_lt W2 _ sa (by omega), hW2_sa]
  have hW3_sb : W3.getD sb false = vb := by rw [getD_append_left_lt W2 _ sb (by omega), hW2_sb]
  have hW3_sc : W3.getD sc false = vc := by rw [getD_append_left_lt W2 _ sc (by omega), hW2_sc]
  have hW3_sd : W3.getD sd false = vd := by rw [getD_append_left_lt W2 _ sd (by omega), hW2_sd]
  have hW3_2 : W3.getD (base + 2) false = ((va || vb) && (vc || vd)) := by
    rw [← hW2_len]; exact getD_append_right_self W2 _
  rw [hW3_sa, hW3_sc]
  set W4 := W3 ++ [va || vc]
  have hW4_len : W4.length = base + 4 := by simp [W4, hW3_len]
  have hW4_sb : W4.getD sb false = vb := by rw [getD_append_left_lt W3 _ sb (by omega), hW3_sb]
  have hW4_sd : W4.getD sd false = vd := by rw [getD_append_left_lt W3 _ sd (by omega), hW3_sd]
  have hW4_2 : W4.getD (base + 2) false = ((va || vb) && (vc || vd)) := by
    rw [getD_append_left_lt W3 _ (base + 2) (by omega), hW3_2]
  have hW4_3 : W4.getD (base + 3) false = (va || vc) := by
    rw [← hW3_len]; exact getD_append_right_self W3 _
  rw [hW4_sb, hW4_sd]
  set W5 := W4 ++ [vb || vd]
  have hW5_len : W5.length = base + 5 := by simp [W5, hW4_len]
  have hW5_2 : W5.getD (base + 2) false = ((va || vb) && (vc || vd)) := by
    rw [getD_append_left_lt W4 _ (base + 2) (by omega), hW4_2]
  have hW5_3 : W5.getD (base + 3) false = (va || vc) := by
    rw [getD_append_left_lt W4 _ (base + 3) (by omega), hW4_3]
  have hW5_4 : W5.getD (base + 4) false = (vb || vd) := by
    rw [← hW4_len]; exact getD_append_right_self W4 _
  rw [hW5_3, hW5_4]
  set W6 := W5 ++ [(va || vc) && (vb || vd)]
  have hW6_len : W6.length = base + 6 := by simp [W6, hW5_len]
  have hW6_2 : W6.getD (base + 2) false = ((va || vb) && (vc || vd)) := by
    rw [getD_append_left_lt W5 _ (base + 2) (by omega), hW5_2]
  have hW6_5 : W6.getD (base + 5) false = ((va || vc) && (vb || vd)) := by
    rw [← hW5_len]; exact getD_append_right_self W5 _
  rw [hW6_2, hW6_5]
  rw [← hW6_len]
  exact getD_append_right_self W6 _

private theorem th2Odd_bool (a b c d : Bool) :
    (((a || b) && (c || d)) || ((a || c) && (b || d))) =
      ((a && b) || (a && c) || (a && d) || (b && c) || (b && d) || (c && d)) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

private theorem th2_four_sig {α : Type*} [DecidableEq α] (a0 a1 a2 a3 u v : α)
    (h01 : a0 ≠ a1) (h02 : a0 ≠ a2) (h03 : a0 ≠ a3)
    (h12 : a1 ≠ a2) (h13 : a1 ≠ a3) (h23 : a2 ≠ a3) :
    let s : α → Bool := fun x => decide (x = u ∨ x = v)
    (((s a0 || s a1) && (s a2 || s a3)) || ((s a0 || s a2) && (s a1 || s a3))) =
      decide (u ≠ v ∧ (u = a0 ∨ u = a1 ∨ u = a2 ∨ u = a3) ∧
        (v = a0 ∨ v = a1 ∨ v = a2 ∨ v = a3)) := by
  intro s
  rw [th2Odd_bool]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.or_eq_true, Bool.and_eq_true, s, decide_eq_true_eq]
  constructor
  · rintro (((((⟨hA, hB⟩ | ⟨hA, hB⟩) | ⟨hA, hB⟩) | ⟨hA, hB⟩) | ⟨hA, hB⟩) | ⟨hA, hB⟩)
    · rcases hA with rfl | rfl <;> rcases hB with rfl | rfl
      · exact False.elim (h01 rfl)
      · exact ⟨h01, Or.inl rfl, Or.inr (Or.inl rfl)⟩
      · exact ⟨h01.symm, Or.inr (Or.inl rfl), Or.inl rfl⟩
      · exact False.elim (h01 rfl)
    · rcases hA with rfl | rfl <;> rcases hB with rfl | rfl
      · exact False.elim (h02 rfl)
      · exact ⟨h02, Or.inl rfl, Or.inr (Or.inr (Or.inl rfl))⟩
      · exact ⟨h02.symm, Or.inr (Or.inr (Or.inl rfl)), Or.inl rfl⟩
      · exact False.elim (h02 rfl)
    · rcases hA with rfl | rfl <;> rcases hB with rfl | rfl
      · exact False.elim (h03 rfl)
      · exact ⟨h03, Or.inl rfl, Or.inr (Or.inr (Or.inr rfl))⟩
      · exact ⟨h03.symm, Or.inr (Or.inr (Or.inr rfl)), Or.inl rfl⟩
      · exact False.elim (h03 rfl)
    · rcases hA with rfl | rfl <;> rcases hB with rfl | rfl
      · exact False.elim (h12 rfl)
      · exact ⟨h12, Or.inr (Or.inl rfl), Or.inr (Or.inr (Or.inl rfl))⟩
      · exact ⟨h12.symm, Or.inr (Or.inr (Or.inl rfl)), Or.inr (Or.inl rfl)⟩
      · exact False.elim (h12 rfl)
    · rcases hA with rfl | rfl <;> rcases hB with rfl | rfl
      · exact False.elim (h13 rfl)
      · exact ⟨h13, Or.inr (Or.inl rfl), Or.inr (Or.inr (Or.inr rfl))⟩
      · exact ⟨h13.symm, Or.inr (Or.inr (Or.inr rfl)), Or.inr (Or.inl rfl)⟩
      · exact False.elim (h13 rfl)
    · rcases hA with rfl | rfl <;> rcases hB with rfl | rfl
      · exact False.elim (h23 rfl)
      · exact ⟨h23, Or.inr (Or.inr (Or.inl rfl)), Or.inr (Or.inr (Or.inr rfl))⟩
      · exact ⟨h23.symm, Or.inr (Or.inr (Or.inr rfl)), Or.inr (Or.inr (Or.inl rfl))⟩
      · exact False.elim (h23 rfl)
  · rintro ⟨huv, hu, hv⟩
    rcases hu with rfl | rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl | rfl
    · exact False.elim (huv rfl)
    · left; left; left; left; left; exact ⟨Or.inl rfl, Or.inr rfl⟩
    · left; left; left; left; right; exact ⟨Or.inl rfl, Or.inr rfl⟩
    · left; left; left; right; exact ⟨Or.inl rfl, Or.inr rfl⟩
    · left; left; left; left; left; exact ⟨Or.inr rfl, Or.inl rfl⟩
    · exact False.elim (huv rfl)
    · left; left; right; exact ⟨Or.inl rfl, Or.inr rfl⟩
    · left; right; exact ⟨Or.inl rfl, Or.inr rfl⟩
    · left; left; left; left; right; exact ⟨Or.inr rfl, Or.inl rfl⟩
    · left; left; right; exact ⟨Or.inr rfl, Or.inl rfl⟩
    · exact False.elim (huv rfl)
    · right; exact ⟨Or.inl rfl, Or.inr rfl⟩
    · left; left; left; right; exact ⟨Or.inr rfl, Or.inl rfl⟩
    · left; right; exact ⟨Or.inr rfl, Or.inl rfl⟩
    · right; exact ⟨Or.inr rfl, Or.inl rfl⟩
    · exact False.elim (huv rfl)

private theorem th2_two_sig {α : Type*} [DecidableEq α] (a0 a1 u v : α) (h01 : a0 ≠ a1) :
    let s : α → Bool := fun x => decide (x = u ∨ x = v)
    (s a0 && s a1) = decide (u ≠ v ∧ (u = a0 ∨ u = a1) ∧ (v = a0 ∨ v = a1)) := by
  intro s
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, s, decide_eq_true_eq]
  constructor
  · rintro ⟨hA, hB⟩
    rcases hA with rfl | rfl <;> rcases hB with rfl | rfl
    · exact False.elim (h01 rfl)
    · exact ⟨h01, Or.inl rfl, Or.inr rfl⟩
    · exact ⟨h01.symm, Or.inr rfl, Or.inl rfl⟩
    · exact False.elim (h01 rfl)
  · rintro ⟨huv, hu, hv⟩
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · exact False.elim (huv rfl)
    · exact ⟨Or.inl rfl, Or.inr rfl⟩
    · exact ⟨Or.inr rfl, Or.inl rfl⟩
    · exact False.elim (huv rfl)

private theorem list_sum_ite_one {α : Type*} [DecidableEq α] (l : List α) (a : α)
    (hnd : l.Nodup) (hmem : a ∈ l) :
    (l.map (fun x => if x = a then 1 else 0)).sum = 1 := by
  induction l with
  | nil => cases hmem
  | cons x xs ih =>
    rw [List.nodup_cons] at hnd
    simp only [List.map_cons, List.sum_cons]
    by_cases hxa : x = a
    · subst hxa
      simp only [↓reduceIte]
      have h0 : (xs.map (fun y => if y = x then 1 else 0)).sum = 0 := by
        rw [List.sum_eq_zero_iff]
        intro k hk
        obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hk
        have hne : y ≠ x := fun h => hnd.1 (h ▸ hy)
        simp [hne]
      omega
    · simp only [hxa, ↓reduceIte, Nat.zero_add]
      have hmem' : a ∈ xs := by
        simp only [List.mem_cons] at hmem
        rcases hmem with rfl | h
        · exact False.elim (hxa rfl)
        · exact h
      exact ih hnd.2 hmem'

private theorem oneEach_getD {n : ℕ} (u v : Fin n) (w : ℕ) (hw : w < 2 * n) :
    (oneEach u v).getD w false =
      if w < n then decide (w = u.val) else decide (w - n = v.val) := by
  unfold oneEach
  rw [List.getD_eq_getElem _ _ (by simp; omega)]
  by_cases hwn : w < n
  · simp only [hwn, ↓reduceIte]
    rw [List.getElem_append_left (by simp; omega), List.getElem_ofFn]
    simp [Fin.ext_iff]
  · simp only [hwn, ↓reduceIte]
    rw [List.getElem_append_right (by simp; omega), List.getElem_ofFn]
    simp [Fin.ext_iff]

private theorem part3_circuit {n : ℕ} (hn : 13 ≤ n) :
    ∃ C : Circuit,
      FanInTwo C ∧
      ReadsBack (2 * n) C ∧
      Represents (Gfun n) C ∧
      2 * n ≤ C.output ∧ C.output < 2 * n + C.size ∧
      notCount C = 1 ∧
      (∀ g ∈ C.gates, g.op = .not → ∃ w : ℕ, g.inputs = [w]) ∧
      C.size ≤ (if n % 2 = 1 then 6 * n else 6 * n - 2) ∧
      ∀ i : Fin n,
        (∃ g ∈ C.gates, g.op = .or ∧ g.inputs = [i.val, n + mateVal n i]) ∧
        (C.gates.map (fun g => g.inputs.count i.val)).sum = 1 ∧
        (C.gates.map (fun g => g.inputs.count (n + i.val))).sum = 1 := by
  let g1 : List Gate :=
    (List.finRange n).map (fun i : Fin n => ⟨GateOp.or, [i.val, n + mateVal n i]⟩)
  have hg1_len : g1.length = n := by simp [g1]
  let UpFin : Finset (Fin n × Fin n) := Finset.univ.filter (fun p : Fin n × Fin n =>
    p.1.val < p.2.val ∧ (p.1.val + p.2.val) % n ∈ targets n)
  let P : List (Fin n × Fin n) := UpFin.toList
  have hP_len : P.length = UpFin.card := Finset.length_toList UpFin
  have hUp_card_odd : n % 2 = 1 → UpFin.card = 2 * n - 2 := by
    intro hodd
    have h1 := card_upperPairs hn
    have h2 := card_F_odd hn hodd
    change 2 * UpFin.card + _ = 4 * n at h1
    omega
  have hUp_card_even : n % 2 = 0 → UpFin.card = 2 * n - 1 := by
    intro heven
    have h1 := card_upperPairs hn
    have h2 := card_F_even hn heven
    change 2 * UpFin.card + _ = 4 * n at h1
    omega
  have hP_pos : 1 ≤ P.length := by
    rw [hP_len]
    by_cases hodd : n % 2 = 1
    · have := hUp_card_odd hodd; omega
    · have := hUp_card_even (by omega); omega
  let g2 : List Gate :=
    P.map (fun p => ⟨GateOp.and, [2 * n + p.1.val, 2 * n + p.2.val]⟩)
  have hg2_len : g2.length = P.length := by simp [g2]
  let b2 : ℕ := 2 * n + n
  let b3 : ℕ := b2 + P.length
  let andWires : List ℕ := List.range' b2 P.length
  have handWires_ne : andWires ≠ [] := by
    intro h
    have := congrArg List.length h
    simp only [andWires, List.length_range', List.length_nil] at this
    omega
  let res3 := orChain b3 andWires
  let g3 : List Gate := res3.1
  let wDbl : ℕ := res3.2
  have hg3_len : g3.length = P.length - 1 := by
    cases h : andWires with
    | nil => exact False.elim (handWires_ne h)
    | cons a as =>
      have hl : a :: as = andWires := h.symm
      have hlen : (a :: as).length = P.length := by rw [hl]; simp [andWires]
      simp only [g3, res3, h, orChain, orChainAcc_length]
      simp only [List.length_cons] at hlen
      omega
  let nonFFin : Finset (Fin n) := Finset.univ.filter (fun i : Fin n => isF n i = false)
  let nonF : List (Fin n) := nonFFin.toList
  have hnonF_len : nonF.length = nonFFin.card := Finset.length_toList nonFFin
  have hnonF_card_odd : n % 2 = 1 → nonFFin.card = n - 4 := by
    intro hodd
    have h1 : (Finset.univ.filter (fun i : Fin n => isF n i = true)).card + nonFFin.card = n := by
      have hdisj : Disjoint (Finset.univ.filter (fun i : Fin n => isF n i = true)) nonFFin := by
        rw [Finset.disjoint_left]
        intro x h1 h2
        simp only [nonFFin, Finset.mem_filter] at h1 h2
        rw [h1.2] at h2
        cases h2.2
      have hun : Finset.univ.filter (fun i : Fin n => isF n i = true) ∪ nonFFin = Finset.univ := by
        ext x
        simp only [nonFFin, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
          iff_true]
        cases isF n x <;> simp
      rw [← Finset.card_union_of_disjoint hdisj, hun, Finset.card_fin]
    have h2 := card_F_odd hn hodd
    omega
  have hnonF_card_even : n % 2 = 0 → nonFFin.card = n - 2 := by
    intro heven
    have h1 : (Finset.univ.filter (fun i : Fin n => isF n i = true)).card + nonFFin.card = n := by
      have hdisj : Disjoint (Finset.univ.filter (fun i : Fin n => isF n i = true)) nonFFin := by
        rw [Finset.disjoint_left]
        intro x h1 h2
        simp only [nonFFin, Finset.mem_filter] at h1 h2
        rw [h1.2] at h2
        cases h2.2
      have hun : Finset.univ.filter (fun i : Fin n => isF n i = true) ∪ nonFFin = Finset.univ := by
        ext x
        simp only [nonFFin, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
          iff_true]
        cases isF n x <;> simp
      rw [← Finset.card_union_of_disjoint hdisj, hun, Finset.card_fin]
    have h2 := card_F_even hn heven
    omega
  have hnonF_pos : 1 ≤ nonF.length := by
    rw [hnonF_len]
    by_cases hodd : n % 2 = 1
    · have := hnonF_card_odd hodd; omega
    · have := hnonF_card_even (by omega); omega
  let b4 : ℕ := b3 + g3.length
  let nonFWires : List ℕ := nonF.map (fun i : Fin n => 2 * n + i.val)
  have hnonFWires_ne : nonFWires ≠ [] := by
    intro h
    have := congrArg List.length h
    simp only [nonFWires, List.length_map, List.length_nil] at this
    omega
  let res4 := orChain b4 nonFWires
  let g4 : List Gate := res4.1
  let wNonF : ℕ := res4.2
  have hg4_len : g4.length = nonF.length - 1 := by
    cases h : nonFWires with
    | nil => exact False.elim (hnonFWires_ne h)
    | cons a as =>
      have hl : a :: as = nonFWires := h.symm
      have hlen : (a :: as).length = nonF.length := by rw [hl]; simp [nonFWires]
      simp only [g4, res4, h, orChain, orChainAcc_length]
      simp only [List.length_cons] at hlen
      omega
  let b5 : ℕ := b4 + g4.length
  let g5 : List Gate :=
    if n % 2 = 1 then th2OddGates n b5 else [⟨GateOp.and, [2 * n + 0, 2 * n + n / 2]⟩]
  let wTh2 : ℕ := if n % 2 = 1 then b5 + 6 else b5
  have hg5_len : g5.length = if n % 2 = 1 then 7 else 1 := by
    by_cases hodd : n % 2 = 1 <;> simp [g5, th2OddGates, hodd]
  let b6 : ℕ := b5 + g5.length
  let g6 : List Gate :=
    [ ⟨GateOp.or, [wNonF, wTh2]⟩,
      ⟨GateOp.not, [b6]⟩,
      ⟨GateOp.or, [wDbl, b6 + 1]⟩ ]
  have hg6_len : g6.length = 3 := rfl
  let allGates : List Gate := g1 ++ g2 ++ g3 ++ g4 ++ g5 ++ g6
  let C : Circuit := ⟨allGates, b6 + 2⟩
  have hC_size : C.size = n + P.length + (P.length - 1) + (nonF.length - 1) + g5.length + 3 := by
    simp only [Circuit.size, C, allGates, List.length_append, hg1_len, hg2_len, hg3_len, hg4_len,
      hg6_len]
  have hb6_eq : b6 = 2 * n + n + P.length + (P.length - 1) + (nonF.length - 1) + g5.length := by
    simp only [b6, b5, b4, b3, b2, hg3_len, hg4_len]
  have hC_bound : C.size ≤ (if n % 2 = 1 then 6 * n else 6 * n - 2) := by
    by_cases hodd : n % 2 = 1
    · simp only [hodd, ↓reduceIte] at hg5_len ⊢
      have hp := hUp_card_odd hodd
      have hnf := hnonF_card_odd hodd
      omega
    · have heven : n % 2 = 0 := by omega
      simp only [hodd, ↓reduceIte] at hg5_len ⊢
      have hp := hUp_card_even heven
      have hnf := hnonF_card_even heven
      omega
  have hwDbl_lt : wDbl < b4 := by
    cases h : andWires with
    | nil => exact False.elim (handWires_ne h)
    | cons a as =>
      have ha_lt : a < b3 := by
        have hmem : a ∈ andWires := by rw [h]; exact List.mem_cons_self ..
        simp only [andWires, List.mem_range'] at hmem
        omega
      have hl : b3 + as.length = b4 := by
        have h1 : g3.length = as.length := by simp [g3, res3, h, orChain, orChainAcc_length]
        omega
      rw [← hl]
      simpa [wDbl, res3, h, orChain] using orChainAcc_out_lt b3 a as ha_lt
  have hwDbl_ge : 2 * n ≤ wDbl := by
    cases h : andWires with
    | nil => exact False.elim (handWires_ne h)
    | cons a as =>
      have ha_ge : 2 * n ≤ a := by
        have hmem : a ∈ andWires := by rw [h]; exact List.mem_cons_self ..
        simp only [andWires, List.mem_range'] at hmem
        omega
      simpa [wDbl, res3, h, orChain] using orChainAcc_out_ge b3 a (2 * n) as ha_ge (by omega)
  have hwNonF_lt : wNonF < b5 := by
    cases h : nonFWires with
    | nil => exact False.elim (hnonFWires_ne h)
    | cons a as =>
      have ha_lt : a < b4 := by
        have hmem : a ∈ nonFWires := by rw [h]; exact List.mem_cons_self ..
        obtain ⟨i, _, rfl⟩ := List.mem_map.mp hmem
        have hi : i.val < n := i.isLt
        omega
      have hl : b4 + as.length = b5 := by
        have h1 : g4.length = as.length := by simp [g4, res4, h, orChain, orChainAcc_length]
        omega
      rw [← hl]
      simpa [wNonF, res4, h, orChain] using orChainAcc_out_lt b4 a as ha_lt
  have hwNonF_ge : 2 * n ≤ wNonF := by
    cases h : nonFWires with
    | nil => exact False.elim (hnonFWires_ne h)
    | cons a as =>
      have ha_ge : 2 * n ≤ a := by
        have hmem : a ∈ nonFWires := by rw [h]; exact List.mem_cons_self ..
        obtain ⟨i, _, rfl⟩ := List.mem_map.mp hmem
        omega
      simpa [wNonF, res4, h, orChain] using orChainAcc_out_ge b4 a (2 * n) as ha_ge (by omega)
  have hwTh2_lt : wTh2 < b6 := by
    by_cases hodd : n % 2 = 1 <;> simp only [wTh2, b6, hodd, ↓reduceIte] at hg5_len ⊢ <;> omega
  have hwTh2_ge : 2 * n ≤ wTh2 := by
    by_cases hodd : n % 2 = 1 <;> simp only [wTh2, hodd, ↓reduceIte] <;> omega
  have hFan : FanInTwo C := by
    intro g hg
    simp only [C, allGates, List.mem_append] at hg
    rcases hg with ((((hg | hg) | hg) | hg) | hg) | hg
    · obtain ⟨i, _, rfl⟩ := List.mem_map.mp hg
      exact ⟨by simp, by simp⟩
    · obtain ⟨p, _, rfl⟩ := List.mem_map.mp hg
      exact ⟨by simp, by simp⟩
    · cases h : andWires with
      | nil => exact False.elim (handWires_ne h)
      | cons a as =>
        simp only [g3, res3, h, orChain] at hg
        exact orChainAcc_fanInTwo b3 a as g hg
    · cases h : nonFWires with
      | nil => exact False.elim (hnonFWires_ne h)
      | cons a as =>
        simp only [g4, res4, h, orChain] at hg
        exact orChainAcc_fanInTwo b4 a as g hg
    · by_cases hodd : n % 2 = 1
      · simp only [g5, hodd, ↓reduceIte, th2OddGates, List.mem_cons, List.not_mem_nil,
          or_false] at hg
        rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by simp⟩
      · simp only [g5, hodd, ↓reduceIte, List.mem_singleton] at hg
        subst hg
        exact ⟨by simp, by simp⟩
    · simp only [g6, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl <;> exact ⟨by simp, by simp⟩
  have hRB : ReadsBack (2 * n) C := by
    apply readsBack_of_readsBackFrom
    have hrb1 : ReadsBackFrom (2 * n) g1 := by
      intro j hj u hu
      have hj' : j < n := by omega
      simp only [g1, List.getElem_map, List.getElem_finRange, List.mem_cons, List.not_mem_nil,
        or_false] at hu
      rcases hu with rfl | rfl
      · omega
      · have hmlt : ∀ x : Fin n, mateVal n x < n := fun x => Nat.mod_lt _ (by omega)
        exact Nat.add_lt_add_left (hmlt _) n |>.trans_le (by omega)
    have hrb2 : ReadsBackFrom b2 g2 := by
      intro j hj u hu
      simp only [g2, List.getElem_map, List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl
      · have := P[j].1.isLt; omega
      · have := P[j].2.isLt; omega
    have hrb3 : ReadsBackFrom b3 g3 := by
      cases h : andWires with
      | nil => exact False.elim (handWires_ne h)
      | cons a as =>
        have hmem_all : ∀ x ∈ a :: as, x < b3 := by
          intro x hx
          have hx' : x ∈ andWires := by rwa [h]
          simp only [andWires, List.mem_range'] at hx'
          omega
        simpa [g3, res3, h, orChain] using
          orChainAcc_readsBack b3 a as (hmem_all a (List.mem_cons_self ..))
            (fun x hx => hmem_all x (List.mem_cons_of_mem _ hx))
    have hrb4 : ReadsBackFrom b4 g4 := by
      cases h : nonFWires with
      | nil => exact False.elim (hnonFWires_ne h)
      | cons a as =>
        have hmem_all : ∀ x ∈ a :: as, x < b4 := by
          intro x hx
          have hx' : x ∈ nonFWires := by rwa [h]
          obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx'
          have hi : i.val < n := i.isLt
          omega
        simpa [g4, res4, h, orChain] using
          orChainAcc_readsBack b4 a as (hmem_all a (List.mem_cons_self ..))
            (fun x hx => hmem_all x (List.mem_cons_of_mem _ hx))
    have hrb5 : ReadsBackFrom b5 g5 := by
      by_cases hodd : n % 2 = 1
      · simp only [g5, hodd, ↓reduceIte]
        intro j hj u hu
        have h3n : 3 * n ≤ b5 := by omega
        rcases j with _ | _ | _ | _ | _ | _ | _ | j
        · simp only [th2OddGates, List.getElem_cons_zero, List.mem_cons, List.not_mem_nil,
            or_false] at hu
          rcases hu with rfl | rfl <;> omega
        · simp only [th2OddGates, List.getElem_cons_succ, List.getElem_cons_zero, List.mem_cons,
            List.not_mem_nil, or_false] at hu
          rcases hu with rfl | rfl <;> omega
        · simp only [th2OddGates, List.getElem_cons_succ, List.getElem_cons_zero, List.mem_cons,
            List.not_mem_nil, or_false] at hu
          rcases hu with rfl | rfl <;> omega
        · simp only [th2OddGates, List.getElem_cons_succ, List.getElem_cons_zero, List.mem_cons,
            List.not_mem_nil, or_false] at hu
          rcases hu with rfl | rfl <;> omega
        · simp only [th2OddGates, List.getElem_cons_succ, List.getElem_cons_zero, List.mem_cons,
            List.not_mem_nil, or_false] at hu
          rcases hu with rfl | rfl <;> omega
        · simp only [th2OddGates, List.getElem_cons_succ, List.getElem_cons_zero, List.mem_cons,
            List.not_mem_nil, or_false] at hu
          rcases hu with rfl | rfl <;> omega
        · simp only [th2OddGates, List.getElem_cons_succ, List.getElem_cons_zero, List.mem_cons,
            List.not_mem_nil, or_false] at hu
          rcases hu with rfl | rfl <;> omega
        · simp [th2OddGates] at hj; omega
      · simp only [g5, hodd, ↓reduceIte]
        intro j hj u hu
        rcases j with _ | j
        · simp only [List.getElem_cons_zero, List.mem_cons, List.not_mem_nil, or_false] at hu
          rcases hu with rfl | rfl <;> omega
        · simp at hj
    have hrb6 : ReadsBackFrom b6 g6 := by
      intro j hj u hu
      rcases j with _ | _ | _ | j
      · simp only [g6, List.getElem_cons_zero, List.mem_cons, List.not_mem_nil, or_false] at hu
        rcases hu with rfl | rfl <;> omega
      · simp only [g6, List.getElem_cons_succ, List.getElem_cons_zero, List.mem_cons,
          List.not_mem_nil, or_false] at hu
        subst hu; omega
      · simp only [g6, List.getElem_cons_succ, List.getElem_cons_zero, List.mem_cons,
          List.not_mem_nil, or_false] at hu
        rcases hu with rfl | rfl <;> omega
      · simp [g6] at hj; omega
    have h12 : ReadsBackFrom (2 * n) (g1 ++ g2) :=
      readsBackFrom_append hrb1 (by simpa [hg1_len, b2] using hrb2)
    have h13 : ReadsBackFrom (2 * n) (g1 ++ g2 ++ g3) :=
      readsBackFrom_append h12
        (by simpa [List.length_append, hg1_len, hg2_len, b3, b2, Nat.add_assoc] using hrb3)
    have h14 : ReadsBackFrom (2 * n) (g1 ++ g2 ++ g3 ++ g4) :=
      readsBackFrom_append h13
        (by simpa [List.length_append, hg1_len, hg2_len, b4, b3, b2, Nat.add_assoc] using hrb4)
    have h15 : ReadsBackFrom (2 * n) (g1 ++ g2 ++ g3 ++ g4 ++ g5) :=
      readsBackFrom_append h14
        (by simpa [List.length_append, hg1_len, hg2_len, b5, b4, b3, b2, Nat.add_assoc] using hrb5)
    exact readsBackFrom_append h15
      (by simpa [List.length_append, hg1_len, hg2_len, b6, b5, b4, b3, b2, Nat.add_assoc] using hrb6)
  have hnoNot1 : NoNotGates g1 := by
    intro g hg; obtain ⟨i, _, rfl⟩ := List.mem_map.mp hg; intro h; cases h
  have hnoNot2 : NoNotGates g2 := by
    intro g hg; obtain ⟨p, _, rfl⟩ := List.mem_map.mp hg; intro h; cases h
  have hnoNot3 : NoNotGates g3 := by
    cases h : andWires with
    | nil => exact False.elim (handWires_ne h)
    | cons a as => simpa [g3, res3, h, orChain] using orChainAcc_noNot b3 a as
  have hnoNot4 : NoNotGates g4 := by
    cases h : nonFWires with
    | nil => exact False.elim (hnonFWires_ne h)
    | cons a as => simpa [g4, res4, h, orChain] using orChainAcc_noNot b4 a as
  have hnoNot5 : NoNotGates g5 := by
    by_cases hodd : n % 2 = 1
    · intro g hg
      simp only [g5, hodd, ↓reduceIte, th2OddGates, List.mem_cons, List.not_mem_nil,
        or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (intro h; cases h)
    · intro g hg
      simp only [g5, hodd, ↓reduceIte, List.mem_singleton] at hg
      subst hg; intro h; cases h
  have hnotCount : notCount C = 1 := by
    unfold notCount
    simp only [C, allGates, List.filter_append, List.length_append]
    rw [filter_len_eq_zero _ (fun g hg => decide_eq_false_iff_not.mpr (hnoNot1 g hg)),
      filter_len_eq_zero _ (fun g hg => decide_eq_false_iff_not.mpr (hnoNot2 g hg)),
      filter_len_eq_zero _ (fun g hg => decide_eq_false_iff_not.mpr (hnoNot3 g hg)),
      filter_len_eq_zero _ (fun g hg => decide_eq_false_iff_not.mpr (hnoNot4 g hg)),
      filter_len_eq_zero _ (fun g hg => decide_eq_false_iff_not.mpr (hnoNot5 g hg))]
    simp [g6]
  have hnotUnary : ∀ g ∈ C.gates, g.op = .not → ∃ w : ℕ, g.inputs = [w] := by
    intro g hg hnot
    simp only [C, allGates, List.mem_append] at hg
    rcases hg with ((((hg | hg) | hg) | hg) | hg) | hg
    · exact False.elim (hnoNot1 g hg hnot)
    · exact False.elim (hnoNot2 g hg hnot)
    · exact False.elim (hnoNot3 g hg hnot)
    · exact False.elim (hnoNot4 g hg hnot)
    · exact False.elim (hnoNot5 g hg hnot)
    · simp only [g6, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl
      · cases hnot
      · exact ⟨b6, rfl⟩
      · cases hnot
  have hrest_ge : ∀ g ∈ g2 ++ g3 ++ g4 ++ g5 ++ g6, ∀ u ∈ g.inputs, 2 * n ≤ u := by
    intro g hg u hu
    simp only [List.mem_append] at hg
    rcases hg with (((hg | hg) | hg) | hg) | hg
    · obtain ⟨p, _, rfl⟩ := List.mem_map.mp hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl <;> omega
    · cases h : andWires with
      | nil => exact False.elim (handWires_ne h)
      | cons a as =>
        have hall : ∀ x ∈ a :: as, 2 * n ≤ x := by
          intro x hx
          have hx' : x ∈ andWires := by rwa [h]
          simp only [andWires, List.mem_range'] at hx'
          omega
        simp only [g3, res3, h, orChain] at hg
        exact orChainAcc_inputs_ge b3 a (2 * n) as (hall a (List.mem_cons_self ..)) (by omega)
          (fun x hx => hall x (List.mem_cons_of_mem _ hx)) g hg u hu
    · cases h : nonFWires with
      | nil => exact False.elim (hnonFWires_ne h)
      | cons a as =>
        have hall : ∀ x ∈ a :: as, 2 * n ≤ x := by
          intro x hx
          have hx' : x ∈ nonFWires := by rwa [h]
          obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx'
          omega
        simp only [g4, res4, h, orChain] at hg
        exact orChainAcc_inputs_ge b4 a (2 * n) as (hall a (List.mem_cons_self ..)) (by omega)
          (fun x hx => hall x (List.mem_cons_of_mem _ hx)) g hg u hu
    · by_cases hodd : n % 2 = 1
      · simp only [g5, hodd, ↓reduceIte, th2OddGates, List.mem_cons, List.not_mem_nil,
          or_false] at hg
        rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          (simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl | rfl <;> omega)
      · simp only [g5, hodd, ↓reduceIte, List.mem_singleton] at hg
        subst hg
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
        rcases hu with rfl | rfl <;> omega
    · simp only [g6, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
        rcases hu with rfl | rfl <;> omega
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
        subst hu; omega
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
        rcases hu with rfl | rfl <;> omega
  have hRep : Represents (Gfun n) C := by
    intro u v
    let v' : Fin n := mateFin hn v
    let sigVal : Fin n → Bool := fun i => decide (i = u ∨ i = v')
    set W0 := oneEach u v
    have hW0_len : W0.length = 2 * n := by simp [W0, oneEach]; omega
    set W1 := runGates g1 W0
    have hW1_eq : W1 = W0 ++ (List.finRange n).map sigVal := by
      have hold1 : ∀ i ∈ List.finRange n,
          ∀ w ∈ (Gate.mk GateOp.or [i.val, n + mateVal n i]).inputs, w < W0.length := by
        intro i _ w hw
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl
        · have := i.isLt; omega
        · have : mateVal n i < n := Nat.mod_lt _ (by omega); omega
      have hrun := runGates_map_reads_old (List.finRange n)
        (fun i : Fin n => ⟨GateOp.or, [i.val, n + mateVal n i]⟩) W0 hold1
      change runGates g1 W0 = _
      rw [show g1 = (List.finRange n).map (fun i : Fin n => ⟨GateOp.or, [i.val, n + mateVal n i]⟩) from rfl]
      rw [hrun]
      congr 1
      apply List.map_congr_left
      intro i _
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq,
        Bool.or_false]
      have hi : i.val < n := i.isLt
      have hm : mateVal n i < n := Nat.mod_lt _ (by omega)
      rw [oneEach_getD u v i.val (by omega), oneEach_getD u v (n + mateVal n i) (by omega)]
      have hnot : ¬ (n + mateVal n i < n) := by omega
      simp only [hi, hnot, ↓reduceIte, Nat.add_sub_cancel_left]
      have h1 : decide (i.val = u.val) = decide (i = u) := by simp [Fin.ext_iff]
      have h2 : decide (mateVal n i = v.val) = decide (i = v') := by
        simp [mateVal_eq_iff hn i v, v']
      rw [h1, h2]
      simp [sigVal]
    have hW1_len : W1.length = b2 := by rw [hW1_eq, List.length_append, hW0_len]; simp [b2]
    have hW1_sig : ∀ i : Fin n, W1.getD (2 * n + i.val) false = sigVal i := by
      intro i
      rw [hW1_eq, List.getD_eq_getElem _ _ (by rw [List.length_append, hW0_len]; simp),
        List.getElem_append_right (by omega)]
      simp only [hW0_len, Nat.add_sub_cancel_left, List.getElem_map, List.getElem_finRange]
      congr 1
    set W2 := runGates g2 W1
    have hW2_eq : W2 = W1 ++ P.map (fun p => sigVal p.1 && sigVal p.2) := by
      have hold2 : ∀ p ∈ P, ∀ w ∈ (Gate.mk GateOp.and [2 * n + p.1.val, 2 * n + p.2.val]).inputs,
          w < W1.length := by
        intro p _ w hw
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl
        · have := p.1.isLt; omega
        · have := p.2.isLt; omega
      have hrun := runGates_map_reads_old P
        (fun p => ⟨GateOp.and, [2 * n + p.1.val, 2 * n + p.2.val]⟩) W1 hold2
      change runGates g2 W1 = _
      rw [show g2 = P.map (fun p => ⟨GateOp.and, [2 * n + p.1.val, 2 * n + p.2.val]⟩) from rfl]
      rw [hrun]
      congr 1
      apply List.map_congr_left
      intro p _
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq,
        Bool.and_true, hW1_sig]
    have hW2_len : W2.length = b3 := by rw [hW2_eq, List.length_append, hW1_len]; simp [b3]
    have hW2_and : ∀ k (hk : k < P.length),
        W2.getD (b2 + k) false = (sigVal P[k].1 && sigVal P[k].2) := by
      intro k hk
      rw [hW2_eq, List.getD_eq_getElem _ _ (by rw [List.length_append, hW1_len]; simp; omega),
        List.getElem_append_right (by omega)]
      simp only [hW1_len, Nat.add_sub_cancel_left, List.getElem_map]
    set W3 := runGates g3 W2
    have hW3_len : W3.length = b4 := by rw [runGates_length, hW2_len]
    have hW3_dbl : W3.getD wDbl false = P.any (fun p => sigVal p.1 && sigVal p.2) := by
      have hany_eq : andWires.any (fun w => W2.getD w false) =
          P.any (fun p => sigVal p.1 && sigVal p.2) := by
        apply Bool.eq_iff_iff.mpr
        simp only [List.any_eq_true, andWires, List.mem_range', Nat.one_mul]
        constructor
        · rintro ⟨w, ⟨k, hk, rfl⟩, hw⟩
          refine ⟨P[k], List.getElem_mem hk, ?_⟩
          rw [hW2_and k hk] at hw
          exact hw
        · rintro ⟨p, hp, hval⟩
          obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hp
          refine ⟨b2 + k, ⟨k, hk, rfl⟩, ?_⟩
          rw [hW2_and k hk]
          exact hval
      cases h : andWires with
      | nil => exact False.elim (handWires_ne h)
      | cons a as =>
        have hall : ∀ x ∈ a :: as, x < b3 := by
          intro x hx
          have hx' : x ∈ andWires := by rwa [h]
          simp only [andWires, List.mem_range'] at hx'
          omega
        have hev := orChainAcc_eval b3 a as W2 hW2_len (hall a (List.mem_cons_self ..))
          (fun x hx => hall x (List.mem_cons_of_mem _ hx))
        change (runGates (orChain b3 andWires).1 W2).getD (orChain b3 andWires).2 false = _
        rw [h, orChain, hev, ← hany_eq, h, List.any_cons]
    set W4 := runGates g4 W3
    have hW4_len : W4.length = b5 := by rw [runGates_length, hW3_len]
    have hW4_sig : ∀ i : Fin n, W4.getD (2 * n + i.val) false = sigVal i := by
      intro i
      have hi : 2 * n + i.val < W1.length := by have := i.isLt; omega
      have h2 : W2.getD (2 * n + i.val) false = W1.getD (2 * n + i.val) false :=
        runGates_getD_old g2 W1 _ hi
      have h3 : W3.getD (2 * n + i.val) false = W2.getD (2 * n + i.val) false :=
        runGates_getD_old g3 W2 _ (by omega)
      have h4 : W4.getD (2 * n + i.val) false = W3.getD (2 * n + i.val) false :=
        runGates_getD_old g4 W3 _ (by omega)
      rw [h4, h3, h2, hW1_sig]
    have hW3_sig : ∀ i : Fin n, W3.getD (2 * n + i.val) false = sigVal i := by
      intro i
      have hi : 2 * n + i.val < W1.length := by have := i.isLt; omega
      rw [runGates_getD_old g3 W2 _ (by omega), runGates_getD_old g2 W1 _ hi, hW1_sig]
    have hW4_nonF : W4.getD wNonF false = nonF.any sigVal := by
      have hany_eq : nonFWires.any (fun w => W3.getD w false) = nonF.any sigVal := by
        simp only [nonFWires, List.any_map]
        apply list_any_congr
        intro i _
        exact hW3_sig i
      cases h : nonFWires with
      | nil => exact False.elim (hnonFWires_ne h)
      | cons a as =>
        have hall : ∀ x ∈ a :: as, x < b4 := by
          intro x hx
          have hx' : x ∈ nonFWires := by rwa [h]
          obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx'
          have hi : i.val < n := i.isLt
          omega
        have hev := orChainAcc_eval b4 a as W3 hW3_len (hall a (List.mem_cons_self ..))
          (fun x hx => hall x (List.mem_cons_of_mem _ hx))
        change (runGates (orChain b4 nonFWires).1 W3).getD (orChain b4 nonFWires).2 false = _
        rw [h, orChain, hev, ← hany_eq, h, List.any_cons]
    set W5 := runGates g5 W4
    have hW5_len : W5.length = b6 := by rw [runGates_length, hW4_len]
    have hW5_dbl : W5.getD wDbl false = P.any (fun p => sigVal p.1 && sigVal p.2) := by
      rw [runGates_getD_old g5 W4 wDbl (by omega), runGates_getD_old g4 W3 wDbl (by omega),
        hW3_dbl]
    have hW5_nonF : W5.getD wNonF false = nonF.any sigVal := by
      rw [runGates_getD_old g5 W4 wNonF (by omega), hW4_nonF]
    have hW5_th2 : W5.getD wTh2 false =
        decide (u ≠ v' ∧ isF n u = true ∧ isF n v' = true) := by
      by_cases hodd : n % 2 = 1
      · have h5 : W5 = runGates (th2OddGates n b5) W4 := by simp [W5, g5, hodd]
        have hw5 : wTh2 = b5 + 6 := by simp [wTh2, hodd]
        rw [h5, hw5, th2OddGates_eval n b5 hn (by omega) W4 hW4_len]
        let a0 : Fin n := ⟨0, by omega⟩
        let a1 : Fin n := ⟨(n - 5) / 2, by omega⟩
        let a2 : Fin n := ⟨(n - 3) / 2, by omega⟩
        let a3 : Fin n := ⟨(n + 1) / 2, by omega⟩
        have h0 : W4.getD (2 * n + 0) false = sigVal a0 := hW4_sig a0
        have h1 : W4.getD (2 * n + (n - 5) / 2) false = sigVal a1 := hW4_sig a1
        have h2 : W4.getD (2 * n + (n - 3) / 2) false = sigVal a2 := hW4_sig a2
        have h3 : W4.getD (2 * n + (n + 1) / 2) false = sigVal a3 := hW4_sig a3
        rw [h0, h1, h2, h3]
        have h01 : a0 ≠ a1 := by intro h; have := congrArg Fin.val h; simp [a0, a1] at this; omega
        have h02 : a0 ≠ a2 := by intro h; have := congrArg Fin.val h; simp [a0, a2] at this; omega
        have h03 : a0 ≠ a3 := by intro h; have := congrArg Fin.val h; simp [a0, a3] at this; omega
        have h12 : a1 ≠ a2 := by intro h; have := congrArg Fin.val h; simp [a1, a2] at this; omega
        have h13 : a1 ≠ a3 := by intro h; have := congrArg Fin.val h; simp [a1, a3] at this; omega
        have h23 : a2 ≠ a3 := by intro h; have := congrArg Fin.val h; simp [a2, a3] at this; omega
        rw [th2_four_sig a0 a1 a2 a3 u v' h01 h02 h03 h12 h13 h23]
        apply Bool.eq_iff_iff.mpr
        simp only [decide_eq_true_eq, isF_odd_iff hn hodd, Fin.ext_iff, a0, a1, a2, a3]
      · have heven : n % 2 = 0 := by omega
        have h5 : W5 = W4 ++ [W4.getD (2 * n + 0) false && W4.getD (2 * n + n / 2) false] := by
          simp [W5, g5, hodd, runGates, GateOp.eval]
        have hw5 : wTh2 = b5 := by simp [wTh2, hodd]
        rw [h5, hw5, ← hW4_len, getD_append_right_self]
        let a0 : Fin n := ⟨0, by omega⟩
        let a1 : Fin n := ⟨n / 2, by omega⟩
        rw [hW4_sig a0, hW4_sig a1]
        have h01 : a0 ≠ a1 := by intro h; have := congrArg Fin.val h; simp [a0, a1] at this; omega
        rw [th2_two_sig a0 a1 u v' h01]
        apply Bool.eq_iff_iff.mpr
        simp only [decide_eq_true_eq, isF_even_iff hn heven, Fin.ext_iff, a0, a1]
    have hevalC : C.eval W0 = (W5.getD wDbl false || !(W5.getD wNonF false || W5.getD wTh2 false)) := by
      unfold Circuit.eval Circuit.wires
      change (runGates allGates W0).getD (b6 + 2) false = _
      have hall_run : runGates allGates W0 = runGates g6 W5 := by
        simp only [allGates, runGates_append, W5, W4, W3, W2, W1]
      rw [hall_run]
      simp only [g6, runGates, List.foldl_cons, List.foldl_nil, GateOp.eval, List.map_cons,
        List.map_nil, List.any_cons, List.any_nil, List.headD_cons, id_eq, Bool.or_false]
      set bBad := W5.getD wNonF false || W5.getD wTh2 false
      set W6a := W5 ++ [bBad]
      have hW6a_len : W6a.length = b6 + 1 := by simp [W6a, hW5_len]
      have hW6a_0 : W6a.getD b6 false = bBad := by rw [← hW5_len]; exact getD_append_right_self W5 _
      have hW6a_dbl : W6a.getD wDbl false = W5.getD wDbl false :=
        getD_append_left_lt W5 _ wDbl (by omega)
      rw [hW6a_0]
      set W6b := W6a ++ [!bBad]
      have hW6b_len : W6b.length = b6 + 2 := by simp [W6b, hW6a_len]
      have hW6b_1 : W6b.getD (b6 + 1) false = !bBad := by
        rw [← hW6a_len]; exact getD_append_right_self W6a _
      have hW6b_dbl : W6b.getD wDbl false = W5.getD wDbl false := by
        rw [getD_append_left_lt W6a _ wDbl (by omega), hW6a_dbl]
      rw [hW6b_dbl, hW6b_1, ← hW6b_len]
      exact getD_append_right_self W6b _
    rw [hevalC, hW5_dbl, hW5_nonF, hW5_th2]
    apply Bool.eq_iff_iff.mpr
    rw [Gfun_iff_target hn u v]
    change _ ↔ (u.val + v'.val) % n ∈ targets n
    have hnonF_iff : nonF.any sigVal = true ↔ (isF n u = false ∨ isF n v' = false) := by
      simp only [List.any_eq_true, nonF, Finset.mem_toList, nonFFin, Finset.mem_filter,
        Finset.mem_univ, true_and, sigVal, decide_eq_true_eq]
      constructor
      · rintro ⟨i, hi, hiu | hiv⟩
        · rw [← hiu]; exact Or.inl hi
        · rw [← hiv]; exact Or.inr hi
      · rintro (h | h)
        · exact ⟨u, h, Or.inl rfl⟩
        · exact ⟨v', h, Or.inr rfl⟩
    have hdbl_iff : P.any (fun p => sigVal p.1 && sigVal p.2) = true ↔
        (u ≠ v' ∧ (u.val + v'.val) % n ∈ targets n) := by
      simp only [List.any_eq_true, P, Finset.mem_toList, UpFin, Finset.mem_filter, Finset.mem_univ,
        true_and, Bool.and_eq_true, sigVal, decide_eq_true_eq]
      constructor
      · rintro ⟨⟨a, b⟩, ⟨hab, ht⟩, ha, hb⟩
        dsimp only at hab ht ha hb
        have hne_ab : a ≠ b := fun h => by rw [h] at hab; omega
        rcases ha with ha | ha <;> rcases hb with hb | hb
        · exact False.elim (hne_ab (ha.trans hb.symm))
        · rw [← ha, ← hb]; exact ⟨hne_ab, ht⟩
        · rw [← ha, ← hb]; exact ⟨hne_ab.symm, by rwa [Nat.add_comm]⟩
        · exact False.elim (hne_ab (ha.trans hb.symm))
      · rintro ⟨huv, ht⟩
        by_cases hlt : u.val < v'.val
        · exact ⟨(u, v'), ⟨hlt, ht⟩, Or.inl rfl, Or.inr rfl⟩
        · have hgt : v'.val < u.val := by
            have hne : u.val ≠ v'.val := fun h => huv (Fin.ext h)
            omega
          exact ⟨(v', u), ⟨hgt, by rwa [Nat.add_comm]⟩, Or.inr rfl, Or.inl rfl⟩
    simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.or_eq_false_iff, decide_eq_false_iff_not]
    rw [hdbl_iff]
    by_cases huv : u = v'
    · have hnot_dbl : ¬ (u ≠ v' ∧ (u.val + v'.val) % n ∈ targets n) := fun h => h.1 huv
      have hnonF_f : nonF.any sigVal = false ↔ isF n u = true := by
        cases h : nonF.any sigVal
        · simp only [true_iff]
          by_contra hnf
          have hf : isF n u = false := Bool.eq_false_iff.mpr hnf
          have ht := hnonF_iff.mpr (Or.inl hf)
          rw [h] at ht; exact Bool.false_ne_true ht
        · simp only [Bool.true_eq_false, false_iff]
          intro htu
          rcases hnonF_iff.mp h with h1 | h1
          · rw [htu] at h1; cases h1
          · rw [← huv, htu] at h1; cases h1
      have hnot_th2 : ¬ (u ≠ v' ∧ isF n u = true ∧ isF n v' = true) := fun h => h.1 huv
      have hsum_eq : u.val + v'.val = 2 * u.val := by rw [← huv]; omega
      rw [eq_false hnot_dbl, hnonF_f, eq_false hnot_th2, hsum_eq]
      simp [isF]
    · have hbad_true : ¬ (nonF.any sigVal = false ∧ ¬ (u ≠ v' ∧ isF n u = true ∧ isF n v' = true)) := by
        rintro ⟨hnf, hnt⟩
        have hfu : isF n u = true := by
          by_contra h1
          have hf := hnonF_iff.mpr (Or.inl (Bool.eq_false_iff.mpr h1))
          rw [hnf] at hf; exact Bool.false_ne_true hf
        have hfv : isF n v' = true := by
          by_contra h1
          have hf := hnonF_iff.mpr (Or.inr (Bool.eq_false_iff.mpr h1))
          rw [hnf] at hf; exact Bool.false_ne_true hf
        exact hnt ⟨huv, hfu, hfv⟩
      rw [eq_false hbad_true]
      simp [huv]
  have hout_ge : 2 * n ≤ C.output := by change 2 * n ≤ b6 + 2; omega
  have hout_lt : C.output < 2 * n + C.size := by change b6 + 2 < 2 * n + C.size; omega
  refine ⟨C, hFan, hRB, hRep, hout_ge, hout_lt, hnotCount, hnotUnary, hC_bound, ?_⟩
  intro i
  have hsum_rest_0 : ∀ w < 2 * n,
      ((g2 ++ g3 ++ g4 ++ g5 ++ g6).map (fun g => g.inputs.count w)).sum = 0 :=
    fun w hw => sum_count_eq_zero_of_ge hrest_ge hw
  have hsplit_gates : allGates = g1 ++ (g2 ++ g3 ++ g4 ++ g5 ++ g6) := by
    simp [allGates, List.append_assoc]
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨⟨GateOp.or, [i.val, n + mateVal n i]⟩, ?_, rfl, rfl⟩
    rw [show C.gates = allGates from rfl, hsplit_gates]
    exact List.mem_append_left _ (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)
  · rw [show C.gates = allGates from rfl, hsplit_gates, List.map_append, List.sum_append,
      hsum_rest_0 i.val (by have := i.isLt; omega), Nat.add_zero]
    simp only [g1, List.map_map]
    have hmap : ((List.finRange n).map
        ((fun g : Gate => g.inputs.count i.val) ∘
          (fun j : Fin n => ⟨GateOp.or, [j.val, n + mateVal n j]⟩))) =
        (List.finRange n).map (fun j : Fin n => if j = i then 1 else 0) := by
      apply List.map_congr_left
      intro j _
      simp only [Function.comp_apply]
      have hi : i.val < n := i.isLt
      have hne : n + mateVal n j ≠ i.val := by omega
      simp only [List.count_cons, List.count_nil, beq_iff_eq, hne, ↓reduceIte, Nat.zero_add]
      by_cases hji : j = i
      · subst hji; simp
      · have hne2 : j.val ≠ i.val := fun h => hji (Fin.ext h)
        simp [hji, hne2]
    rw [hmap]
    exact list_sum_ite_one (List.finRange n) i (List.nodup_finRange n) (List.mem_finRange i)
  · rw [show C.gates = allGates from rfl, hsplit_gates, List.map_append, List.sum_append,
      hsum_rest_0 (n + i.val) (by have := i.isLt; omega), Nat.add_zero]
    simp only [g1, List.map_map]
    have hmap : ((List.finRange n).map
        ((fun g : Gate => g.inputs.count (n + i.val)) ∘
          (fun j : Fin n => ⟨GateOp.or, [j.val, n + mateVal n j]⟩))) =
        (List.finRange n).map (fun j : Fin n => if j = mateFin hn i then 1 else 0) := by
      apply List.map_congr_left
      intro j _
      simp only [Function.comp_apply]
      have hj : j.val < n := j.isLt
      have hne : j.val ≠ n + i.val := by omega
      simp only [List.count_cons, List.count_nil, beq_iff_eq, hne, ↓reduceIte, Nat.add_zero]
      have hiff : mateVal n j = i.val ↔ j = mateFin hn i := mateVal_eq_iff hn j i
      by_cases hjm : j = mateFin hn i
      · have hm : mateVal n j = i.val := hiff.mpr hjm
        rw [hm]
        simp [hjm]
      · have hm : mateVal n j ≠ i.val := fun h => hjm (hiff.mp h)
        simp [hjm, hm]
    rw [hmap]
    exact list_sum_ite_one (List.finRange n) (mateFin hn i)
      (List.nodup_finRange n) (List.mem_finRange _)

private theorem main_aux : (∀ (n : ℕ), 13 ≤ n →
  let offsets : Finset ℕ := {0, 1, 4, 6}
  let G := fun (u v : Fin n) => decide ((v.val + n - u.val) % n ∈ offsets)
  let mate := fun (source : Fin n) => (n + 1 - source.val) % n
  let signals := fun (u v : Fin n) => Finset.univ.filter
    (fun lit : Fin n => lit = u ∨ mate lit = v.val)
  (∀ i j : Fin n, i ≠ j → 6 ≤ (Finset.univ.filter (fun col => G i col ≠ G j col)).card) ∧
  (∀ i j : Fin n, i ≠ j → 6 ≤ (Finset.univ.filter (fun row => G row i ≠ G row j)).card) ∧
  (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (2 * n) C ∧
    PEqualNP.Represents.Represents G C ∧
    2 * n ≤ C.output ∧ C.output < 2 * n + C.size ∧
    PEqualNP.NotBracket.notCount C = 1 ∧
    (∀ g ∈ C.gates, g.op = .not → ∃ w : ℕ, g.inputs = [w]) ∧
    C.size ≤ (if n % 2 = 1 then 6 * n else 6 * n - 2) ∧
    ∀ i : Fin n,
      (∃ g ∈ C.gates, g.op = .or ∧ g.inputs = [i.val, n + mate i]) ∧
      (C.gates.map (fun g => g.inputs.count i.val)).sum = 1 ∧
      (C.gates.map (fun g => g.inputs.count (n + i.val))).sum = 1) ∧
  ¬ ∃ accept : Finset (Fin n) → Prop,
    (∀ S T, S ⊆ T → accept S → accept T) ∧
    ∀ u v : Fin n, accept (signals u v) ↔ G u v = true) := by
  intro n hn
  exact ⟨part1_rows hn, part1_cols hn, part3_circuit hn, part4_not_mono hn⟩

end PEqualNP.Outside.L_meta_25561_aux

theorem PEqualNP.Outside.L_meta_25561 : (∀ (n : ℕ), 13 ≤ n →
  let offsets : Finset ℕ := {0, 1, 4, 6}
  let G := fun (u v : Fin n) => decide ((v.val + n - u.val) % n ∈ offsets)
  let mate := fun (source : Fin n) => (n + 1 - source.val) % n
  let signals := fun (u v : Fin n) => Finset.univ.filter
    (fun lit : Fin n => lit = u ∨ mate lit = v.val)
  (∀ i j : Fin n, i ≠ j → 6 ≤ (Finset.univ.filter (fun col => G i col ≠ G j col)).card) ∧
  (∀ i j : Fin n, i ≠ j → 6 ≤ (Finset.univ.filter (fun row => G row i ≠ G row j)).card) ∧
  (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (2 * n) C ∧
    PEqualNP.Represents.Represents G C ∧
    2 * n ≤ C.output ∧ C.output < 2 * n + C.size ∧
    PEqualNP.NotBracket.notCount C = 1 ∧
    (∀ g ∈ C.gates, g.op = .not → ∃ w : ℕ, g.inputs = [w]) ∧
    C.size ≤ (if n % 2 = 1 then 6 * n else 6 * n - 2) ∧
    ∀ i : Fin n,
      (∃ g ∈ C.gates, g.op = .or ∧ g.inputs = [i.val, n + mate i]) ∧
      (C.gates.map (fun g => g.inputs.count i.val)).sum = 1 ∧
      (C.gates.map (fun g => g.inputs.count (n + i.val))).sum = 1) ∧
  ¬ ∃ accept : Finset (Fin n) → Prop,
    (∀ S T, S ⊆ T → accept S → accept T) ∧
    ∀ u v : Fin n, accept (signals u v) ↔ G u v = true) :=
  PEqualNP.Outside.L_meta_25561_aux.main_aux
