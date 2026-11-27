import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_574_aux

private def locFn (n : Nat) (hn : 0 < n) (k : Nat) : Fin n :=
  ⟨k % n, Nat.mod_lt _ hn⟩

private def winFn {n h : Nat} (hn : 0 < n) (x : Fin n → Bool) (p : Fin n) : Fin (n - h) → Bool :=
  fun j => x (locFn n hn (p.val + j.val))

private def tilePos (a h : Nat) (arc : Bool) (t c : Nat) : Nat :=
  (if arc then a else 0) + t * h + c

private theorem tilePos_lt_sub {a b h q : Nat} (hqa : q * h < a) (hqb : (q + 1) * h ≤ b)
    (arc : Bool) {t c : Nat} (ht : t < q) (hc : c < h) :
    tilePos a h arc t c < (a + b) - h := by
  have hth : (t + 1) * h ≤ q * h := Nat.mul_le_mul_right h (by omega)
  rw [Nat.add_mul, Nat.one_mul] at hth
  have hqb' : q * h + h ≤ b := by rw [Nat.add_mul, Nat.one_mul] at hqb; exact hqb
  cases arc <;> dsimp only [tilePos] <;> simp only [↓reduceIte, Bool.false_eq_true] <;> omega

private theorem tilePos_lt {a b h q : Nat} (hqa : q * h < a) (hqb : (q + 1) * h ≤ b)
    (arc : Bool) {t c : Nat} (ht : t < q) (hc : c < h) :
    tilePos a h arc t c < a + b :=
  (tilePos_lt_sub hqa hqb arc ht hc).trans_le (Nat.sub_le _ _)

private theorem tilePos_inj {a h q : Nat} (hqa : q * h < a)
    {arc1 arc2 : Bool} {t1 t2 c1 c2 : Nat}
    (ht1 : t1 < q) (ht2 : t2 < q) (hc1 : c1 < h) (hc2 : c2 < h)
    (heq : tilePos a h arc1 t1 c1 = tilePos a h arc2 t2 c2) :
    arc1 = arc2 ∧ t1 = t2 ∧ c1 = c2 := by
  have h1 : t1 * h + c1 < q * h := by
    have := Nat.mul_le_mul_right h (show t1 + 1 ≤ q by omega)
    rw [Nat.add_mul, Nat.one_mul] at this; omega
  have h2 : t2 * h + c2 < q * h := by
    have := Nat.mul_le_mul_right h (show t2 + 1 ≤ q by omega)
    rw [Nat.add_mul, Nat.one_mul] at this; omega
  have harc : arc1 = arc2 := by
    cases arc1 <;> cases arc2 <;> dsimp only [tilePos] at heq <;>
      simp only [↓reduceIte, Bool.false_eq_true] at heq <;> first | rfl | omega
  subst harc
  have htc : t1 * h + c1 = t2 * h + c2 := by
    cases arc1 <;> dsimp only [tilePos] at heq <;> simp only [↓reduceIte, Bool.false_eq_true] at heq <;> omega
  have hhpos : 0 < h := by omega
  have ht : t1 = t2 := by
    have hd1 : (t1 * h + c1) / h = t1 := by
      rw [Nat.mul_comm t1 h, Nat.mul_add_div hhpos, Nat.div_eq_of_lt hc1, Nat.add_zero]
    have hd2 : (t2 * h + c2) / h = t2 := by
      rw [Nat.mul_comm t2 h, Nat.mul_add_div hhpos, Nat.div_eq_of_lt hc2, Nat.add_zero]
    rw [← hd1, ← hd2, htc]
  subst ht
  exact ⟨rfl, rfl, by omega⟩

private def winOffset {n h : Nat} (p k : Fin n) (hp : h ≤ p.val)
    (hk : k.val < p.val - h ∨ p.val ≤ k.val) : Fin (n - h) :=
  if hle : p.val ≤ k.val then
    ⟨k.val - p.val, by have := k.isLt; omega⟩
  else
    ⟨n - p.val + k.val, by have := hk.resolve_right hle; omega⟩

private theorem loc_winOffset {n h : Nat} (hn : 0 < n) (p k : Fin n) (hp : h ≤ p.val)
    (hk : k.val < p.val - h ∨ p.val ≤ k.val) :
    locFn n hn (p.val + (winOffset p k hp hk).val) = k := by
  dsimp only [winOffset]
  split_ifs with hle
  · apply Fin.ext
    dsimp only [locFn]
    rw [show p.val + (k.val - p.val) = k.val by omega, Nat.mod_eq_of_lt k.isLt]
  · apply Fin.ext
    dsimp only [locFn]
    have hp_lt := p.isLt
    rw [show p.val + (n - p.val + k.val) = n + k.val by omega, Nat.add_mod_left, Nat.mod_eq_of_lt k.isLt]

private theorem winFn_winOffset {n h : Nat} (hn : 0 < n) (x : Fin n → Bool) (p k : Fin n)
    (hp : h ≤ p.val) (hk : k.val < p.val - h ∨ p.val ≤ k.val) :
    winFn (h := h) hn x p (winOffset p k hp hk) = x k := by
  dsimp only [winFn]
  rw [loc_winOffset]

private theorem winFn_zero {n h : Nat} (hn : 0 < n) (x : Fin n → Bool) (j : Fin (n - h)) :
    winFn (h := h) hn x ⟨0, hn⟩ j = x ⟨j.val, by have := j.isLt; omega⟩ := by
  dsimp only [winFn, locFn]
  congr 1
  apply Fin.ext
  dsimp only
  rw [Nat.zero_add, Nat.mod_eq_of_lt (by have := j.isLt; omega)]

private theorem port_div_spec {p h q : Nat} (hh : 0 < h) (hp : 0 < p) (hle : p ≤ q * h) (hmod : p % h = 0) :
    0 < p / h ∧ p / h ≤ q ∧ (p / h - 1 + 1) * h = p := by
  have h1 : h * (p / h) = p := by
    have := Nat.div_add_mod p h
    rw [hmod, Nat.add_zero] at this
    exact this
  have hpos : 0 < p / h :=
    Nat.pos_of_ne_zero fun h0 => by rw [h0, Nat.mul_zero] at h1; omega
  have hdiv : p / h ≤ q :=
    Nat.le_of_mul_le_mul_right (by rw [Nat.mul_comm, h1]; exact hle) hh
  have heq : (p / h - 1 + 1) * h = p := by
    rw [Nat.sub_add_cancel hpos, Nat.mul_comm, h1]
  exact ⟨hpos, hdiv, heq⟩

private theorem tilePos_outside_portL {a b h q : Nat} (hqa : q * h < a) (_hqb : (q + 1) * h ≤ b)
    (t0 : Fin q) (arc : Bool) (t : Fin q) (c : Fin h) (hne : (arc, t) ≠ (false, t0)) :
    tilePos a h arc t.val c.val < (t0.val + 1) * h - h ∨
    (t0.val + 1) * h ≤ tilePos a h arc t.val c.val := by
  have hsub : (t0.val + 1) * h - h = t0.val * h := by rw [Nat.add_mul, Nat.one_mul]; omega
  rw [hsub]
  cases arc
  · have htn : t.val ≠ t0.val := fun heq => hne (Prod.ext rfl (Fin.ext heq))
    dsimp only [tilePos]
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
    by_cases hlt : t.val < t0.val
    · left
      have h1 : (t.val + 1) * h ≤ t0.val * h := Nat.mul_le_mul_right h (by omega)
      rw [Nat.add_mul, Nat.one_mul] at h1
      have := c.isLt; omega
    · right
      have h1 : (t0.val + 1) * h ≤ t.val * h := Nat.mul_le_mul_right h (by omega)
      omega
  · right
    dsimp only [tilePos]
    simp only [↓reduceIte]
    have h1 : (t0.val + 1) * h ≤ q * h := Nat.mul_le_mul_right h (by have := t0.isLt; omega)
    omega

private theorem tilePos_outside_portR {a b h q : Nat} (hqa : q * h < a) (_hqb : (q + 1) * h ≤ b)
    (t0 : Fin q) (arc : Bool) (t : Fin q) (c : Fin h) (hne : (arc, t) ≠ (true, t0)) :
    tilePos a h arc t.val c.val < a + (t0.val + 1) * h - h ∨
    a + (t0.val + 1) * h ≤ tilePos a h arc t.val c.val := by
  have hsub : a + (t0.val + 1) * h - h = a + t0.val * h := by rw [Nat.add_mul, Nat.one_mul]; omega
  rw [hsub]
  cases arc
  · left
    dsimp only [tilePos]
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
    have h1 : (t.val + 1) * h ≤ q * h := Nat.mul_le_mul_right h (by have := t.isLt; omega)
    rw [Nat.add_mul, Nat.one_mul] at h1
    have := c.isLt; omega
  · have htn : t.val ≠ t0.val := fun heq => hne (Prod.ext rfl (Fin.ext heq))
    dsimp only [tilePos]
    simp only [↓reduceIte]
    by_cases hlt : t.val < t0.val
    · left
      have h1 : (t.val + 1) * h ≤ t0.val * h := Nat.mul_le_mul_right h (by omega)
      rw [Nat.add_mul, Nat.one_mul] at h1
      have := c.isLt; omega
    · right
      have h1 : (t0.val + 1) * h ≤ t.val * h := Nat.mul_le_mul_right h (by omega)
      omega

private theorem filter_card_mod2_iff {α : Type*} [Fintype α] [DecidableEq α]
    (f : α → Bool) (p0 : α) :
    (Finset.univ.filter (fun p => f p = true)).card % 2 = 0 ↔
      f p0 = decide (((Finset.univ.erase p0).filter (fun p => f p = true)).card % 2 = 1) := by
  let S0 := (Finset.univ.erase p0).filter (fun p => f p = true)
  have hnot : p0 ∉ S0 := by simp [S0]
  cases hp0 : f p0
  · have heq : Finset.univ.filter (fun p => f p = true) = S0 := by
      ext p
      simp only [S0, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true, true_and]
      constructor
      · intro hf
        refine ⟨fun he => ?_, hf⟩
        subst he; rw [hp0] at hf; cases hf
      · exact And.right
    rw [heq]
    change S0.card % 2 = 0 ↔ false = decide (S0.card % 2 = 1)
    rcases Nat.mod_two_eq_zero_or_one S0.card with h0 | h1
    · rw [h0]; decide
    · rw [h1]; decide
  · have heq : Finset.univ.filter (fun p => f p = true) = insert p0 S0 := by
      ext p
      simp only [S0, Finset.mem_insert, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true, true_and]
      by_cases hpe : p = p0
      · subst hpe; simp [hp0]
      · simp [hpe]
    rw [heq, Finset.card_insert_of_notMem hnot]
    change (S0.card + 1) % 2 = 0 ↔ true = decide (S0.card % 2 = 1)
    rcases Nat.mod_two_eq_zero_or_one S0.card with h0 | h1
    · rw [Nat.add_mod, h0]; decide
    · rw [Nat.add_mod, h1]; decide

private def isZeroLabelPat {a b h s q : Nat} (hsh : s ≤ h) (hqa : q * h < a) (hqb : (q + 1) * h ≤ b)
    (pat : Fin (a + b - h) → Bool) (arc : Bool) (t : Fin q) : Bool :=
  decide (∀ c : Fin s, pat ⟨tilePos a h arc t.val c.val,
    tilePos_lt_sub hqa hqb arc t.isLt (c.isLt.trans_le hsh)⟩ = false)

private def validPat {a b h s q : Nat} (hsh : s ≤ h) (hqa : q * h < a) (hqb : (q + 1) * h ≤ b)
    (pat : Fin (a + b - h) → Bool) : Bool :=
  decide ((Finset.univ.filter (fun t : Fin q => isZeroLabelPat hsh hqa hqb pat false t = true)).card = 1) &&
  decide ((Finset.univ.filter (fun t : Fin q => isZeroLabelPat hsh hqa hqb pat true t = true)).card = 1) &&
  decide (∀ c : Fin (h - s),
    (Finset.univ.filter (fun p : Bool × Fin q =>
      pat ⟨tilePos a h p.1 p.2.val (s + c.val),
        tilePos_lt_sub hqa hqb p.1 p.2.isLt (by have := c.isLt; omega)⟩ = true)).card % 2 = 0)

private def isZeroLabelWord {a b h s q : Nat} (hsh : s ≤ h) (hqa : q * h < a) (hqb : (q + 1) * h ≤ b)
    (x : Fin (a + b) → Bool) (arc : Bool) (t : Fin q) : Bool :=
  decide (∀ c : Fin s, x ⟨tilePos a h arc t.val c.val,
    tilePos_lt hqa hqb arc t.isLt (c.isLt.trans_le hsh)⟩ = false)

private def ValidWord {a b h s q : Nat} (hsh : s ≤ h) (hqa : q * h < a) (hqb : (q + 1) * h ≤ b)
    (x : Fin (a + b) → Bool) : Prop :=
  (Finset.univ.filter (fun t : Fin q => isZeroLabelWord hsh hqa hqb x false t = true)).card = 1 ∧
  (Finset.univ.filter (fun t : Fin q => isZeroLabelWord hsh hqa hqb x true t = true)).card = 1 ∧
  ∀ c : Fin (h - s),
    (Finset.univ.filter (fun p : Bool × Fin q =>
      x ⟨tilePos a h p.1 p.2.val (s + c.val),
        tilePos_lt hqa hqb p.1 p.2.isLt (by have := c.isLt; omega)⟩ = true)).card % 2 = 0

private theorem validPat_win_zero_iff {a b h s q : Nat} (hn : 0 < a + b) (hsh : s ≤ h)
    (hqa : q * h < a) (hqb : (q + 1) * h ≤ b) (x : Fin (a + b) → Bool) :
    validPat hsh hqa hqb (winFn (h := h) hn x ⟨0, hn⟩) = true ↔
      ValidWord hsh hqa hqb x := by
  have hzl : ∀ arc t, isZeroLabelPat hsh hqa hqb (winFn (h := h) hn x ⟨0, hn⟩) arc t =
      isZeroLabelWord hsh hqa hqb x arc t := by
    intro arc t
    dsimp only [isZeroLabelPat, isZeroLabelWord]
    congr 1; apply propext
    constructor
    · intro hall c; have hc := hall c; rw [winFn_zero] at hc; exact hc
    · intro hall c; rw [winFn_zero]; exact hall c
  dsimp only [validPat, ValidWord]
  simp only [Bool.and_eq_true, decide_eq_true_eq, hzl, winFn_zero]
  tauto

private def tileSite {a b h q : Nat} (hqa : q * h < a) (hqb : (q + 1) * h ≤ b)
    (arc : Bool) (t : Fin q) (c : Fin h) : Fin (a + b) :=
  ⟨tilePos a h arc t.val c.val, tilePos_lt hqa hqb arc t.isLt c.isLt⟩

private theorem tileSite_inj {a b h q : Nat} (hqa : q * h < a) (hqb : (q + 1) * h ≤ b)
    {a1 a2 : Bool} {t1 t2 : Fin q} {c1 c2 : Fin h}
    (heq : tileSite hqa hqb a1 t1 c1 = tileSite hqa hqb a2 t2 c2) :
    a1 = a2 ∧ t1 = t2 ∧ c1 = c2 := by
  rcases tilePos_inj hqa t1.isLt t2.isLt c1.isLt c2.isLt (congrArg Fin.val heq) with ⟨ha, ht, hc⟩
  exact ⟨ha, Fin.ext ht, Fin.ext hc⟩

private def labelCoords {a b h s q : Nat} (hsh : s ≤ h) (hqa : q * h < a) (hqb : (q + 1) * h ≤ b) :
    Finset (Fin (a + b)) :=
  Finset.univ.image (fun p : Bool × Fin q × Fin s =>
    tileSite hqa hqb p.1 p.2.1 ⟨p.2.2.val, p.2.2.isLt.trans_le hsh⟩)

private def parCoords {a b h s q : Nat} (hq : 0 < q) (hsh : s ≤ h)
    (hqa : q * h < a) (hqb : (q + 1) * h ≤ b) :
    Finset (Fin (a + b)) :=
  Finset.univ.image (fun c : Fin (h - s) =>
    tileSite hqa hqb false ⟨0, hq⟩ ⟨s + c.val, by have := c.isLt; omega⟩)

private def constrainedCoords {a b h s q : Nat} (hq : 0 < q) (hsh : s ≤ h)
    (hqa : q * h < a) (hqb : (q + 1) * h ≤ b) :
    Finset (Fin (a + b)) :=
  labelCoords hsh hqa hqb ∪ parCoords hq hsh hqa hqb

private theorem label_par_disjoint {a b h s q : Nat} (hq : 0 < q) (hsh : s ≤ h)
    (hqa : q * h < a) (hqb : (q + 1) * h ≤ b) :
    Disjoint (labelCoords hsh hqa hqb) (parCoords hq hsh hqa hqb) := by
  rw [Finset.disjoint_left]
  intro k hkL hkP
  simp only [labelCoords, parCoords, Finset.mem_image, Finset.mem_univ, true_and] at hkL hkP
  rcases hkL with ⟨⟨arc, t, c1⟩, rfl⟩
  rcases hkP with ⟨c2, hEq⟩
  rcases tileSite_inj hqa hqb hEq with ⟨_, _, hc⟩
  have hcv := congrArg Fin.val hc
  dsimp only at hcv
  have := c1.isLt; omega

private theorem constrainedCoords_card {a b h s q : Nat} (hq : 0 < q) (hsh : s ≤ h)
    (hqa : q * h < a) (hqb : (q + 1) * h ≤ b) :
    (constrainedCoords hq hsh hqa hqb).card = 2 * q * s + (h - s) := by
  rw [constrainedCoords, Finset.card_union_of_disjoint (label_par_disjoint hq hsh hqa hqb)]
  have hL : (labelCoords hsh hqa hqb).card = 2 * q * s := by
    rw [labelCoords, Finset.card_image_of_injective]
    · simp [Nat.mul_assoc]
    · rintro ⟨a1, t1, c1⟩ ⟨a2, t2, c2⟩ heq
      dsimp only at heq
      rcases tileSite_inj hqa hqb heq with ⟨ha, ht, hc⟩
      have hcv := congrArg Fin.val hc
      dsimp only at hcv
      exact Prod.ext ha (Prod.ext ht (Fin.ext hcv))
  have hP : (parCoords hq hsh hqa hqb).card = h - s := by
    rw [parCoords, Finset.card_image_of_injective]
    · simp
    · intro c1 c2 heq
      dsimp only at heq
      rcases tileSite_inj hqa hqb heq with ⟨_, _, hc⟩
      have hcv := congrArg Fin.val hc
      dsimp only at hcv
      exact Fin.ext (by omega)
  rw [hL, hP]

private abbrev NonZero (s : Nat) := {v : Fin s → Bool // v ≠ fun _ => false}

private theorem card_nonZero (s : Nat) : Fintype.card (NonZero s) = 2 ^ s - 1 := by
  have h := Fintype.card_subtype_compl (fun v : Fin s → Bool => v = fun _ => false)
  have h1 : Fintype.card {v : Fin s → Bool // v = fun _ => false} = 1 := by
    rw [Fintype.card_subtype_eq]
  have h2 : Fintype.card (Fin s → Bool) = 2 ^ s := by simp
  have h3 : Fintype.card (NonZero s) = Fintype.card {v : Fin s → Bool // ¬(v = fun _ => false)} := rfl
  rw [h3, h, h2, h1]

private abbrev Param (a b h s q : Nat) (hq : 0 < q) (hsh : s ≤ h)
    (hqa : q * h < a) (hqb : (q + 1) * h ≤ b) :=
  Σ (tL : Fin q) (tR : Fin q),
    ({t : Fin q // t ≠ tL} → NonZero s) ×
    ({t : Fin q // t ≠ tR} → NonZero s) ×
    ({k : Fin (a + b) // k ∉ constrainedCoords hq hsh hqa hqb} → Bool)

private theorem exists_unique_of_filter_card_one {α : Type*} [Fintype α] [DecidableEq α]
    {P : α → Bool} (hcard : (Finset.univ.filter (fun a => P a = true)).card = 1) :
    ∃! a : α, P a = true := by
  rcases Finset.card_eq_one.mp hcard with ⟨a, ha⟩
  refine ⟨a, ?_, ?_⟩
  · have hm : a ∈ Finset.univ.filter (fun b => P b = true) := by rw [ha]; exact Finset.mem_singleton_self a
    exact (Finset.mem_filter.mp hm).2
  · intro b hb
    have hm : b ∈ Finset.univ.filter (fun c => P c = true) := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩
    rw [ha, Finset.mem_singleton] at hm
    exact hm

private noncomputable def uniqueZeroTile {a b h s q : Nat} (hsh : s ≤ h)
    (hqa : q * h < a) (hqb : (q + 1) * h ≤ b)
    (x : Fin (a + b) → Bool) (hx : ValidWord hsh hqa hqb x) (arc : Bool) : Fin q :=
  Classical.choose (exists_unique_of_filter_card_one (by cases arc <;> [exact hx.1; exact hx.2.1]))

private theorem uniqueZeroTile_spec {a b h s q : Nat} (hsh : s ≤ h)
    (hqa : q * h < a) (hqb : (q + 1) * h ≤ b)
    (x : Fin (a + b) → Bool) (hx : ValidWord hsh hqa hqb x) (arc : Bool) :
    isZeroLabelWord hsh hqa hqb x arc (uniqueZeroTile hsh hqa hqb x hx arc) = true ∧
    ∀ t : Fin q, isZeroLabelWord hsh hqa hqb x arc t = true → t = uniqueZeroTile hsh hqa hqb x hx arc :=
  Classical.choose_spec (exists_unique_of_filter_card_one (by cases arc <;> [exact hx.1; exact hx.2.1]))

private theorem par_tile_not_constrained {a b h s q : Nat} (hq : 0 < q) (hsh : s ≤ h)
    (hqa : q * h < a) (hqb : (q + 1) * h ≤ b)
    (p : Bool × Fin q) (hp : p ≠ (false, ⟨0, hq⟩)) (c : Fin (h - s)) :
    tileSite hqa hqb p.1 p.2 ⟨s + c.val, by have := c.isLt; omega⟩ ∉ constrainedCoords hq hsh hqa hqb := by
  intro hmem
  rw [constrainedCoords, Finset.mem_union] at hmem
  rcases hmem with hL | hP
  · simp only [labelCoords, Finset.mem_image, Finset.mem_univ, true_and] at hL
    rcases hL with ⟨⟨a1, t1, c1⟩, hEq⟩
    dsimp only at hEq
    rcases tileSite_inj hqa hqb hEq with ⟨_, _, hc⟩
    have hcv := congrArg Fin.val hc
    dsimp only at hcv
    have := c1.isLt; omega
  · simp only [parCoords, Finset.mem_image, Finset.mem_univ, true_and] at hP
    rcases hP with ⟨c2, hEq⟩
    rcases tileSite_inj hqa hqb hEq with ⟨ha, ht, _⟩
    exact hp (Prod.ext ha.symm ht.symm)

private noncomputable def ofParamWord {a b h s q : Nat} (hq : 0 < q) (hsh : s ≤ h)
    (hqa : q * h < a) (hqb : (q + 1) * h ≤ b)
    (P : Param a b h s q hq hsh hqa hqb) : Fin (a + b) → Bool :=
  let tL := P.1
  let tR := P.2.1
  let nzL := P.2.2.1
  let nzR := P.2.2.2.1
  let free := P.2.2.2.2
  fun k =>
    if hL : ∃ p : Bool × Fin q × Fin s,
        tileSite hqa hqb p.1 p.2.1 ⟨p.2.2.val, p.2.2.isLt.trans_le hsh⟩ = k then
      let p := Classical.choose hL
      match p.1 with
      | false => if ht : p.2.1 = tL then false else (nzL ⟨p.2.1, ht⟩).1 p.2.2
      | true => if ht : p.2.1 = tR then false else (nzR ⟨p.2.1, ht⟩).1 p.2.2
    else if hP : ∃ c : Fin (h - s),
        tileSite hqa hqb false ⟨0, hq⟩ ⟨s + c.val, by have := c.isLt; omega⟩ = k then
      let c := Classical.choose hP
      decide (((Finset.univ.erase (false, ⟨0, hq⟩)).filter (fun p : Bool × Fin q =>
        if hp : p ≠ (false, ⟨0, hq⟩) then
          free ⟨tileSite hqa hqb p.1 p.2 ⟨s + c.val, by have := c.isLt; omega⟩,
            par_tile_not_constrained hq hsh hqa hqb p hp c⟩ = true
        else false)).card % 2 = 1)
    else
      have hnot : k ∉ constrainedCoords hq hsh hqa hqb := by
        intro hmem
        rw [constrainedCoords, Finset.mem_union] at hmem
        rcases hmem with hmL | hmP
        · simp only [labelCoords, Finset.mem_image, Finset.mem_univ, true_and] at hmL
          exact hL hmL
        · simp only [parCoords, Finset.mem_image, Finset.mem_univ, true_and] at hmP
          exact hP hmP
      free ⟨k, hnot⟩

private theorem ofParamWord_label {a b h s q : Nat} (hq : 0 < q) (hsh : s ≤ h)
    (hqa : q * h < a) (hqb : (q + 1) * h ≤ b)
    (P : Param a b h s q hq hsh hqa hqb) (arc : Bool) (t : Fin q) (c : Fin s) :
    ofParamWord hq hsh hqa hqb P (tileSite hqa hqb arc t ⟨c.val, c.isLt.trans_le hsh⟩) =
      match arc with
      | false => if ht : t = P.1 then false else (P.2.2.1 ⟨t, ht⟩).1 c
      | true => if ht : t = P.2.1 then false else (P.2.2.2.1 ⟨t, ht⟩).1 c := by
  have hex : ∃ p : Bool × Fin q × Fin s,
      tileSite hqa hqb p.1 p.2.1 ⟨p.2.2.val, p.2.2.isLt.trans_le hsh⟩ =
      tileSite hqa hqb arc t ⟨c.val, c.isLt.trans_le hsh⟩ := ⟨(arc, t, c), rfl⟩
  dsimp only [ofParamWord]
  simp only [hex, ↓reduceDIte]
  rcases tileSite_inj hqa hqb (Classical.choose_spec hex) with ⟨ha, ht, hc⟩
  have hcv := congrArg Fin.val hc
  dsimp only at hcv
  have hp : Classical.choose hex = (arc, t, c) := Prod.ext ha (Prod.ext ht (Fin.ext hcv))
  rw [hp]

private theorem ofParamWord_free {a b h s q : Nat} (hq : 0 < q) (hsh : s ≤ h)
    (hqa : q * h < a) (hqb : (q + 1) * h ≤ b)
    (P : Param a b h s q hq hsh hqa hqb) (k : Fin (a + b))
    (hk : k ∉ constrainedCoords hq hsh hqa hqb) :
    ofParamWord hq hsh hqa hqb P k = P.2.2.2.2 ⟨k, hk⟩ := by
  have hL : ¬∃ p : Bool × Fin q × Fin s,
      tileSite hqa hqb p.1 p.2.1 ⟨p.2.2.val, p.2.2.isLt.trans_le hsh⟩ = k := by
    rintro ⟨p, rfl⟩
    exact hk (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨p, Finset.mem_univ _, rfl⟩))
  have hP : ¬∃ c : Fin (h - s),
      tileSite hqa hqb false ⟨0, hq⟩ ⟨s + c.val, by have := c.isLt; omega⟩ = k := by
    rintro ⟨c, rfl⟩
    exact hk (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨c, Finset.mem_univ _, rfl⟩))
  dsimp only [ofParamWord]
  simp only [hL, hP, ↓reduceDIte]

private theorem ofParamWord_par0 {a b h s q : Nat} (hq : 0 < q) (hsh : s ≤ h)
    (hqa : q * h < a) (hqb : (q + 1) * h ≤ b)
    (P : Param a b h s q hq hsh hqa hqb) (c : Fin (h - s)) :
    ofParamWord hq hsh hqa hqb P (tileSite hqa hqb false ⟨0, hq⟩ ⟨s + c.val, by have := c.isLt; omega⟩) =
      decide (((Finset.univ.erase (false, ⟨0, hq⟩)).filter (fun p : Bool × Fin q =>
        ofParamWord hq hsh hqa hqb P (tileSite hqa hqb p.1 p.2 ⟨s + c.val, by have := c.isLt; omega⟩) = true)).card % 2 = 1) := by
  have hL : ¬∃ p : Bool × Fin q × Fin s,
      tileSite hqa hqb p.1 p.2.1 ⟨p.2.2.val, p.2.2.isLt.trans_le hsh⟩ =
      tileSite hqa hqb false ⟨0, hq⟩ ⟨s + c.val, by have := c.isLt; omega⟩ := by
    rintro ⟨p, hEq⟩
    rcases tileSite_inj hqa hqb hEq with ⟨_, _, hc⟩
    have hcv := congrArg Fin.val hc
    dsimp only at hcv
    have := p.2.2.isLt; omega
  have hP : ∃ c1 : Fin (h - s),
      tileSite hqa hqb false ⟨0, hq⟩ ⟨s + c1.val, by have := c1.isLt; omega⟩ =
      tileSite hqa hqb false ⟨0, hq⟩ ⟨s + c.val, by have := c.isLt; omega⟩ := ⟨c, rfl⟩
  have hcEq : Classical.choose hP = c := by
    rcases tileSite_inj hqa hqb (Classical.choose_spec hP) with ⟨_, _, hc⟩
    have hcv := congrArg Fin.val hc
    dsimp only at hcv
    exact Fin.ext (by omega)
  have hlhs : ofParamWord hq hsh hqa hqb P (tileSite hqa hqb false ⟨0, hq⟩ ⟨s + c.val, by have := c.isLt; omega⟩) =
      decide (((Finset.univ.erase (false, ⟨0, hq⟩)).filter (fun p : Bool × Fin q =>
        if hp : p ≠ (false, ⟨0, hq⟩) then
          P.2.2.2.2 ⟨tileSite hqa hqb p.1 p.2 ⟨s + c.val, by have := c.isLt; omega⟩,
            par_tile_not_constrained hq hsh hqa hqb p hp c⟩ = true
        else false)).card % 2 = 1) := by
    dsimp only [ofParamWord]
    simp only [hL, hP, ↓reduceDIte]
    have hcast : ∀ c1 : Fin (h - s), c1 = c →
        decide (((Finset.univ.erase (false, ⟨0, hq⟩)).filter (fun p : Bool × Fin q =>
          if hp : p ≠ (false, ⟨0, hq⟩) then
            P.2.2.2.2 ⟨tileSite hqa hqb p.1 p.2 ⟨s + c1.val, by have := c1.isLt; omega⟩,
              par_tile_not_constrained hq hsh hqa hqb p hp c1⟩ = true
          else false)).card % 2 = 1) =
        decide (((Finset.univ.erase (false, ⟨0, hq⟩)).filter (fun p : Bool × Fin q =>
          if hp : p ≠ (false, ⟨0, hq⟩) then
            P.2.2.2.2 ⟨tileSite hqa hqb p.1 p.2 ⟨s + c.val, by have := c.isLt; omega⟩,
              par_tile_not_constrained hq hsh hqa hqb p hp c⟩ = true
          else false)).card % 2 = 1) := by
      rintro _ rfl; rfl
    exact hcast _ hcEq
  rw [hlhs]
  apply congrArg (fun S : Finset (Bool × Fin q) => decide (S.card % 2 = 1))
  apply Finset.filter_congr
  intro p hp
  have hne : p ≠ (false, ⟨0, hq⟩) := (Finset.mem_erase.mp hp).1
  split_ifs
  rw [ofParamWord_free hq hsh hqa hqb P _ (par_tile_not_constrained hq hsh hqa hqb p hne c)]

private theorem ofParamWord_valid {a b h s q : Nat} (hq : 0 < q) (hsh : s ≤ h)
    (hqa : q * h < a) (hqb : (q + 1) * h ≤ b)
    (P : Param a b h s q hq hsh hqa hqb) :
    ValidWord hsh hqa hqb (ofParamWord hq hsh hqa hqb P) := by
  have hzlL : ∀ t : Fin q,
      isZeroLabelWord hsh hqa hqb (ofParamWord hq hsh hqa hqb P) false t = true ↔ t = P.1 := by
    intro t
    dsimp only [isZeroLabelWord]
    rw [decide_eq_true_eq]
    constructor
    · intro hall
      by_contra hne
      apply (P.2.2.1 ⟨t, hne⟩).2
      funext c
      have hc := hall c
      change ofParamWord hq hsh hqa hqb P (tileSite hqa hqb false t ⟨c.val, c.isLt.trans_le hsh⟩) = false at hc
      rw [ofParamWord_label] at hc
      simpa [hne] using hc
    · rintro rfl c
      change ofParamWord hq hsh hqa hqb P (tileSite hqa hqb false P.1 ⟨c.val, c.isLt.trans_le hsh⟩) = false
      rw [ofParamWord_label]
      simp
  have hzlR : ∀ t : Fin q,
      isZeroLabelWord hsh hqa hqb (ofParamWord hq hsh hqa hqb P) true t = true ↔ t = P.2.1 := by
    intro t
    dsimp only [isZeroLabelWord]
    rw [decide_eq_true_eq]
    constructor
    · intro hall
      by_contra hne
      apply (P.2.2.2.1 ⟨t, hne⟩).2
      funext c
      have hc := hall c
      change ofParamWord hq hsh hqa hqb P (tileSite hqa hqb true t ⟨c.val, c.isLt.trans_le hsh⟩) = false at hc
      rw [ofParamWord_label] at hc
      simpa [hne] using hc
    · rintro rfl c
      change ofParamWord hq hsh hqa hqb P (tileSite hqa hqb true P.2.1 ⟨c.val, c.isLt.trans_le hsh⟩) = false
      rw [ofParamWord_label]
      simp
  refine ⟨?_, ?_, ?_⟩
  · have hfilt : Finset.univ.filter (fun t : Fin q =>
        isZeroLabelWord hsh hqa hqb (ofParamWord hq hsh hqa hqb P) false t = true) = {P.1} := by
      ext t; simp [hzlL]
    rw [hfilt, Finset.card_singleton]
  · have hfilt : Finset.univ.filter (fun t : Fin q =>
        isZeroLabelWord hsh hqa hqb (ofParamWord hq hsh hqa hqb P) true t = true) = {P.2.1} := by
      ext t; simp [hzlR]
    rw [hfilt, Finset.card_singleton]
  · intro c
    exact (filter_card_mod2_iff (fun p : Bool × Fin q =>
      ofParamWord hq hsh hqa hqb P (tileSite hqa hqb p.1 p.2 ⟨s + c.val, by have := c.isLt; omega⟩))
      (false, ⟨0, hq⟩)).mpr (ofParamWord_par0 hq hsh hqa hqb P c)

private noncomputable def toParamOfValid {a b h s q : Nat} (hq : 0 < q) (hsh : s ≤ h)
    (hqa : q * h < a) (hqb : (q + 1) * h ≤ b)
    (v : {x : Fin (a + b) → Bool // ValidWord hsh hqa hqb x}) :
    Param a b h s q hq hsh hqa hqb :=
  let x := v.1
  let hx := v.2
  let tL := uniqueZeroTile hsh hqa hqb x hx false
  let tR := uniqueZeroTile hsh hqa hqb x hx true
  let nzL : {t : Fin q // t ≠ tL} → NonZero s := fun ⟨t, ht⟩ =>
    ⟨fun c => x (tileSite hqa hqb false t ⟨c.val, c.isLt.trans_le hsh⟩), fun heq => by
      have hzero : isZeroLabelWord hsh hqa hqb x false t = true := by
        dsimp only [isZeroLabelWord]
        rw [decide_eq_true_eq]
        intro c
        exact congrFun heq c
      exact ht ((uniqueZeroTile_spec hsh hqa hqb x hx false).2 t hzero)⟩
  let nzR : {t : Fin q // t ≠ tR} → NonZero s := fun ⟨t, ht⟩ =>
    ⟨fun c => x (tileSite hqa hqb true t ⟨c.val, c.isLt.trans_le hsh⟩), fun heq => by
      have hzero : isZeroLabelWord hsh hqa hqb x true t = true := by
        dsimp only [isZeroLabelWord]
        rw [decide_eq_true_eq]
        intro c
        exact congrFun heq c
      exact ht ((uniqueZeroTile_spec hsh hqa hqb x hx true).2 t hzero)⟩
  let free : {k : Fin (a + b) // k ∉ constrainedCoords hq hsh hqa hqb} → Bool :=
    fun ⟨k, _⟩ => x k
  ⟨tL, tR, nzL, nzR, free⟩

private noncomputable def validWordEquivParam {a b h s q : Nat} (hq : 0 < q) (hsh : s ≤ h)
    (hqa : q * h < a) (hqb : (q + 1) * h ≤ b) :
    {x : Fin (a + b) → Bool // ValidWord hsh hqa hqb x} ≃ Param a b h s q hq hsh hqa hqb where
  toFun := toParamOfValid hq hsh hqa hqb
  invFun := fun P => ⟨ofParamWord hq hsh hqa hqb P, ofParamWord_valid hq hsh hqa hqb P⟩
  left_inv := by
    rintro ⟨x, hx⟩
    apply Subtype.ext
    funext k
    dsimp only
    let P := toParamOfValid hq hsh hqa hqb ⟨x, hx⟩
    change ofParamWord hq hsh hqa hqb P k = x k
    by_cases hk : k ∈ constrainedCoords hq hsh hqa hqb
    · rw [constrainedCoords, Finset.mem_union] at hk
      rcases hk with hkL | hkP
      · simp only [labelCoords, Finset.mem_image, Finset.mem_univ, true_and] at hkL
        rcases hkL with ⟨⟨arc, t, c⟩, rfl⟩
        dsimp only
        rw [ofParamWord_label]
        cases arc
        · dsimp only
          split_ifs with ht
          · subst ht
            have h0 := (uniqueZeroTile_spec hsh hqa hqb x hx false).1
            dsimp only [isZeroLabelWord] at h0
            rw [decide_eq_true_eq] at h0
            exact (h0 c).symm
          · rfl
        · dsimp only
          split_ifs with ht
          · subst ht
            have h0 := (uniqueZeroTile_spec hsh hqa hqb x hx true).1
            dsimp only [isZeroLabelWord] at h0
            rw [decide_eq_true_eq] at h0
            exact (h0 c).symm
          · rfl
      · simp only [parCoords, Finset.mem_image, Finset.mem_univ, true_and] at hkP
        rcases hkP with ⟨c, rfl⟩
        rw [ofParamWord_par0]
        have hfilt : (Finset.univ.erase (false, (⟨0, hq⟩ : Fin q))).filter (fun p : Bool × Fin q =>
              ofParamWord hq hsh hqa hqb P
                (tileSite hqa hqb p.1 p.2 ⟨s + c.val, by have := c.isLt; omega⟩) = true) =
            (Finset.univ.erase (false, (⟨0, hq⟩ : Fin q))).filter (fun p : Bool × Fin q =>
              x (tileSite hqa hqb p.1 p.2 ⟨s + c.val, by have := c.isLt; omega⟩) = true) := by
          apply Finset.filter_congr
          intro p hp
          have hne : p ≠ (false, ⟨0, hq⟩) := (Finset.mem_erase.mp hp).1
          rw [ofParamWord_free hq hsh hqa hqb P _ (par_tile_not_constrained hq hsh hqa hqb p hne c)]
          rfl
        rw [hfilt]
        exact ((filter_card_mod2_iff (fun p : Bool × Fin q =>
          x (tileSite hqa hqb p.1 p.2 ⟨s + c.val, by have := c.isLt; omega⟩))
          (false, ⟨0, hq⟩)).mp (hx.2.2 c)).symm
    · rw [ofParamWord_free hq hsh hqa hqb P k hk]; rfl
  right_inv := by
    rintro ⟨tL, tR, nzL, nzR, free⟩
    let P : Param a b h s q hq hsh hqa hqb := ⟨tL, tR, nzL, nzR, free⟩
    let x := ofParamWord hq hsh hqa hqb P
    let hx := ofParamWord_valid hq hsh hqa hqb P
    have htL : uniqueZeroTile hsh hqa hqb x hx false = tL := by
      symm
      apply (uniqueZeroTile_spec hsh hqa hqb x hx false).2
      dsimp only [isZeroLabelWord]
      rw [decide_eq_true_eq]
      intro c
      change ofParamWord hq hsh hqa hqb P (tileSite hqa hqb false tL ⟨c.val, c.isLt.trans_le hsh⟩) = false
      rw [ofParamWord_label]; simp [P]
    have htR : uniqueZeroTile hsh hqa hqb x hx true = tR := by
      symm
      apply (uniqueZeroTile_spec hsh hqa hqb x hx true).2
      dsimp only [isZeroLabelWord]
      rw [decide_eq_true_eq]
      intro c
      change ofParamWord hq hsh hqa hqb P (tileSite hqa hqb true tR ⟨c.val, c.isLt.trans_le hsh⟩) = false
      rw [ofParamWord_label]; simp [P]
    have hrec : ∀ (tL' : Fin q) (hEq : tL' = tL) (tR' : Fin q) (hEqR : tR' = tR)
        (f1 : {t : Fin q // t ≠ tL'} → NonZero s) (f2 : {t : Fin q // t ≠ tR'} → NonZero s)
        (fr : {k : Fin (a + b) // k ∉ constrainedCoords hq hsh hqa hqb} → Bool),
        (∀ (t : Fin q) (ht : t ≠ tL), f1 ⟨t, by rwa [hEq]⟩ = nzL ⟨t, ht⟩) →
        (∀ (t : Fin q) (ht : t ≠ tR), f2 ⟨t, by rwa [hEqR]⟩ = nzR ⟨t, ht⟩) →
        fr = free →
        (⟨tL', tR', f1, f2, fr⟩ : Param a b h s q hq hsh hqa hqb) = ⟨tL, tR, nzL, nzR, free⟩ := by
      rintro tL' rfl tR' rfl f1 f2 fr h1 h2 rfl
      refine Sigma.ext rfl (heq_of_eq (Sigma.ext rfl (heq_of_eq (Prod.ext ?_ (Prod.ext ?_ rfl)))))
      · funext ⟨t, ht⟩; exact h1 t ht
      · funext ⟨t, ht⟩; exact h2 t ht
    change toParamOfValid hq hsh hqa hqb ⟨x, hx⟩ = ⟨tL, tR, nzL, nzR, free⟩
    dsimp only [toParamOfValid]
    apply hrec _ htL _ htR
    · intro t ht
      apply Subtype.ext; funext c
      change ofParamWord hq hsh hqa hqb P (tileSite hqa hqb false t ⟨c.val, c.isLt.trans_le hsh⟩) = (nzL ⟨t, ht⟩).1 c
      rw [ofParamWord_label]; simp [P, ht]
    · intro t ht
      apply Subtype.ext; funext c
      change ofParamWord hq hsh hqa hqb P (tileSite hqa hqb true t ⟨c.val, c.isLt.trans_le hsh⟩) = (nzR ⟨t, ht⟩).1 c
      rw [ofParamWord_label]; simp [P, ht]
    · funext ⟨k, hk⟩
      exact ofParamWord_free hq hsh hqa hqb P k hk

private theorem card_validWord {a b h s q : Nat} (hq : 0 < q) (hsh : s ≤ h)
    (hqa : q * h < a) (hqb : (q + 1) * h ≤ b)
    [Fintype {x : Fin (a + b) → Bool // ValidWord hsh hqa hqb x}] :
    Fintype.card {x : Fin (a + b) → Bool // ValidWord hsh hqa hqb x} =
      q ^ 2 * (2 ^ s - 1) ^ (2 * (q - 1)) * 2 ^ (a + b - (2 * q * s + (h - s))) := by
  classical
  have hfree : Fintype.card {k : Fin (a + b) // k ∉ constrainedCoords hq hsh hqa hqb} =
      a + b - (2 * q * s + (h - s)) := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin]
    have hmem : Fintype.card {k : Fin (a + b) // k ∈ constrainedCoords hq hsh hqa hqb} =
        (constrainedCoords hq hsh hqa hqb).card := Fintype.card_coe _
    rw [hmem, constrainedCoords_card hq hsh hqa hqb]
  have hsub : ∀ t0 : Fin q, Fintype.card {t : Fin q // t ≠ t0} = q - 1 := by
    intro t0
    have h := Fintype.card_subtype_compl (fun t : Fin q => t = t0)
    have h1 : Fintype.card {t : Fin q // t = t0} = 1 := Fintype.card_subtype_eq t0
    have h2 : Fintype.card (Fin q) = q := Fintype.card_fin q
    have h3 : Fintype.card {t : Fin q // t ≠ t0} = Fintype.card {t : Fin q // ¬(t = t0)} := rfl
    rw [h3, h, h2, h1]
  rw [@Fintype.card_congr _ _ _
    (@Sigma.instFintype _ _ (fun _ => @Sigma.instFintype _ _ (fun _ => inferInstance) inferInstance) inferInstance)
    (validWordEquivParam hq hsh hqa hqb)]
  simp only [Fintype.card_sigma, Fintype.card_prod, Fintype.card_fun, card_nonZero,
    hsub, hfree, Fintype.card_bool, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have hpow : (2 ^ s - 1) ^ (q - 1) * (2 ^ s - 1) ^ (q - 1) = (2 ^ s - 1) ^ (2 * (q - 1)) := by
    rw [← pow_add, ← two_mul]
  calc q * (q * ((2 ^ s - 1) ^ (q - 1) * ((2 ^ s - 1) ^ (q - 1) * 2 ^ (a + b - (2 * q * s + (h - s))))))
      = (q * q) * ((2 ^ s - 1) ^ (q - 1) * (2 ^ s - 1) ^ (q - 1)) * 2 ^ (a + b - (2 * q * s + (h - s))) := by ring
    _ = q ^ 2 * (2 ^ s - 1) ^ (2 * (q - 1)) * 2 ^ (a + b - (2 * q * s + (h - s))) := by
        rw [sq, hpow]

private def portL {a b h q : Nat} (hqa : q * h < a) (hqb : (q + 1) * h ≤ b) (t : Fin q) : Fin (a + b) :=
  ⟨(t.val + 1) * h, by
    have h1 : (t.val + 1) * h ≤ q * h := Nat.mul_le_mul_right h (by have := t.isLt; omega)
    omega⟩

private def portR {a b h s q : Nat} (hs : 0 < s) (hsh : s ≤ h) (_hqa : q * h < a) (hqb : (q + 1) * h ≤ b)
    (t : Fin q) : Fin (a + b) :=
  ⟨a + (t.val + 1) * h, by
    have h1 : (t.val + 1) * h ≤ q * h := Nat.mul_le_mul_right h (by have := t.isLt; omega)
    have h2 : q * h + h ≤ b := by rw [Nat.add_mul, Nat.one_mul] at hqb; exact hqb
    omega⟩

private def baseFn {a b h s q : Nat} (_hn : 0 < a + b) (hs : 0 < s) (hsh : s ≤ h)
    (hqa : q * h < a) (hqb : (q + 1) * h ≤ b)
    (slot : Fin (a + b) × (Fin (a + b - h) → Bool)) : Bool :=
  let p := slot.1
  let pat := slot.2
  if p.val = 0 then
    validPat hsh hqa hqb pat
  else if hL : 0 < p.val ∧ p.val ≤ q * h ∧ p.val % h = 0 then
    have hds := port_div_spec (by omega) hL.1 hL.2.1 hL.2.2
    let t0 : Fin q := ⟨p.val / h - 1, by omega⟩
    have hp_eq : p.val = (t0.val + 1) * h := hds.2.2.symm
    have hhp : h ≤ p.val := by rw [hp_eq]; exact Nat.le_mul_of_pos_left h (by omega)
    decide (∃ t' : Fin q, ∃ hne : t' ≠ t0,
      ∀ c : Fin s, pat (winOffset p (tileSite hqa hqb false t' ⟨c.val, c.isLt.trans_le hsh⟩) hhp
        (by
          have hk := tilePos_outside_portL hqa hqb t0 false t' ⟨c.val, c.isLt.trans_le hsh⟩
            (fun hEq => hne (congrArg Prod.snd hEq))
          dsimp only [tileSite]
          rwa [hp_eq])) = false)
  else if hR : a < p.val ∧ p.val ≤ a + q * h ∧ (p.val - a) % h = 0 then
    have hds := port_div_spec (q := q) (by omega) (by omega) (by omega) hR.2.2
    let t0 : Fin q := ⟨(p.val - a) / h - 1, by omega⟩
    have hp_eq : p.val = a + (t0.val + 1) * h := by
      have h1 : (t0.val + 1) * h = p.val - a := hds.2.2
      omega
    have hhp : h ≤ p.val := by
      rw [hp_eq]
      have : h ≤ (t0.val + 1) * h := Nat.le_mul_of_pos_left h (by omega)
      omega
    decide (∃ t' : Fin q, ∃ hne : t' ≠ t0,
      ∀ c : Fin s, pat (winOffset p (tileSite hqa hqb true t' ⟨c.val, c.isLt.trans_le hsh⟩) hhp
        (by
          have hk := tilePos_outside_portR hqa hqb t0 true t' ⟨c.val, c.isLt.trans_le hsh⟩
            (fun hEq => hne (congrArg Prod.snd hEq))
          dsimp only [tileSite]
          rwa [hp_eq])) = false)
  else
    true

private theorem baseFn_valid_word {a b h s q : Nat} (hn : 0 < a + b) (hs : 0 < s) (hsh : s ≤ h)
    (hqa : q * h < a) (hqb : (q + 1) * h ≤ b)
    (x : Fin (a + b) → Bool) (hx : ValidWord hsh hqa hqb x) (p : Fin (a + b)) :
    baseFn hn hs hsh hqa hqb (p, winFn (h := h) hn x p) = false ↔
      p = portL hqa hqb (uniqueZeroTile hsh hqa hqb x hx false) ∨
      p = portR hs hsh hqa hqb (uniqueZeroTile hsh hqa hqb x hx true) := by
  have hh : 0 < h := by omega
  let tL := uniqueZeroTile hsh hqa hqb x hx false
  let tR := uniqueZeroTile hsh hqa hqb x hx true
  have hspecL := uniqueZeroTile_spec hsh hqa hqb x hx false
  have hspecR := uniqueZeroTile_spec hsh hqa hqb x hx true
  change baseFn hn hs hsh hqa hqb (p, winFn (h := h) hn x p) = false ↔
    p = portL hqa hqb tL ∨ p = portR hs hsh hqa hqb tR
  dsimp only [baseFn]
  by_cases hp0 : p.val = 0
  · simp only [hp0, ↓reduceIte]
    have hp_eq : p = ⟨0, hn⟩ := Fin.ext hp0
    rw [hp_eq, (validPat_win_zero_iff hn hsh hqa hqb x).mpr hx]
    simp only [Bool.true_eq_false, false_iff, not_or]
    constructor
    · intro heq
      have hv := congrArg Fin.val heq
      dsimp only [portL] at hv
      have : h ≤ (tL.val + 1) * h := Nat.le_mul_of_pos_left h (by omega)
      omega
    · intro heq
      have hv := congrArg Fin.val heq
      dsimp only [portR] at hv
      have : h ≤ (tR.val + 1) * h := Nat.le_mul_of_pos_left h (by omega)
      omega
  · simp only [hp0, ↓reduceIte]
    by_cases hL : 0 < p.val ∧ p.val ≤ q * h ∧ p.val % h = 0
    · simp only [hL, and_self, ↓reduceDIte]
      have hds := port_div_spec hh hL.1 hL.2.1 hL.2.2
      let t0 : Fin q := ⟨p.val / h - 1, by omega⟩
      have hp_eq : p = portL hqa hqb t0 := Fin.ext hds.2.2.symm
      have hneR : p ≠ portR hs hsh hqa hqb tR := by
        intro heq
        have hv := congrArg Fin.val heq
        dsimp only [portR] at hv; omega
      simp only [hneR, or_false, decide_eq_false_iff_not, not_exists, not_forall]
      constructor
      · intro hno
        have hteq : t0 = tL := by
          by_contra hne
          rcases hno tL (Ne.symm hne) with ⟨c, hc⟩
          rw [winFn_winOffset] at hc
          have h0 := hspecL.1
          dsimp only [isZeroLabelWord] at h0
          rw [decide_eq_true_eq] at h0
          exact hc (h0 c)
        rw [hp_eq, hteq]
      · intro hpeq t' hne
        have hteq : t0 = tL := by
          have hv := congrArg Fin.val (hp_eq.symm.trans hpeq)
          dsimp only [portL] at hv
          have h1 : t0.val + 1 = tL.val + 1 := Nat.eq_of_mul_eq_mul_right hh hv
          exact Fin.ext (by omega)
        have htne : t' ≠ tL := hteq ▸ hne
        have hnotz : isZeroLabelWord hsh hqa hqb x false t' ≠ true := fun hz => htne (hspecL.2 t' hz)
        dsimp only [isZeroLabelWord] at hnotz
        rw [ne_eq, decide_eq_true_eq] at hnotz
        push Not at hnotz
        rcases hnotz with ⟨c, hc⟩
        refine ⟨c, ?_⟩
        rw [winFn_winOffset]
        exact hc
    · simp only [hL, ↓reduceDIte]
      have hneL : p ≠ portL hqa hqb tL := by
        intro heq
        apply hL
        have hv := congrArg Fin.val heq
        dsimp only [portL] at hv
        have hle : (tL.val + 1) * h ≤ q * h := Nat.mul_le_mul_right h (by have := tL.isLt; omega)
        have hpos : 0 < (tL.val + 1) * h := Nat.mul_pos (by omega) hh
        exact ⟨by omega, by omega, by rw [hv]; exact Nat.mul_mod_left _ _⟩
      by_cases hR : a < p.val ∧ p.val ≤ a + q * h ∧ (p.val - a) % h = 0
      · simp only [hR, and_self, ↓reduceDIte]
        have hds := port_div_spec (q := q) hh (by omega) (by omega) hR.2.2
        let t0 : Fin q := ⟨(p.val - a) / h - 1, by omega⟩
        have hp_eq : p = portR hs hsh hqa hqb t0 := by
          apply Fin.ext
          dsimp only [portR, t0]
          have h1 : ((p.val - a) / h - 1 + 1) * h = p.val - a := hds.2.2
          omega
        simp only [hneL, false_or, decide_eq_false_iff_not, not_exists, not_forall]
        constructor
        · intro hno
          have hteq : t0 = tR := by
            by_contra hne
            rcases hno tR (Ne.symm hne) with ⟨c, hc⟩
            rw [winFn_winOffset] at hc
            have h0 := hspecR.1
            dsimp only [isZeroLabelWord] at h0
            rw [decide_eq_true_eq] at h0
            exact hc (h0 c)
          rw [hp_eq, hteq]
        · intro hpeq t' hne
          have hteq : t0 = tR := by
            have hv := congrArg Fin.val (hp_eq.symm.trans hpeq)
            dsimp only [portR] at hv
            have hmul : (t0.val + 1) * h = (tR.val + 1) * h := by omega
            have h1 : t0.val + 1 = tR.val + 1 := Nat.eq_of_mul_eq_mul_right hh hmul
            exact Fin.ext (by omega)
          have htne : t' ≠ tR := hteq ▸ hne
          have hnotz : isZeroLabelWord hsh hqa hqb x true t' ≠ true := fun hz => htne (hspecR.2 t' hz)
          dsimp only [isZeroLabelWord] at hnotz
          rw [ne_eq, decide_eq_true_eq] at hnotz
          push Not at hnotz
          rcases hnotz with ⟨c, hc⟩
          refine ⟨c, ?_⟩
          rw [winFn_winOffset]
          exact hc
      · simp only [hR, ↓reduceDIte, Bool.true_eq_false, false_iff, not_or]
        refine ⟨hneL, fun heq => hR ?_⟩
        have hv := congrArg Fin.val heq
        dsimp only [portR] at hv
        have hle : (tR.val + 1) * h ≤ q * h := Nat.mul_le_mul_right h (by have := tR.isLt; omega)
        have hpos : 0 < (tR.val + 1) * h := Nat.mul_pos (by omega) hh
        exact ⟨by omega, by omega, by rw [hv, Nat.add_sub_cancel_left]; exact Nat.mul_mod_left _ _⟩

private theorem recover_from_port {a b h s q : Nat} (hn : 0 < a + b) (hs : 0 < s) (hsh : s ≤ h)
    (hqa : q * h < a) (hqb : (q + 1) * h ≤ b)
    (arc : Bool) (x1 x2 : Fin (a + b) → Bool)
    (hx1 : ValidWord hsh hqa hqb x1) (hx2 : ValidWord hsh hqa hqb x2)
    (ht_eq : uniqueZeroTile hsh hqa hqb x1 hx1 arc = uniqueZeroTile hsh hqa hqb x2 hx2 arc)
    (hwin : winFn (h := h) hn x1
        (if arc then portR hs hsh hqa hqb (uniqueZeroTile hsh hqa hqb x1 hx1 arc)
         else portL hqa hqb (uniqueZeroTile hsh hqa hqb x1 hx1 arc)) =
      winFn (h := h) hn x2
        (if arc then portR hs hsh hqa hqb (uniqueZeroTile hsh hqa hqb x2 hx2 arc)
         else portL hqa hqb (uniqueZeroTile hsh hqa hqb x2 hx2 arc))) :
    x1 = x2 := by
  let t0 := uniqueZeroTile hsh hqa hqb x1 hx1 arc
  let p : Fin (a + b) := if arc then portR hs hsh hqa hqb t0 else portL hqa hqb t0
  have hwin' : winFn (h := h) hn x1 p = winFn (h := h) hn x2 p := by
    dsimp only [p, t0]; simpa [ht_eq] using hwin
  have hhp : h ≤ p.val := by
    cases arc <;> dsimp only [p, portL, portR] <;> simp only [↓reduceIte, Bool.false_eq_true]
    · exact Nat.le_mul_of_pos_left h (by omega)
    · have : h ≤ (t0.val + 1) * h := Nat.le_mul_of_pos_left h (by omega); omega
  have hout : ∀ k : Fin (a + b), (k.val < p.val - h ∨ p.val ≤ k.val) → x1 k = x2 k := by
    intro k hk
    rw [← winFn_winOffset hn x1 p k hhp hk, ← winFn_winOffset hn x2 p k hhp hk, hwin']
  have htile_out : ∀ (p' : Bool × Fin q) (c : Fin h), p' ≠ (arc, t0) →
      x1 (tileSite hqa hqb p'.1 p'.2 c) = x2 (tileSite hqa hqb p'.1 p'.2 c) := by
    intro p' c hne
    apply hout
    cases arc <;> dsimp only [p, portL, portR] <;> simp only [↓reduceIte, Bool.false_eq_true]
    · exact tilePos_outside_portL hqa hqb t0 p'.1 p'.2 c hne
    · exact tilePos_outside_portR hqa hqb t0 p'.1 p'.2 c hne
  funext k
  by_cases hk : k.val < p.val - h ∨ p.val ≤ k.val
  · exact hout k hk
  · have hrange : p.val - h ≤ k.val ∧ k.val < p.val := by omega
    have hpbase : p.val - h = (if arc then a else 0) + t0.val * h := by
      cases arc <;> dsimp only [p, portL, portR] <;>
        simp only [↓reduceIte, Bool.false_eq_true] <;> rw [Nat.add_mul, Nat.one_mul] <;> omega
    let c : Fin h := ⟨k.val - (p.val - h), by omega⟩
    have hk_eq : k = tileSite hqa hqb arc t0 c := by
      apply Fin.ext
      dsimp only [tileSite, tilePos, c]
      omega
    rw [hk_eq]
    by_cases hcs : c.val < s
    · have h1 := (uniqueZeroTile_spec hsh hqa hqb x1 hx1 arc).1
      have h2 := (uniqueZeroTile_spec hsh hqa hqb x2 hx2 arc).1
      dsimp only [isZeroLabelWord] at h1 h2
      rw [decide_eq_true_eq] at h1 h2
      have hv1 := h1 ⟨c.val, hcs⟩
      have hv2 := h2 ⟨c.val, hcs⟩
      rw [← ht_eq] at hv2
      change x1 (tileSite hqa hqb arc t0 c) = false at hv1
      change x2 (tileSite hqa hqb arc t0 c) = false at hv2
      rw [hv1, hv2]
    · let c' : Fin (h - s) := ⟨c.val - s, by have := c.isLt; omega⟩
      have hc_eq : c = ⟨s + c'.val, by have := c'.isLt; omega⟩ := Fin.ext (by dsimp only [c']; omega)
      rw [hc_eq]
      have hm1 := (filter_card_mod2_iff (fun pr : Bool × Fin q =>
        x1 (tileSite hqa hqb pr.1 pr.2 ⟨s + c'.val, by have := c'.isLt; omega⟩)) (arc, t0)).mp (hx1.2.2 c')
      have hm2 := (filter_card_mod2_iff (fun pr : Bool × Fin q =>
        x2 (tileSite hqa hqb pr.1 pr.2 ⟨s + c'.val, by have := c'.isLt; omega⟩)) (arc, t0)).mp (hx2.2.2 c')
      rw [hm1, hm2]
      apply congrArg (fun S : Finset (Bool × Fin q) => decide (S.card % 2 = 1))
      apply Finset.filter_congr
      intro pr hpr
      have hne : pr ≠ (arc, t0) := (Finset.mem_erase.mp hpr).1
      rw [htile_out pr _ hne]

end PEqualNP.Outside.L_lib_574_aux

theorem PEqualNP.Outside.L_lib_574 :
    ∀ (a b h s q : Nat) (hn : 0 < a+b), 0 < q → 0 < s → s ≤ h →
      q*h < a → (q+1)*h ≤ b →
      let n := a+b
      let M := q^2 * (2^s-1)^(2*(q-1)) * 2^(n-(2*q*s+(h-s)))
      let Word := Fin n → Bool
      let Pat := Fin (n-h) → Bool
      let Slot := Fin n × Pat
      let loc := fun k : Nat => (⟨k%n, Nat.mod_lt _ hn⟩ : Fin n)
      let solutions := fun (tab : Slot → Bool) =>
        (Finset.univ : Finset Word).filter (fun x =>
          ∀ i : Fin n, tab (i,fun j => x (loc (i.val+j.val))) = true)
      ∃ (code : Fin M → Word) (base : Slot → Bool) (left right : Fin M → Slot),
        Function.Injective code ∧ Function.Injective left ∧ Function.Injective right ∧
        (∀ i, (left i).1.val < a ∧ a ≤ (right i).1.val ∧
          base (left i) = false ∧ base (right i) = false) ∧
        ∀ A B : Finset (Fin M), solutions (fun slot =>
          base slot || decide (slot ∈ A.image left) || decide (slot ∈ B.image right)) =
            (A ∩ B).image code := by
  intro a b h s q hn hq hs hsh hqa hqb n M Word Pat Slot loc solutions
  classical
  have hcard : Fintype.card {x : Fin (a + b) → Bool //
      PEqualNP.Outside.L_lib_574_aux.ValidWord hsh hqa hqb x} = M :=
    PEqualNP.Outside.L_lib_574_aux.card_validWord hq hsh hqa hqb
  let e : Fin M ≃ {x : Fin (a + b) → Bool //
      PEqualNP.Outside.L_lib_574_aux.ValidWord hsh hqa hqb x} :=
    (Fintype.equivFinOfCardEq hcard).symm
  let code : Fin M → Word := fun i => (e i).1
  let base : Slot → Bool := PEqualNP.Outside.L_lib_574_aux.baseFn hn hs hsh hqa hqb
  let left : Fin M → Slot := fun i =>
    let p := PEqualNP.Outside.L_lib_574_aux.portL hqa hqb
      (PEqualNP.Outside.L_lib_574_aux.uniqueZeroTile hsh hqa hqb (e i).1 (e i).2 false)
    (p, PEqualNP.Outside.L_lib_574_aux.winFn (h := h) hn (e i).1 p)
  let right : Fin M → Slot := fun i =>
    let p := PEqualNP.Outside.L_lib_574_aux.portR hs hsh hqa hqb
      (PEqualNP.Outside.L_lib_574_aux.uniqueZeroTile hsh hqa hqb (e i).1 (e i).2 true)
    (p, PEqualNP.Outside.L_lib_574_aux.winFn (h := h) hn (e i).1 p)
  have hcode_inj : Function.Injective code := Subtype.val_injective.comp e.injective
  have hh : 0 < h := by omega
  have hleft_lt : ∀ i : Fin M, (left i).1.val < a := by
    intro i
    dsimp only [left, PEqualNP.Outside.L_lib_574_aux.portL]
    have ht := (PEqualNP.Outside.L_lib_574_aux.uniqueZeroTile hsh hqa hqb (e i).1 (e i).2 false).isLt
    have h1 : ((PEqualNP.Outside.L_lib_574_aux.uniqueZeroTile hsh hqa hqb (e i).1 (e i).2 false).val + 1) * h ≤ q * h :=
      Nat.mul_le_mul_right h (by omega)
    omega
  have hright_ge : ∀ i : Fin M, a ≤ (right i).1.val := by
    intro i
    dsimp only [right, PEqualNP.Outside.L_lib_574_aux.portR]
    omega
  have hleft_pos : ∀ i : Fin M, 0 < (left i).1.val := by
    intro i
    dsimp only [left, PEqualNP.Outside.L_lib_574_aux.portL]
    exact Nat.mul_pos (by omega) hh
  have hright_pos : ∀ i : Fin M, 0 < (right i).1.val := by
    intro i
    dsimp only [right, PEqualNP.Outside.L_lib_574_aux.portR]
    have : 0 < ((PEqualNP.Outside.L_lib_574_aux.uniqueZeroTile hsh hqa hqb (e i).1 (e i).2 true).val + 1) * h :=
      Nat.mul_pos (by omega) hh
    omega
  have hleft_inj : Function.Injective left := by
    intro i1 i2 heq
    have hp := congrArg Prod.fst heq
    have hw := congrArg Prod.snd heq
    have htv : ((PEqualNP.Outside.L_lib_574_aux.uniqueZeroTile hsh hqa hqb (e i1).1 (e i1).2 false).val + 1) * h =
        ((PEqualNP.Outside.L_lib_574_aux.uniqueZeroTile hsh hqa hqb (e i2).1 (e i2).2 false).val + 1) * h :=
      congrArg Fin.val hp
    have ht_eq : PEqualNP.Outside.L_lib_574_aux.uniqueZeroTile hsh hqa hqb (e i1).1 (e i1).2 false =
        PEqualNP.Outside.L_lib_574_aux.uniqueZeroTile hsh hqa hqb (e i2).1 (e i2).2 false := by
      have h1 := Nat.eq_of_mul_eq_mul_right hh htv
      exact Fin.ext (by omega)
    have hx_eq := PEqualNP.Outside.L_lib_574_aux.recover_from_port hn hs hsh hqa hqb false
      (e i1).1 (e i2).1 (e i1).2 (e i2).2 ht_eq hw
    exact hcode_inj hx_eq
  have hright_inj : Function.Injective right := by
    intro i1 i2 heq
    have hp := congrArg Prod.fst heq
    have hw := congrArg Prod.snd heq
    have htv : a + ((PEqualNP.Outside.L_lib_574_aux.uniqueZeroTile hsh hqa hqb (e i1).1 (e i1).2 true).val + 1) * h =
        a + ((PEqualNP.Outside.L_lib_574_aux.uniqueZeroTile hsh hqa hqb (e i2).1 (e i2).2 true).val + 1) * h :=
      congrArg Fin.val hp
    have hmul : ((PEqualNP.Outside.L_lib_574_aux.uniqueZeroTile hsh hqa hqb (e i1).1 (e i1).2 true).val + 1) * h =
        ((PEqualNP.Outside.L_lib_574_aux.uniqueZeroTile hsh hqa hqb (e i2).1 (e i2).2 true).val + 1) * h := by
      omega
    have ht_eq : PEqualNP.Outside.L_lib_574_aux.uniqueZeroTile hsh hqa hqb (e i1).1 (e i1).2 true =
        PEqualNP.Outside.L_lib_574_aux.uniqueZeroTile hsh hqa hqb (e i2).1 (e i2).2 true := by
      have h1 := Nat.eq_of_mul_eq_mul_right hh hmul
      exact Fin.ext (by omega)
    have hx_eq := PEqualNP.Outside.L_lib_574_aux.recover_from_port hn hs hsh hqa hqb true
      (e i1).1 (e i2).1 (e i1).2 (e i2).2 ht_eq hw
    exact hcode_inj hx_eq
  have hbase_left : ∀ i : Fin M, base (left i) = false := fun i =>
    (PEqualNP.Outside.L_lib_574_aux.baseFn_valid_word hn hs hsh hqa hqb (e i).1 (e i).2 _).mpr (Or.inl rfl)
  have hbase_right : ∀ i : Fin M, base (right i) = false := fun i =>
    (PEqualNP.Outside.L_lib_574_aux.baseFn_valid_word hn hs hsh hqa hqb (e i).1 (e i).2 _).mpr (Or.inr rfl)
  refine ⟨code, base, left, right, hcode_inj, hleft_inj, hright_inj,
    fun i => ⟨hleft_lt i, hright_ge i, hbase_left i, hbase_right i⟩, ?_⟩
  intro A B
  ext x
  simp only [solutions, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [Finset.mem_image]
  constructor
  · intro hall
    have h0 := hall ⟨0, hn⟩
    have hnotA0 : (⟨0, hn⟩, PEqualNP.Outside.L_lib_574_aux.winFn (h := h) hn x ⟨0, hn⟩) ∉ A.image left := by
      intro hm
      rcases Finset.mem_image.mp hm with ⟨j, _, hEq⟩
      have hv := congrArg (fun sl : Slot => sl.1.val) hEq
      dsimp only at hv
      have := hleft_pos j; omega
    have hnotB0 : (⟨0, hn⟩, PEqualNP.Outside.L_lib_574_aux.winFn (h := h) hn x ⟨0, hn⟩) ∉ B.image right := by
      intro hm
      rcases Finset.mem_image.mp hm with ⟨j, _, hEq⟩
      have hv := congrArg (fun sl : Slot => sl.1.val) hEq
      dsimp only at hv
      have := hright_pos j; omega
    have hvalid : PEqualNP.Outside.L_lib_574_aux.ValidWord hsh hqa hqb x := by
      change (base (⟨0, hn⟩, PEqualNP.Outside.L_lib_574_aux.winFn (h := h) hn x ⟨0, hn⟩) ||
        decide ((⟨0, hn⟩, PEqualNP.Outside.L_lib_574_aux.winFn (h := h) hn x ⟨0, hn⟩) ∈ A.image left) ||
        decide ((⟨0, hn⟩, PEqualNP.Outside.L_lib_574_aux.winFn (h := h) hn x ⟨0, hn⟩) ∈ B.image right)) = true at h0
      rw [decide_eq_false hnotA0, decide_eq_false hnotB0, Bool.or_false, Bool.or_false] at h0
      dsimp only [base, PEqualNP.Outside.L_lib_574_aux.baseFn] at h0
      simp only [↓reduceIte] at h0
      exact (PEqualNP.Outside.L_lib_574_aux.validPat_win_zero_iff hn hsh hqa hqb x).mp h0
    let i : Fin M := e.symm ⟨x, hvalid⟩
    have hcode_i : code i = x := congrArg Subtype.val (e.apply_symm_apply ⟨x, hvalid⟩)
    have hsub_i : e i = ⟨x, hvalid⟩ := e.apply_symm_apply ⟨x, hvalid⟩
    have hiA : i ∈ A := by
      have hL := hall (left i).1
      have hsl : ((left i).1, PEqualNP.Outside.L_lib_574_aux.winFn (h := h) hn x (left i).1) = left i := by
        dsimp only [left]; rw [hsub_i]
      change (base ((left i).1, PEqualNP.Outside.L_lib_574_aux.winFn (h := h) hn x (left i).1) ||
        decide (((left i).1, PEqualNP.Outside.L_lib_574_aux.winFn (h := h) hn x (left i).1) ∈ A.image left) ||
        decide (((left i).1, PEqualNP.Outside.L_lib_574_aux.winFn (h := h) hn x (left i).1) ∈ B.image right)) = true at hL
      rw [hsl, hbase_left i, Bool.false_or] at hL
      have hnotB : left i ∉ B.image right := by
        intro hm
        rcases Finset.mem_image.mp hm with ⟨j, _, hEq⟩
        have hv := congrArg (fun sl : Slot => sl.1.val) hEq
        have := hleft_lt i; have := hright_ge j; omega
      rw [decide_eq_false hnotB, Bool.or_false, decide_eq_true_eq] at hL
      rcases Finset.mem_image.mp hL with ⟨j, hjA, hjEq⟩
      rw [hleft_inj hjEq] at hjA
      exact hjA
    have hiB : i ∈ B := by
      have hR := hall (right i).1
      have hsl : ((right i).1, PEqualNP.Outside.L_lib_574_aux.winFn (h := h) hn x (right i).1) = right i := by
        dsimp only [right]; rw [hsub_i]
      change (base ((right i).1, PEqualNP.Outside.L_lib_574_aux.winFn (h := h) hn x (right i).1) ||
        decide (((right i).1, PEqualNP.Outside.L_lib_574_aux.winFn (h := h) hn x (right i).1) ∈ A.image left) ||
        decide (((right i).1, PEqualNP.Outside.L_lib_574_aux.winFn (h := h) hn x (right i).1) ∈ B.image right)) = true at hR
      rw [hsl, hbase_right i, Bool.false_or] at hR
      have hnotA : right i ∉ A.image left := by
        intro hm
        rcases Finset.mem_image.mp hm with ⟨j, _, hEq⟩
        have hv := congrArg (fun sl : Slot => sl.1.val) hEq
        have := hleft_lt j; have := hright_ge i; omega
      rw [decide_eq_false hnotA, Bool.false_or, decide_eq_true_eq] at hR
      rcases Finset.mem_image.mp hR with ⟨j, hjB, hjEq⟩
      rw [hright_inj hjEq] at hjB
      exact hjB
    exact ⟨i, Finset.mem_inter.mpr ⟨hiA, hiB⟩, hcode_i⟩
  · rintro ⟨i, hiAB, rfl⟩ p
    rcases Finset.mem_inter.mp hiAB with ⟨hiA, hiB⟩
    change (base (p, PEqualNP.Outside.L_lib_574_aux.winFn (h := h) hn (e i).1 p) ||
      decide ((p, PEqualNP.Outside.L_lib_574_aux.winFn (h := h) hn (e i).1 p) ∈ A.image left) ||
      decide ((p, PEqualNP.Outside.L_lib_574_aux.winFn (h := h) hn (e i).1 p) ∈ B.image right)) = true
    cases hb : base (p, PEqualNP.Outside.L_lib_574_aux.winFn (h := h) hn (e i).1 p)
    · rcases (PEqualNP.Outside.L_lib_574_aux.baseFn_valid_word hn hs hsh hqa hqb (e i).1 (e i).2 p).mp hb with hpL | hpR
      · have hmemA : (p, PEqualNP.Outside.L_lib_574_aux.winFn (h := h) hn (e i).1 p) ∈ A.image left := by
          rw [hpL]
          exact Finset.mem_image.mpr ⟨i, hiA, rfl⟩
        simp [hmemA]
      · have hmemB : (p, PEqualNP.Outside.L_lib_574_aux.winFn (h := h) hn (e i).1 p) ∈ B.image right := by
          rw [hpR]
          exact Finset.mem_image.mpr ⟨i, hiB, rfl⟩
        simp [hmemB]
    · simp
