import PEqualNP.Defs
import Mathlib.Data.Fin.Rev

namespace PEqualNP.Outside.L_clb_067_aux

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.NotBracket

def evalGates (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

lemma evalGates_append (gs1 gs2 : List Gate) (w : List Bool) :
    evalGates (gs1 ++ gs2) w = evalGates gs2 (evalGates gs1 w) := by
  simp [evalGates, List.foldl_append]

lemma evalGates_length (gs : List Gate) (w : List Bool) :
    (evalGates gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [evalGates]
  | cons g rest ih =>
    simp only [evalGates, List.foldl_cons] at ih ⊢
    rw [ih, List.length_append, List.length_singleton, List.length_cons]
    omega

lemma evalGates_prefix (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (evalGates gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g rest ih =>
    simp only [evalGates, List.foldl_cons] at ih ⊢
    have hlen : i < (w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]).length := by
      simp; omega
    rw [ih _ hlen, List.getD_append _ _ _ _ hi]

def wireVal (gs : List Gate) (x : List Bool) (w : ℕ) : Bool :=
  (evalGates gs x).getD w false

lemma wireVal_snoc_lt {I : ℕ} {gs : List Gate} {g : Gate} {x : List Bool} {w : ℕ}
    (hx : x.length = I) (hw : w < I + gs.length) :
    wireVal (gs ++ [g]) x w = wireVal gs x w := by
  simp only [wireVal, evalGates_append]
  apply evalGates_prefix
  rw [evalGates_length, hx]
  exact hw

lemma wireVal_snoc_last {I : ℕ} {gs : List Gate} {g : Gate} {x : List Bool}
    (hx : x.length = I) :
    wireVal (gs ++ [g]) x (I + gs.length) =
      g.op.eval (g.inputs.map fun i => wireVal gs x i) := by
  simp only [wireVal]
  rw [evalGates_append]
  simp only [evalGates, List.foldl_cons, List.foldl_nil]
  have hlen : (evalGates gs x).length = I + gs.length := by
    rw [evalGates_length, hx]
  have hlen' :
      (List.foldl (fun acc g => acc ++ [g.op.eval (List.map (fun i => acc.getD i false) g.inputs)])
        x gs).length = I + gs.length := hlen
  rw [List.getD_append_right _ _ _ _ (by omega)]
  rw [hlen', Nat.sub_self]
  rfl

lemma separated_card_le {L : ℕ} (A B : Finset (Fin L))
    (hsep : ∀ t1 ∈ B, ∀ t2 ∈ B, t1.val < t2.val → ∃ s ∈ A, t1.val < s.val ∧ s.val < t2.val) :
    B.card ≤ A.card + 1 := by
  induction hn : B.card using Nat.strong_induction_on generalizing A B with
  | ind m ih =>
    by_cases hB : B.Nonempty
    · let mx := B.max' hB
      have hmx_mem : mx ∈ B := Finset.max'_mem B hB
      let B' := B.erase mx
      have hB'_card : B'.card + 1 = m := by
        rw [← hn]
        exact Finset.card_erase_add_one hmx_mem
      by_cases hB' : B'.Nonempty
      · let mx' := B'.max' hB'
        have hmx'_mem : mx' ∈ B' := Finset.max'_mem B' hB'
        have hmx'_inB : mx' ∈ B := Finset.mem_of_mem_erase hmx'_mem
        have hmx'_ne : mx' ≠ mx := Finset.ne_of_mem_erase hmx'_mem
        have hmx'_le : mx' ≤ mx := Finset.le_max' B mx' hmx'_inB
        have hmx'_lt : mx'.val < mx.val := lt_of_le_of_ne hmx'_le (fun h => hmx'_ne (Fin.ext h))
        rcases hsep mx' hmx'_inB mx hmx_mem hmx'_lt with ⟨s, hsA, h1, _⟩
        let A' := A.filter (fun r => r.val < s.val)
        have hA'_sub : A' ⊂ A := by
          rw [Finset.ssubset_iff_subset_ne]
          refine ⟨Finset.filter_subset _ _, ?_⟩
          intro heq
          have hsA' : s ∈ A' := heq.symm ▸ hsA
          have := (Finset.mem_filter.mp hsA').2
          omega
        have hA'_lt : A'.card < A.card := Finset.card_lt_card hA'_sub
        have hsep' : ∀ t1 ∈ B', ∀ t2 ∈ B', t1.val < t2.val →
            ∃ r ∈ A', t1.val < r.val ∧ r.val < t2.val := by
          intro t1 ht1 t2 ht2 hlt
          have ht2_le : t2 ≤ mx' := Finset.le_max' B' t2 ht2
          rcases hsep t1 (Finset.mem_of_mem_erase ht1) t2 (Finset.mem_of_mem_erase ht2) hlt with
            ⟨r, hrA, hr1, hr2⟩
          refine ⟨r, Finset.mem_filter.mpr ⟨hrA, ?_⟩, hr1, hr2⟩
          have : t2.val ≤ mx'.val := ht2_le
          omega
        have hih := ih B'.card (by omega) A' B' hsep' rfl
        omega
      · have hB'_zero : B'.card = 0 := Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hB')
        omega
    · have hB_zero : B.card = 0 := Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hB)
      omega

lemma exists_bool_drop_between {L : ℕ} (f : Fin (L + 1) → Bool)
    (a b : ℕ) (ha : a ≤ b) (hb : b ≤ L)
    (hfa : f ⟨a, by omega⟩ = true) (hfb : f ⟨b, by omega⟩ = false) :
    ∃ s : Fin L, a ≤ s.val ∧ s.val < b ∧ f s.castSucc = true ∧ f s.succ = false := by
  have aux : ∀ d a' : ℕ, (ha' : a' ≤ b) → b - a' = d → f ⟨a', by omega⟩ = true →
      ∃ s : Fin L, a' ≤ s.val ∧ s.val < b ∧ f s.castSucc = true ∧ f s.succ = false := by
    intro d
    induction d with
    | zero =>
      intro a' ha' hd hfa'
      have hab : a' = b := by omega
      subst hab
      rw [hfa'] at hfb
      exact absurd hfb (by decide)
    | succ d' ih =>
      intro a' ha' hd hfa'
      cases hmid : f ⟨a' + 1, by omega⟩
      · exact ⟨⟨a', by omega⟩, le_refl a', by dsimp; omega, hfa', hmid⟩
      · rcases ih (a' + 1) (by omega) (by omega) hmid with ⟨s, hs1, hs2, hsf1, hsf2⟩
        exact ⟨s, by omega, hs2, hsf1, hsf2⟩
  exact aux (b - a) a ha rfl hfa

def prefixDrops {L : ℕ} (I : ℕ) (gs : List Gate) (xs : Fin (L + 1) → List Bool) : Finset (Fin L) :=
  Finset.univ.filter (fun t : Fin L =>
    ∃ w : Fin (I + gs.length), wireVal gs (xs t.castSucc) w.val = true ∧
      wireVal gs (xs t.succ) w.val = false)

def isNotGate (g : Gate) : Bool :=
  match g.op with
  | GateOp.not => true
  | _ => false

def gatesNotCount (gs : List Gate) : ℕ :=
  (gs.filter isNotGate).length

lemma notCount_eq_gatesNotCount (C : Circuit) : notCount C = gatesNotCount C.gates := by
  unfold notCount gatesNotCount
  congr 1
  apply List.filter_congr
  intro g _
  rcases g with ⟨op, ins⟩
  cases op <;> simp [isNotGate]

lemma gatesNotCount_snoc (gs : List Gate) (g : Gate) :
    gatesNotCount (gs ++ [g]) = gatesNotCount gs + if isNotGate g then 1 else 0 := by
  unfold gatesNotCount
  rw [List.filter_append, List.length_append]
  cases h : isNotGate g <;> simp [h]

lemma markov_drop_bound {L : ℕ} (I : ℕ) (gs : List Gate) (xs : Fin (L + 1) → List Bool)
    (hlen : ∀ s, (xs s).length = I)
    (hmono : ∀ (t : Fin L) (w : ℕ), (xs t.castSucc).getD w false = true →
      (xs t.succ).getD w false = true)
    (hfan : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      g.inputs.length ≤ 2)
    (hread : ∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < I + j) :
    1 + (prefixDrops I gs xs).card ≤ 2 ^ gatesNotCount gs := by
  induction gs using List.reverseRecOn with
  | nil =>
    have hempty : prefixDrops I [] xs = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro t ht
      rcases (Finset.mem_filter.mp ht).2 with ⟨w, hw1, hw2⟩
      simp only [wireVal, evalGates, List.foldl_nil] at hw1 hw2
      have := hmono t w.val hw1
      rw [this] at hw2
      exact absurd hw2 (by decide)
    simp [hempty, gatesNotCount]
  | append_singleton gs g ih =>
    have hfan_gs : ∀ g' ∈ gs, g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
        g'.inputs.length ≤ 2 := fun g' hg' => hfan g' (by simp [hg'])
    have hread_gs : ∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < I + j := by
      intro j hj i hi
      have hj' : j < (gs ++ [g]).length := by simp; omega
      have hget : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ :=
        List.getD_append _ _ _ _ hj
      exact hread j hj' i (hget.symm ▸ hi)
    have hih := ih hfan_gs hread_gs
    have hg_op : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) := (hfan g (by simp)).1
    have hg_in : ∀ i ∈ g.inputs, i < I + gs.length := by
      intro i hi
      have hlen_lt : gs.length < (gs ++ [g]).length := by simp
      have hget : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        rw [List.getD_append_right _ _ _ _ (le_refl _)]
        simp
      exact hread gs.length hlen_lt i (hget.symm ▸ hi)
    let A := prefixDrops I gs xs
    let B := (prefixDrops I (gs ++ [g]) xs) \ A
    have hA_card : A.card = (prefixDrops I gs xs).card := rfl
    have hcard_split : (prefixDrops I (gs ++ [g]) xs).card ≤ A.card + B.card := by
      have hsub : prefixDrops I (gs ++ [g]) xs ⊆ A ∪ B := by
        intro t ht
        by_cases htA : t ∈ A
        · exact Finset.mem_union_left _ htA
        · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨ht, htA⟩)
      exact le_trans (Finset.card_le_card hsub) (Finset.card_union_le A B)
    have hB_new : ∀ t ∈ B,
        wireVal (gs ++ [g]) (xs t.castSucc) (I + gs.length) = true ∧
        wireVal (gs ++ [g]) (xs t.succ) (I + gs.length) = false := by
      intro t ht
      rcases Finset.mem_sdiff.mp ht with ⟨ht1, htnotA⟩
      rcases (Finset.mem_filter.mp ht1).2 with ⟨w, hw1, hw2⟩
      by_cases hlt : w.val < I + gs.length
      · exfalso
        apply htnotA
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ t, ⟨⟨w.val, hlt⟩, ?_, ?_⟩⟩
        · rwa [wireVal_snoc_lt (hlen _) hlt] at hw1
        · rwa [wireVal_snoc_lt (hlen _) hlt] at hw2
      · have hweq : w.val = I + gs.length := by
          have := w.isLt
          simp only [List.length_append, List.length_singleton] at this
          omega
        rw [hweq] at hw1 hw2
        exact ⟨hw1, hw2⟩
    have hnotA_mono : ∀ t : Fin L, t ∉ A → ∀ w < I + gs.length,
        wireVal gs (xs t.castSucc) w = true → wireVal gs (xs t.succ) w = true := by
      intro t ht w hw h1
      cases h2 : wireVal gs (xs t.succ) w
      · exfalso
        exact ht (Finset.mem_filter.mpr ⟨Finset.mem_univ t, ⟨⟨w, hw⟩, h1, h2⟩⟩)
      · rfl
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg_op
    rcases hg_op with hop | hop | hop
    · have hB_empty : B = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro t ht
        rcases hB_new t ht with ⟨h1, h2⟩
        have htnotA : t ∉ A := (Finset.mem_sdiff.mp ht).2
        rw [wireVal_snoc_last (hlen _), hop] at h1 h2
        simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq] at h1
        have hall : (g.inputs.map (wireVal gs (xs t.succ))).all id = true := by
          rw [List.all_eq_true]
          intro b hb
          rcases List.mem_map.mp hb with ⟨i, hi, rfl⟩
          exact hnotA_mono t htnotA i (hg_in i hi) (h1 _ ⟨i, hi, rfl⟩)
        rw [GateOp.eval, hall] at h2
        exact absurd h2 (by decide)
      rw [gatesNotCount_snoc]
      have hnot : isNotGate g = false := by simp [isNotGate, hop]
      have hBc : B.card = 0 := by simp [hB_empty]
      simp only [hnot, Bool.false_eq_true, ↓reduceIte, add_zero]
      omega
    · have hB_empty : B = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro t ht
        rcases hB_new t ht with ⟨h1, h2⟩
        have htnotA : t ∉ A := (Finset.mem_sdiff.mp ht).2
        rw [wireVal_snoc_last (hlen _), hop] at h1 h2
        simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at h1
        rcases h1 with ⟨b, ⟨i, hi, rfl⟩, hbi⟩
        have hany : (g.inputs.map (wireVal gs (xs t.succ))).any id = true := by
          rw [List.any_eq_true]
          exact ⟨true, List.mem_map.mpr ⟨i, hi, hnotA_mono t htnotA i (hg_in i hi) hbi⟩, rfl⟩
        rw [GateOp.eval, hany] at h2
        exact absurd h2 (by decide)
      rw [gatesNotCount_snoc]
      have hnot : isNotGate g = false := by simp [isNotGate, hop]
      have hBc : B.card = 0 := by simp [hB_empty]
      simp only [hnot, Bool.false_eq_true, ↓reduceIte, add_zero]
      omega
    · have hB_le : B.card ≤ A.card + 1 := by
        cases hgin : g.inputs with
        | nil =>
          have hB_empty : B = ∅ := by
            rw [Finset.eq_empty_iff_forall_notMem]
            intro t ht
            rcases hB_new t ht with ⟨_, h2⟩
            rw [wireVal_snoc_last (hlen _), hop, hgin] at h2
            simp [GateOp.eval] at h2
          simp [hB_empty]
        | cons u us =>
          have hu : u < I + gs.length := hg_in u (by simp [hgin])
          apply separated_card_le A B
          intro t1 ht1 t2 ht2 hlt
          have h1 := (hB_new t1 ht1).2
          have h2 := (hB_new t2 ht2).1
          rw [wireVal_snoc_last (hlen _), hop, hgin] at h1 h2
          simp only [GateOp.eval, List.map_cons, List.headD_cons, Bool.not_eq_false',
            Bool.not_eq_true'] at h1 h2
          rcases exists_bool_drop_between (fun s => wireVal gs (xs s) u)
              (t1.val + 1) t2.val (by omega) (by omega) h1 h2 with
            ⟨s, hs1, hs2, hsf1, hsf2⟩
          refine ⟨s, Finset.mem_filter.mpr ⟨Finset.mem_univ s, ⟨⟨u, hu⟩, hsf1, hsf2⟩⟩,
            by omega, hs2⟩
      rw [gatesNotCount_snoc]
      have hnot : isNotGate g = true := by simp [isNotGate, hop]
      simp only [hnot, ↓reduceIte, pow_succ]
      omega

lemma sum_testBit_lsb (k m : ℕ) :
    (Finset.univ.sum fun j : Fin k => if m.testBit j.val then 2 ^ j.val else 0) = m % 2 ^ k := by
  induction k with
  | zero => simp [Nat.mod_one]
  | succ k ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, ih]
    rw [Nat.testBit_eq_decide_div_mod_eq]
    have hdiv : m % 2 ^ (k + 1) = (m / 2 ^ k % 2) * 2 ^ k + m % 2 ^ k := by
      have h1 := Nat.div_add_mod m (2 ^ k)
      have h2 := Nat.div_add_mod (m / 2 ^ k) 2
      have hlt : m % 2 ^ k < 2 ^ k := Nat.mod_lt m (by positivity)
      have hlt2 : m / 2 ^ k % 2 < 2 := Nat.mod_lt _ (by norm_num)
      rw [pow_succ]
      have h3 : m = 2 ^ k * 2 * (m / 2 ^ k / 2) + ((m / 2 ^ k % 2) * 2 ^ k + m % 2 ^ k) := by
        calc m = 2 ^ k * (m / 2 ^ k) + m % 2 ^ k := h1.symm
          _ = 2 ^ k * (2 * (m / 2 ^ k / 2) + m / 2 ^ k % 2) + m % 2 ^ k := by rw [h2]
          _ = 2 ^ k * 2 * (m / 2 ^ k / 2) + ((m / 2 ^ k % 2) * 2 ^ k + m % 2 ^ k) := by ring
      conv_lhs => rw [h3]
      rw [Nat.mul_add_mod]
      apply Nat.mod_eq_of_lt
      have hle1 : m / 2 ^ k % 2 ≤ 1 := by omega
      have hmul : (m / 2 ^ k % 2) * 2 ^ k ≤ 1 * 2 ^ k := Nat.mul_le_mul_right _ hle1
      omega
    have hlt2 : m / 2 ^ k % 2 < 2 := Nat.mod_lt _ (by norm_num)
    by_cases hb : m / 2 ^ k % 2 = 1
    · simp [hb, hdiv]; omega
    · have hb0 : m / 2 ^ k % 2 = 0 := by omega
      simp [hb0, hdiv]

lemma sum_testBit_msb (k m : ℕ) :
    (Finset.univ.sum fun j : Fin k => if m.testBit (k - 1 - j.val) then 2 ^ (k - 1 - j.val) else 0) =
      m % 2 ^ k := by
  rw [← sum_testBit_lsb k m]
  exact Fintype.sum_equiv (Fin.revPerm (n := k)) _ _ (fun j => by
    have h : k - (j.val + 1) = k - 1 - j.val := by omega
    simp [Fin.revPerm, Fin.val_rev, h])

lemma exists_bit_drop (n u v : ℕ) (hu : u < 2 ^ n) (hv : v < 2 ^ n) (hlt : u < v) :
    ∃ pos : Fin n, v.testBit (n - 1 - pos.val) = true ∧ u.testBit (n - 1 - pos.val) = false := by
  by_contra hno
  push Not at hno
  have hle : v ≤ u := by
    have hv_eq : v = Finset.univ.sum fun pos : Fin n =>
        if v.testBit (n - 1 - pos.val) then 2 ^ (n - 1 - pos.val) else 0 := by
      rw [sum_testBit_msb, Nat.mod_eq_of_lt hv]
    have hu_eq : u = Finset.univ.sum fun pos : Fin n =>
        if u.testBit (n - 1 - pos.val) then 2 ^ (n - 1 - pos.val) else 0 := by
      rw [sum_testBit_msb, Nat.mod_eq_of_lt hu]
    rw [hv_eq, hu_eq]
    apply Finset.sum_le_sum
    intro pos _
    cases hvp : v.testBit (n - 1 - pos.val)
    · simp
    · have hup : u.testBit (n - 1 - pos.val) = true := by
        cases h : u.testBit (n - 1 - pos.val)
        · exact absurd h (hno pos hvp)
        · rfl
      simp [hup]
  omega

lemma flatten_ofFn_length {α : Type} {m n : ℕ} (f : Fin m → Fin n → α) :
    (List.ofFn (fun j : Fin m => List.ofFn (f j))).flatten.length = m * n := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.ofFn_succ, List.flatten_cons, List.length_append, List.length_ofFn,
      ih (fun j => f j.succ)]
    ring

lemma flatten_ofFn_getD {α : Type} {m n : ℕ} (f : Fin m → Fin n → α) (d : α)
    (j : Fin m) (i : Fin n) :
    (List.ofFn (fun j' : Fin m => List.ofFn (f j'))).flatten.getD (j.val * n + i.val) d =
      f j i := by
  induction m with
  | zero => exact Fin.elim0 j
  | succ m ih =>
    rw [List.ofFn_succ, List.flatten_cons]
    refine Fin.cases ?_ ?_ j
    · simp only [Fin.val_zero, zero_mul, zero_add]
      rw [List.getD_append _ _ _ _ (by simp [i.isLt])]
      simp [List.getD_eq_getElem?_getD, i.isLt]
    · intro j'
      simp only [Fin.val_succ]
      have hge : (List.ofFn (f 0)).length ≤ (j'.val + 1) * n + i.val := by
        simp only [List.length_ofFn]; nlinarith
      rw [List.getD_append_right _ _ _ _ hge]
      simp only [List.length_ofFn]
      have hsub : (j'.val + 1) * n + i.val - n = j'.val * n + i.val := by
        have : (j'.val + 1) * n = j'.val * n + n := by ring
        omega
      rw [hsub]
      exact ih (fun k => f k.succ) j'

def packRec (k : ℕ) : (m : ℕ) → (Fin m → ℕ) → ℕ
  | 0, _ => 0
  | m + 1, d => packRec k m (fun g => d g.castSucc) * 2 ^ k + d (Fin.last m)

lemma packRec_lt (k m : ℕ) (d : Fin m → ℕ) (hd : ∀ g, d g < 2 ^ k) :
    packRec k m d < 2 ^ (m * k) := by
  induction m with
  | zero => simp [packRec]
  | succ m ih =>
    simp only [packRec]
    have h1 := ih (fun g => d g.castSucc) (fun g => hd g.castSucc)
    have h2 := hd (Fin.last m)
    have hpow : 2 ^ ((m + 1) * k) = 2 ^ (m * k) * 2 ^ k := by
      rw [Nat.add_mul, Nat.one_mul, pow_add]
    rw [hpow]
    have h3 : packRec k m (fun g => d g.castSucc) + 1 ≤ 2 ^ (m * k) := h1
    have h4 : (packRec k m (fun g => d g.castSucc) + 1) * 2 ^ k ≤ 2 ^ (m * k) * 2 ^ k :=
      Nat.mul_le_mul_right _ h3
    rw [Nat.add_mul, Nat.one_mul] at h4
    omega

lemma packRec_digit (k m : ℕ) (d : Fin m → ℕ) (hd : ∀ g, d g < 2 ^ k) (g : Fin m) :
    (packRec k m d / 2 ^ ((m - 1 - g.val) * k)) % 2 ^ k = d g := by
  induction m with
  | zero => exact Fin.elim0 g
  | succ m ih =>
    refine Fin.lastCases ?_ ?_ g
    · simp only [packRec, Fin.val_last, Nat.add_sub_cancel, Nat.sub_self, zero_mul, pow_zero,
        Nat.div_one]
      rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt (hd (Fin.last m))]
    · intro g'
      simp only [packRec, Fin.val_castSucc]
      have hsub : (m + 1 - 1 - g'.val) * k = k + (m - 1 - g'.val) * k := by
        have hg' : g'.val < m := g'.isLt
        have h1 : m - g'.val = 1 + (m - 1 - g'.val) := by omega
        rw [Nat.add_sub_cancel, h1, Nat.add_mul, Nat.one_mul]
      rw [hsub, pow_add, ← Nat.div_div_eq_div_mul]
      have hdiv : (packRec k m (fun i => d i.castSucc) * 2 ^ k + d (Fin.last m)) / 2 ^ k =
          packRec k m (fun i => d i.castSucc) := by
        rw [mul_comm, Nat.mul_add_div (by positivity), Nat.div_eq_of_lt (hd (Fin.last m)), add_zero]
      rw [hdiv]
      exact ih (fun i => d i.castSucc) (fun i => hd i.castSucc) g'

lemma packRec_split (k G : ℕ) (hG : 1 ≤ G) (d : Fin G → ℕ) :
    packRec k G d =
      packRec k (G - 1) (fun g : Fin (G - 1) => d ⟨g.val, by omega⟩) * 2 ^ k +
        d ⟨G - 1, by omega⟩ := by
  cases G with
  | zero => omega
  | succ G' => rfl

lemma packRec_reconstruct (k m x : ℕ) (hx : x < 2 ^ (m * k)) :
    packRec k m (fun g : Fin m => (x / 2 ^ ((m - 1 - g.val) * k)) % 2 ^ k) = x := by
  induction m generalizing x with
  | zero => simp [packRec]; simp at hx; omega
  | succ m ih =>
    simp only [packRec, Fin.val_castSucc, Fin.val_last, Nat.add_sub_cancel, Nat.sub_self,
      zero_mul, pow_zero, Nat.div_one]
    have hpow : 2 ^ ((m + 1) * k) = 2 ^ (m * k) * 2 ^ k := by
      rw [Nat.add_mul, Nat.one_mul, pow_add]
    have hxdiv : x / 2 ^ k < 2 ^ (m * k) := by
      rw [Nat.div_lt_iff_lt_mul (by positivity), ← hpow]
      exact hx
    have hfun : (fun g : Fin m => (x / 2 ^ ((m - g.val) * k)) % 2 ^ k) =
        (fun g : Fin m => ((x / 2 ^ k) / 2 ^ ((m - 1 - g.val) * k)) % 2 ^ k) := by
      funext g
      have hg : g.val < m := g.isLt
      have h1 : (m - g.val) * k = k + (m - 1 - g.val) * k := by
        have : m - g.val = 1 + (m - 1 - g.val) := by omega
        rw [this, Nat.add_mul, Nat.one_mul]
      rw [h1, pow_add, ← Nat.div_div_eq_div_mul]
    rw [hfun, ih (x / 2 ^ k) hxdiv]
    rw [mul_comm, Nat.div_add_mod]

lemma packRec_mono (k m : ℕ) (d1 d2 : Fin m → ℕ) (hle : ∀ g, d1 g ≤ d2 g) :
    packRec k m d1 ≤ packRec k m d2 := by
  induction m with
  | zero => simp [packRec]
  | succ m ih =>
    simp only [packRec]
    have h1 := ih (fun g => d1 g.castSucc) (fun g => d2 g.castSucc) (fun g => hle g.castSucc)
    have h2 := hle (Fin.last m)
    have h3 : packRec k m (fun g => d1 g.castSucc) * 2 ^ k ≤
        packRec k m (fun g => d2 g.castSucc) * 2 ^ k := Nat.mul_le_mul_right _ h1
    omega

lemma packRec_lt_of_le_lt (k m : ℕ) (d1 d2 : Fin m → ℕ)
    (hle : ∀ g, d1 g ≤ d2 g) (gstar : Fin m) (hlt : d1 gstar < d2 gstar) :
    packRec k m d1 < packRec k m d2 := by
  induction m with
  | zero => exact Fin.elim0 gstar
  | succ m ih =>
    simp only [packRec]
    refine Fin.lastCases ?_ ?_ gstar hlt
    · intro hlast
      have h1 := packRec_mono k m (fun g => d1 g.castSucc) (fun g => d2 g.castSucc)
        (fun g => hle g.castSucc)
      have h2 : packRec k m (fun g => d1 g.castSucc) * 2 ^ k ≤
          packRec k m (fun g => d2 g.castSucc) * 2 ^ k := Nat.mul_le_mul_right _ h1
      omega
    · intro g' hlt'
      have h1 := ih (fun g => d1 g.castSucc) (fun g => d2 g.castSucc)
        (fun g => hle g.castSucc) g' hlt'
      have h2 := hle (Fin.last m)
      have h3 : packRec k m (fun g => d1 g.castSucc) * 2 ^ k <
          packRec k m (fun g => d2 g.castSucc) * 2 ^ k :=
        Nat.mul_lt_mul_of_pos_right h1 (by positivity)
      omega

def patBlockVal (k w : ℕ) (hk : k ≤ w + 1) (pat : Fin (w + 1) → Bool) : ℕ :=
  Finset.univ.sum fun j : Fin k => if pat ⟨j.val, by omega⟩ then 2 ^ (k - 1 - j.val) else 0

def lowCut (K t g : ℕ) : ℕ :=
  K - min K (t - g * K)

lemma lowCut_le (K t g : ℕ) : lowCut K t g ≤ K := Nat.sub_le _ _

lemma lowCut_antitone (K g t1 t2 : ℕ) (h : t1 ≤ t2) : lowCut K t2 g ≤ lowCut K t1 g := by
  unfold lowCut
  omega

def allowed (K j0 G t g v : ℕ) : Bool :=
  decide (lowCut K t g ≤ v) || (decide (g + 1 = G) && decide (v < j0))

lemma allowed_mono (K j0 G t1 t2 g v : ℕ) (h : t1 ≤ t2)
    (ha : allowed K j0 G t1 g v = true) : allowed K j0 G t2 g v = true := by
  have hlc := lowCut_antitone K g t1 t2 h
  simp only [allowed, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at ha ⊢
  rcases ha with h1 | h2
  · left; omega
  · right; exact h2

lemma lowCut_last_ge_j0 (K j0 G t : ℕ) (hG : 1 ≤ G) (hj0 : j0 ≤ K) (ht : t ≤ G * K - j0) :
    j0 ≤ lowCut K t (G - 1) := by
  unfold lowCut
  have hmul : (G - 1) * K + K = G * K := by
    have : G - 1 + 1 = G := by omega
    calc (G - 1) * K + K = (G - 1 + 1) * K := by rw [Nat.add_mul, Nat.one_mul]
      _ = G * K := by rw [this]
  omega

lemma lowCut_step_lt (K t : ℕ) (hK : 0 < K) :
    lowCut K (t + 1) (t / K) < lowCut K t (t / K) := by
  unfold lowCut
  have hmod : t % K < K := Nat.mod_lt t hK
  have hdiv : (t / K) * K + t % K = t := by
    rw [mul_comm, Nat.div_add_mod]
  omega

lemma high_bits_zero_iff (n M z : ℕ) (hMn : M ≤ n) (hz : z < 2 ^ n) :
    z < 2 ^ M ↔ ∀ pos : ℕ, pos < n - M → z.testBit (n - 1 - pos) = false := by
  constructor
  · intro hlt pos hpos
    apply Nat.testBit_lt_two_pow
    have hpow : 2 ^ M ≤ 2 ^ (n - 1 - pos) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  · intro hall
    set m := z / 2 ^ M
    have hm_lt : m < 2 ^ (n - M) := by
      rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add]
      have : n - M + M = n := by omega
      rw [this]
      exact hz
    have hm_zero : m = 0 := by
      have hsum := sum_testBit_msb (n - M) m
      rw [Nat.mod_eq_of_lt hm_lt] at hsum
      rw [← hsum]
      apply Finset.sum_eq_zero
      intro j _
      have htb : m.testBit (n - M - 1 - j.val) = false := by
        rw [Nat.testBit_div_two_pow]
        have heq : n - M - 1 - j.val + M = n - 1 - j.val := by
          have := j.isLt; omega
        rw [heq]
        exact hall j.val j.isLt
      simp [htb]
    have hdiv := Nat.div_add_mod z (2 ^ M)
    have hmod : z % 2 ^ M < 2 ^ M := Nat.mod_lt z (by positivity)
    have hzm : z / 2 ^ M = 0 := hm_zero
    rw [hzm, mul_zero, zero_add] at hdiv
    omega

def stepTable (n w k : ℕ) (hk : k ≤ w + 1) (K j0 G t : ℕ) (rem : ℕ) :
    Fin n → (Fin (w + 1) → Bool) → Bool := fun i pat =>
  if i.val < rem then
    !(pat ⟨0, by omega⟩)
  else if (i.val - rem) % k = 0 ∧ (i.val - rem) / k < G then
    allowed K j0 G t ((i.val - rem) / k) (patBlockVal k w hk pat)
  else
    true

lemma stepTable_mono (n w k : ℕ) (hk : k ≤ w + 1) (K j0 G rem t1 t2 : ℕ) (hle : t1 ≤ t2) :
    ∀ i pat, stepTable n w k hk K j0 G t1 rem i pat = true →
      stepTable n w k hk K j0 G t2 rem i pat = true := by
  intro i pat h
  unfold stepTable at h ⊢
  split_ifs at h ⊢ with h1 h2
  · exact h
  · exact allowed_mono K j0 G t1 t2 _ _ hle h
  · rfl

lemma main_proof (n w : ℕ) (_hn : 0 < n) (q : Fin (2 ^ n))
    (C : Circuit) (outBit : Fin n → Fin (n * 2 ^ (w + 1) + C.size))
    (hfan : FanInTwo C) (hread : ReadsBack (n * 2 ^ (w + 1)) C)
    (hcirc : ∀ table : Fin n → (Fin (w + 1) → Bool) → Bool,
      let inputs := (List.ofFn (fun i : Fin n => List.ofFn (fun pat : Fin (2 ^ (w + 1)) =>
        table i (fun j => pat.val.testBit j.val)))).flatten
      let sols := (Finset.univ : Finset (Fin (2 ^ n))).filter (fun z => ∀ i : Fin n,
        table i (fun j => z.val.testBit (n - 1 - ((i.val + j.val) % n))) = true)
      q.val < sols.card → ∃ z ∈ sols,
        (sols.filter (fun y => y.val < z.val)).card = q.val ∧
        ∀ pos : Fin n, (C.wires inputs).getD (outBit pos).val false =
          z.val.testBit (n - 1 - pos.val))
    (k b : ℕ) (hk0 : 0 < k) (hkw : k ≤ w + 1) (hkbn : k + b ≤ n) (hqkb : q.val < 2 ^ (k + b)) :
    1 + ((n - b) / k) * (2 ^ k - 1) - q.val / 2 ^ b ≤ 2 ^ notCount C := by
  let I := n * 2 ^ (w + 1)
  set G := (n - b) / k
  set K := 2 ^ k - 1
  set j0 := q.val / 2 ^ b
  set r0 := q.val % 2 ^ b
  have hK_pos : 0 < K := by
    have : 2 ≤ 2 ^ k := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk0
    omega
  have hK_succ : K + 1 = 2 ^ k := by omega
  have hG_pos : 1 ≤ G := by
    change 1 ≤ (n - b) / k
    exact Nat.div_pos (by omega) hk0
  have hGk_le : G * k ≤ n - b := Nat.div_mul_le_self (n - b) k
  have hGkb_le : G * k + b ≤ n := by omega
  set rem := n - (G * k + b)
  have hrem_eq : rem + G * k + b = n := by omega
  have hj0_lt : j0 < 2 ^ k := by
    change q.val / 2 ^ b < 2 ^ k
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add]
    exact hqkb
  have hj0_le_K : j0 ≤ K := by omega
  have hr0_lt : r0 < 2 ^ b := Nat.mod_lt q.val (by positivity)
  have hqr_eq : j0 * 2 ^ b + r0 = q.val := by
    change (q.val / 2 ^ b) * 2 ^ b + q.val % 2 ^ b = q.val
    rw [mul_comm, Nat.div_add_mod]
  have hj0_le_GK : j0 ≤ G * K := by
    have : 1 * K ≤ G * K := Nat.mul_le_mul_right K hG_pos
    omega
  set L := G * K - j0
  have htarget_eq : 1 + G * K - j0 = 1 + L := by omega
  rw [htarget_eq]
  let tbl : Fin (L + 1) → Fin n → (Fin (w + 1) → Bool) → Bool :=
    fun t => stepTable n w k hkw K j0 G t.val rem
  let xs : Fin (L + 1) → List Bool := fun t =>
    (List.ofFn (fun i : Fin n => List.ofFn (fun pat : Fin (2 ^ (w + 1)) =>
      tbl t i (fun j => pat.val.testBit j.val)))).flatten
  have hxs_len : ∀ t, (xs t).length = I := fun t => flatten_ofFn_length _
  have hxs_mono : ∀ (t : Fin L) (idx : ℕ),
      (xs t.castSucc).getD idx false = true → (xs t.succ).getD idx false = true := by
    intro t idx h1
    by_cases hlt : idx < I
    · set stride := 2 ^ (w + 1)
      have hstr_pos : 0 < stride := by positivity
      have hi_lt : idx / stride < n := by
        rw [Nat.div_lt_iff_lt_mul hstr_pos]
        exact hlt
      have hp_lt : idx % stride < stride := Nat.mod_lt idx hstr_pos
      have hidx_eq : (idx / stride) * stride + idx % stride = idx := by
        rw [mul_comm, Nat.div_add_mod]
      have hv1 := flatten_ofFn_getD (fun (i : Fin n) (pat : Fin stride) =>
        tbl t.castSucc i (fun j => pat.val.testBit j.val)) false ⟨idx / stride, hi_lt⟩ ⟨idx % stride, hp_lt⟩
      have hv2 := flatten_ofFn_getD (fun (i : Fin n) (pat : Fin stride) =>
        tbl t.succ i (fun j => pat.val.testBit j.val)) false ⟨idx / stride, hi_lt⟩ ⟨idx % stride, hp_lt⟩
      simp only [hidx_eq] at hv1 hv2
      change (xs t.castSucc).getD idx false = _ at hv1
      change (xs t.succ).getD idx false = _ at hv2
      rw [hv1] at h1
      rw [hv2]
      exact stepTable_mono n w k hkw K j0 G rem t.castSucc.val t.succ.val
        (by simp) _ _ h1
    · exfalso
      have hge : (xs t.castSucc).length ≤ idx := by rw [hxs_len]; omega
      rw [List.getD_eq_default _ _ hge] at h1
      exact Bool.false_ne_true h1
  have hmarkov : 1 + (prefixDrops I C.gates xs).card ≤ 2 ^ notCount C := by
    rw [notCount_eq_gatesNotCount]
    exact markov_drop_bound I C.gates xs hxs_len hxs_mono hfan hread
  have hsol_iff : ∀ (t : Fin (L + 1)) (z : Fin (2 ^ n)),
      (∀ i : Fin n, tbl t i (fun j => z.val.testBit (n - 1 - ((i.val + j.val) % n))) = true) ↔
        (z.val < 2 ^ (G * k + b) ∧
          ∀ g : Fin G, allowed K j0 G t.val g.val
            ((z.val / 2 ^ (b + (G - 1 - g.val) * k)) % 2 ^ k) = true) := by
    intro t z
    have hpat_eq : ∀ g : Fin G,
        patBlockVal k w hkw (fun j : Fin (w + 1) =>
          z.val.testBit (n - 1 - ((rem + g.val * k + j.val) % n))) =
        (z.val / 2 ^ (b + (G - 1 - g.val) * k)) % 2 ^ k := by
      intro g
      unfold patBlockVal
      rw [← sum_testBit_msb k (z.val / 2 ^ (b + (G - 1 - g.val) * k))]
      apply Finset.sum_congr rfl
      intro j _
      dsimp only
      have hg : g.val + 1 ≤ G := g.isLt
      have hj : j.val < k := j.isLt
      have hmul : (g.val + 1) * k ≤ G * k := Nat.mul_le_mul_right k hg
      have hlt_n : rem + g.val * k + j.val < n := by
        rw [Nat.add_mul, Nat.one_mul] at hmul; omega
      have hbit : n - 1 - (rem + g.val * k + j.val) =
          (k - 1 - j.val) + (b + (G - 1 - g.val) * k) := by
        have h1 : (G - 1 - g.val) * k + g.val * k + k = G * k := by
          have : G - 1 - g.val + g.val + 1 = G := by omega
          calc (G - 1 - g.val) * k + g.val * k + k
              = (G - 1 - g.val + g.val + 1) * k := by ring
            _ = G * k := by rw [this]
        omega
      simp only [Nat.mod_eq_of_lt hlt_n, Nat.testBit_div_two_pow, hbit]
    constructor
    · intro hall
      have hlt : z.val < 2 ^ (G * k + b) := by
        rw [high_bits_zero_iff n (G * k + b) z.val hGkb_le z.isLt]
        intro pos hpos
        have hpos_lt : pos < n := by omega
        have hi := hall ⟨pos, hpos_lt⟩
        simp only [tbl, stepTable, show pos < rem by omega, ↓reduceIte, add_zero,
          Nat.mod_eq_of_lt hpos_lt, Bool.not_eq_true'] at hi
        exact hi
      refine ⟨hlt, ?_⟩
      intro g
      have hpos_lt : rem + g.val * k < n := by
        have : (g.val + 1) * k ≤ G * k := Nat.mul_le_mul_right k g.isLt
        rw [Nat.add_mul, Nat.one_mul] at this
        omega
      have hi := hall ⟨rem + g.val * k, hpos_lt⟩
      simp only [tbl, stepTable] at hi
      have hnot_rem : ¬ (rem + g.val * k < rem) := by omega
      have hsub : rem + g.val * k - rem = g.val * k := by omega
      have hmod0 : (g.val * k) % k = 0 := Nat.mul_mod_left g.val k
      have hdivg : (g.val * k) / k = g.val := Nat.mul_div_cancel g.val hk0
      simp only [hnot_rem, ↓reduceIte, hsub, hmod0, hdivg, g.isLt, and_self] at hi
      rw [hpat_eq g] at hi
      exact hi
    · rintro ⟨hlt, hdig⟩ i
      simp only [tbl, stepTable]
      split_ifs with h1 h2
      · simp only [add_zero, Nat.mod_eq_of_lt i.isLt, Bool.not_eq_true']
        exact (high_bits_zero_iff n (G * k + b) z.val hGkb_le z.isLt).mp hlt i.val h1
      · rcases h2 with ⟨hmod0, hdivlt⟩
        set g : Fin G := ⟨(i.val - rem) / k, hdivlt⟩
        have hi_eq : i.val = rem + g.val * k := by
          have hdm := Nat.div_add_mod (i.val - rem) k
          rw [hmod0, add_zero, mul_comm] at hdm
          have hgd : g.val = (i.val - rem) / k := rfl
          rw [hgd]
          omega
        have hpat := hpat_eq g
        have hi_eq' : (fun j : Fin (w + 1) => z.val.testBit (n - 1 - ((i.val + j.val) % n))) =
            (fun j : Fin (w + 1) => z.val.testBit (n - 1 - ((rem + g.val * k + j.val) % n))) := by
          funext j; rw [hi_eq]
        rw [hi_eq', hpat]
        exact hdig g
      · rfl
  let targetDigit : Fin (L + 1) → Fin G → ℕ := fun t g => lowCut K t.val g.val
  let targetNum : Fin (L + 1) → ℕ := fun t => packRec k G (targetDigit t) * 2 ^ b + r0
  have htarget_lt_M : ∀ t, targetNum t < 2 ^ (G * k + b) := by
    intro t
    have hpack : packRec k G (targetDigit t) < 2 ^ (G * k) :=
      packRec_lt k G (targetDigit t) (fun g => by
        dsimp only [targetDigit]; have := lowCut_le K t.val g.val; omega)
    dsimp only [targetNum]
    rw [pow_add]
    have h1 : packRec k G (targetDigit t) + 1 ≤ 2 ^ (G * k) := hpack
    have h2 : (packRec k G (targetDigit t) + 1) * 2 ^ b ≤ 2 ^ (G * k) * 2 ^ b :=
      Nat.mul_le_mul_right _ h1
    rw [Nat.add_mul, Nat.one_mul] at h2
    omega
  have htarget_lt : ∀ t, targetNum t < 2 ^ n := fun t =>
    lt_of_lt_of_le (htarget_lt_M t) (Nat.pow_le_pow_right (by norm_num) hGkb_le)
  let targetFin : Fin (L + 1) → Fin (2 ^ n) := fun t => ⟨targetNum t, htarget_lt t⟩
  have hdiv_block : ∀ (d : Fin G → ℕ) (tl : ℕ) (hd : ∀ g, d g < 2 ^ k) (htl : tl < 2 ^ b) (g : Fin G),
      ((packRec k G d * 2 ^ b + tl) / 2 ^ (b + (G - 1 - g.val) * k)) % 2 ^ k = d g := by
    intro d tl hd htl g
    rw [pow_add, ← Nat.div_div_eq_div_mul]
    have h1 : (packRec k G d * 2 ^ b + tl) / 2 ^ b = packRec k G d := by
      rw [mul_comm, Nat.mul_add_div (by positivity), Nat.div_eq_of_lt htl, add_zero]
    rw [h1]
    exact packRec_digit k G d hd g
  have hcirc_out : ∀ (t : Fin (L + 1)) (pos : Fin n),
      (C.wires (xs t)).getD (outBit pos).val false =
        (targetNum t).testBit (n - 1 - pos.val) := by
    intro t
    set sols := (Finset.univ : Finset (Fin (2 ^ n))).filter (fun z => ∀ i : Fin n,
      tbl t i (fun j => z.val.testBit (n - 1 - ((i.val + j.val) % n))) = true)
    have hzt_mem : targetFin t ∈ sols := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rw [hsol_iff t (targetFin t)]
      refine ⟨htarget_lt_M t, fun g => ?_⟩
      change allowed K j0 G t.val g.val
        (((packRec k G (targetDigit t) * 2 ^ b + r0) / 2 ^ (b + (G - 1 - g.val) * k)) % 2 ^ k) = true
      rw [hdiv_block (targetDigit t) r0 (fun g' => by
        dsimp only [targetDigit]; have := lowCut_le K t.val g'.val; omega) hr0_lt g]
      simp [allowed, targetDigit]
    set G' := G - 1
    have hG_eq : G = G' + 1 := by omega
    have hlt_card : (sols.filter (fun y => y.val < (targetFin t).val)).card = q.val := by
      have hlast_ge : j0 ≤ lowCut K t.val G' :=
        lowCut_last_ge_j0 K j0 G t.val hG_pos hj0_le_K (by omega)
      let prefD : Fin G' → ℕ := fun g => lowCut K t.val g.val
      have hpref_lt : ∀ g : Fin G', prefD g < 2 ^ k := fun g => by
        dsimp only [prefD]; have := lowCut_le K t.val g.val; omega
      let P_ref := packRec k G' prefD
      have hPref_lt : P_ref < 2 ^ (G' * k) := packRec_lt k G' prefD hpref_lt
      have hpack_split : ∀ (d : Fin G → ℕ),
          packRec k G d =
            packRec k G' (fun g : Fin G' => d ⟨g.val, by omega⟩) * 2 ^ k + d ⟨G', by omega⟩ :=
        fun d => packRec_split k G hG_pos d
      have htarget_split :
          targetNum t = (P_ref * 2 ^ k + lowCut K t.val G') * 2 ^ b + r0 := by
        change packRec k G (targetDigit t) * 2 ^ b + r0 = _
        rw [hpack_split (targetDigit t)]
      let φ : Fin q.val → Fin (2 ^ n) := fun u =>
        let uhi := u.val / 2 ^ b
        let ulo := u.val % 2 ^ b
        let elast := if uhi < j0 then uhi else lowCut K t.val G'
        let num := (P_ref * 2 ^ k + elast) * 2 ^ b + ulo
        have hnum_lt : num < 2 ^ n := by
          have hel_lt : elast < 2 ^ k := by
            dsimp only [elast]
            split_ifs
            · omega
            · have := lowCut_le K t.val G'; omega
          have hulo_lt : ulo < 2 ^ b := Nat.mod_lt u.val (by positivity)
          have h1 : P_ref + 1 ≤ 2 ^ (G' * k) := hPref_lt
          have h2 : (P_ref + 1) * 2 ^ k ≤ 2 ^ (G' * k) * 2 ^ k := Nat.mul_le_mul_right _ h1
          rw [Nat.add_mul, Nat.one_mul] at h2
          have h3 : P_ref * 2 ^ k + elast + 1 ≤ 2 ^ (G' * k) * 2 ^ k := by omega
          have h4 : (P_ref * 2 ^ k + elast + 1) * 2 ^ b ≤ 2 ^ (G' * k) * 2 ^ k * 2 ^ b :=
            Nat.mul_le_mul_right _ h3
          rw [Nat.add_mul, Nat.one_mul] at h4
          have hpow : 2 ^ (G' * k) * 2 ^ k * 2 ^ b = 2 ^ (G * k + b) := by
            rw [← pow_add, ← pow_add]
            congr 1
            have : G' * k + k = G * k := by
              rw [hG_eq, Nat.add_mul, Nat.one_mul]
            omega
          have hle_n : 2 ^ (G * k + b) ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hGkb_le
          omega
        ⟨num, hnum_lt⟩
      have hφ_inj : Function.Injective φ := by
        intro u1 u2 heq
        have hval := congrArg Fin.val heq
        dsimp only [φ] at hval
        have hulo1 : u1.val % 2 ^ b < 2 ^ b := Nat.mod_lt _ (by positivity)
        have hulo2 : u2.val % 2 ^ b < 2 ^ b := Nat.mod_lt _ (by positivity)
        have hlo_eq : u1.val % 2 ^ b = u2.val % 2 ^ b := by
          have hm1 := congrArg (· % 2 ^ b) hval
          rw [Nat.mul_add_mod_self_right, Nat.mul_add_mod_self_right,
            Nat.mod_eq_of_lt hulo1, Nat.mod_eq_of_lt hulo2] at hm1
          exact hm1
        have hq_eq : (if u1.val / 2 ^ b < j0 then u1.val / 2 ^ b else lowCut K t.val G') =
            (if u2.val / 2 ^ b < j0 then u2.val / 2 ^ b else lowCut K t.val G') := by
          have hd := congrArg (· / 2 ^ b) hval
          rw [mul_comm _ (2 ^ b), mul_comm _ (2 ^ b),
            Nat.mul_add_div (by positivity), Nat.mul_add_div (by positivity),
            Nat.div_eq_of_lt hulo1, Nat.div_eq_of_lt hulo2, add_zero, add_zero] at hd
          omega
        have hhi1_le : u1.val / 2 ^ b ≤ j0 := by
          have : u1.val < j0 * 2 ^ b + 2 ^ b := by omega
          have : u1.val < (j0 + 1) * 2 ^ b := by rw [Nat.add_mul, Nat.one_mul]; omega
          have := (Nat.div_lt_iff_lt_mul (by positivity)).mpr this
          omega
        have hhi2_le : u2.val / 2 ^ b ≤ j0 := by
          have : u2.val < j0 * 2 ^ b + 2 ^ b := by omega
          have : u2.val < (j0 + 1) * 2 ^ b := by rw [Nat.add_mul, Nat.one_mul]; omega
          have := (Nat.div_lt_iff_lt_mul (by positivity)).mpr this
          omega
        have hhi_eq : u1.val / 2 ^ b = u2.val / 2 ^ b := by
          split_ifs at hq_eq with c1 c2
          · exact hq_eq
          · omega
          · omega
          · omega
        apply Fin.ext
        have h1 := Nat.div_add_mod u1.val (2 ^ b)
        have h2 := Nat.div_add_mod u2.val (2 ^ b)
        have hmul : 2 ^ b * (u1.val / 2 ^ b) = 2 ^ b * (u2.val / 2 ^ b) :=
          congrArg (2 ^ b * ·) hhi_eq
        omega
      have hφ_img : Finset.univ.image φ = sols.filter (fun y => y.val < (targetFin t).val) := by
        ext y
        simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter, sols]
        constructor
        · rintro ⟨u, rfl⟩
          set uhi := u.val / 2 ^ b
          set ulo := u.val % 2 ^ b
          set elast := if uhi < j0 then uhi else lowCut K t.val G'
          have hulo_lt : ulo < 2 ^ b := Nat.mod_lt _ (by positivity)
          have hel_lt : elast < 2 ^ k := by
            dsimp only [elast]
            split_ifs
            · omega
            · have := lowCut_le K t.val G'; omega
          let d_u : Fin G → ℕ := fun g =>
            if h : g.val < G' then prefD ⟨g.val, h⟩ else elast
          have hdu_lt : ∀ g, d_u g < 2 ^ k := by
            intro g; dsimp only [d_u]; split_ifs with h
            · exact hpref_lt ⟨g.val, h⟩
            · exact hel_lt
          have hpack_u : packRec k G d_u = P_ref * 2 ^ k + elast := by
            rw [hpack_split d_u]
            congr 1
            · congr 1
              · congr 1
                funext g
                simp [d_u, g.isLt]
            · simp [d_u]
          have hphi_val : (φ u).val = packRec k G d_u * 2 ^ b + ulo := by
            change (P_ref * 2 ^ k + elast) * 2 ^ b + ulo = _
            rw [hpack_u]
          refine ⟨?_, ?_⟩
          · rw [hsol_iff t (φ u)]
            have hM : (φ u).val < 2 ^ (G * k + b) := by
              rw [hphi_val, pow_add]
              have hp := packRec_lt k G d_u hdu_lt
              have h1 : packRec k G d_u + 1 ≤ 2 ^ (G * k) := hp
              have h2 : (packRec k G d_u + 1) * 2 ^ b ≤ 2 ^ (G * k) * 2 ^ b :=
                Nat.mul_le_mul_right _ h1
              rw [Nat.add_mul, Nat.one_mul] at h2
              omega
            refine ⟨hM, fun g => ?_⟩
            rw [hphi_val, hdiv_block d_u ulo hdu_lt hulo_lt g]
            dsimp only [d_u]
            split_ifs with h
            · simp [allowed, prefD]
            · have hg_eq : g.val + 1 = G := by have := g.isLt; omega
              dsimp only [elast]
              split_ifs with hltj
              · simp [allowed, hg_eq, hltj]
              · have hg' : g.val = G' := by omega
                simp [allowed, hg']
          · change (P_ref * 2 ^ k + elast) * 2 ^ b + ulo < targetNum t
            rw [htarget_split]
            by_cases hltj : uhi < j0
            · have hel_eq : elast = uhi := by simp [elast, hltj]
              rw [hel_eq]
              have h1 : P_ref * 2 ^ k + uhi + 1 ≤ P_ref * 2 ^ k + lowCut K t.val G' := by omega
              have h2 : (P_ref * 2 ^ k + uhi + 1) * 2 ^ b ≤
                  (P_ref * 2 ^ k + lowCut K t.val G') * 2 ^ b := Nat.mul_le_mul_right _ h1
              rw [Nat.add_mul, Nat.one_mul] at h2
              omega
            · have hel_eq : elast = lowCut K t.val G' := by simp [elast, hltj]
              rw [hel_eq]
              have hdm : uhi * 2 ^ b + ulo = u.val := by
                dsimp only [uhi, ulo]; rw [mul_comm, Nat.div_add_mod]
              have hu_lt : u.val < j0 * 2 ^ b + r0 := by rw [hqr_eq]; exact u.isLt
              have hhi_ge : j0 * 2 ^ b ≤ uhi * 2 ^ b := Nat.mul_le_mul_right _ (by omega)
              omega
        · rintro ⟨hy_sol, hy_lt⟩
          rw [hsol_iff t y] at hy_sol
          rcases hy_sol with ⟨hyM, hydig⟩
          let e : Fin G → ℕ := fun g => (y.val / 2 ^ (b + (G - 1 - g.val) * k)) % 2 ^ k
          have he_lt : ∀ g, e g < 2 ^ k := fun g => Nat.mod_lt _ (by positivity)
          let tail_y := y.val % 2 ^ b
          have htail_lt : tail_y < 2 ^ b := Nat.mod_lt _ (by positivity)
          have hy_div_lt : y.val / 2 ^ b < 2 ^ (G * k) := by
            rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add]
            exact hyM
          have hy_reconstruct : y.val = packRec k G e * 2 ^ b + tail_y := by
            have hrec := packRec_reconstruct k G (y.val / 2 ^ b) hy_div_lt
            have hfun_e : (fun g : Fin G => ((y.val / 2 ^ b) / 2 ^ ((G - 1 - g.val) * k)) % 2 ^ k) = e := by
              funext g
              dsimp only [e]
              rw [pow_add, ← Nat.div_div_eq_div_mul]
            rw [hfun_e] at hrec
            rw [hrec, mul_comm, Nat.div_add_mod]
          set P_y := packRec k G' (fun g : Fin G' => e ⟨g.val, by omega⟩)
          set elast_y := e ⟨G', by omega⟩
          have hy_split : y.val = (P_y * 2 ^ k + elast_y) * 2 ^ b + tail_y := by
            rw [hy_reconstruct, hpack_split e]
          have he_ge_pref : ∀ g : Fin G', prefD g ≤ e ⟨g.val, by omega⟩ := by
            intro g
            have hd := hydig ⟨g.val, by omega⟩
            have hne : ¬ (g.val + 1 = G) := by have := g.isLt; omega
            simp only [allowed, hne, decide_false, Bool.false_and, Bool.or_false,
              decide_eq_true_eq] at hd
            exact hd
          have hPy_ge : P_ref ≤ P_y := packRec_mono k G' prefD _ he_ge_pref
          have hy_lt' : (P_y * 2 ^ k + elast_y) * 2 ^ b + tail_y <
              (P_ref * 2 ^ k + lowCut K t.val G') * 2 ^ b + r0 := by
            rw [← hy_split, ← htarget_split]; exact hy_lt
          have hPy_eq : P_y = P_ref := by
            by_contra hne
            have hgt : P_ref + 1 ≤ P_y := by omega
            have h1 : (P_ref + 1) * 2 ^ k ≤ P_y * 2 ^ k := Nat.mul_le_mul_right _ hgt
            rw [Nat.add_mul, Nat.one_mul] at h1
            have hlc_lt : lowCut K t.val G' < 2 ^ k := by
              have := lowCut_le K t.val G'; omega
            have h2 : P_ref * 2 ^ k + lowCut K t.val G' + 1 ≤ P_y * 2 ^ k + elast_y := by omega
            have h3 : (P_ref * 2 ^ k + lowCut K t.val G' + 1) * 2 ^ b ≤
                (P_y * 2 ^ k + elast_y) * 2 ^ b := Nat.mul_le_mul_right _ h2
            rw [Nat.add_mul, Nat.one_mul] at h3
            omega
          rw [hPy_eq] at hy_lt' hy_split
          have hel_le : elast_y ≤ lowCut K t.val G' := by
            by_contra hgt
            have h1 : P_ref * 2 ^ k + lowCut K t.val G' + 1 ≤ P_ref * 2 ^ k + elast_y := by omega
            have h2 : (P_ref * 2 ^ k + lowCut K t.val G' + 1) * 2 ^ b ≤
                (P_ref * 2 ^ k + elast_y) * 2 ^ b := Nat.mul_le_mul_right _ h1
            rw [Nat.add_mul, Nat.one_mul] at h2
            omega
          by_cases hel_lt_lc : elast_y < lowCut K t.val G'
          · have hd_last := hydig ⟨G', by omega⟩
            simp only [allowed, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hd_last
            have hel_eq_div : (y.val / 2 ^ (b + (G - 1 - G') * k)) % 2 ^ k = elast_y := rfl
            rw [hel_eq_div] at hd_last
            have hel_lt_j0 : elast_y < j0 := by
              rcases hd_last with h1 | ⟨_, h2⟩
              · omega
              · exact h2
            have hu_lt : elast_y * 2 ^ b + tail_y < q.val := by
              rw [← hqr_eq]
              have h1 : elast_y + 1 ≤ j0 := hel_lt_j0
              have h2 : (elast_y + 1) * 2 ^ b ≤ j0 * 2 ^ b := Nat.mul_le_mul_right _ h1
              rw [Nat.add_mul, Nat.one_mul] at h2
              omega
            refine ⟨⟨elast_y * 2 ^ b + tail_y, hu_lt⟩, Fin.ext ?_⟩
            dsimp only [φ]
            have hdiv : (elast_y * 2 ^ b + tail_y) / 2 ^ b = elast_y := by
              rw [mul_comm, Nat.mul_add_div (by positivity), Nat.div_eq_of_lt htail_lt, add_zero]
            have hmod : (elast_y * 2 ^ b + tail_y) % 2 ^ b = tail_y := by
              rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt htail_lt]
            rw [hdiv, hmod]
            simp only [hel_lt_j0, ↓reduceIte, ← hy_split]
          · have hel_eq_lc : elast_y = lowCut K t.val G' := by omega
            have htail_lt_r0 : tail_y < r0 := by rw [hel_eq_lc] at hy_lt'; omega
            have hu_lt : j0 * 2 ^ b + tail_y < q.val := by rw [← hqr_eq]; omega
            refine ⟨⟨j0 * 2 ^ b + tail_y, hu_lt⟩, Fin.ext ?_⟩
            dsimp only [φ]
            have hdiv : (j0 * 2 ^ b + tail_y) / 2 ^ b = j0 := by
              rw [mul_comm, Nat.mul_add_div (by positivity), Nat.div_eq_of_lt htail_lt, add_zero]
            have hmod : (j0 * 2 ^ b + tail_y) % 2 ^ b = tail_y := by
              rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt htail_lt]
            rw [hdiv, hmod]
            simp only [lt_irrefl j0, ↓reduceIte, ← hel_eq_lc, ← hy_split]
      rw [← hφ_img, Finset.card_image_of_injective _ hφ_inj, Finset.card_univ, Fintype.card_fin]
    have hq_lt_sols : q.val < sols.card := by
      have hss : sols.filter (fun y => y.val < (targetFin t).val) ⊂ sols := by
        rw [Finset.ssubset_iff_subset_ne]
        refine ⟨Finset.filter_subset _ _, ?_⟩
        intro heq
        have hmem : targetFin t ∈ sols.filter (fun y => y.val < (targetFin t).val) :=
          heq.symm ▸ hzt_mem
        have := (Finset.mem_filter.mp hmem).2
        omega
      have := Finset.card_lt_card hss
      omega
    rcases hcirc (tbl t) hq_lt_sols with ⟨z, hz_mem, hz_rank, hz_out⟩
    have hz_rank' : (sols.filter (fun y => y.val < z.val)).card = q.val := hz_rank
    have hz_eq : z = targetFin t := by
      by_contra hne
      rcases lt_or_gt_of_ne (fun h => hne (Fin.ext h)) with hlt | hgt
      · have hss : sols.filter (fun y => y.val < z.val) ⊂
            sols.filter (fun y => y.val < (targetFin t).val) := by
          rw [Finset.ssubset_iff_subset_ne]
          refine ⟨fun y hy => Finset.mem_filter.mpr
            ⟨(Finset.mem_filter.mp hy).1, lt_trans (Finset.mem_filter.mp hy).2 hlt⟩, ?_⟩
          intro heq
          have hz_in : z ∈ sols.filter (fun y => y.val < z.val) :=
            heq ▸ Finset.mem_filter.mpr ⟨hz_mem, hlt⟩
          have := (Finset.mem_filter.mp hz_in).2
          omega
        have := Finset.card_lt_card hss
        omega
      · have hss : sols.filter (fun y => y.val < (targetFin t).val) ⊂
            sols.filter (fun y => y.val < z.val) := by
          rw [Finset.ssubset_iff_subset_ne]
          refine ⟨fun y hy => Finset.mem_filter.mpr
            ⟨(Finset.mem_filter.mp hy).1, lt_trans (Finset.mem_filter.mp hy).2 hgt⟩, ?_⟩
          intro heq
          have hzt_in : targetFin t ∈ sols.filter (fun y => y.val < (targetFin t).val) :=
            heq ▸ Finset.mem_filter.mpr ⟨hzt_mem, hgt⟩
          have := (Finset.mem_filter.mp hzt_in).2
          omega
        have := Finset.card_lt_card hss
        omega
    rw [hz_eq] at hz_out
    exact hz_out
  have hall_drop : prefixDrops I C.gates xs = Finset.univ := by
    rw [Finset.eq_univ_iff_forall]
    intro t
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ t, ?_⟩
    have hlt_num : targetNum t.succ < targetNum t.castSucc := by
      dsimp only [targetNum]
      have hg_lt : t.val / K < G := by
        have ht_lt : t.val < G * K := lt_of_lt_of_le t.isLt (Nat.sub_le _ _)
        exact (Nat.div_lt_iff_lt_mul hK_pos).mpr ht_lt
      have hpack_lt : packRec k G (targetDigit t.succ) < packRec k G (targetDigit t.castSucc) :=
        packRec_lt_of_le_lt k G (targetDigit t.succ) (targetDigit t.castSucc)
          (fun g => lowCut_antitone K g.val t.castSucc.val t.succ.val (by simp))
          ⟨t.val / K, hg_lt⟩
          (lowCut_step_lt K t.val hK_pos)
      have hmul_lt : packRec k G (targetDigit t.succ) * 2 ^ b <
          packRec k G (targetDigit t.castSucc) * 2 ^ b :=
        Nat.mul_lt_mul_of_pos_right hpack_lt (by positivity)
      omega
    rcases exists_bit_drop n (targetNum t.succ) (targetNum t.castSucc)
        (htarget_lt t.succ) (htarget_lt t.castSucc) hlt_num with ⟨pos, htrue, hfalse⟩
    refine ⟨outBit pos, ?_, ?_⟩
    · change (C.wires (xs t.castSucc)).getD (outBit pos).val false = true
      rw [hcirc_out t.castSucc pos]; exact htrue
    · change (C.wires (xs t.succ)).getD (outBit pos).val false = false
      rw [hcirc_out t.succ pos]; exact hfalse
  rw [hall_drop, Finset.card_univ, Fintype.card_fin] at hmarkov
  exact hmarkov

end PEqualNP.Outside.L_clb_067_aux

theorem PEqualNP.Outside.L_clb_067 : ∀ (n w : ℕ) (hn : 0 < n) (q : Fin (2 ^ n)),
  let I := n * 2 ^ (w + 1)
  ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (outBit : Fin n → Fin (I + C.size)),
    PEqualNP.MetaComplexity.FanInTwo C →
    PEqualNP.MetaComplexity.NestedCover.ReadsBack I C →
    (∀ table : Fin n → (Fin (w + 1) → Bool) → Bool,
      let inputs := (List.ofFn (fun i : Fin n => List.ofFn (fun pat : Fin (2 ^ (w + 1)) =>
        table i (fun j => pat.val.testBit j.val)))).flatten
      let sols := (Finset.univ : Finset (Fin (2 ^ n))).filter (fun z => ∀ i : Fin n,
        table i (fun j => z.val.testBit (n - 1 - ((i.val + j.val) % n))) = true)
      q.val < sols.card → ∃ z ∈ sols,
        (sols.filter (fun y => y.val < z.val)).card = q.val ∧
        ∀ pos : Fin n, (C.wires inputs).getD (outBit pos).val false =
          z.val.testBit (n - 1 - pos.val)) →
    ∀ k b : ℕ, 0 < k → k ≤ w + 1 → k + b ≤ n → q.val < 2 ^ (k + b) →
      1 + ((n - b) / k) * (2 ^ k - 1) - q.val / 2 ^ b ≤
        2 ^ PEqualNP.NotBracket.notCount C := by
  intro n w hn q _I C outBit hfan hread hcirc k b hk0 hkw hkbn hqkb
  exact PEqualNP.Outside.L_clb_067_aux.main_proof n w hn q C outBit hfan hread hcirc k b
    hk0 hkw hkbn hqkb
