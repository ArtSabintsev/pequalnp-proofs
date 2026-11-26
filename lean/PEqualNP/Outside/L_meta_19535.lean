import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19535

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

private def orChain (base startWire : ℕ) : ℕ → List Gate
  | 0 => []
  | k + 1 => orChain base startWire k ++
      [⟨GateOp.or, [if k = 0 then startWire else base + k - 1, startWire + k + 1]⟩]

private def chainOut (base startWire k : ℕ) : ℕ :=
  if k = 0 then startWire else base + k - 1

private theorem orChain_length (base startWire : ℕ) :
    ∀ k, (orChain base startWire k).length = k
  | 0 => rfl
  | k + 1 => by simp [orChain, orChain_length]

private theorem orChain_mono (base startWire : ℕ) :
    ∀ k g, g ∈ orChain base startWire k → (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2
  | 0, _, h => by cases h
  | k + 1, g, h => by
    simp only [orChain, List.mem_append, List.mem_singleton] at h
    rcases h with h | rfl
    · exact orChain_mono base startWire k g h
    · simp

private def stepGate (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem wires_foldl_prefix (gs : List Gate) :
    ∀ w : List Bool, ∃ t : List Bool, gs.foldl stepGate w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp, rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (stepGate w g)
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    simpa [List.foldl_cons, stepGate, List.append_assoc] using ht

private theorem getD_foldl_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepGate w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wires_foldl_prefix gs w
  rw [ht, List.getD_append _ _ _ _ hi]

private theorem length_foldl (gs : List Gate) (w : List Bool) :
    (gs.foldl stepGate w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wires_foldl_prefix gs w
  rw [ht, List.length_append, hl]

private theorem getD_orChain (base startWire : ℕ) (w : List Bool) (hb : base = w.length) :
    ∀ k, startWire + k < w.length →
      ((orChain base startWire k).foldl stepGate w).getD (chainOut base startWire k) false =
        decide (∃ j, j ≤ k ∧ w.getD (startWire + j) false = true)
  | 0, _ => by
    simp only [orChain, List.foldl_nil, chainOut, ↓reduceIte, Nat.le_zero, exists_eq_left, add_zero]
    cases w.getD startWire false <;> rfl
  | k + 1, hk => by
    have ih := getD_orChain base startWire w hb k (by omega)
    simp only [orChain, List.foldl_append, List.foldl_cons, List.foldl_nil, stepGate]
    set w1 := (orChain base startWire k).foldl stepGate w
    have hlen1 : w1.length = base + k := by rw [length_foldl, orChain_length, hb]
    have hcur_eq : w1.getD (startWire + k + 1) false = w.getD (startWire + k + 1) false :=
      getD_foldl_lt _ w _ (by omega)
    have hidx : chainOut base startWire (k + 1) = w1.length := by
      simp [chainOut]; omega
    rw [hidx, List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self]
    simp only [List.getD_cons_zero, List.map_cons, List.map_nil, GateOp.eval,
      List.any_cons, List.any_nil, id_eq, Bool.or_false]
    change (w1.getD (chainOut base startWire k) false || w1.getD (startWire + k + 1) false) = _
    rw [ih, hcur_eq]
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    constructor
    · rintro (⟨j, hj, h⟩ | h)
      · exact ⟨j, by omega, h⟩
      · exact ⟨k + 1, le_refl _, by simpa [Nat.add_assoc] using h⟩
    · rintro ⟨j, hj, h⟩
      by_cases hlt : j ≤ k
      · exact Or.inl ⟨j, hlt, h⟩
      · have hj' : j = k + 1 := by omega
        subst hj'
        exact Or.inr (by simpa [Nat.add_assoc] using h)

private theorem getD_oneEach {n : ℕ} (u v : Fin n) (i : ℕ) (hi : i < n + n) :
    (oneEach u v).getD i false = decide (i = u.val ∨ i = n + v.val) := by
  have hlen : (oneEach u v).length = n + n := by simp [oneEach]
  rw [List.getD_eq_getElem _ _ (by omega)]
  simp only [oneEach, List.getElem_append, List.length_ofFn, List.getElem_ofFn]
  split_ifs with h
  · have hne : ¬ i = n + v.val := by omega
    simp [Fin.ext_iff, hne, eq_comm]
  · have hne : ¬ i = u.val := by omega
    have hiff : i - n = v.val ↔ i = n + v.val := by omega
    simp [Fin.ext_iff, hne, hiff]

private def buildC (n : ℕ) : Circuit :=
  let k := n - 3
  let qBase := 2 * n
  let qGates := orChain qBase (n + 1) k
  let qOut := chainOut qBase (n + 1) k
  let dBase := 2 * n + k
  let dGates := orChain dBase 2 k
  let dOut := chainOut dBase 2 k
  let b := 2 * n + 2 * k
  let tail : List Gate := [
    ⟨GateOp.or, [qOut, 2 * n - 1]⟩,
    ⟨GateOp.or, [n, qOut]⟩,
    ⟨GateOp.and, [0, b]⟩,
    ⟨GateOp.and, [1, n]⟩,
    ⟨GateOp.and, [dOut, b + 1]⟩,
    ⟨GateOp.or, [b + 2, b + 3]⟩,
    ⟨GateOp.or, [b + 5, b + 4]⟩
  ]
  { gates := qGates ++ dGates ++ tail, output := b + 6 }

private theorem buildC_mono (n : ℕ) : Monotone2 (buildC n) := by
  intro g hg
  simp only [buildC, List.mem_append] at hg
  rcases hg with (hq | hd) | ht
  · exact orChain_mono _ _ _ g hq
  · exact orChain_mono _ _ _ g hd
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

private theorem buildC_size (n : ℕ) (hn : 3 ≤ n) : (buildC n).size ≤ 2 * n + 1 := by
  simp only [Circuit.size, buildC, List.length_append, orChain_length, List.length_cons, List.length_nil]
  omega

private theorem getD_step_push (w : List Bool) (op : GateOp) (a b : ℕ) :
    (stepGate w ⟨op, [a, b]⟩).getD w.length false =
      op.eval [w.getD a false, w.getD b false] := by
  simp [stepGate, List.getD_append_right _ _ _ _ (le_refl _)]

private theorem getD_step_lt (w : List Bool) (g : Gate) (i : ℕ) (hi : i < w.length) :
    (stepGate w g).getD i false = w.getD i false := by
  rw [stepGate, List.getD_append _ _ _ _ hi]

private theorem buildC_rep (n : ℕ) (hn : 3 ≤ n) :
    Represents (fun u v : Fin n =>
      decide ((u.val = 0 ∧ 1 ≤ v.val) ∨ (u.val = 1 ∧ v.val = 0) ∨ (2 ≤ u.val ∧ v.val + 2 ≤ n)))
      (buildC n) := by
  intro u v
  simp only [Circuit.eval, Circuit.wires, buildC]
  change (((orChain (2 * n) (n + 1) (n - 3) ++ orChain (2 * n + (n - 3)) 2 (n - 3) ++
    ([⟨GateOp.or, [chainOut (2 * n) (n + 1) (n - 3), 2 * n - 1]⟩,
      ⟨GateOp.or, [n, chainOut (2 * n) (n + 1) (n - 3)]⟩,
      ⟨GateOp.and, [0, 2 * n + 2 * (n - 3)]⟩,
      ⟨GateOp.and, [1, n]⟩,
      ⟨GateOp.and, [chainOut (2 * n + (n - 3)) 2 (n - 3), 2 * n + 2 * (n - 3) + 1]⟩,
      ⟨GateOp.or, [2 * n + 2 * (n - 3) + 2, 2 * n + 2 * (n - 3) + 3]⟩,
      ⟨GateOp.or, [2 * n + 2 * (n - 3) + 5, 2 * n + 2 * (n - 3) + 4]⟩] : List Gate)).foldl
    stepGate (oneEach u v)).getD (2 * n + 2 * (n - 3) + 6) false) = _
  set w0 := oneEach u v
  have hlen0 : w0.length = 2 * n := by simp [w0, oneEach]; omega
  set k := n - 3
  set w1 := (orChain (2 * n) (n + 1) k).foldl stepGate w0
  have hlen1 : w1.length = 2 * n + k := by rw [length_foldl, orChain_length, hlen0]
  set w2 := (orChain (2 * n + k) 2 k).foldl stepGate w1
  have hlen2 : w2.length = 2 * n + 2 * k := by rw [length_foldl, orChain_length, hlen1]; omega
  have hqOut_lt : chainOut (2 * n) (n + 1) k < w1.length := by
    simp only [chainOut]; split_ifs <;> omega
  have hq1 : w1.getD (chainOut (2 * n) (n + 1) k) false =
      decide (∃ j, j ≤ k ∧ w0.getD (n + 1 + j) false = true) :=
    getD_orChain (2 * n) (n + 1) w0 hlen0.symm k (by omega)
  have hq2 : w2.getD (chainOut (2 * n) (n + 1) k) false =
      decide (1 ≤ v.val ∧ v.val + 2 ≤ n) := by
    rw [getD_foldl_lt _ w1 _ hqOut_lt, hq1]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    constructor
    · rintro ⟨j, hj, h⟩
      rw [getD_oneEach u v (n + 1 + j) (by omega)] at h
      simp only [decide_eq_true_eq] at h
      have := u.isLt; have := v.isLt; omega
    · rintro ⟨h1, h2⟩
      refine ⟨v.val - 1, by omega, ?_⟩
      rw [getD_oneEach u v (n + 1 + (v.val - 1)) (by omega)]
      simp only [decide_eq_true_eq]
      right; omega
  have hd2 : w2.getD (chainOut (2 * n + k) 2 k) false = decide (2 ≤ u.val) := by
    rw [getD_orChain (2 * n + k) 2 w1 hlen1.symm k (by omega)]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    constructor
    · rintro ⟨j, hj, h⟩
      rw [getD_foldl_lt _ w0 _ (by omega), getD_oneEach u v (2 + j) (by omega)] at h
      simp only [decide_eq_true_eq] at h
      have := u.isLt; have := v.isLt; omega
    · intro h2
      refine ⟨u.val - 2, by omega, ?_⟩
      rw [getD_foldl_lt _ w0 _ (by omega), getD_oneEach u v (2 + (u.val - 2)) (by omega)]
      simp only [decide_eq_true_eq]
      left; omega
  have hw2_in : ∀ i, i < 2 * n → w2.getD i false = decide (i = u.val ∨ i = n + v.val) := by
    intro i hi
    rw [getD_foldl_lt _ w1 _ (by omega), getD_foldl_lt _ w0 _ (by omega),
      getD_oneEach u v i (by omega)]
  have h0 : w2.getD 0 false = decide (u.val = 0) := by
    rw [hw2_in 0 (by omega)]; apply Bool.eq_iff_iff.mpr; simp; omega
  have h1 : w2.getD 1 false = decide (u.val = 1) := by
    rw [hw2_in 1 (by omega)]; apply Bool.eq_iff_iff.mpr; simp; omega
  have hy0 : w2.getD n false = decide (v.val = 0) := by
    rw [hw2_in n (by omega)]; apply Bool.eq_iff_iff.mpr; simp; have := u.isLt; omega
  have hylast : w2.getD (2 * n - 1) false = decide (v.val = n - 1) := by
    rw [hw2_in (2 * n - 1) (by omega)]; apply Bool.eq_iff_iff.mpr; simp; have := u.isLt; omega
  simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
  set b := 2 * n + 2 * k
  set qO := chainOut (2 * n) (n + 1) k
  set dO := chainOut (2 * n + k) 2 k
  have hqO_b : qO < b := by omega
  have hdO_b : dO < b := by simp only [dO, chainOut]; split_ifs <;> omega
  set s0 := stepGate w2 ⟨GateOp.or, [qO, 2 * n - 1]⟩
  have hls0 : s0.length = b + 1 := by simp [s0, stepGate, hlen2, b]
  have hs0_b : s0.getD b false = (w2.getD qO false || w2.getD (2 * n - 1) false) := by
    simpa [s0, hlen2, b, GateOp.eval] using getD_step_push w2 GateOp.or qO (2 * n - 1)
  set s1 := stepGate s0 ⟨GateOp.or, [n, qO]⟩
  have hls1 : s1.length = b + 2 := by simp [s1, stepGate, hls0]
  have hs1_b1 : s1.getD (b + 1) false = (w2.getD n false || w2.getD qO false) := by
    have := getD_step_push s0 GateOp.or n qO
    rw [hls0] at this
    rw [this, getD_step_lt w2 _ n (by omega), getD_step_lt w2 _ qO (by omega)]
    simp [GateOp.eval]
  have hs1_b : s1.getD b false = s0.getD b false := getD_step_lt s0 _ b (by omega)
  set s2 := stepGate s1 ⟨GateOp.and, [0, b]⟩
  have hls2 : s2.length = b + 3 := by simp [s2, stepGate, hls1]
  have hs2_b2 : s2.getD (b + 2) false = (w2.getD 0 false && s0.getD b false) := by
    have := getD_step_push s1 GateOp.and 0 b
    rw [hls1] at this
    rw [this, getD_step_lt s0 _ 0 (by omega), getD_step_lt w2 _ 0 (by omega), hs1_b]
    simp [GateOp.eval]
  set s3 := stepGate s2 ⟨GateOp.and, [1, n]⟩
  have hls3 : s3.length = b + 4 := by simp [s3, stepGate, hls2]
  have hs3_b3 : s3.getD (b + 3) false = (w2.getD 1 false && w2.getD n false) := by
    have := getD_step_push s2 GateOp.and 1 n
    rw [hls2] at this
    rw [this,
      getD_step_lt s1 _ 1 (by omega), getD_step_lt s0 _ 1 (by omega), getD_step_lt w2 _ 1 (by omega),
      getD_step_lt s1 _ n (by omega), getD_step_lt s0 _ n (by omega), getD_step_lt w2 _ n (by omega)]
    simp [GateOp.eval]
  set s4 := stepGate s3 ⟨GateOp.and, [dO, b + 1]⟩
  have hls4 : s4.length = b + 5 := by simp [s4, stepGate, hls3]
  have hs4_b4 : s4.getD (b + 4) false = (w2.getD dO false && s1.getD (b + 1) false) := by
    have := getD_step_push s3 GateOp.and dO (b + 1)
    rw [hls3] at this
    rw [this,
      getD_step_lt s2 _ dO (by omega), getD_step_lt s1 _ dO (by omega),
      getD_step_lt s0 _ dO (by omega), getD_step_lt w2 _ dO (by omega),
      getD_step_lt s2 _ (b + 1) (by omega), getD_step_lt s1 _ (b + 1) (by omega)]
    simp [GateOp.eval]
  set s5 := stepGate s4 ⟨GateOp.or, [b + 2, b + 3]⟩
  have hls5 : s5.length = b + 6 := by simp [s5, stepGate, hls4]
  have hs5_b5 : s5.getD (b + 5) false = (s2.getD (b + 2) false || s3.getD (b + 3) false) := by
    have := getD_step_push s4 GateOp.or (b + 2) (b + 3)
    rw [hls4] at this
    rw [this,
      getD_step_lt s3 _ (b + 2) (by omega), getD_step_lt s2 _ (b + 2) (by omega),
      getD_step_lt s3 _ (b + 3) (by omega)]
    simp [GateOp.eval]
  have hout : (stepGate s5 ⟨GateOp.or, [b + 5, b + 4]⟩).getD (b + 6) false =
      (s5.getD (b + 5) false || s4.getD (b + 4) false) := by
    have := getD_step_push s5 GateOp.or (b + 5) (b + 4)
    rw [hls5] at this
    rw [this, getD_step_lt s4 _ (b + 4) (by omega)]
    simp [GateOp.eval]
  rw [hout, hs5_b5, hs2_b2, hs3_b3, hs4_b4, hs0_b, hs1_b1, h0, h1, hy0, hylast, hq2, hd2]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  have := u.isLt; have := v.isLt
  omega

end PEqualNP.Outside.L_meta_19535

theorem PEqualNP.Outside.L_meta_19535 : ∀ n : ℕ, 3 ≤ n → PEqualNP.Represents.RepSizeAtMost (fun u v : Fin n => decide ((u.val = 0 ∧ 1 ≤ v.val) ∨ (u.val = 1 ∧ v.val = 0) ∨ (2 ≤ u.val ∧ v.val + 2 ≤ n))) (2 * n + 1) := by
  intro n hn
  exact ⟨PEqualNP.Outside.L_meta_19535.buildC n,
    PEqualNP.Outside.L_meta_19535.buildC_mono n,
    PEqualNP.Outside.L_meta_19535.buildC_size n hn,
    PEqualNP.Outside.L_meta_19535.buildC_rep n hn⟩
