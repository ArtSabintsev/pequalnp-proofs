import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22879

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

private def stepGate (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

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

private theorem getD_append_lt (l1 l2 : List Bool) (i : ℕ) (hi : i < l1.length) :
    (l1 ++ l2).getD i false = l1.getD i false :=
  List.getD_append l1 l2 false i hi

private theorem getD_append_ge (l1 l2 : List Bool) (i : ℕ) (hi : l1.length ≤ i) :
    (l1 ++ l2).getD i false = l2.getD (i - l1.length) false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right hi]

private def buildC (n : ℕ) : Circuit :=
  { gates := [
      ⟨GateOp.or, [3, n]⟩,
      ⟨GateOp.or, [1, n + 3]⟩,
      ⟨GateOp.or, [2, n + 2]⟩,
      ⟨GateOp.or, [0, n + 1]⟩,
      ⟨GateOp.or, [2 * n + 1, 2 * n + 2]⟩,
      ⟨GateOp.not, [2 * n + 4]⟩,
      ⟨GateOp.and, [2 * n, 2 * n + 5]⟩,
      ⟨GateOp.or, [2 * n + 3, 2 * n + 2]⟩,
      ⟨GateOp.and, [2 * n + 1, 2 * n + 7]⟩,
      ⟨GateOp.or, [2 * n + 6, 2 * n + 8]⟩
    ],
    output := 2 * n + 9 }

private theorem buildC_fan (n : ℕ) : FanInTwo (buildC n) := by
  intro g hg
  simp only [buildC, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

private theorem buildC_rep (n : ℕ) (hn : 5 ≤ n) :
    Represents (fun (u : Fin n) (v : Fin n) => decide ((u.val = 0 ∧ (v.val = 0 ∨ v.val = 3)) ∨ (u.val = 1 ∧ (v.val = 1 ∨ v.val = 2)) ∨ (u.val = 2 ∧ v.val = 3) ∨ (u.val = 3 ∧ (v.val ≤ 1 ∨ 4 ≤ v.val)) ∨ (4 ≤ u.val ∧ v.val = 0))) (buildC n) := by
  intro u v
  simp only [Circuit.eval, Circuit.wires, buildC]
  change (([
      ⟨GateOp.or, [3, n]⟩,
      ⟨GateOp.or, [1, n + 3]⟩,
      ⟨GateOp.or, [2, n + 2]⟩,
      ⟨GateOp.or, [0, n + 1]⟩,
      ⟨GateOp.or, [2 * n + 1, 2 * n + 2]⟩,
      ⟨GateOp.not, [2 * n + 4]⟩,
      ⟨GateOp.and, [2 * n, 2 * n + 5]⟩,
      ⟨GateOp.or, [2 * n + 3, 2 * n + 2]⟩,
      ⟨GateOp.and, [2 * n + 1, 2 * n + 7]⟩,
      ⟨GateOp.or, [2 * n + 6, 2 * n + 8]⟩
    ] : List Gate).foldl stepGate (oneEach u v)).getD (2 * n + 9) false = _
  simp only [List.foldl_cons, List.foldl_nil]
  set w0 := oneEach u v
  have hl0 : w0.length = 2 * n := by simp [w0, oneEach]; omega
  set a := w0.getD 3 false || w0.getD n false
  set d := w0.getD 1 false || w0.getD (n + 3) false
  set e := w0.getD 2 false || w0.getD (n + 2) false
  set b := w0.getD 0 false || w0.getD (n + 1) false
  have h0 : stepGate w0 ⟨GateOp.or, [3, n]⟩ = w0 ++ [a] := by
    simp [stepGate, GateOp.eval, a]
  rw [h0]
  have h1 : stepGate (w0 ++ [a]) ⟨GateOp.or, [1, n + 3]⟩ = w0 ++ [a, d] := by
    simp only [stepGate, List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]
    rw [getD_append_lt w0 [a] 1 (by omega), getD_append_lt w0 [a] (n + 3) (by omega), List.append_assoc]
    rfl
  rw [h1]
  have h2 : stepGate (w0 ++ [a, d]) ⟨GateOp.or, [2, n + 2]⟩ = w0 ++ [a, d, e] := by
    simp only [stepGate, List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]
    rw [getD_append_lt w0 [a, d] 2 (by omega), getD_append_lt w0 [a, d] (n + 2) (by omega), List.append_assoc]
    rfl
  rw [h2]
  have h3 : stepGate (w0 ++ [a, d, e]) ⟨GateOp.or, [0, n + 1]⟩ = w0 ++ [a, d, e, b] := by
    simp only [stepGate, List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]
    rw [getD_append_lt w0 [a, d, e] 0 (by omega), getD_append_lt w0 [a, d, e] (n + 1) (by omega), List.append_assoc]
    rfl
  rw [h3]
  set de := d || e
  have h4 : stepGate (w0 ++ [a, d, e, b]) ⟨GateOp.or, [2 * n + 1, 2 * n + 2]⟩ = w0 ++ [a, d, e, b, de] := by
    simp only [stepGate, List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]
    rw [getD_append_ge w0 [a, d, e, b] (2 * n + 1) (by omega), getD_append_ge w0 [a, d, e, b] (2 * n + 2) (by omega), hl0]
    have hm1 : 2 * n + 1 - 2 * n = 1 := by omega
    have hm2 : 2 * n + 2 - 2 * n = 2 := by omega
    rw [hm1, hm2, List.append_assoc]
    rfl
  rw [h4]
  set nde := !de
  have h5 : stepGate (w0 ++ [a, d, e, b, de]) ⟨GateOp.not, [2 * n + 4]⟩ = w0 ++ [a, d, e, b, de, nde] := by
    simp only [stepGate, List.map_cons, List.map_nil, GateOp.eval, List.headD_cons]
    rw [getD_append_ge w0 [a, d, e, b, de] (2 * n + 4) (by omega), hl0]
    have hm4 : 2 * n + 4 - 2 * n = 4 := by omega
    rw [hm4, List.append_assoc]
    rfl
  rw [h5]
  set p1 := a && nde
  have h6 : stepGate (w0 ++ [a, d, e, b, de, nde]) ⟨GateOp.and, [2 * n, 2 * n + 5]⟩ = w0 ++ [a, d, e, b, de, nde, p1] := by
    simp only [stepGate, List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true]
    rw [getD_append_ge w0 [a, d, e, b, de, nde] (2 * n) (by omega), getD_append_ge w0 [a, d, e, b, de, nde] (2 * n + 5) (by omega), hl0]
    have hm0 : 2 * n - 2 * n = 0 := by omega
    have hm5 : 2 * n + 5 - 2 * n = 5 := by omega
    rw [hm0, hm5, List.append_assoc]
    rfl
  rw [h6]
  set be := b || e
  have h7 : stepGate (w0 ++ [a, d, e, b, de, nde, p1]) ⟨GateOp.or, [2 * n + 3, 2 * n + 2]⟩ = w0 ++ [a, d, e, b, de, nde, p1, be] := by
    simp only [stepGate, List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]
    rw [getD_append_ge w0 [a, d, e, b, de, nde, p1] (2 * n + 3) (by omega), getD_append_ge w0 [a, d, e, b, de, nde, p1] (2 * n + 2) (by omega), hl0]
    have hm3 : 2 * n + 3 - 2 * n = 3 := by omega
    have hm2 : 2 * n + 2 - 2 * n = 2 := by omega
    rw [hm3, hm2, List.append_assoc]
    rfl
  rw [h7]
  set p2 := d && be
  have h8 : stepGate (w0 ++ [a, d, e, b, de, nde, p1, be]) ⟨GateOp.and, [2 * n + 1, 2 * n + 7]⟩ = w0 ++ [a, d, e, b, de, nde, p1, be, p2] := by
    simp only [stepGate, List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true]
    rw [getD_append_ge w0 [a, d, e, b, de, nde, p1, be] (2 * n + 1) (by omega), getD_append_ge w0 [a, d, e, b, de, nde, p1, be] (2 * n + 7) (by omega), hl0]
    have hm1 : 2 * n + 1 - 2 * n = 1 := by omega
    have hm7 : 2 * n + 7 - 2 * n = 7 := by omega
    rw [hm1, hm7, List.append_assoc]
    rfl
  rw [h8]
  set out := p1 || p2
  have h9 : stepGate (w0 ++ [a, d, e, b, de, nde, p1, be, p2]) ⟨GateOp.or, [2 * n + 6, 2 * n + 8]⟩ = w0 ++ [a, d, e, b, de, nde, p1, be, p2, out] := by
    simp only [stepGate, List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]
    rw [getD_append_ge w0 [a, d, e, b, de, nde, p1, be, p2] (2 * n + 6) (by omega), getD_append_ge w0 [a, d, e, b, de, nde, p1, be, p2] (2 * n + 8) (by omega), hl0]
    have hm6 : 2 * n + 6 - 2 * n = 6 := by omega
    have hm8 : 2 * n + 8 - 2 * n = 8 := by omega
    rw [hm6, hm8, List.append_assoc]
    rfl
  rw [h9, getD_append_ge w0 [a, d, e, b, de, nde, p1, be, p2, out] (2 * n + 9) (by omega), hl0]
  have hm9 : 2 * n + 9 - 2 * n = 9 := by omega
  rw [hm9]
  change out = _
  dsimp only [out, p1, p2, nde, de, be, a, d, e, b, w0]
  rw [getD_oneEach u v 0 (by omega), getD_oneEach u v 1 (by omega),
    getD_oneEach u v 2 (by omega), getD_oneEach u v 3 (by omega),
    getD_oneEach u v n (by omega), getD_oneEach u v (n + 1) (by omega),
    getD_oneEach u v (n + 2) (by omega), getD_oneEach u v (n + 3) (by omega)]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_false_iff,
    decide_eq_true_eq, decide_eq_false_iff_not]
  have := u.isLt; have := v.isLt
  omega

end PEqualNP.Outside.L_meta_22879

theorem PEqualNP.Outside.L_meta_22879 : ∀ n : ℕ, 5 ≤ n → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun (u : Fin n) (v : Fin n) => decide ((u.val = 0 ∧ (v.val = 0 ∨ v.val = 3)) ∨ (u.val = 1 ∧ (v.val = 1 ∨ v.val = 2)) ∨ (u.val = 2 ∧ v.val = 3) ∨ (u.val = 3 ∧ (v.val ≤ 1 ∨ 4 ≤ v.val)) ∨ (4 ≤ u.val ∧ v.val = 0))) C := by
  intro n hn
  exact ⟨PEqualNP.Outside.L_meta_22879.buildC n,
    PEqualNP.Outside.L_meta_22879.buildC_fan n,
    by simp [PEqualNP.Outside.L_meta_22879.buildC, PEqualNP.CircuitLowerBounds.Circuit.size],
    PEqualNP.Outside.L_meta_22879.buildC_rep n hn⟩
