import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23958

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def matA (n : ℕ) (u v : Fin n) : Bool :=
  decide ((u.val = 0 ∧ v.val ≠ 0) ∨ (u.val = 1 ∧ v.val ≤ 1) ∨ (2 ≤ u.val ∧ v.val = 0))

def wiresPrefix (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem wiresPrefix_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    wiresPrefix (g :: gs) x = wiresPrefix gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) := rfl

theorem wiresPrefix_length (gs : List Gate) (x : List Bool) :
    (wiresPrefix gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [wiresPrefix]
  | cons g gs ih =>
    rw [wiresPrefix_cons, ih]
    simp
    omega

theorem wiresPrefix_append (gs1 gs2 : List Gate) (x : List Bool) :
    wiresPrefix (gs1 ++ gs2) x = wiresPrefix gs2 (wiresPrefix gs1 x) := by
  simp [wiresPrefix, List.foldl_append]

theorem wiresPrefix_getD_lt (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (wiresPrefix gs x).getD i false = x.getD i false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [wiresPrefix_cons]
    have hlt : i < (x ++ [g.op.eval (g.inputs.map fun j => x.getD j false)]).length := by
      simp
      omega
    rw [ih _ hlt]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left hi]

theorem wiresPrefix_getD_gate (gs : List Gate) (x : List Bool) (k : ℕ) (hk : k < gs.length) :
    (wiresPrefix gs x).getD (x.length + k) false =
      (gs[k]'hk).op.eval ((gs[k]'hk).inputs.map fun j => (wiresPrefix (gs.take k) x).getD j false) := by
  have hsplit : gs = gs.take k ++ [gs[k]'hk] ++ gs.drop (k + 1) := by
    conv_lhs => rw [← List.take_append_drop k gs]
    rw [List.append_assoc]
    congr 1
    simpa using (List.cons_getElem_drop_succ (h := hk)).symm
  conv_lhs => rw [hsplit, wiresPrefix_append, wiresPrefix_append]
  have hlen1 : (wiresPrefix (gs.take k) x).length = x.length + k := by
    rw [wiresPrefix_length, List.length_take]
    omega
  have hlt : x.length + k < (wiresPrefix ([gs[k]'hk]) (wiresPrefix (gs.take k) x)).length := by
    rw [wiresPrefix_length, hlen1]
    simp
  rw [wiresPrefix_getD_lt _ _ _ hlt]
  rw [wiresPrefix_cons]
  change (wiresPrefix (gs.take k) x ++ [(gs[k]'hk).op.eval ((gs[k]'hk).inputs.map fun j => (wiresPrefix (gs.take k) x).getD j false)]).getD (x.length + k) false = _
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by omega), hlen1, Nat.sub_self]
  rfl

theorem gateOp_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l1 l2 : List Bool) (hlen : l1.length = l2.length)
    (hle : ∀ i (h1 : i < l1.length) (h2 : i < l2.length), l1[i]'h1 = true → l2[i]'h2 = true) :
    op.eval l1 = true → op.eval l2 = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, id_eq]
    intro h1 b hb
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hb
    have hi1 : i < l1.length := by omega
    exact hle i hi1 hi (h1 _ (List.getElem_mem hi1))
  · simp only [GateOp.eval, List.any_eq_true, id_eq]
    intro ⟨a, ha, hae⟩
    obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp ha
    have hi2 : i < l2.length := by omega
    exact ⟨l2[i]'hi2, List.getElem_mem hi2, hle i hi hi2 (heq.trans hae)⟩

theorem wiresPrefix_mono (gs : List Gate) (hmono : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (x y : List Bool) (hlen : x.length = y.length)
    (hle : ∀ i, x.getD i false = true → y.getD i false = true) :
    ∀ i, (wiresPrefix gs x).getD i false = true → (wiresPrefix gs y).getD i false = true := by
  induction gs generalizing x y with
  | nil => exact hle
  | cons g gs ih =>
    rw [wiresPrefix_cons]
    have hg := hmono g List.mem_cons_self
    have hgs : ∀ g' ∈ gs, g'.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g'.inputs.length ≤ 2 :=
      fun g' hg' => hmono g' (List.mem_cons_of_mem _ hg')
    have hval : g.op.eval (g.inputs.map fun i => x.getD i false) = true →
        g.op.eval (g.inputs.map fun i => y.getD i false) = true := by
      apply gateOp_mono g.op (by simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hg.1)
      · simp
      · intro idx h1 h2
        simp only [List.getElem_map]
        exact hle _
    apply ih hgs
    · simp [hlen]
    · intro i hi
      by_cases hilt : i < x.length
      · have hilt2 : i < y.length := by omega
        simp only [List.getD_eq_getElem?_getD] at hi ⊢
        rw [List.getElem?_append_left hilt] at hi
        rw [List.getElem?_append_left hilt2]
        exact hle i (by simpa [List.getD_eq_getElem?_getD] using hi)
      · by_cases hieq : i = x.length
        · subst hieq
          simp only [List.getD_eq_getElem?_getD] at hi ⊢
          rw [List.getElem?_append_right (le_refl _), Nat.sub_self] at hi
          rw [hlen, List.getElem?_append_right (le_refl _), Nat.sub_self]
          exact hval (by simpa using hi)
        · simp only [List.getD_eq_getElem?_getD] at hi
          rw [List.getElem?_eq_none (by simp; omega)] at hi
          simp at hi

theorem circuit_mono (C : Circuit) (hm : Monotone2 C) (x y : List Bool) (hlen : x.length = y.length)
    (hle : ∀ i, x.getD i false = true → y.getD i false = true) :
    C.eval x = true → C.eval y = true :=
  wiresPrefix_mono C.gates hm x y hlen hle C.output

def validCh (N : ℕ) (C : Circuit) (w : ℕ) : Finset ℕ :=
  if h : N ≤ w ∧ w - N < C.gates.length then
    ((C.gates[w - N]'h.2).inputs.filter (fun i => i < w)).toFinset
  else ∅

theorem mem_validCh_lt (N : ℕ) (C : Circuit) (w i : ℕ) (hi : i ∈ validCh N C w) : i < w := by
  unfold validCh at hi
  split_ifs at hi with h
  · exact of_decide_eq_true (List.mem_filter.mp (List.mem_toFinset.mp hi)).2
  · simp at hi

theorem card_validCh_le (N : ℕ) (C : Circuit) (hm : Monotone2 C) (w : ℕ) :
    (validCh N C w).card ≤ 2 := by
  unfold validCh
  split_ifs with h
  · calc (((C.gates[w - N]'h.2).inputs.filter (fun i => i < w)).toFinset).card
        ≤ ((C.gates[w - N]'h.2).inputs.filter (fun i => i < w)).length := List.toFinset_card_le _
      _ ≤ (C.gates[w - N]'h.2).inputs.length := List.length_filter_le _ _
      _ ≤ 2 := (hm _ (List.getElem_mem h.2)).2
  · simp

def subTree (N : ℕ) (C : Circuit) : ℕ → Finset ℕ
  | w => insert w ((validCh N C w).attach.biUnion fun i => subTree N C i.val)
termination_by w => w
decreasing_by
  exact mem_validCh_lt N C w i.val i.property

theorem self_mem_subTree (N : ℕ) (C : Circuit) (w : ℕ) : w ∈ subTree N C w := by
  rw [subTree]
  exact Finset.mem_insert_self _ _

theorem subTree_le (N : ℕ) (C : Circuit) : ∀ w v, v ∈ subTree N C w → v ≤ w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro v hv
    rw [subTree] at hv
    rcases Finset.mem_insert.mp hv with rfl | hmem
    · exact le_refl _
    · rw [Finset.mem_biUnion] at hmem
      obtain ⟨⟨i, hi⟩, _, hvi⟩ := hmem
      have hlt := mem_validCh_lt N C w i hi
      exact (ih i hlt v hvi).trans hlt.le

theorem subTree_child_subset (N : ℕ) (C : Circuit) (w i : ℕ) (hi : i ∈ validCh N C w) :
    subTree N C i ⊆ subTree N C w := by
  intro v hv
  rw [subTree]
  apply Finset.mem_insert_of_mem
  rw [Finset.mem_biUnion]
  exact ⟨⟨i, hi⟩, Finset.mem_attach _ _, hv⟩

theorem child_mem_subTree (N : ℕ) (C : Circuit) (w i : ℕ) (hi : i ∈ validCh N C w) :
    i ∈ subTree N C w :=
  subTree_child_subset N C w i hi (self_mem_subTree N C i)

theorem subTree_mem_parent (N : ℕ) (C : Circuit) :
    ∀ w v, v ∈ subTree N C w → v ≠ w → ∃ p ∈ subTree N C w, v ∈ validCh N C p := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro v hv hne
    rw [subTree] at hv
    rcases Finset.mem_insert.mp hv with rfl | hmem
    · exact absurd rfl hne
    · rw [Finset.mem_biUnion] at hmem
      obtain ⟨⟨i, hi⟩, _, hvi⟩ := hmem
      by_cases hvi_eq : v = i
      · subst hvi_eq
        exact ⟨w, self_mem_subTree N C w, hi⟩
      · have hlt := mem_validCh_lt N C w i hi
        obtain ⟨p, hp, hvp⟩ := ih i hlt v hvi hvi_eq
        exact ⟨p, subTree_child_subset N C w i hi hp, hvp⟩

theorem wiresPrefix_congr_subTree (N : ℕ) (C : Circuit) (x y : List Bool)
    (hx : x.length = N) (hy : y.length = N) :
    ∀ w, w < N + C.gates.length →
      (∀ i, i < N → i ∈ subTree N C w → x.getD i false = y.getD i false) →
      (C.wires x).getD w false = (C.wires y).getD w false := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hagree
    change (wiresPrefix C.gates x).getD w false = (wiresPrefix C.gates y).getD w false
    by_cases hlt : w < N
    · rw [wiresPrefix_getD_lt _ _ _ (by omega), wiresPrefix_getD_lt _ _ _ (by omega)]
      exact hagree w hlt (self_mem_subTree N C w)
    · have hk : w - N < C.gates.length := by omega
      have hweq : x.length + (w - N) = w := by omega
      have hweq2 : y.length + (w - N) = w := by omega
      conv_lhs => rw [← hweq]
      rw [wiresPrefix_getD_gate C.gates x (w - N) hk]
      conv_rhs => rw [← hweq2]
      rw [wiresPrefix_getD_gate C.gates y (w - N) hk]
      congr 1
      apply List.map_congr_left
      intro j hj
      by_cases hjlt : j < w
      · have hlenx : (wiresPrefix (C.gates.take (w - N)) x).length = w := by
          rw [wiresPrefix_length, List.length_take]
          omega
        have hleny : (wiresPrefix (C.gates.take (w - N)) y).length = w := by
          rw [wiresPrefix_length, List.length_take]
          omega
        have hsp : C.gates = C.gates.take (w - N) ++ C.gates.drop (w - N) := (List.take_append_drop _ _).symm
        have hgx : (C.wires x).getD j false = (wiresPrefix (C.gates.take (w - N)) x).getD j false := by
          change (wiresPrefix C.gates x).getD j false = _
          conv_lhs => rw [hsp, wiresPrefix_append]
          exact wiresPrefix_getD_lt _ _ _ (by omega)
        have hgy : (C.wires y).getD j false = (wiresPrefix (C.gates.take (w - N)) y).getD j false := by
          change (wiresPrefix C.gates y).getD j false = _
          conv_lhs => rw [hsp, wiresPrefix_append]
          exact wiresPrefix_getD_lt _ _ _ (by omega)
        rw [← hgx, ← hgy]
        have hjch : j ∈ validCh N C w := by
          unfold validCh
          rw [dif_pos ⟨by omega, hk⟩]
          exact List.mem_toFinset.mpr (List.mem_filter.mpr ⟨hj, decide_eq_true hjlt⟩)
        exact ih j hjlt (by omega) (fun i hi him => hagree i hi (subTree_child_subset N C w j hjch him))
      · have hlenx : (wiresPrefix (C.gates.take (w - N)) x).length = w := by
          rw [wiresPrefix_length, List.length_take]
          omega
        have hleny : (wiresPrefix (C.gates.take (w - N)) y).length = w := by
          rw [wiresPrefix_length, List.length_take]
          omega
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

theorem oneEach_length {n : ℕ} (u v : Fin n) : (oneEach u v).length = 2 * n := by
  simp [oneEach]
  omega

theorem oneEach_getD {n : ℕ} (u v : Fin n) (i : ℕ) :
    (oneEach u v).getD i false =
      if i < n then decide (i = u.val)
      else if i < 2 * n then decide (i - n = v.val)
      else false := by
  unfold oneEach
  simp only [List.getD_eq_getElem?_getD]
  by_cases h1 : i < n
  · rw [List.getElem?_append_left (by simp; omega)]
    rw [List.getElem?_ofFn]
    simp [h1, Fin.ext_iff]
  · by_cases h2 : i < 2 * n
    · rw [List.getElem?_append_right (by simp; omega)]
      simp only [List.length_ofFn]
      rw [List.getElem?_ofFn]
      have hsub : i - n < n := by omega
      simp [h1, h2, hsub, Fin.ext_iff]
    · rw [List.getElem?_eq_none (by simp; omega)]
      simp [h1, h2]

theorem matA_eval_zero_row (n : ℕ) (hn : 3 ≤ n) (v : Fin n) :
    matA n ⟨0, by omega⟩ v = decide (v.val ≠ 0) := by
  unfold matA
  simp

theorem matA_eval_one_row (n : ℕ) (hn : 3 ≤ n) (v : Fin n) :
    matA n ⟨1, by omega⟩ v = decide (v.val ≤ 1) := by
  unfold matA
  simp

theorem matA_eval_ge2_row (n : ℕ) (u : Fin n) (hu : 2 ≤ u.val) (v : Fin n) :
    matA n u v = decide (v.val = 0) := by
  unfold matA
  have h0 : u.val ≠ 0 := by omega
  have h1 : u.val ≠ 1 := by omega
  simp [h0, h1, hu]

theorem row_witness (n : ℕ) (hn : 3 ≤ n) (u : Fin n) :
    ∃ v : Fin n, ∃ u' : Fin n, matA n u v = true ∧ matA n u' v = false := by
  by_cases h0 : u.val = 0
  · refine ⟨⟨1, by omega⟩, ⟨2, by omega⟩, ?_, ?_⟩
    · unfold matA; simp [h0]
    · unfold matA; simp
  · by_cases h1 : u.val = 1
    · refine ⟨⟨0, by omega⟩, ⟨0, by omega⟩, ?_, ?_⟩
      · unfold matA; simp [h1]
      · unfold matA; simp
    · refine ⟨⟨0, by omega⟩, ⟨0, by omega⟩, ?_, ?_⟩
      · have hu2 : 2 ≤ u.val := by omega
        exact decide_eq_true (Or.inr (Or.inr ⟨hu2, rfl⟩))
      · unfold matA; simp

theorem col_witness (n : ℕ) (hn : 3 ≤ n) (v : Fin n) :
    ∃ u : Fin n, ∃ v' : Fin n, matA n u v = true ∧ matA n u v' = false := by
  by_cases h0 : v.val = 0
  · refine ⟨⟨1, by omega⟩, ⟨2, by omega⟩, ?_, ?_⟩
    · unfold matA; simp [h0]
    · unfold matA; simp
  · refine ⟨⟨0, by omega⟩, ⟨0, by omega⟩, ?_, ?_⟩
    · unfold matA; simp [h0]
    · unfold matA; simp

theorem no_full_row (n : ℕ) (hn : 3 ≤ n) (u : Fin n) : ∃ v : Fin n, matA n u v = false := by
  by_cases h0 : u.val = 0
  · exact ⟨⟨0, by omega⟩, by unfold matA; simp [h0]⟩
  · by_cases h1 : u.val = 1
    · exact ⟨⟨2, by omega⟩, by unfold matA; simp [h1]⟩
    · exact ⟨⟨1, by omega⟩, by unfold matA; apply decide_eq_false; intro h; rcases h with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩; exact h0 h; exact h1 h; exact Nat.one_ne_zero h⟩

theorem no_full_col (n : ℕ) (hn : 3 ≤ n) (v : Fin n) : ∃ u : Fin n, matA n u v = false := by
  by_cases h0 : v.val = 0
  · exact ⟨⟨0, by omega⟩, by unfold matA; simp [h0]⟩
  · exact ⟨⟨2, by omega⟩, by unfold matA; simp [h0]⟩

theorem output_is_gate (n : ℕ) (hn : 3 ≤ n) (C : Circuit) (hrep : Represents (matA n) C) :
    2 * n ≤ C.output ∧ C.output < 2 * n + C.gates.length := by
  constructor
  · by_contra hlt
    push_neg at hlt
    by_cases hr : C.output < n
    · obtain ⟨v, hv⟩ := no_full_row n hn ⟨C.output, hr⟩
      have hev := hrep ⟨C.output, hr⟩ v
      unfold Circuit.eval at hev
      change (wiresPrefix C.gates (oneEach ⟨C.output, hr⟩ v)).getD C.output false = matA n ⟨C.output, hr⟩ v at hev
      rw [wiresPrefix_getD_lt _ _ _ (by rw [oneEach_length]; omega), oneEach_getD] at hev
      simp [hr] at hev
      rw [hv] at hev
      contradiction
    · have hc : C.output - n < n := by omega
      obtain ⟨u, hu⟩ := no_full_col n hn ⟨C.output - n, hc⟩
      have hev := hrep u ⟨C.output - n, hc⟩
      unfold Circuit.eval at hev
      change (wiresPrefix C.gates (oneEach u ⟨C.output - n, hc⟩)).getD C.output false = matA n u ⟨C.output - n, hc⟩ at hev
      rw [wiresPrefix_getD_lt _ _ _ (by rw [oneEach_length]; omega), oneEach_getD] at hev
      simp [hr, hlt] at hev
      rw [hu] at hev
      contradiction
  · by_contra hge
    have hge' : 2 * n + C.gates.length ≤ C.output := Nat.le_of_not_lt hge
    let u1 : Fin n := ⟨1, by omega⟩
    let v0 : Fin n := ⟨0, by omega⟩
    have hev := hrep u1 v0
    unfold Circuit.eval at hev
    change (wiresPrefix C.gates (oneEach u1 v0)).getD C.output false = _ at hev
    have hlen : (wiresPrefix C.gates (oneEach u1 v0)).length = 2 * n + C.gates.length := by
      rw [wiresPrefix_length, oneEach_length]
    simp only [List.getD_eq_getElem?_getD] at hev
    rw [List.getElem?_eq_none (by omega)] at hev
    have htrue : matA n u1 v0 = true := by unfold matA; simp [u1, v0]
    rw [htrue] at hev
    simp at hev

theorem all_inputs_in_subTree (n : ℕ) (hn : 3 ≤ n) (C : Circuit) (hm : Monotone2 C)
    (hrep : Represents (matA n) C) (i : ℕ) (hi : i < 2 * n) :
    i ∈ subTree (2 * n) C C.output := by
  have hout := output_is_gate n hn C hrep
  by_contra hnot
  by_cases hir : i < n
  · obtain ⟨v, u', h1, h2⟩ := row_witness n hn ⟨i, hir⟩
    let x0 : List Bool := List.replicate n false ++ List.ofFn (fun j : Fin n => decide (j = v))
    have hx0len : x0.length = 2 * n := by simp [x0]; omega
    have hx0get : ∀ k, x0.getD k false = if k < n then false else if k < 2 * n then decide (k - n = v.val) else false := by
      intro k
      simp only [x0, List.getD_eq_getElem?_getD]
      by_cases hk1 : k < n
      · rw [List.getElem?_append_left (by simp; omega), List.getElem?_replicate]
        simp [hk1]
      · by_cases hk2 : k < 2 * n
        · rw [List.getElem?_append_right (by simp; omega)]
          simp only [List.length_replicate, List.getElem?_ofFn]
          have hsub : k - n < n := by omega
          simp [hk1, hk2, hsub, Fin.ext_iff]
        · rw [List.getElem?_eq_none (by simp; omega)]
          simp [hk1, hk2]
    have hcong : C.eval (oneEach ⟨i, hir⟩ v) = C.eval x0 := by
      unfold Circuit.eval
      exact wiresPrefix_congr_subTree (2 * n) C _ _ (oneEach_length _ _) hx0len C.output hout.2
        (fun k hk hmem => by
          rw [oneEach_getD, hx0get]
          by_cases hkn : k < n
          · have hne : k ≠ i := fun h => hnot (h ▸ hmem)
            simp [hkn, hne]
          · simp [hkn, hk])
    have hle : ∀ k, x0.getD k false = true → (oneEach u' v).getD k false = true := by
      intro k hk
      rw [hx0get] at hk
      rw [oneEach_getD]
      split_ifs at hk with h1' h2'
      simp [h1', h2', hk]
    have ht : C.eval x0 = true := by rw [← hcong, hrep, h1]
    have hf : C.eval (oneEach u' v) = true :=
      circuit_mono C hm x0 (oneEach u' v) (by rw [hx0len, oneEach_length]) hle ht
    rw [hrep, h2] at hf
    contradiction
  · have hic : i - n < n := by omega
    obtain ⟨u, v', h1, h2⟩ := col_witness n hn ⟨i - n, hic⟩
    let x0 : List Bool := List.ofFn (fun j : Fin n => decide (j = u)) ++ List.replicate n false
    have hx0len : x0.length = 2 * n := by simp [x0]; omega
    have hx0get : ∀ k, x0.getD k false = if k < n then decide (k = u.val) else false := by
      intro k
      simp only [x0, List.getD_eq_getElem?_getD]
      by_cases hk1 : k < n
      · rw [List.getElem?_append_left (by simp; omega), List.getElem?_ofFn]
        simp [hk1, Fin.ext_iff]
      · by_cases hk2 : k < 2 * n
        · rw [List.getElem?_append_right (by simp; omega)]
          simp only [List.length_ofFn, List.getElem?_replicate]
          have hsub : k - n < n := by omega
          simp [hk1, hsub]
        · rw [List.getElem?_eq_none (by simp; omega)]
          simp [hk1]
    have hcong : C.eval (oneEach u ⟨i - n, hic⟩) = C.eval x0 := by
      unfold Circuit.eval
      exact wiresPrefix_congr_subTree (2 * n) C _ _ (oneEach_length _ _) hx0len C.output hout.2
        (fun k hk hmem => by
          rw [oneEach_getD, hx0get]
          by_cases hkn : k < n
          · simp [hkn]
          · have hne : k - n ≠ i - n := fun h => hnot (by
              have : k = i := by omega
              exact this ▸ hmem)
            simp [hkn, hk, hne])
    have hle : ∀ k, x0.getD k false = true → (oneEach u v').getD k false = true := by
      intro k hk
      rw [hx0get] at hk
      rw [oneEach_getD]
      split_ifs at hk with h1'
      simp [h1', hk]
    have ht : C.eval x0 = true := by rw [← hcong, hrep, h1]
    have hf : C.eval (oneEach u v') = true :=
      circuit_mono C hm x0 (oneEach u v') (by rw [hx0len, oneEach_length]) hle ht
    rw [hrep, h2] at hf
    contradiction

theorem tree_structure (n : ℕ) (hn : 3 ≤ n) (C : Circuit) (hm : Monotone2 C)
    (hsize : C.size ≤ 2 * n - 1) (hrep : Represents (matA n) C) :
    let R := subTree (2 * n) C C.output
    (∀ w ∈ R, 2 * n ≤ w → (validCh (2 * n) C w).card = 2) ∧
    (∀ v ∈ R, ∀ p1 ∈ R, ∀ p2 ∈ R, v ∈ validCh (2 * n) C p1 → v ∈ validCh (2 * n) C p2 → p1 = p2) := by
  intro R
  have hout := output_is_gate n hn C hrep
  let G : Finset ℕ := R.filter (fun w => 2 * n ≤ w)
  let I : Finset ℕ := Finset.range (2 * n)
  have hI_sub : I ⊆ R := fun i hi => all_inputs_in_subTree n hn C hm hrep i (Finset.mem_range.mp hi)
  have hR_eq : R = I ∪ G := by
    ext w
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_range, I, G]
    constructor
    · intro hw
      by_cases hlt : w < 2 * n
      · exact Or.inl hlt
      · exact Or.inr ⟨hw, by omega⟩
    · rintro (hlt | ⟨hw, _⟩)
      · exact all_inputs_in_subTree n hn C hm hrep w hlt
      · exact hw
  have hdisj : Disjoint I G := by
    rw [Finset.disjoint_left]
    intro w h1 h2
    have := Finset.mem_range.mp h1
    have := (Finset.mem_filter.mp h2).2
    omega
  have hR_card : R.card = 2 * n + G.card := by
    rw [hR_eq, Finset.card_union_of_disjoint hdisj, Finset.card_range]
  have hG_sub : G ⊆ Finset.Ico (2 * n) (2 * n + C.gates.length) := by
    intro w hw
    have hwR := (Finset.mem_filter.mp hw).1
    have hwge := (Finset.mem_filter.mp hw).2
    have hwle := subTree_le (2 * n) C C.output w hwR
    exact Finset.mem_Ico.mpr ⟨hwge, by omega⟩
  have hG_le : G.card ≤ 2 * n - 1 := by
    calc G.card ≤ (Finset.Ico (2 * n) (2 * n + C.gates.length)).card := Finset.card_le_card hG_sub
      _ = C.gates.length := by simp
      _ = C.size := rfl
      _ ≤ 2 * n - 1 := hsize
  let edges : Finset (ℕ × ℕ) := G.biUnion (fun p => (validCh (2 * n) C p).map ⟨fun v => (p, v), fun _ _ h => (Prod.mk.inj h).2⟩)
  have hedges_card : edges.card = ∑ p ∈ G, (validCh (2 * n) C p).card := by
    rw [Finset.card_biUnion]
    · apply Finset.sum_congr rfl
      intro p _
      exact Finset.card_map _
    · intro p1 _ p2 _ hne
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro e he1 he2
      simp only [Finset.mem_map, Function.Embedding.coeFn_mk] at he1 he2
      obtain ⟨_, _, rfl⟩ := he1
      obtain ⟨_, _, heq⟩ := he2
      exact hne (Prod.mk.inj heq).1.symm
  have hedges_le : edges.card ≤ 2 * G.card := by
    rw [hedges_card]
    calc ∑ p ∈ G, (validCh (2 * n) C p).card
        ≤ ∑ _p ∈ G, 2 := Finset.sum_le_sum (fun p _ => card_validCh_le (2 * n) C hm p)
      _ = 2 * G.card := by simp [Nat.mul_comm]
  let pars : ℕ → Finset ℕ := fun v => G.filter (fun p => v ∈ validCh (2 * n) C p)
  have hpars_sum : ∑ v ∈ R.erase C.output, (pars v).card ≤ edges.card := by
    have hdisj_p : (R.erase C.output : Set ℕ).PairwiseDisjoint (fun v => (pars v).map ⟨fun p => (p, v), fun _ _ h => (Prod.mk.inj h).1⟩) := by
      intro v1 _ v2 _ hne
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro e he1 he2
      simp only [Finset.mem_map, Function.Embedding.coeFn_mk] at he1 he2
      obtain ⟨_, _, rfl⟩ := he1
      obtain ⟨_, _, heq⟩ := he2
      exact hne (Prod.mk.inj heq).2.symm
    have hsub_e : (R.erase C.output).biUnion (fun v => (pars v).map ⟨fun p => (p, v), fun _ _ h => (Prod.mk.inj h).1⟩) ⊆ edges := by
      intro e he
      rw [Finset.mem_biUnion] at he
      obtain ⟨v, _, hev⟩ := he
      simp only [Finset.mem_map, Function.Embedding.coeFn_mk, Finset.mem_filter, pars] at hev
      obtain ⟨p, ⟨hpG, hvp⟩, rfl⟩ := hev
      rw [Finset.mem_biUnion]
      exact ⟨p, hpG, Finset.mem_map.mpr ⟨v, hvp, rfl⟩⟩
    calc ∑ v ∈ R.erase C.output, (pars v).card
        = ∑ v ∈ R.erase C.output, ((pars v).map ⟨fun p => (p, v), fun _ _ h => (Prod.mk.inj h).1⟩).card := by
          apply Finset.sum_congr rfl; intro v _; exact (Finset.card_map _).symm
      _ = ((R.erase C.output).biUnion (fun v => (pars v).map ⟨fun p => (p, v), fun _ _ h => (Prod.mk.inj h).1⟩)).card :=
          (Finset.card_biUnion hdisj_p).symm
      _ ≤ edges.card := Finset.card_le_card hsub_e
  have hpars_pos : ∀ v ∈ R.erase C.output, 1 ≤ (pars v).card := by
    intro v hv
    have hne := (Finset.mem_erase.mp hv).1
    have hvR := (Finset.mem_erase.mp hv).2
    obtain ⟨p, hpR, hvp⟩ := subTree_mem_parent (2 * n) C C.output v hvR hne
    have hpge : 2 * n ≤ p := by
      unfold validCh at hvp
      split_ifs at hvp with h
      · exact h.1
      · simp at hvp
    exact Finset.card_pos.mpr ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hpR, hpge⟩, hvp⟩⟩
  have hR_erase_card : (R.erase C.output).card = 2 * n + G.card - 1 := by
    rw [Finset.card_erase_of_mem (self_mem_subTree (2 * n) C C.output), hR_card]
  have hsum_ge : 2 * n + G.card - 1 ≤ ∑ v ∈ R.erase C.output, (pars v).card := by
    calc 2 * n + G.card - 1
        = (R.erase C.output).card := hR_erase_card.symm
      _ = ∑ _v ∈ R.erase C.output, 1 := by simp
      _ ≤ ∑ v ∈ R.erase C.output, (pars v).card := Finset.sum_le_sum hpars_pos
  have hG_eq : G.card = 2 * n - 1 := by omega
  have hedges_eq : edges.card = 2 * G.card := by omega
  have hsum_eq : ∑ v ∈ R.erase C.output, (pars v).card = (R.erase C.output).card := by omega
  constructor
  · intro w hwR hwge
    have hwG : w ∈ G := Finset.mem_filter.mpr ⟨hwR, hwge⟩
    by_contra hne2
    have hlt2 : (validCh (2 * n) C w).card < 2 := Nat.lt_of_le_of_ne (card_validCh_le (2 * n) C hm w) hne2
    have hlt_sum : ∑ p ∈ G, (validCh (2 * n) C p).card < ∑ _p ∈ G, 2 :=
      Finset.sum_lt_sum (fun p _ => card_validCh_le (2 * n) C hm p) ⟨w, hwG, hlt2⟩
    have hconst : ∑ _p ∈ G, 2 = 2 * G.card := by simp [Nat.mul_comm]
    omega
  · intro v hvR p1 hp1R p2 hp2R hv1 hv2
    have hlt1 := mem_validCh_lt (2 * n) C p1 v hv1
    have hle1 := subTree_le (2 * n) C C.output p1 hp1R
    have hvne : v ≠ C.output := by omega
    have hvE : v ∈ R.erase C.output := Finset.mem_erase.mpr ⟨hvne, hvR⟩
    have hp1ge : 2 * n ≤ p1 := by
      unfold validCh at hv1; split_ifs at hv1 with h; exact h.1; simp at hv1
    have hp2ge : 2 * n ≤ p2 := by
      unfold validCh at hv2; split_ifs at hv2 with h; exact h.1; simp at hv2
    have hp1 : p1 ∈ pars v := Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hp1R, hp1ge⟩, hv1⟩
    have hp2 : p2 ∈ pars v := Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hp2R, hp2ge⟩, hv2⟩
    have hcard1 : (pars v).card = 1 := by
      by_contra hne1
      have hgt1 : 1 < (pars v).card := Nat.lt_of_le_of_ne (hpars_pos v hvE) (Ne.symm hne1)
      have hgt_sum : ∑ _u ∈ R.erase C.output, 1 < ∑ u ∈ R.erase C.output, (pars u).card :=
        Finset.sum_lt_sum hpars_pos ⟨v, hvE, hgt1⟩
      have hconst : ∑ _u ∈ R.erase C.output, 1 = (R.erase C.output).card := by simp
      omega
    obtain ⟨q, hq⟩ := Finset.card_eq_one.mp hcard1
    rw [hq] at hp1 hp2
    exact (Finset.mem_singleton.mp hp1).trans (Finset.mem_singleton.mp hp2).symm

theorem subTree_subset_of_mem (N : ℕ) (C : Circuit) :
    ∀ r w, w ∈ subTree N C r → subTree N C w ⊆ subTree N C r := by
  intro r
  induction r using Nat.strong_induction_on with
  | ind r ih =>
    intro w hw z hz
    rw [subTree] at hw
    rcases Finset.mem_insert.mp hw with rfl | hmem
    · exact hz
    · rw [Finset.mem_biUnion] at hmem
      obtain ⟨⟨c, hc⟩, _, hwc⟩ := hmem
      have hlt := mem_validCh_lt N C r c hc
      exact subTree_child_subset N C r c hc (ih c hlt w hwc hz)

theorem disjoint_subTrees (N : ℕ) (C : Circuit) (root : ℕ)
    (huniq : ∀ v ∈ subTree N C root, ∀ p1 ∈ subTree N C root, ∀ p2 ∈ subTree N C root,
      v ∈ validCh N C p1 → v ∈ validCh N C p2 → p1 = p2)
    (w a b : ℕ) (hw : w ∈ subTree N C root) (ha : a ∈ validCh N C w) (hb : b ∈ validCh N C w) (hab : a ≠ b) :
    Disjoint (subTree N C a) (subTree N C b) := by
  rw [Finset.disjoint_left]
  intro x hxa hxb
  have hne : (subTree N C a ∩ subTree N C b).Nonempty := ⟨x, Finset.mem_inter.mpr ⟨hxa, hxb⟩⟩
  set m := (subTree N C a ∩ subTree N C b).max' hne with hm_def
  have hm : m ∈ subTree N C a ∩ subTree N C b := Finset.max'_mem _ hne
  have hma : m ∈ subTree N C a := (Finset.mem_inter.mp hm).1
  have hmb : m ∈ subTree N C b := (Finset.mem_inter.mp hm).2
  have hwsub : subTree N C w ⊆ subTree N C root := subTree_subset_of_mem N C root w hw
  have hmR : m ∈ subTree N C root := hwsub (subTree_child_subset N C w a ha hma)
  by_cases hmeqa : m = a
  · have hne_b : m ≠ b := by rw [hmeqa]; exact hab
    obtain ⟨pb, hpb_sub, hmpb⟩ := subTree_mem_parent N C b m hmb hne_b
    have hpbR : pb ∈ subTree N C root := hwsub (subTree_child_subset N C w b hb hpb_sub)
    have hpb_lt : pb < w := (subTree_le N C b pb hpb_sub).trans_lt (mem_validCh_lt N C w b hb)
    have hma_ch : m ∈ validCh N C w := hmeqa ▸ ha
    have heq := huniq m hmR w hw pb hpbR hma_ch hmpb
    omega
  · by_cases hmeqb : m = b
    · obtain ⟨pa, hpa_sub, hmpa⟩ := subTree_mem_parent N C a m hma hmeqa
      have hpaR : pa ∈ subTree N C root := hwsub (subTree_child_subset N C w a ha hpa_sub)
      have hpa_lt : pa < w := (subTree_le N C a pa hpa_sub).trans_lt (mem_validCh_lt N C w a ha)
      have hmb_ch : m ∈ validCh N C w := hmeqb ▸ hb
      have heq := huniq m hmR w hw pa hpaR hmb_ch hmpa
      omega
    · obtain ⟨pa, hpa_sub, hmpa⟩ := subTree_mem_parent N C a m hma hmeqa
      obtain ⟨pb, hpb_sub, hmpb⟩ := subTree_mem_parent N C b m hmb hmeqb
      have hpaR : pa ∈ subTree N C root := hwsub (subTree_child_subset N C w a ha hpa_sub)
      have hpbR : pb ∈ subTree N C root := hwsub (subTree_child_subset N C w b hb hpb_sub)
      have heq := huniq m hmR pa hpaR pb hpbR hmpa hmpb
      have hpa_b : pa ∈ subTree N C b := heq ▸ hpb_sub
      have hlt_m : m < pa := mem_validCh_lt N C pa m hmpa
      have hle_m : pa ≤ m := Finset.le_max' (subTree N C a ∩ subTree N C b) pa (Finset.mem_inter.mpr ⟨hpa_sub, hpa_b⟩)
      omega

def inp4 (n : ℕ) (b0 b1 b2 b3 : Bool) : List Bool :=
  List.ofFn (fun i : Fin (2 * n) =>
    if i.val = 1 then b0
    else if i.val = 2 then b1
    else if i.val = n then b2
    else if i.val = n + 1 then b3
    else false)

theorem inp4_length (n : ℕ) (b0 b1 b2 b3 : Bool) : (inp4 n b0 b1 b2 b3).length = 2 * n := by
  simp [inp4]

theorem inp4_getD (n : ℕ) (b0 b1 b2 b3 : Bool) (i : ℕ) :
    (inp4 n b0 b1 b2 b3).getD i false =
      if i < 2 * n then
        (if i = 1 then b0 else if i = 2 then b1 else if i = n then b2 else if i = n + 1 then b3 else false)
      else false := by
  unfold inp4
  simp only [List.getD_eq_getElem?_getD]
  by_cases hi : i < 2 * n
  · rw [List.getElem?_ofFn]
    simp [hi]
  · rw [List.getElem?_eq_none (by simp; omega)]
    simp [hi]

def isAndOp : GateOp → Bool
  | GateOp.and => true
  | _ => false

theorem inp4_eval_step (n : ℕ) (hn : 3 ≤ n) (C : Circuit) (hm : Monotone2 C)
    (w : ℕ) (hwge : 2 * n ≤ w) (hwlt : w < 2 * n + C.gates.length)
    (a b : ℕ) (hab : a ≠ b) (hch : validCh (2 * n) C w = {a, b}) (x : List Bool) (hx : x.length = 2 * n) :
    (C.wires x).getD w false =
      if isAndOp (C.gates[w - 2 * n]'(by omega)).op then
        (C.wires x).getD a false && (C.wires x).getD b false
      else
        (C.wires x).getD a false || (C.wires x).getD b false := by
  have hk : w - 2 * n < C.gates.length := by omega
  let g := C.gates[w - 2 * n]'hk
  have hgin : g.inputs.length ≤ 2 := (hm g (List.getElem_mem hk)).2
  have hgop := (hm g (List.getElem_mem hk)).1
  have hmem_a : a ∈ validCh (2 * n) C w := by rw [hch]; simp
  have hmem_b : b ∈ validCh (2 * n) C w := by rw [hch]; simp
  unfold validCh at hmem_a hmem_b
  simp only [hwge, hk, and_self, ↓reduceDIte] at hmem_a hmem_b
  have ha_in : a ∈ g.inputs ∧ a < w := by
    have := List.mem_filter.mp (List.mem_toFinset.mp hmem_a)
    exact ⟨this.1, of_decide_eq_true this.2⟩
  have hb_in : b ∈ g.inputs ∧ b < w := by
    have := List.mem_filter.mp (List.mem_toFinset.mp hmem_b)
    exact ⟨this.1, of_decide_eq_true this.2⟩
  have hpair : g.inputs = [a, b] ∨ g.inputs = [b, a] := by
    match heq : g.inputs with
    | [] => simp [heq] at ha_in
    | [c] =>
      simp [heq] at ha_in hb_in
      exact absurd (ha_in.1.trans hb_in.1.symm) hab
    | [c, d] =>
      simp [heq] at ha_in hb_in
      rcases ha_in.1 with rfl | rfl <;> rcases hb_in.1 with rfl | rfl
      · exact absurd rfl hab
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact absurd rfl hab
    | _ :: _ :: _ :: _ =>
      rw [heq] at hgin
      simp at hgin
  have hstep : (C.wires x).getD w false = g.op.eval (g.inputs.map fun j => (wiresPrefix (C.gates.take (w - 2 * n)) x).getD j false) := by
    change (wiresPrefix C.gates x).getD w false = _
    have hweq : x.length + (w - 2 * n) = w := by omega
    conv_lhs => rw [← hweq]
    exact wiresPrefix_getD_gate C.gates x (w - 2 * n) hk
  have htake_eq : ∀ j, j < w → (wiresPrefix (C.gates.take (w - 2 * n)) x).getD j false = (C.wires x).getD j false := by
    intro j hj
    have hlen : (wiresPrefix (C.gates.take (w - 2 * n)) x).length = w := by
      rw [wiresPrefix_length, List.length_take]
      omega
    change _ = (wiresPrefix C.gates x).getD j false
    conv_rhs => rw [← List.take_append_drop (w - 2 * n) C.gates, wiresPrefix_append]
    exact (wiresPrefix_getD_lt _ _ _ (by omega)).symm
  rw [hstep]
  have hae := htake_eq a ha_in.2
  have hbe := htake_eq b hb_in.2
  rcases hgop with hop | hop
  · rw [hop]
    simp only [isAndOp, ite_true]
    rcases hpair with hp | hp <;> rw [hp] <;> simp only [List.map_cons, List.map_nil, hae, hbe, GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true, Bool.true_and, Bool.and_comm]
  · simp only [Set.mem_singleton_iff] at hop
    rw [hop]
    simp only [isAndOp, Bool.false_eq_true, ite_false]
    rcases hpair with hp | hp <;> rw [hp] <;> simp only [List.map_cons, List.map_nil, hae, hbe, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false, Bool.false_or, Bool.or_comm]

theorem no_p4_on_tree (n : ℕ) (hn : 3 ≤ n) (C : Circuit) (hm : Monotone2 C) (root : ℕ)
    (hroot_lt : root < 2 * n + C.gates.length)
    (hcard2 : ∀ w ∈ subTree (2 * n) C root, 2 * n ≤ w → (validCh (2 * n) C w).card = 2)
    (huniq : ∀ v ∈ subTree (2 * n) C root, ∀ p1 ∈ subTree (2 * n) C root, ∀ p2 ∈ subTree (2 * n) C root,
      v ∈ validCh (2 * n) C p1 → v ∈ validCh (2 * n) C p2 → p1 = p2) :
    ∀ w, w ∈ subTree (2 * n) C root →
      let f := fun b0 b1 b2 b3 => (C.wires (inp4 n b0 b1 b2 b3)).getD w false
      ¬ (f true false true false = true ∧
         f true false false true = true ∧
         f false true true false = true ∧
         f false true false true = false ∧
         f true false false false = false ∧
         f false false true false = false) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    dsimp only
    rintro ⟨h10, h11, h20, h21, h1x, hx0⟩
    have hwlt : w < 2 * n + C.gates.length := (subTree_le (2 * n) C root w hw).trans_lt hroot_lt
    by_cases hleaf : w < 2 * n
    · have eval_leaf : ∀ b0 b1 b2 b3, (C.wires (inp4 n b0 b1 b2 b3)).getD w false =
          (if w = 1 then b0 else if w = 2 then b1 else if w = n then b2 else if w = n + 1 then b3 else false) := by
        intro b0 b1 b2 b3
        change (wiresPrefix C.gates (inp4 n b0 b1 b2 b3)).getD w false = _
        rw [wiresPrefix_getD_lt _ _ _ (by rw [inp4_length]; exact hleaf), inp4_getD]
        simp [hleaf]
      rw [eval_leaf] at h10 h11 h20 h21 h1x hx0
      split_ifs at h10 h11 h20 h21 h1x hx0 <;> simp_all
    · have hwge : 2 * n ≤ w := by omega
      have hc2 := hcard2 w hw hwge
      obtain ⟨a, b, hab, hch⟩ := Finset.card_eq_two.mp hc2
      have ha_ch : a ∈ validCh (2 * n) C w := by rw [hch]; simp
      have hb_ch : b ∈ validCh (2 * n) C w := by rw [hch]; simp
      have ha_lt : a < w := mem_validCh_lt (2 * n) C w a ha_ch
      have hb_lt : b < w := mem_validCh_lt (2 * n) C w b hb_ch
      have hwsub : subTree (2 * n) C w ⊆ subTree (2 * n) C root := subTree_subset_of_mem (2 * n) C root w hw
      have haR : a ∈ subTree (2 * n) C root := hwsub (child_mem_subTree (2 * n) C w a ha_ch)
      have hbR : b ∈ subTree (2 * n) C root := hwsub (child_mem_subTree (2 * n) C w b hb_ch)
      have hdisj := disjoint_subTrees (2 * n) C root huniq w a b hw ha_ch hb_ch hab
      let fa := fun b0 b1 b2 b3 => (C.wires (inp4 n b0 b1 b2 b3)).getD a false
      let fb := fun b0 b1 b2 b3 => (C.wires (inp4 n b0 b1 b2 b3)).getD b false
      have hmono_w : ∀ u, ∀ a0 a1 a2 a3 c0 c1 c2 c3,
          (a0 = true → c0 = true) → (a1 = true → c1 = true) → (a2 = true → c2 = true) → (a3 = true → c3 = true) →
          (C.wires (inp4 n a0 a1 a2 a3)).getD u false = true →
          (C.wires (inp4 n c0 c1 c2 c3)).getD u false = true := by
        intro u a0 a1 a2 a3 c0 c1 c2 c3 h0 h1 h2 h3
        apply wiresPrefix_mono C.gates hm _ _ (by rw [inp4_length, inp4_length])
        intro i hi
        rw [inp4_getD] at hi ⊢
        split_ifs at hi ⊢ with hlt i1 i2 in0 in1
        · exact h0 hi
        · exact h1 hi
        · exact h2 hi
        · exact h3 hi
      have hign : ∀ u, u < 2 * n + C.gates.length → ∀ a0 a1 a2 a3 c0 c1 c2 c3,
          (1 ∈ subTree (2 * n) C u → a0 = c0) →
          (2 ∈ subTree (2 * n) C u → a1 = c1) →
          (n ∈ subTree (2 * n) C u → a2 = c2) →
          (n + 1 ∈ subTree (2 * n) C u → a3 = c3) →
          (C.wires (inp4 n a0 a1 a2 a3)).getD u false = (C.wires (inp4 n c0 c1 c2 c3)).getD u false := by
        intro u hult a0 a1 a2 a3 c0 c1 c2 c3 h0 h1 h2 h3
        apply wiresPrefix_congr_subTree (2 * n) C _ _ (inp4_length _ _ _ _ _) (inp4_length _ _ _ _ _) u hult
        intro i hi him
        rw [inp4_getD, inp4_getD]
        simp only [hi, ite_true]
        split_ifs with i1 i2 in0 in1
        · exact h0 (i1 ▸ him)
        · exact h1 (i2 ▸ him)
        · exact h2 (in0 ▸ him)
        · exact h3 (in1 ▸ him)
        · rfl
      have heval_step : ∀ b0 b1 b2 b3, (C.wires (inp4 n b0 b1 b2 b3)).getD w false =
          if isAndOp (C.gates[w - 2 * n]'(by omega)).op then fa b0 b1 b2 b3 && fb b0 b1 b2 b3
          else fa b0 b1 b2 b3 || fb b0 b1 b2 b3 := fun b0 b1 b2 b3 =>
        inp4_eval_step n hn C hm w hwge hwlt a b hab hch _ (inp4_length _ _ _ _ _)
      rw [heval_step] at h10 h11 h20 h21 h1x hx0
      split_ifs at h10 h11 h20 h21 h1x hx0 with hop
      · simp only [Bool.and_eq_true] at h10 h11 h20
        by_cases ha0 : fa false false false false = true
        · have hat : ∀ b0 b1 b2 b3, fa b0 b1 b2 b3 = true := fun b0 b1 b2 b3 =>
            hmono_w a false false false false b0 b1 b2 b3 (by simp) (by simp) (by simp) (by simp) ha0
          rw [hat] at h21 h1x hx0
          simp only [Bool.true_and] at h21 h1x hx0
          exact ih b hb_lt hbR ⟨h10.2, h11.2, h20.2, h21, h1x, hx0⟩
        · by_cases hb0 : fb false false false false = true
          · have hbt : ∀ b0 b1 b2 b3, fb b0 b1 b2 b3 = true := fun b0 b1 b2 b3 =>
              hmono_w b false false false false b0 b1 b2 b3 (by simp) (by simp) (by simp) (by simp) hb0
            rw [hbt] at h21 h1x hx0
            simp only [Bool.and_true] at h21 h1x hx0
            exact ih a ha_lt haR ⟨h10.1, h11.1, h20.1, h21, h1x, hx0⟩
          · have ha0f : fa false false false false = false := Bool.eq_false_iff.mpr ha0
            have hb0f : fb false false false false = false := Bool.eq_false_iff.mpr hb0
            have hit : ∀ u (hult : u < 2 * n + C.gates.length),
                (C.wires (inp4 n false false false false)).getD u false = false →
                (C.wires (inp4 n true false true false)).getD u false = true →
                (C.wires (inp4 n true false false true)).getD u false = true →
                (C.wires (inp4 n false true true false)).getD u false = true →
                (1 ∈ subTree (2 * n) C u ∨ n ∈ subTree (2 * n) C u) ∧
                (1 ∈ subTree (2 * n) C u ∨ n + 1 ∈ subTree (2 * n) C u) ∧
                (2 ∈ subTree (2 * n) C u ∨ n ∈ subTree (2 * n) C u) := by
              intro u hult hu0 hu10 hu11 hu20
              refine ⟨?_, ?_, ?_⟩
              · by_contra hc; push_neg at hc
                have := hign u hult true false true false false false false false (fun h => absurd h hc.1) (fun _ => rfl) (fun h => absurd h hc.2) (fun _ => rfl)
                rw [hu10, hu0] at this; contradiction
              · by_contra hc; push_neg at hc
                have := hign u hult true false false true false false false false (fun h => absurd h hc.1) (fun _ => rfl) (fun _ => rfl) (fun h => absurd h hc.2)
                rw [hu11, hu0] at this; contradiction
              · by_contra hc; push_neg at hc
                have := hign u hult false true true false false false false false (fun _ => rfl) (fun h => absurd h hc.1) (fun h => absurd h hc.2) (fun _ => rfl)
                rw [hu20, hu0] at this; contradiction
            have hha := hit a (ha_lt.trans hwlt) ha0f h10.1 h11.1 h20.1
            have hhb := hit b (hb_lt.trans hwlt) hb0f h10.2 h11.2 h20.2
            have hna : ∀ v, v ∈ subTree (2 * n) C a → v ∉ subTree (2 * n) C b :=
              fun v hv => Finset.disjoint_left.mp hdisj hv
            have hnb : ∀ v, v ∈ subTree (2 * n) C b → v ∉ subTree (2 * n) C a :=
              fun v hv => Finset.disjoint_right.mp hdisj hv
            by_cases h1a : 1 ∈ subTree (2 * n) C a
            · have h1nb : 1 ∉ subTree (2 * n) C b := hna 1 h1a
              have hnb_n : n ∈ subTree (2 * n) C b := hhb.1.resolve_left h1nb
              have hnb_n1 : n + 1 ∈ subTree (2 * n) C b := hhb.2.1.resolve_left h1nb
              have hna_n : n ∉ subTree (2 * n) C a := hnb n hnb_n
              have hna_n1 : n + 1 ∉ subTree (2 * n) C a := hnb (n + 1) hnb_n1
              have h2a : 2 ∈ subTree (2 * n) C a := hha.2.2.resolve_right hna_n
              have h2nb : 2 ∉ subTree (2 * n) C b := hna 2 h2a
              have ha21 : fa false true false true = true := by
                dsimp only [fa]
                rw [hign a (ha_lt.trans hwlt) false true false true false true true false (fun _ => rfl) (fun _ => rfl) (fun h => absurd h hna_n) (fun h => absurd h hna_n1)]
                exact h20.1
              have hb21 : fb false true false true = true := by
                dsimp only [fb]
                rw [hign b (hb_lt.trans hwlt) false true false true true false false true (fun h => absurd h h1nb) (fun h => absurd h h2nb) (fun _ => rfl) (fun _ => rfl)]
                exact h11.2
              rw [ha21, hb21] at h21; simp at h21
            · have hna_n : n ∈ subTree (2 * n) C a := hha.1.resolve_left h1a
              have hna_n1 : n + 1 ∈ subTree (2 * n) C a := hha.2.1.resolve_left h1a
              have hnb_n : n ∉ subTree (2 * n) C b := hna n hna_n
              have hnb_n1 : n + 1 ∉ subTree (2 * n) C b := hna (n + 1) hna_n1
              have h1b : 1 ∈ subTree (2 * n) C b := hhb.1.resolve_right hnb_n
              have h2b : 2 ∈ subTree (2 * n) C b := hhb.2.2.resolve_right hnb_n
              have h2na : 2 ∉ subTree (2 * n) C a := hnb 2 h2b
              have ha21 : fa false true false true = true := by
                dsimp only [fa]
                rw [hign a (ha_lt.trans hwlt) false true false true true false false true (fun h => absurd h h1a) (fun h => absurd h h2na) (fun _ => rfl) (fun _ => rfl)]
                exact h11.1
              have hb21 : fb false true false true = true := by
                dsimp only [fb]
                rw [hign b (hb_lt.trans hwlt) false true false true false true true false (fun _ => rfl) (fun _ => rfl) (fun h => absurd h hnb_n) (fun h => absurd h hnb_n1)]
                exact h20.2
              rw [ha21, hb21] at h21; simp at h21
      · simp only [Bool.or_eq_false_iff, Bool.or_eq_true] at h10 h11 h20 h21 h1x hx0
        have ha_f : fa false true false true = false ∧ fa true false false false = false ∧ fa false false true false = false :=
          ⟨h21.1, h1x.1, hx0.1⟩
        have hb_f : fb false true false true = false ∧ fb true false false false = false ∧ fb false false true false = false :=
          ⟨h21.2, h1x.2, hx0.2⟩
        have need_1_n1 : ∀ u (hult : u < 2 * n + C.gates.length),
            (C.wires (inp4 n false true false true)).getD u false = false →
            (C.wires (inp4 n true false false false)).getD u false = false →
            (C.wires (inp4 n true false false true)).getD u false = true →
            1 ∈ subTree (2 * n) C u ∧ n + 1 ∈ subTree (2 * n) C u := by
          intro u hult h21u h1xu h11u
          constructor
          · by_contra hc
            have h01 : (C.wires (inp4 n false false false true)).getD u false = true := by
              rw [← hign u hult true false false true false false false true (fun h => absurd h hc) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)]
              exact h11u
            have := hmono_w u false false false true false true false true (by simp) (by simp) (by simp) (by simp) h01
            rw [h21u] at this; contradiction
          · by_contra hc
            have := hign u hult true false false true true false false false (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun h => absurd h hc)
            rw [h11u, h1xu] at this; contradiction
        have need_2_n : ∀ u (hult : u < 2 * n + C.gates.length),
            (C.wires (inp4 n false true false true)).getD u false = false →
            (C.wires (inp4 n false false true false)).getD u false = false →
            (C.wires (inp4 n false true true false)).getD u false = true →
            2 ∈ subTree (2 * n) C u ∧ n ∈ subTree (2 * n) C u := by
          intro u hult h21u hx0u h20u
          constructor
          · by_contra hc
            have := hign u hult false true true false false false true false (fun _ => rfl) (fun h => absurd h hc) (fun _ => rfl) (fun _ => rfl)
            rw [h20u, hx0u] at this; contradiction
          · by_contra hc
            have h2_0 : (C.wires (inp4 n false true false false)).getD u false = true := by
              rw [← hign u hult false true true false false true false false (fun _ => rfl) (fun _ => rfl) (fun h => absurd h hc) (fun _ => rfl)]
              exact h20u
            have := hmono_w u false true false false false true false true (by simp) (by simp) (by simp) (by simp) h2_0
            rw [h21u] at this; contradiction
        have hna : ∀ v, v ∈ subTree (2 * n) C a → v ∉ subTree (2 * n) C b :=
          fun v hv => Finset.disjoint_left.mp hdisj hv
        have hnb : ∀ v, v ∈ subTree (2 * n) C b → v ∉ subTree (2 * n) C a :=
          fun v hv => Finset.disjoint_right.mp hdisj hv
        rcases h11 with h11a | h11b
        · have ⟨h1a, hn1a⟩ := need_1_n1 a (ha_lt.trans hwlt) ha_f.1 ha_f.2.1 h11a
          rcases h20 with h20a | h20b
          · have ⟨h2a, hna_n⟩ := need_2_n a (ha_lt.trans hwlt) ha_f.1 ha_f.2.2 h20a
            have hb10 : fb true false true false = false := by
              dsimp only [fb]
              rw [hign b (hb_lt.trans hwlt) true false true false false true false true
                (fun h => absurd h (hna 1 h1a)) (fun h => absurd h (hna 2 h2a))
                (fun h => absurd h (hna n hna_n)) (fun h => absurd h (hna (n + 1) hn1a))]
              exact hb_f.1
            have ha10 : fa true false true false = true := h10.resolve_right (by rw [hb10]; simp)
            exact ih a ha_lt haR ⟨ha10, h11a, h20a, ha_f.1, ha_f.2.1, ha_f.2.2⟩
          · have ⟨h2b, hnb_n⟩ := need_2_n b (hb_lt.trans hwlt) hb_f.1 hb_f.2.2 h20b
            have ha10f : fa true false true false = false := by
              dsimp only [fa]
              rw [hign a (ha_lt.trans hwlt) true false true false true false false false
                (fun _ => rfl) (fun _ => rfl) (fun h => absurd h (hnb n hnb_n)) (fun _ => rfl)]
              exact ha_f.2.1
            have hb10f : fb true false true false = false := by
              dsimp only [fb]
              rw [hign b (hb_lt.trans hwlt) true false true false false false true false
                (fun h => absurd h (hna 1 h1a)) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)]
              exact hb_f.2.2
            rcases h10 with h10a | h10b
            · rw [ha10f] at h10a; contradiction
            · rw [hb10f] at h10b; contradiction
        · have ⟨h1b, hn1b⟩ := need_1_n1 b (hb_lt.trans hwlt) hb_f.1 hb_f.2.1 h11b
          rcases h20 with h20a | h20b
          · have ⟨h2a, hna_n⟩ := need_2_n a (ha_lt.trans hwlt) ha_f.1 ha_f.2.2 h20a
            have ha10f : fa true false true false = false := by
              dsimp only [fa]
              rw [hign a (ha_lt.trans hwlt) true false true false false false true false
                (fun h => absurd h (hnb 1 h1b)) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)]
              exact ha_f.2.2
            have hb10f : fb true false true false = false := by
              dsimp only [fb]
              rw [hign b (hb_lt.trans hwlt) true false true false true false false false
                (fun _ => rfl) (fun _ => rfl) (fun h => absurd h (hna n hna_n)) (fun _ => rfl)]
              exact hb_f.2.1
            rcases h10 with h10a | h10b
            · rw [ha10f] at h10a; contradiction
            · rw [hb10f] at h10b; contradiction
          · have ⟨h2b, hnb_n⟩ := need_2_n b (hb_lt.trans hwlt) hb_f.1 hb_f.2.2 h20b
            have ha10 : fa true false true false = false := by
              dsimp only [fa]
              rw [hign a (ha_lt.trans hwlt) true false true false false true false true
                (fun h => absurd h (hnb 1 h1b)) (fun h => absurd h (hnb 2 h2b))
                (fun h => absurd h (hnb n hnb_n)) (fun h => absurd h (hnb (n + 1) hn1b))]
              exact ha_f.1
            have hb10 : fb true false true false = true := h10.resolve_left (by rw [ha10]; simp)
            exact ih b hb_lt hbR ⟨hb10, h11b, h20b, hb_f.1, hb_f.2.1, hb_f.2.2⟩

theorem inp4_eq_oneEach (n : ℕ) (hn : 3 ≤ n) (b0 b1 b2 b3 : Bool) (u v : Fin n)
    (h1 : b0 = decide (1 = u.val)) (h2 : b1 = decide (2 = u.val))
    (h3 : b2 = decide (0 = v.val)) (h4 : b3 = decide (1 = v.val))
    (hu : u.val = 1 ∨ u.val = 2) (hv : v.val = 0 ∨ v.val = 1) :
    inp4 n b0 b1 b2 b3 = oneEach u v := by
  apply List.ext_getElem
  · rw [inp4_length, oneEach_length]
  · intro i hi1 hi2
    have e1 := inp4_getD n b0 b1 b2 b3 i
    have e2 := oneEach_getD u v i
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi1, List.getElem?_eq_getElem hi2, Option.getD_some] at e1 e2
    rw [e1, e2]
    rw [inp4_length] at hi1
    simp only [hi1, ite_true]
    by_cases hlt : i < n
    · simp only [hlt, ite_true]
      by_cases hi_1 : i = 1
      · subst hi_1; simp [h1]
      · by_cases hi_2 : i = 2
        · subst hi_2; simp [hi_1, h2]
        · have hne_n : i ≠ n := by omega
          have hne_n1 : i ≠ n + 1 := by omega
          have hne_u : i ≠ u.val := by omega
          simp [hi_1, hi_2, hne_n, hne_n1, hne_u]
    · simp only [hlt, ite_false, hi1, ite_true]
      have hne1 : i ≠ 1 := by omega
      have hne2 : i ≠ 2 := by omega
      simp only [hne1, hne2, ite_false]
      by_cases hin : i = n
      · subst hin; simp [h3]
      · by_cases hin1 : i = n + 1
        · subst hin1; simp [hin, show n + 1 - n = 1 by omega, h4]
        · have hne_v : i - n ≠ v.val := by omega
          simp [hin, hin1, hne_v]

theorem main_proof (n : ℕ) (hn : 3 ≤ n) : ¬ RepSizeAtMost (matA n) (2 * n - 1) := by
  rintro ⟨C, hm, hsize, hrep⟩
  have hout := output_is_gate n hn C hrep
  have ⟨hcard2, huniq⟩ := tree_structure n hn C hm hsize hrep
  have hnp4 := no_p4_on_tree n hn C hm C.output hout.2 hcard2 huniq C.output (self_mem_subTree (2 * n) C C.output)
  apply hnp4
  let u0 : Fin n := ⟨0, by omega⟩
  let u1 : Fin n := ⟨1, by omega⟩
  let u2 : Fin n := ⟨2, by omega⟩
  have h10 : inp4 n true false true false = oneEach u1 u0 :=
    inp4_eq_oneEach n hn true false true false u1 u0 rfl rfl rfl rfl (Or.inl rfl) (Or.inl rfl)
  have h11 : inp4 n true false false true = oneEach u1 u1 :=
    inp4_eq_oneEach n hn true false false true u1 u1 rfl rfl rfl rfl (Or.inl rfl) (Or.inr rfl)
  have h20 : inp4 n false true true false = oneEach u2 u0 :=
    inp4_eq_oneEach n hn false true true false u2 u0 rfl rfl rfl rfl (Or.inr rfl) (Or.inl rfl)
  have h21 : inp4 n false true false true = oneEach u2 u1 :=
    inp4_eq_oneEach n hn false true false true u2 u1 rfl rfl rfl rfl (Or.inr rfl) (Or.inr rfl)
  have hle_12 : ∀ i, (inp4 n true false false false).getD i false = true → (oneEach u1 u2).getD i false = true := by
    intro i hi
    rw [inp4_getD] at hi
    rw [oneEach_getD]
    split_ifs at hi with h1 i1 i2 in0 in1
    subst i1; simp [show 1 < n by omega, u1]
  have hle_00 : ∀ i, (inp4 n false false true false).getD i false = true → (oneEach u0 u0).getD i false = true := by
    intro i hi
    rw [inp4_getD] at hi
    rw [oneEach_getD]
    split_ifs at hi with h1 i1 i2 in0 in1
    have hlt2 : ¬(i < n) := by omega
    have heq0 : i - n = 0 := by omega
    simp [hlt2, h1, heq0, u0]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · change C.eval _ = true; rw [h10, hrep]; unfold matA; simp [u1, u0]
  · change C.eval _ = true; rw [h11, hrep]; unfold matA; simp [u1]
  · change C.eval _ = true; rw [h20, hrep]; unfold matA; simp [u2, u0]
  · change C.eval _ = false; rw [h21, hrep]; unfold matA; simp [u2, u1]
  · change C.eval _ = false
    by_contra h
    have ht : C.eval (inp4 n true false false false) = true := Bool.eq_true_of_not_eq_false h
    have hf := circuit_mono C hm (inp4 n true false false false) (oneEach u1 u2) (by rw [inp4_length, oneEach_length]) hle_12 ht
    rw [hrep] at hf; unfold matA at hf; simp [u1, u2] at hf
  · change C.eval _ = false
    by_contra h
    have ht : C.eval (inp4 n false false true false) = true := Bool.eq_true_of_not_eq_false h
    have hf := circuit_mono C hm (inp4 n false false true false) (oneEach u0 u0) (by rw [inp4_length, oneEach_length]) hle_00 ht
    rw [hrep] at hf; unfold matA at hf; simp [u0] at hf

end PEqualNP.Outside.L_meta_23958

theorem PEqualNP.Outside.L_meta_23958 : ∀ n : ℕ, 3 ≤ n → ¬ PEqualNP.Represents.RepSizeAtMost (fun (u : Fin n) (v : Fin n) => decide ((u.val = 0 ∧ v.val ≠ 0) ∨ (u.val = 1 ∧ v.val ≤ 1) ∨ (2 ≤ u.val ∧ v.val = 0))) (2 * n - 1) :=
  PEqualNP.Outside.L_meta_23958.main_proof
