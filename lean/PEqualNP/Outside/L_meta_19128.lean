import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

namespace PEqualNP.Outside.L_meta_19128

def evalWires (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem foldl_wires_append (gs : List Gate) (w : List Bool) :
    ∃ ext : List Bool, ext.length = gs.length ∧
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w = w ++ ext := by
  induction gs generalizing w with
  | nil => exact ⟨[], rfl, by simp⟩
  | cons g gs ih =>
    simp only [List.foldl_cons]
    obtain ⟨ext, hlen, heq⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: ext, by simp [hlen], ?_⟩
    rw [heq]; simp

theorem evalWires_length (gs : List Gate) (x : List Bool) :
    (evalWires gs x).length = x.length + gs.length := by
  obtain ⟨ext, hlen, heq⟩ := foldl_wires_append gs x
  rw [evalWires, heq, List.length_append, hlen]

theorem evalWires_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    evalWires (gs ++ [g]) x =
      evalWires gs x ++ [g.op.eval (g.inputs.map fun i => (evalWires gs x).getD i false)] := by
  simp [evalWires, List.foldl_append]

theorem evalWires_mono (gs : List Gate)
    (hm : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (x y : List Bool) (hlen : x.length = y.length)
    (hxy : ∀ i, x.getD i false = true → y.getD i false = true) :
    ∀ w, (evalWires gs x).getD w false = true → (evalWires gs y).getD w false = true := by
  induction gs using List.reverseRecOn with
  | nil => simpa [evalWires] using hxy
  | append_singleton gs g ih =>
    have hm_gs : ∀ g' ∈ gs, g'.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g'.inputs.length ≤ 2 :=
      fun g' hg' => hm g' (by simp [hg'])
    have hm_g := hm g (by simp)
    have hih := ih hm_gs
    intro w hw
    rw [evalWires_snoc] at hw ⊢
    have hlx : (evalWires gs x).length = x.length + gs.length := evalWires_length gs x
    have hly : (evalWires gs y).length = y.length + gs.length := evalWires_length gs y
    by_cases hlt : w < x.length + gs.length
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega)] at hw ⊢
      rw [← List.getD_eq_getElem?_getD] at hw ⊢
      exact hih w hw
    · by_cases heq : w = x.length + gs.length
      · subst heq
        have h1 : (evalWires gs x ++ [g.op.eval (g.inputs.map fun i => (evalWires gs x).getD i false)]).getD
            (x.length + gs.length) false =
            g.op.eval (g.inputs.map fun i => (evalWires gs x).getD i false) := by
          simp [List.getD_eq_getElem?_getD, ← hlx]
        have h2 : (evalWires gs y ++ [g.op.eval (g.inputs.map fun i => (evalWires gs y).getD i false)]).getD
            (x.length + gs.length) false =
            g.op.eval (g.inputs.map fun i => (evalWires gs y).getD i false) := by
          have : x.length + gs.length = (evalWires gs y).length := by omega
          simp [List.getD_eq_getElem?_getD, this]
        rw [h1] at hw; rw [h2]
        have hop : g.op = GateOp.and ∨ g.op = GateOp.or := by
          simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hm_g.1
        rcases hop with hand | hor
        · rw [hand] at hw ⊢
          simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq] at hw ⊢
          rintro _ ⟨i, hi, rfl⟩
          exact hih i (hw _ ⟨i, hi, rfl⟩)
        · rw [hor] at hw ⊢
          simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at hw ⊢
          rcases hw with ⟨_, ⟨i, hi, rfl⟩, htrue⟩
          exact ⟨_, ⟨i, hi, rfl⟩, hih i htrue⟩
      · have hgt : (evalWires gs x ++ [g.op.eval (g.inputs.map fun i => (evalWires gs x).getD i false)]).length ≤ w := by
          simp [hlx]; omega
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hgt] at hw
        simp at hw

def coneStep (acc : List (Finset ℕ)) (g : Gate) : List (Finset ℕ) :=
  acc ++ [insert acc.length (g.inputs.foldl (fun s i => s ∪ acc.getD i ∅) ∅)]

def wireCones (gs : List Gate) : List (Finset ℕ) :=
  gs.foldl coneStep ((List.range 10).map fun i => ({i} : Finset ℕ))

theorem foldl_union_mem (acc : List (Finset ℕ)) (ins : List ℕ) (s : Finset ℕ) (u : ℕ) :
    u ∈ ins.foldl (fun accS i => accS ∪ acc.getD i ∅) s ↔
      u ∈ s ∨ ∃ i ∈ ins, u ∈ acc.getD i ∅ := by
  induction ins generalizing s with
  | nil => simp
  | cons a rest ih =>
    simp only [List.foldl_cons, ih, Finset.mem_union, List.mem_cons]
    constructor
    · rintro ((hs | ha) | ⟨i, hi, hu⟩)
      · exact Or.inl hs
      · exact Or.inr ⟨a, Or.inl rfl, ha⟩
      · exact Or.inr ⟨i, Or.inr hi, hu⟩
    · rintro (hs | ⟨i, rfl | hi, hu⟩)
      · exact Or.inl (Or.inl hs)
      · exact Or.inl (Or.inr hu)
      · exact Or.inr ⟨i, hi, hu⟩

theorem wireCones_spec (gs : List Gate) :
    let cs := wireCones gs
    cs.length = 10 + gs.length ∧
    (∀ w < 10 + gs.length,
      w ∈ cs.getD w ∅ ∧
      (∀ u ∈ cs.getD w ∅, u ≤ w) ∧
      (∀ u ∈ cs.getD w ∅, u ≠ w →
        ∃ j < gs.length, 10 + j ∈ cs.getD w ∅ ∧ u ∈ (gs.getD j ⟨GateOp.and, []⟩).inputs)) ∧
    (∀ x y : List Bool, x.length = 10 → y.length = 10 →
      ∀ w < 10 + gs.length,
        (∀ i < 10, i ∈ cs.getD w ∅ → x.getD i false = y.getD i false) →
        (evalWires gs x).getD w false = (evalWires gs y).getD w false) := by
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨by simp [wireCones], ?_, ?_⟩
    · intro w hw
      have hget : (wireCones []).getD w ∅ = {w} := by
        rw [wireCones, List.foldl_nil, List.getD_eq_getElem?_getD, List.getElem?_map,
            List.getElem?_range (by simpa using hw)]
        rfl
      rw [hget]
      exact ⟨by simp, fun u hu => by simp at hu; omega, fun u hu hne => by simp at hu; exact (hne hu).elim⟩
    · intro x y _ _ w hw hagree
      have hget : (wireCones []).getD w ∅ = {w} := by
        rw [wireCones, List.foldl_nil, List.getD_eq_getElem?_getD, List.getElem?_map,
            List.getElem?_range (by simpa using hw)]
        rfl
      rw [hget] at hagree
      simpa [evalWires] using hagree w (by omega) (by simp)
  | append_singleton gs g ih =>
    obtain ⟨hlen, hprop, heval⟩ := ih
    let cs := wireCones gs
    have hlen_cs : cs.length = 10 + gs.length := hlen
    have hcs_snoc : wireCones (gs ++ [g]) = coneStep cs g := by
      simp [wireCones, cs, List.foldl_append]
    have hlen' : (wireCones (gs ++ [g])).length = 10 + (gs ++ [g]).length := by
      rw [hcs_snoc]; simp [coneStep, hlen_cs]; omega
    have hget_lt : ∀ w < 10 + gs.length, (wireCones (gs ++ [g])).getD w ∅ = cs.getD w ∅ := by
      intro w hw
      rw [hcs_snoc, coneStep]
      have : w < cs.length := by omega
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left this]
    have hget_last : (wireCones (gs ++ [g])).getD (10 + gs.length) ∅ =
        insert (10 + gs.length) (g.inputs.foldl (fun s i => s ∪ cs.getD i ∅) ∅) := by
      rw [hcs_snoc, coneStep]
      have hcl : cs.length = 10 + gs.length := hlen
      simp [List.getD_eq_getElem?_getD, ← hcl]
    have hgate_lt : ∀ j < gs.length,
        (gs ++ [g]).getD j ⟨GateOp.and, []⟩ = gs.getD j ⟨GateOp.and, []⟩ := by
      intro j hj
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hj]
    have hgate_last : (gs ++ [g]).getD gs.length ⟨GateOp.and, []⟩ = g := by
      simp [List.getD_eq_getElem?_getD]
    refine ⟨hlen', ?_, ?_⟩
    · intro w hw
      simp only [List.length_append, List.length_singleton] at hw
      by_cases hlt : w < 10 + gs.length
      · rw [hget_lt w hlt]
        obtain ⟨hwmem, hle, hcl⟩ := hprop w hlt
        refine ⟨hwmem, hle, ?_⟩
        intro u hu hne
        obtain ⟨j, hj, hjmem, huin⟩ := hcl u hu hne
        exact ⟨j, by simp; omega, hjmem, by rw [hgate_lt j hj]; exact huin⟩
      · have hweq : w = 10 + gs.length := by omega
        subst hweq
        rw [hget_last]
        refine ⟨Finset.mem_insert_self _ _, ?_, ?_⟩
        · intro u hu
          rw [Finset.mem_insert, foldl_union_mem] at hu
          rcases hu with rfl | (hbot | ⟨a, _, hua⟩)
          · exact Nat.le_refl _
          · simp at hbot
          · by_cases ha : a < 10 + gs.length
            · have := (hprop a ha).2.1 u hua
              omega
            · have hnone : cs[a]? = none := List.getElem?_eq_none (by omega)
              rw [List.getD_eq_getElem?_getD, hnone] at hua
              simp at hua
        · intro u hu hne
          rw [Finset.mem_insert, foldl_union_mem] at hu
          rcases hu with rfl | (hbot | ⟨a, hain, hua⟩)
          · exact (hne rfl).elim
          · simp at hbot
          · by_cases hua_eq : u = a
            · subst hua_eq
              exact ⟨gs.length, by simp, Finset.mem_insert_self _ _, by rw [hgate_last]; exact hain⟩
            · by_cases ha : a < 10 + gs.length
              · obtain ⟨j, hj, hjmem, huin⟩ := (hprop a ha).2.2 u hua hua_eq
                refine ⟨j, by simp; omega, ?_, by rw [hgate_lt j hj]; exact huin⟩
                rw [Finset.mem_insert, foldl_union_mem]
                exact Or.inr (Or.inr ⟨a, hain, hjmem⟩)
              · have hnone : cs[a]? = none := List.getElem?_eq_none (by omega)
                rw [List.getD_eq_getElem?_getD, hnone] at hua
                simp at hua
    · intro x y hx hy w hw hagree
      simp only [List.length_append, List.length_singleton] at hw
      rw [evalWires_snoc, evalWires_snoc]
      have hlx : (evalWires gs x).length = 10 + gs.length := by rw [evalWires_length, hx]
      have hly : (evalWires gs y).length = 10 + gs.length := by rw [evalWires_length, hy]
      by_cases hlt : w < 10 + gs.length
      · rw [hget_lt w hlt] at hagree
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega),
            List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega),
            ← List.getD_eq_getElem?_getD, ← List.getD_eq_getElem?_getD]
        exact heval x y hx hy w hlt hagree
      · have hweq : w = 10 + gs.length := by omega
        subst hweq
        rw [hget_last] at hagree
        have h1 : (evalWires gs x ++ [g.op.eval (g.inputs.map fun i => (evalWires gs x).getD i false)]).getD
            (10 + gs.length) false =
            g.op.eval (g.inputs.map fun i => (evalWires gs x).getD i false) := by
          simp [List.getD_eq_getElem?_getD, ← hlx]
        have h2 : (evalWires gs y ++ [g.op.eval (g.inputs.map fun i => (evalWires gs y).getD i false)]).getD
            (10 + gs.length) false =
            g.op.eval (g.inputs.map fun i => (evalWires gs y).getD i false) := by
          simp [List.getD_eq_getElem?_getD, ← hly]
        rw [h1, h2]
        congr 1
        apply List.map_congr_left
        intro a ha
        by_cases halt : a < 10 + gs.length
        · apply heval x y hx hy a halt
          intro i hi hia
          apply hagree i hi
          rw [Finset.mem_insert, foldl_union_mem]
          exact Or.inr (Or.inr ⟨a, ha, hia⟩)
        · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega),
              List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]

theorem no_size6 :
    ¬ (RepSizeAtMost (fun u v : Fin 5 => !(decide (u = 0) && decide (v = 0))) 6) := by
  rintro ⟨C, hmono, hsize, hrep⟩
  have h00 : (evalWires C.gates (oneEach (0 : Fin 5) (0 : Fin 5))).getD C.output false = false := by
    simpa [Circuit.eval, Circuit.wires, evalWires] using hrep 0 0
  have h10 : (evalWires C.gates (oneEach (1 : Fin 5) (0 : Fin 5))).getD C.output false = true := by
    simpa [Circuit.eval, Circuit.wires, evalWires] using hrep 1 0
  have hout_lt : C.output < 10 + C.gates.length := by
    by_contra hge
    have hl : (evalWires C.gates (oneEach (1 : Fin 5) (0 : Fin 5))).length = 10 + C.gates.length := by
      rw [evalWires_length]; simp [oneEach]
    have hnone : (evalWires C.gates (oneEach (1 : Fin 5) (0 : Fin 5)))[C.output]? = none :=
      List.getElem?_eq_none (by omega)
    rw [List.getD_eq_getElem?_getD, hnone] at h10
    simp at h10
  obtain ⟨_, hprop, heval⟩ := wireCones_spec C.gates
  let S : Finset ℕ := (wireCones C.gates).getD C.output ∅
  obtain ⟨hout_mem, hle, hcl⟩ := hprop C.output hout_lt
  let Iset : Finset ℕ := S.filter (fun u => u < 10)
  let Gset : Finset ℕ := S.filter (fun u => 10 ≤ u)
  have hSG : S.card = Iset.card + Gset.card := by
    have hdisj : Disjoint Iset Gset := by
      rw [Finset.disjoint_left]
      intro u hu1 hu2
      simp only [Iset, Gset, Finset.mem_filter] at hu1 hu2
      omega
    have hunion : Iset ∪ Gset = S := by
      ext u
      simp only [Iset, Gset, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
      · intro h
        by_cases h10 : u < 10
        · exact Or.inl ⟨h, h10⟩
        · exact Or.inr ⟨h, by omega⟩
    rw [← hunion, Finset.card_union_of_disjoint hdisj]
  have hG_le : Gset.card ≤ C.gates.length := by
    have hsub : Gset ⊆ (Finset.range C.gates.length).image (fun j => 10 + j) := by
      intro u hu
      simp only [Gset, Finset.mem_filter] at hu
      have hult : u < 10 + C.gates.length := Nat.lt_of_le_of_lt (hle u hu.1) hout_lt
      simp only [Finset.mem_image, Finset.mem_range]
      exact ⟨u - 10, by omega, by omega⟩
    exact (Finset.card_le_card hsub).trans Finset.card_image_le |>.trans (by simp)
  have hS_er : (S.erase C.output).card ≤ 2 * Gset.card := by
    have hsub : S.erase C.output ⊆ Gset.biUnion (fun u => (C.gates.getD (u - 10) ⟨GateOp.and, []⟩).inputs.toFinset) := by
      intro u hu
      rw [Finset.mem_erase] at hu
      obtain ⟨j, hj, hjmem, huin⟩ := hcl u hu.2 hu.1
      rw [Finset.mem_biUnion]
      refine ⟨10 + j, ?_, ?_⟩
      · simp only [Gset, Finset.mem_filter]
        exact ⟨hjmem, by omega⟩
      · simpa [List.getD_eq_getElem?_getD] using huin
    calc (S.erase C.output).card
        ≤ (Gset.biUnion (fun u => (C.gates.getD (u - 10) ⟨GateOp.and, []⟩).inputs.toFinset)).card :=
          Finset.card_le_card hsub
      _ ≤ ∑ u ∈ Gset, ((C.gates.getD (u - 10) ⟨GateOp.and, []⟩).inputs.toFinset).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _u ∈ Gset, 2 := by
          apply Finset.sum_le_sum
          intro u hu
          simp only [Gset, Finset.mem_filter] at hu
          have hult : u < 10 + C.gates.length := Nat.lt_of_le_of_lt (hle u hu.1) hout_lt
          have hmem_g : C.gates.getD (u - 10) ⟨GateOp.and, []⟩ ∈ C.gates := by
            have hlt' : u - 10 < C.gates.length := by omega
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt', Option.getD_some]
            exact List.getElem_mem hlt'
          exact (List.toFinset_card_le _).trans (hmono _ hmem_g).2
      _ = 2 * Gset.card := by simp [Nat.mul_comm]
  have hI_le7 : Iset.card ≤ 7 := by
    have hcard_er : (S.erase C.output).card = S.card - 1 := Finset.card_erase_of_mem hout_mem
    have hpos : 1 ≤ S.card := Finset.card_pos.mpr ⟨C.output, hout_mem⟩
    have hsz : C.gates.length ≤ 6 := hsize
    omega
  have hleft_mem : ∀ u : Fin 5, u ≠ 0 → u.val ∈ Iset := by
    intro u hu
    by_contra hnot
    let x' : List Bool :=
      List.ofFn (fun k : Fin 5 => decide (k = 0 ∨ k = u)) ++ List.ofFn (fun k : Fin 5 => decide (k = 0))
    have hlen_x' : x'.length = 10 := by simp [x']
    have hlen_00 : (oneEach (0 : Fin 5) (0 : Fin 5)).length = 10 := by simp [oneEach]
    have hlen_u0 : (oneEach u (0 : Fin 5)).length = 10 := by simp [oneEach]
    have hle_u0 : ∀ i, (oneEach u (0 : Fin 5)).getD i false = true → x'.getD i false = true := by
      intro i hi
      by_cases h5 : i < 5
      · simp only [oneEach, x', List.getD_eq_getElem?_getD] at hi ⊢
        rw [List.getElem?_append_left (by simp [h5]), List.getElem?_ofFn] at hi ⊢
        simp [h5] at hi ⊢
        exact Or.inr hi
      · by_cases h10 : i < 10
        · simp only [oneEach, x', List.getD_eq_getElem?_getD] at hi ⊢
          rw [List.getElem?_append_right (by simp; omega)] at hi ⊢
          simpa using hi
        · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at hi
          simp at hi
    have hu0_true : (evalWires C.gates (oneEach u (0 : Fin 5))).getD C.output false = true := by
      have hr := hrep u 0
      have hne0 : ¬(u = 0) := hu
      simpa [Circuit.eval, Circuit.wires, evalWires, hne0] using hr
    have hx'_true : (evalWires C.gates x').getD C.output false = true :=
      evalWires_mono C.gates hmono (oneEach u 0) x' (by omega) hle_u0 C.output hu0_true
    have hagree : ∀ i < 10, i ∈ S → (oneEach (0 : Fin 5) (0 : Fin 5)).getD i false = x'.getD i false := by
      intro i hi hiS
      have hne_i : i ≠ u.val := by
        intro heq; subst heq
        exact hnot (Finset.mem_filter.mpr ⟨hiS, hi⟩)
      by_cases h5 : i < 5
      · simp only [oneEach, x', List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left (by simp [h5]), List.getElem?_append_left (by simp [h5]),
            List.getElem?_ofFn, List.getElem?_ofFn]
        simp [h5, Fin.ext_iff, hne_i]
      · simp only [oneEach, x', List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by simp; omega), List.getElem?_append_right (by simp; omega)]
        simp
    have heq_eval := heval (oneEach 0 0) x' hlen_00 hlen_x' C.output hout_lt hagree
    rw [h00, hx'_true] at heq_eval
    cases heq_eval
  have hright_mem : ∀ v : Fin 5, v ≠ 0 → 5 + v.val ∈ Iset := by
    intro v hv
    by_contra hnot
    let y' : List Bool :=
      List.ofFn (fun k : Fin 5 => decide (k = 0)) ++ List.ofFn (fun k : Fin 5 => decide (k = 0 ∨ k = v))
    have hlen_y' : y'.length = 10 := by simp [y']
    have hlen_00 : (oneEach (0 : Fin 5) (0 : Fin 5)).length = 10 := by simp [oneEach]
    have hlen_0v : (oneEach (0 : Fin 5) v).length = 10 := by simp [oneEach]
    have hle_0v : ∀ i, (oneEach (0 : Fin 5) v).getD i false = true → y'.getD i false = true := by
      intro i hi
      by_cases h5 : i < 5
      · simp only [oneEach, y', List.getD_eq_getElem?_getD] at hi ⊢
        rw [List.getElem?_append_left (by simp [h5])] at hi ⊢
        exact hi
      · by_cases h10 : i < 10
        · simp only [oneEach, y', List.getD_eq_getElem?_getD] at hi ⊢
          rw [List.getElem?_append_right (by simp; omega), List.getElem?_ofFn] at hi ⊢
          simp only [List.length_ofFn, show i - 5 < 5 by omega, ↓reduceDIte, Option.getD_some,
            decide_eq_true_eq] at hi ⊢
          exact Or.inr hi
        · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at hi
          simp at hi
    have h0v_true : (evalWires C.gates (oneEach (0 : Fin 5) v)).getD C.output false = true := by
      have hr := hrep 0 v
      have hne0 : ¬(v = 0) := hv
      simpa [Circuit.eval, Circuit.wires, evalWires, hne0] using hr
    have hy'_true : (evalWires C.gates y').getD C.output false = true :=
      evalWires_mono C.gates hmono (oneEach 0 v) y' (by omega) hle_0v C.output h0v_true
    have hagree : ∀ i < 10, i ∈ S → (oneEach (0 : Fin 5) (0 : Fin 5)).getD i false = y'.getD i false := by
      intro i hi hiS
      have hne_i : i ≠ 5 + v.val := by
        intro heq; subst heq
        exact hnot (Finset.mem_filter.mpr ⟨hiS, hi⟩)
      by_cases h5 : i < 5
      · simp only [oneEach, y', List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left (by simp [h5]), List.getElem?_append_left (by simp [h5])]
      · simp only [oneEach, y', List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by simp; omega), List.getElem?_append_right (by simp; omega),
            List.getElem?_ofFn, List.getElem?_ofFn]
        simp only [List.length_ofFn, show i - 5 < 5 by omega, ↓reduceDIte, Option.getD_some]
        have hsub_ne : i - 5 ≠ v.val := by omega
        simp [Fin.ext_iff, hsub_ne]
    have heq_eval := heval (oneEach 0 0) y' hlen_00 hlen_y' C.output hout_lt hagree
    rw [h00, hy'_true] at heq_eval
    cases heq_eval
  have h8_sub : ({1, 2, 3, 4, 6, 7, 8, 9} : Finset ℕ) ⊆ Iset := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hleft_mem ⟨1, by omega⟩ (by simp [Fin.ext_iff])
    · exact hleft_mem ⟨2, by omega⟩ (by simp [Fin.ext_iff])
    · exact hleft_mem ⟨3, by omega⟩ (by simp [Fin.ext_iff])
    · exact hleft_mem ⟨4, by omega⟩ (by simp [Fin.ext_iff])
    · exact hright_mem ⟨1, by omega⟩ (by simp [Fin.ext_iff])
    · exact hright_mem ⟨2, by omega⟩ (by simp [Fin.ext_iff])
    · exact hright_mem ⟨3, by omega⟩ (by simp [Fin.ext_iff])
    · exact hright_mem ⟨4, by omega⟩ (by simp [Fin.ext_iff])
  have h8_le : 8 ≤ Iset.card := by
    have hcard : ({1, 2, 3, 4, 6, 7, 8, 9} : Finset ℕ).card = 8 := by decide
    exact hcard ▸ Finset.card_le_card h8_sub
  omega

end PEqualNP.Outside.L_meta_19128

theorem PEqualNP.Outside.L_meta_19128 :
    ¬ (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => !(decide (u = 0) && decide (v = 0))) 6) :=
  PEqualNP.Outside.L_meta_19128.no_size6
