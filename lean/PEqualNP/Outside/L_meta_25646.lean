import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.L_meta_25615
import PEqualNP.Outside.L_meta_25644

namespace PEqualNP.Outside.L_meta_25646_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents

def wiresAux (gs : List Gate) (init : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) init

theorem wiresAux_nil (w : List Bool) : wiresAux [] w = w := rfl

theorem wiresAux_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wiresAux (g :: gs) w =
      wiresAux gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

theorem wiresAux_append (gs1 gs2 : List Gate) (w : List Bool) :
    wiresAux (gs1 ++ gs2) w = wiresAux gs2 (wiresAux gs1 w) := by
  simp [wiresAux, List.foldl_append]

theorem wiresAux_length (gs : List Gate) (w : List Bool) :
    (wiresAux gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [wiresAux]
  | cons g gs ih =>
    rw [wiresAux_cons, ih]
    simp
    omega

theorem getD_append_left {α : Type*} (l1 l2 : List α) (d : α) (i : ℕ) (hi : i < l1.length) :
    (l1 ++ l2).getD i d = l1.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem getD_append_right {α : Type*} (l1 l2 : List α) (d : α) (i : ℕ) (hi : l1.length ≤ i) :
    (l1 ++ l2).getD i d = l2.getD (i - l1.length) d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right hi]

theorem getD_of_ge {α : Type*} (l : List α) (d : α) (i : ℕ) (hi : l.length ≤ i) :
    l.getD i d = d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

theorem wiresAux_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (wiresAux gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [wiresAux_cons, ih]
    · exact getD_append_left w _ false i hi
    · simp; omega

theorem circuit_wires_eq (C : Circuit) (x : List Bool) :
    C.wires x = wiresAux C.gates x := rfl

theorem circuit_eval_eq (C : Circuit) (x : List Bool) :
    C.eval x = (wiresAux C.gates x).getD C.output false := rfl

def shift (jw w : ℕ) : ℕ :=
  if jw < w then w - 1 else w

theorem shift_lt {jw w : ℕ} (h : w < jw) : shift jw w = w := by
  simp [shift, Nat.not_lt.mpr (Nat.le_of_lt h)]

theorem shift_gt {jw w : ℕ} (h : jw < w) : shift jw w = w - 1 := by
  simp [shift, h]

theorem gate_eval_and (bs : List Bool) : GateOp.and.eval bs = bs.all id := rfl
theorem gate_eval_or (bs : List Bool) : GateOp.or.eval bs = bs.any id := rfl

def remapCopy (jw u : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (fun w => if w = jw then u else shift jw w)⟩

def remapFalse (jw : ℕ) (g : Gate) : Gate :=
  match g.op with
  | GateOp.and =>
    if jw ∈ g.inputs then ⟨GateOp.or, []⟩
    else ⟨GateOp.and, g.inputs.map (shift jw)⟩
  | GateOp.or =>
    ⟨GateOp.or, (g.inputs.filter (fun w => decide (w ≠ jw))).map (shift jw)⟩
  | op => ⟨op, g.inputs.map (shift jw)⟩

def remapTrue (jw : ℕ) (g : Gate) : Gate :=
  match g.op with
  | GateOp.or =>
    if jw ∈ g.inputs then ⟨GateOp.and, []⟩
    else ⟨GateOp.or, g.inputs.map (shift jw)⟩
  | GateOp.and =>
    ⟨GateOp.and, (g.inputs.filter (fun w => decide (w ≠ jw))).map (shift jw)⟩
  | op => ⟨op, g.inputs.map (shift jw)⟩

def remapUnused (jw : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (shift jw)⟩

theorem mono_gate_remapCopy (jw u : ℕ) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    (remapCopy jw u g).op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧
      (remapCopy jw u g).inputs.length ≤ 2 := by
  simpa [remapCopy] using hg

theorem mono_gate_remapFalse (jw : ℕ) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    (remapFalse jw g).op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧
      (remapFalse jw g).inputs.length ≤ 2 := by
  rcases hg with ⟨hop, hlen⟩
  rcases hop with hop | hop
  · rw [remapFalse, hop]
    dsimp only
    split_ifs
    · simp
    · simp [hlen]
  · rw [remapFalse, hop]
    dsimp only
    refine ⟨Or.inr rfl, ?_⟩
    rw [List.length_map]
    exact (List.length_filter_le _ _).trans hlen

theorem mono_gate_remapTrue (jw : ℕ) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    (remapTrue jw g).op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧
      (remapTrue jw g).inputs.length ≤ 2 := by
  rcases hg with ⟨hop, hlen⟩
  rcases hop with hop | hop
  · rw [remapTrue, hop]
    dsimp only
    refine ⟨Or.inl rfl, ?_⟩
    rw [List.length_map]
    exact (List.length_filter_le _ _).trans hlen
  · rw [remapTrue, hop]
    dsimp only
    split_ifs
    · simp
    · simp [hlen]

theorem mono_gate_remapUnused (jw : ℕ) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    (remapUnused jw g).op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧
      (remapUnused jw g).inputs.length ≤ 2 := by
  simpa [remapUnused] using hg

theorem step_inv (jw : ℕ) (Wold Wnew : List Bool) (b : Bool)
    (hlen : Wold.length = Wnew.length + 1) (hjw : jw < Wold.length)
    (hinv : ∀ w, w ≠ jw → Wnew.getD (shift jw w) false = Wold.getD w false) :
    (Wold ++ [b]).length = (Wnew ++ [b]).length + 1 ∧
      jw < (Wold ++ [b]).length ∧
      (∀ w, w ≠ jw → (Wnew ++ [b]).getD (shift jw w) false = (Wold ++ [b]).getD w false) := by
  refine ⟨by simp; omega, by simp; omega, ?_⟩
  intro w hw
  by_cases hlt : w < Wold.length
  · have hlt' : shift jw w < Wnew.length := by
      unfold shift
      split_ifs <;> omega
    rw [getD_append_left Wnew [b] false _ hlt', getD_append_left Wold [b] false _ hlt]
    exact hinv w hw
  · by_cases heq : w = Wold.length
    · subst heq
      have hgt : jw < Wold.length := hjw
      rw [shift_gt hgt]
      have hsub : Wold.length - 1 = Wnew.length := by omega
      rw [hsub, getD_append_right Wnew [b] false Wnew.length (le_refl _),
        getD_append_right Wold [b] false Wold.length (le_refl _)]
      simp
    · have hge1 : (Wold ++ [b]).length ≤ w := by simp; omega
      have hge2 : (Wnew ++ [b]).length ≤ shift jw w := by
        unfold shift
        split_ifs <;> (simp; omega)
      rw [getD_of_ge (Wnew ++ [b]) false _ hge2, getD_of_ge (Wold ++ [b]) false _ hge1]

theorem sim_copy (jw u : ℕ) (post : List Gate) (Wold Wnew : List Bool)
    (hlen : Wold.length = Wnew.length + 1) (hjw : jw < Wold.length)
    (huj : u < jw)
    (heq_u : Wold.getD jw false = Wold.getD u false)
    (hinv : ∀ w, w ≠ jw → Wnew.getD (shift jw w) false = Wold.getD w false) :
    ∀ w, w ≠ jw →
      (wiresAux (post.map (remapCopy jw u)) Wnew).getD (shift jw w) false =
      (wiresAux post Wold).getD w false := by
  induction post generalizing Wold Wnew with
  | nil => simpa [wiresAux] using hinv
  | cons g gs ih =>
    rw [List.map_cons, wiresAux_cons, wiresAux_cons]
    have hbit :
        (remapCopy jw u g).op.eval ((remapCopy jw u g).inputs.map fun i => Wnew.getD i false) =
        g.op.eval (g.inputs.map fun i => Wold.getD i false) := by
      dsimp [remapCopy]
      congr 1
      rw [List.map_map]
      apply List.map_congr_left
      intro w _
      dsimp only [Function.comp_apply]
      by_cases hw : w = jw
      · subst hw
        simp only [ite_true]
        have hu := hinv u (Nat.ne_of_lt huj)
        rw [shift_lt huj] at hu
        rw [hu, heq_u]
      · simp only [hw, ite_false]
        exact hinv w hw
    rw [hbit]
    let b := g.op.eval (g.inputs.map fun i => Wold.getD i false)
    obtain ⟨hl', hj', hi'⟩ := step_inv jw Wold Wnew b hlen hjw hinv
    have heq_u' : (Wold ++ [b]).getD jw false = (Wold ++ [b]).getD u false := by
      rw [getD_append_left Wold _ false jw hjw,
        getD_append_left Wold _ false u (Nat.lt_trans huj hjw)]
      exact heq_u
    exact ih _ _ hl' hj' heq_u' hi'

theorem sim_false (jw : ℕ) (post : List Gate) (Wold Wnew : List Bool)
    (hmono : ∀ g ∈ post, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (hlen : Wold.length = Wnew.length + 1) (hjw : jw < Wold.length)
    (hval : Wold.getD jw false = false)
    (hinv : ∀ w, w ≠ jw → Wnew.getD (shift jw w) false = Wold.getD w false) :
    ∀ w, w ≠ jw →
      (wiresAux (post.map (remapFalse jw)) Wnew).getD (shift jw w) false =
      (wiresAux post Wold).getD w false := by
  induction post generalizing Wold Wnew with
  | nil => simpa [wiresAux] using hinv
  | cons g gs ih =>
    rw [List.map_cons, wiresAux_cons, wiresAux_cons]
    have hgop : g.op = GateOp.and ∨ g.op = GateOp.or := by
      simpa using hmono g (List.mem_cons_self ..)
    have hgs : ∀ g' ∈ gs, g'.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) :=
      fun g' hg' => hmono g' (List.mem_cons_of_mem _ hg')
    have hbit :
        (remapFalse jw g).op.eval ((remapFalse jw g).inputs.map fun i => Wnew.getD i false) =
        g.op.eval (g.inputs.map fun i => Wold.getD i false) := by
      rcases hgop with hop | hop
      · rw [remapFalse, hop]
        dsimp only
        split_ifs with hmem
        · change false = (g.inputs.map fun i => Wold.getD i false).all id
          symm
          rw [List.all_eq_false]
          exact ⟨false, List.mem_map.mpr ⟨jw, hmem, hval⟩, by decide⟩
        · dsimp only [GateOp.eval]
          congr 1
          rw [List.map_map]
          apply List.map_congr_left
          intro w hw
          exact hinv w (fun h => hmem (h ▸ hw))
      · rw [remapFalse, hop]
        dsimp only [GateOp.eval]
        apply Bool.eq_iff_iff.mpr
        simp only [List.any_eq_true, List.mem_map, List.mem_filter, decide_eq_true_eq, id_eq]
        constructor
        · rintro ⟨_, ⟨_, ⟨w, ⟨hwm, hwn⟩, rfl⟩, rfl⟩, ht⟩
          rw [hinv w hwn] at ht
          exact ⟨true, ⟨w, hwm, ht⟩, rfl⟩
        · rintro ⟨_, ⟨w, hwm, ht⟩, rfl⟩
          have hwn : w ≠ jw := by
            intro heq
            subst heq
            rw [hval] at ht
            cases ht
          exact ⟨true, ⟨shift jw w, ⟨w, ⟨hwm, hwn⟩, rfl⟩, by rw [hinv w hwn, ht]⟩, rfl⟩
    rw [hbit]
    let b := g.op.eval (g.inputs.map fun i => Wold.getD i false)
    obtain ⟨hl', hj', hi'⟩ := step_inv jw Wold Wnew b hlen hjw hinv
    have hval' : (Wold ++ [b]).getD jw false = false := by
      rw [getD_append_left Wold _ false jw hjw]
      exact hval
    exact ih _ _ hgs hl' hj' hval' hi'

theorem sim_true (jw : ℕ) (post : List Gate) (Wold Wnew : List Bool)
    (hmono : ∀ g ∈ post, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (hlen : Wold.length = Wnew.length + 1) (hjw : jw < Wold.length)
    (hval : Wold.getD jw false = true)
    (hinv : ∀ w, w ≠ jw → Wnew.getD (shift jw w) false = Wold.getD w false) :
    ∀ w, w ≠ jw →
      (wiresAux (post.map (remapTrue jw)) Wnew).getD (shift jw w) false =
      (wiresAux post Wold).getD w false := by
  induction post generalizing Wold Wnew with
  | nil => simpa [wiresAux] using hinv
  | cons g gs ih =>
    rw [List.map_cons, wiresAux_cons, wiresAux_cons]
    have hgop : g.op = GateOp.and ∨ g.op = GateOp.or := by
      simpa using hmono g (List.mem_cons_self ..)
    have hgs : ∀ g' ∈ gs, g'.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) :=
      fun g' hg' => hmono g' (List.mem_cons_of_mem _ hg')
    have hbit :
        (remapTrue jw g).op.eval ((remapTrue jw g).inputs.map fun i => Wnew.getD i false) =
        g.op.eval (g.inputs.map fun i => Wold.getD i false) := by
      rcases hgop with hop | hop
      · rw [remapTrue, hop]
        dsimp only [GateOp.eval]
        apply Bool.eq_iff_iff.mpr
        simp only [List.all_eq_true, List.mem_map, List.mem_filter, decide_eq_true_eq, id_eq]
        constructor
        · intro hall b hb
          rcases hb with ⟨w, hwm, rfl⟩
          by_cases hwn : w = jw
          · subst hwn; exact hval
          · have h1 := hall (Wnew.getD (shift jw w) false) ⟨shift jw w, ⟨w, ⟨hwm, hwn⟩, rfl⟩, rfl⟩
            rwa [hinv w hwn] at h1
        · intro hall b hb
          rcases hb with ⟨_, ⟨w, ⟨hwm, hwn⟩, rfl⟩, rfl⟩
          rw [hinv w hwn]
          exact hall (Wold.getD w false) ⟨w, hwm, rfl⟩
      · rw [remapTrue, hop]
        dsimp only
        split_ifs with hmem
        · change true = (g.inputs.map fun i => Wold.getD i false).any id
          symm
          rw [List.any_eq_true]
          exact ⟨true, List.mem_map.mpr ⟨jw, hmem, hval⟩, rfl⟩
        · dsimp only [GateOp.eval]
          congr 1
          rw [List.map_map]
          apply List.map_congr_left
          intro w hw
          exact hinv w (fun h => hmem (h ▸ hw))
    rw [hbit]
    let b := g.op.eval (g.inputs.map fun i => Wold.getD i false)
    obtain ⟨hl', hj', hi'⟩ := step_inv jw Wold Wnew b hlen hjw hinv
    have hval' : (Wold ++ [b]).getD jw false = true := by
      rw [getD_append_left Wold _ false jw hjw]
      exact hval
    exact ih _ _ hgs hl' hj' hval' hi'

theorem sim_unused (jw : ℕ) (post : List Gate) (Wold Wnew : List Bool)
    (hun : ∀ g ∈ post, jw ∉ g.inputs)
    (hlen : Wold.length = Wnew.length + 1) (hjw : jw < Wold.length)
    (hinv : ∀ w, w ≠ jw → Wnew.getD (shift jw w) false = Wold.getD w false) :
    ∀ w, w ≠ jw →
      (wiresAux (post.map (remapUnused jw)) Wnew).getD (shift jw w) false =
      (wiresAux post Wold).getD w false := by
  induction post generalizing Wold Wnew with
  | nil => simpa [wiresAux] using hinv
  | cons g gs ih =>
    rw [List.map_cons, wiresAux_cons, wiresAux_cons]
    have hmem : jw ∉ g.inputs := hun g (List.mem_cons_self ..)
    have hgs : ∀ g' ∈ gs, jw ∉ g'.inputs := fun g' hg' => hun g' (List.mem_cons_of_mem _ hg')
    have hbit :
        (remapUnused jw g).op.eval ((remapUnused jw g).inputs.map fun i => Wnew.getD i false) =
        g.op.eval (g.inputs.map fun i => Wold.getD i false) := by
      dsimp [remapUnused]
      congr 1
      rw [List.map_map]
      apply List.map_congr_left
      intro w hw
      exact hinv w (fun h => hmem (h ▸ hw))
    rw [hbit]
    obtain ⟨hl', hj', hi'⟩ := step_inv jw Wold Wnew _ hlen hjw hinv
    exact ih _ _ hgs hl' hj' hi'

theorem init_inv (w_pre : List Bool) (b : Bool) :
    (w_pre ++ [b]).length = w_pre.length + 1 ∧
      w_pre.length < (w_pre ++ [b]).length ∧
      (∀ w, w ≠ w_pre.length →
        w_pre.getD (shift w_pre.length w) false = (w_pre ++ [b]).getD w false) := by
  refine ⟨by simp, by simp, ?_⟩
  intro w hw
  by_cases hlt : w < w_pre.length
  · rw [shift_lt hlt, getD_append_left w_pre [b] false w hlt]
  · have hgt : w_pre.length < w := by omega
    rw [shift_gt hgt]
    have hge1 : w_pre.length ≤ w - 1 := by omega
    have hge2 : (w_pre ++ [b]).length ≤ w := by simp; omega
    rw [getD_of_ge w_pre false _ hge1, getD_of_ge (w_pre ++ [b]) false _ hge2]

theorem list_split_at {α : Type*} (l : List α) (j : ℕ) (hj : j < l.length) :
    l = l.take j ++ l[j] :: l.drop (j + 1) := by
  have h1 := (List.take_append_drop j l).symm
  rw [List.drop_eq_getElem_cons hj] at h1
  exact h1

theorem gateAt_eq_getElem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]

theorem eval_gate_at (raw : ℕ) (C : Circuit) (x : List Bool) (hx : x.length = raw)
    (j : ℕ) (hj : j < C.gates.length) :
    let w_pre := wiresAux (C.gates.take j) x
    w_pre.length = raw + j ∧
    C.wires x = wiresAux (C.gates.drop (j + 1))
      (w_pre ++ [(gateAt C j).op.eval ((gateAt C j).inputs.map fun i => w_pre.getD i false)]) := by
  dsimp only
  have hlen : (wiresAux (C.gates.take j) x).length = raw + j := by
    rw [wiresAux_length, hx, List.length_take]
    omega
  refine ⟨hlen, ?_⟩
  rw [circuit_wires_eq]
  conv_lhs => rw [list_split_at C.gates j hj]
  rw [wiresAux_append, wiresAux_cons, gateAt_eq_getElem C j hj]

theorem simplify_mono (raw : ℕ) :
    ∀ (s : ℕ) (C : Circuit), C.size = s → Monotone2 C →
      (∃ b : Bool, ∀ x : List Bool, x.length = raw → C.eval x = b) ∨
      (∃ i < raw, ∀ x : List Bool, x.length = raw → C.eval x = x.getD i false) ∨
      (∃ C' : Circuit, C'.size ≤ C.size ∧
        (∀ x : List Bool, x.length = raw → C'.eval x = C.eval x) ∧
        Monotone2 C' ∧
        (∀ g ∈ C'.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∧
        ReadsBack raw C' ∧
        0 < C'.size ∧
        C'.output + 1 = raw + C'.size ∧
        (∀ j < C'.size, j + 1 < C'.size → 0 < readsIn C' (Finset.range C'.size) (raw + j))) := by
  intro s
  induction s using Nat.strong_induction_on with
  | ind s ih =>
    intro C hsize hmono
    have hglen : C.gates.length = s := hsize
    by_cases hout_hi : raw + s ≤ C.output
    · left
      refine ⟨false, fun x hx => ?_⟩
      rw [circuit_eval_eq, getD_of_ge]
      rw [wiresAux_length, hx, hglen]
      exact hout_hi
    by_cases hout_lo : C.output < raw
    · right; left
      refine ⟨C.output, hout_lo, fun x hx => ?_⟩
      rw [circuit_eval_eq, wiresAux_getD_lt _ _ _ (hx.symm ▸ hout_lo)]
    by_cases hout_last : C.output + 1 < raw + s
    · let k := C.output - raw + 1
      let C1 : Circuit := ⟨C.gates.take k, C.output⟩
      have hklt : k < s := by omega
      have hsz1 : C1.size = k := by
        show (C.gates.take k).length = k
        rw [List.length_take]
        omega
      have hmono1 : Monotone2 C1 := fun g hg => hmono g (List.mem_of_mem_take hg)
      have hev1 : ∀ x : List Bool, x.length = raw → C1.eval x = C.eval x := by
        intro x hx
        rw [circuit_eval_eq, circuit_eval_eq]
        have hsplit := (List.take_append_drop k C.gates).symm
        conv_rhs =>
          rw [hsplit, wiresAux_append, wiresAux_getD_lt _ _ _
            (by rw [wiresAux_length, hx, List.length_take]; omega)]
      rcases ih k hklt C1 hsz1 hmono1 with ⟨b, hb⟩ | ⟨i, hi, hfi⟩ | ⟨C', hsz', hev', hrest⟩
      · exact Or.inl ⟨b, fun x hx => (hev1 x hx).symm.trans (hb x hx)⟩
      · exact Or.inr (Or.inl ⟨i, hi, fun x hx => (hev1 x hx).symm.trans (hfi x hx)⟩)
      · exact Or.inr (Or.inr ⟨C', by omega, fun x hx => (hev' x hx).trans (hev1 x hx), hrest⟩)
    have hout_eq : C.output + 1 = raw + s := by omega
    have hs_pos : 0 < s := by omega
    have hreduce_copy : ∀ j < s, ∀ u < raw + j,
        (∀ x : List Bool, x.length = raw →
          let w_pre := wiresAux (C.gates.take j) x
          (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => w_pre.getD i false) =
            w_pre.getD u false) →
        (∃ b : Bool, ∀ x : List Bool, x.length = raw → C.eval x = b) ∨
        (∃ i < raw, ∀ x : List Bool, x.length = raw → C.eval x = x.getD i false) ∨
        (∃ C' : Circuit, C'.size ≤ C.size ∧
          (∀ x : List Bool, x.length = raw → C'.eval x = C.eval x) ∧
          Monotone2 C' ∧
          (∀ g ∈ C'.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∧
          ReadsBack raw C' ∧
          0 < C'.size ∧
          C'.output + 1 = raw + C'.size ∧
          (∀ j < C'.size, j + 1 < C'.size →
            0 < readsIn C' (Finset.range C'.size) (raw + j))) := by
      intro j hj u hu heq_copy
      let jw := raw + j
      let pre := C.gates.take j
      let post := C.gates.drop (j + 1)
      let C1 : Circuit :=
        ⟨pre ++ post.map (remapCopy jw u), if C.output = jw then u else shift jw C.output⟩
      have hsz1 : C1.size = s - 1 := by
        show (pre ++ post.map (remapCopy jw u)).length = s - 1
        simp [pre, post, List.length_take, List.length_drop, hglen]
        omega
      have hmono1 : Monotone2 C1 := by
        intro g hg
        rcases List.mem_append.mp hg with hp | hq
        · exact hmono g (List.mem_of_mem_take hp)
        · rcases List.mem_map.mp hq with ⟨g0, hg0, rfl⟩
          exact mono_gate_remapCopy jw u g0 (hmono g0 (List.mem_of_mem_drop hg0))
      have hev1 : ∀ x : List Bool, x.length = raw → C1.eval x = C.eval x := by
        intro x hx
        have hj' : j < C.gates.length := hglen.symm ▸ hj
        obtain ⟨hpre_len, hCw⟩ := eval_gate_at raw C x hx j hj'
        let w_pre := wiresAux pre x
        let val_j := (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => w_pre.getD i false)
        have hlen_pre : w_pre.length = jw := hpre_len
        have hval_eq : val_j = w_pre.getD u false := heq_copy x hx
        obtain ⟨hl0, hj0, hi0⟩ := init_inv w_pre val_j
        rw [hlen_pre] at hj0 hi0
        have heq_u0 : (w_pre ++ [val_j]).getD jw false = (w_pre ++ [val_j]).getD u false := by
          rw [← hlen_pre, getD_append_right w_pre [val_j] false w_pre.length (le_refl _),
            getD_append_left w_pre [val_j] false u (hlen_pre.symm ▸ hu)]
          simpa using hval_eq
        have hsim := sim_copy jw u post (w_pre ++ [val_j]) w_pre hl0 hj0 hu heq_u0 hi0
        rw [circuit_eval_eq, circuit_eval_eq]
        show (wiresAux (pre ++ post.map (remapCopy jw u)) x).getD
          (if C.output = jw then u else shift jw C.output) false =
          (C.wires x).getD C.output false
        rw [wiresAux_append, hCw]
        change (wiresAux (post.map (remapCopy jw u)) w_pre).getD
          (if C.output = jw then u else shift jw C.output) false =
          (wiresAux post (w_pre ++ [val_j])).getD C.output false
        by_cases hco : C.output = jw
        · simp only [hco, ite_true]
          have h1 := hsim u (Nat.ne_of_lt hu)
          rw [shift_lt hu] at h1
          rw [h1, wiresAux_getD_lt post _ u (by simp; omega),
            wiresAux_getD_lt post _ jw (by simp; omega)]
          exact heq_u0.symm
        · simp only [hco, ite_false]
          exact hsim C.output hco
      rcases ih (s - 1) (by omega) C1 hsz1 hmono1 with
        ⟨b, hb⟩ | ⟨i, hi, hfi⟩ | ⟨C', hsz', hev', hrest⟩
      · exact Or.inl ⟨b, fun x hx => (hev1 x hx).symm.trans (hb x hx)⟩
      · exact Or.inr (Or.inl ⟨i, hi, fun x hx => (hev1 x hx).symm.trans (hfi x hx)⟩)
      · exact Or.inr (Or.inr ⟨C', by omega, fun x hx => (hev' x hx).trans (hev1 x hx), hrest⟩)
    have hreduce_const : ∀ j < s, ∀ b : Bool,
        (∀ x : List Bool, x.length = raw →
          let w_pre := wiresAux (C.gates.take j) x
          (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => w_pre.getD i false) = b) →
        (∃ b0 : Bool, ∀ x : List Bool, x.length = raw → C.eval x = b0) ∨
        (∃ i < raw, ∀ x : List Bool, x.length = raw → C.eval x = x.getD i false) ∨
        (∃ C' : Circuit, C'.size ≤ C.size ∧
          (∀ x : List Bool, x.length = raw → C'.eval x = C.eval x) ∧
          Monotone2 C' ∧
          (∀ g ∈ C'.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∧
          ReadsBack raw C' ∧
          0 < C'.size ∧
          C'.output + 1 = raw + C'.size ∧
          (∀ j < C'.size, j + 1 < C'.size →
            0 < readsIn C' (Finset.range C'.size) (raw + j))) := by
      intro j hj b heq_b
      let jw := raw + j
      by_cases hco : C.output = jw
      · left
        refine ⟨b, fun x hx => ?_⟩
        have hj' : j < C.gates.length := hglen.symm ▸ hj
        obtain ⟨hpre_len, hCw⟩ := eval_gate_at raw C x hx j hj'
        rw [Circuit.eval, hCw, hco]
        rw [wiresAux_getD_lt _ _ jw (by simp; omega)]
        dsimp only [jw]
        rw [← hpre_len, getD_append_right _ _ false _ (le_refl _)]
        simpa using heq_b x hx
      · let pre := C.gates.take j
        let post := C.gates.drop (j + 1)
        let remap := if b then remapTrue jw else remapFalse jw
        let C1 : Circuit := ⟨pre ++ post.map remap, shift jw C.output⟩
        have hsz1 : C1.size = s - 1 := by
          show (pre ++ post.map remap).length = s - 1
          simp [pre, post, List.length_take, List.length_drop, hglen]
          omega
        have hmono1 : Monotone2 C1 := by
          intro g hg
          rcases List.mem_append.mp hg with hp | hq
          · exact hmono g (List.mem_of_mem_take hp)
          · rcases List.mem_map.mp hq with ⟨g0, hg0, rfl⟩
            have hg0m := hmono g0 (List.mem_of_mem_drop hg0)
            cases b
            · exact mono_gate_remapFalse jw g0 hg0m
            · exact mono_gate_remapTrue jw g0 hg0m
        have hpost_mono : ∀ g ∈ post, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) :=
          fun g hg => (hmono g (List.mem_of_mem_drop hg)).1
        have hev1 : ∀ x : List Bool, x.length = raw → C1.eval x = C.eval x := by
          intro x hx
          have hj' : j < C.gates.length := hglen.symm ▸ hj
          obtain ⟨hpre_len, hCw⟩ := eval_gate_at raw C x hx j hj'
          let w_pre := wiresAux pre x
          let val_j := (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => w_pre.getD i false)
          have hlen_pre : w_pre.length = jw := hpre_len
          have hval_eq : val_j = b := heq_b x hx
          obtain ⟨hl0, hj0, hi0⟩ := init_inv w_pre val_j
          rw [hlen_pre] at hj0 hi0
          have hval0 : (w_pre ++ [val_j]).getD jw false = b := by
            rw [← hlen_pre, getD_append_right w_pre [val_j] false w_pre.length (le_refl _)]
            simpa using hval_eq
          rw [circuit_eval_eq, Circuit.eval, hCw]
          show (wiresAux (pre ++ post.map remap) x).getD (shift jw C.output) false =
            (wiresAux post (w_pre ++ [val_j])).getD C.output false
          rw [wiresAux_append]
          cases b
          · exact sim_false jw post (w_pre ++ [val_j]) w_pre hpost_mono hl0 hj0 hval0 hi0
              C.output hco
          · exact sim_true jw post (w_pre ++ [val_j]) w_pre hpost_mono hl0 hj0 hval0 hi0
              C.output hco
        rcases ih (s - 1) (by omega) C1 hsz1 hmono1 with
          ⟨b0, hb0⟩ | ⟨i, hi, hfi⟩ | ⟨C', hsz', hev', hrest⟩
        · exact Or.inl ⟨b0, fun x hx => (hev1 x hx).symm.trans (hb0 x hx)⟩
        · exact Or.inr (Or.inl ⟨i, hi, fun x hx => (hev1 x hx).symm.trans (hfi x hx)⟩)
        · exact Or.inr (Or.inr ⟨C', by omega, fun x hx => (hev' x hx).trans (hev1 x hx), hrest⟩)
    by_cases hback : ReadsBack raw C
    · by_cases hlen2 : ∀ j < s, (gateAt C j).inputs.length = 2
      · by_cases hused : ∀ j < s, j + 1 < s → 0 < readsIn C (Finset.range s) (raw + j)
        · right; right
          refine ⟨C, le_refl _, fun _ _ => rfl, hmono, ?_, hback,
            hsize.symm ▸ hs_pos, hsize.symm ▸ hout_eq, hsize.symm ▸ hused⟩
          intro g hg
          obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
          have hjm := hmono C.gates[j] hg
          have hjl := hlen2 j (hglen ▸ hj)
          rw [gateAt_eq_getElem C j hj] at hjl
          exact ⟨by simpa using hjm.1, hjl⟩
        · push Not at hused
          rcases hused with ⟨j, hjs, hjlt, hzero⟩
          let jw := raw + j
          have hzero' : readsIn C (Finset.range s) jw = 0 := Nat.le_zero.mp hzero
          let pre := C.gates.take j
          let post := C.gates.drop (j + 1)
          let C1 : Circuit := ⟨pre ++ post.map (remapUnused jw), shift jw C.output⟩
          have hsz1 : C1.size = s - 1 := by
            show (pre ++ post.map (remapUnused jw)).length = s - 1
            simp [pre, post, List.length_take, List.length_drop, hglen]
            omega
          have hmono1 : Monotone2 C1 := by
            intro g hg
            rcases List.mem_append.mp hg with hp | hq
            · exact hmono g (List.mem_of_mem_take hp)
            · rcases List.mem_map.mp hq with ⟨g0, hg0, rfl⟩
              exact mono_gate_remapUnused jw g0 (hmono g0 (List.mem_of_mem_drop hg0))
          have hun : ∀ g ∈ post, jw ∉ g.inputs := by
            intro g hg hmem
            have hmem' : g ∈ C.gates.drop (j + 1) := hg
            obtain ⟨k, hk, hgk⟩ := List.getElem_of_mem hmem'
            rw [List.getElem_drop] at hgk
            have hidx : j + 1 + k < s := by
              rw [List.length_drop] at hk
              omega
            have hcnt : 0 < (gateAt C (j + 1 + k)).inputs.count jw := by
              rw [gateAt_eq_getElem C (j + 1 + k) (hglen.symm ▸ hidx), hgk]
              exact List.count_pos_iff.mpr hmem
            have hle : (gateAt C (j + 1 + k)).inputs.count jw ≤
                readsIn C (Finset.range s) jw := by
              unfold readsIn
              exact Finset.single_le_sum (f := fun t => (gateAt C t).inputs.count jw)
                (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hidx)
            omega
          have hco : C.output ≠ jw := by omega
          have hev1 : ∀ x : List Bool, x.length = raw → C1.eval x = C.eval x := by
            intro x hx
            have hj' : j < C.gates.length := hglen.symm ▸ hjs
            obtain ⟨hpre_len, hCw⟩ := eval_gate_at raw C x hx j hj'
            let w_pre := wiresAux pre x
            let val_j := (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => w_pre.getD i false)
            obtain ⟨hl0, hj0, hi0⟩ := init_inv w_pre val_j
            rw [hpre_len] at hj0 hi0
            rw [circuit_eval_eq, Circuit.eval, hCw]
            show (wiresAux (pre ++ post.map (remapUnused jw)) x).getD (shift jw C.output) false =
              (wiresAux post (w_pre ++ [val_j])).getD C.output false
            rw [wiresAux_append]
            exact sim_unused jw post (w_pre ++ [val_j]) w_pre hun hl0 hj0 hi0 C.output hco
          rcases ih (s - 1) (by omega) C1 hsz1 hmono1 with
            ⟨b0, hb0⟩ | ⟨i, hi, hfi⟩ | ⟨C', hsz', hev', hrest⟩
          · exact Or.inl ⟨b0, fun x hx => (hev1 x hx).symm.trans (hb0 x hx)⟩
          · exact Or.inr (Or.inl ⟨i, hi, fun x hx => (hev1 x hx).symm.trans (hfi x hx)⟩)
          · exact Or.inr (Or.inr ⟨C', by omega, fun x hx => (hev' x hx).trans (hev1 x hx), hrest⟩)
      · push Not at hlen2
        rcases hlen2 with ⟨j, hjs, hne2⟩
        have hj' : j < C.gates.length := hglen.symm ▸ hjs
        have hgm : (gateAt C j).op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧
            (gateAt C j).inputs.length ≤ 2 := by
          rw [gateAt_eq_getElem C j hj']
          exact hmono C.gates[j] (List.getElem_mem hj')
        have hgop : (gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or := by
          simpa using hgm.1
        cases hin : (gateAt C j).inputs with
        | nil =>
          rcases hgop with hop | hop
          · apply hreduce_const j hjs true
            intro x _
            simp [hop, hin, GateOp.eval]
          · apply hreduce_const j hjs false
            intro x _
            simp [hop, hin, GateOp.eval]
        | cons u rest =>
          cases rest with
          | nil =>
            have hu : u < raw + j := hback j hj' u (by rw [hin]; simp)
            apply hreduce_copy j hjs u hu
            intro x _
            rcases hgop with hop | hop <;> simp [hop, hin, GateOp.eval]
          | cons v rest2 =>
            cases rest2 with
            | nil =>
              rw [hin] at hne2
              exact absurd rfl hne2
            | cons _ _ =>
              have hle := hgm.2
              rw [hin] at hle
              simp at hle
    · unfold ReadsBack at hback
      push Not at hback
      rcases hback with ⟨j, hj', bad, hbad_mem, hbad_ge⟩
      have hjs : j < s := hglen ▸ hj'
      have hgm : (gateAt C j).op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧
          (gateAt C j).inputs.length ≤ 2 := by
        rw [gateAt_eq_getElem C j hj']
        exact hmono C.gates[j] (List.getElem_mem hj')
      have hgop : (gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or := by
        simpa using hgm.1
      rcases hgop with hop | hop
      · apply hreduce_const j hjs false
        intro x hx
        have hlen_pre : (wiresAux (C.gates.take j) x).length = raw + j := by
          rw [wiresAux_length, hx, List.length_take]; omega
        simp only [hop, GateOp.eval, List.all_eq_false, List.mem_map, id_eq]
        refine ⟨false, ⟨bad, hbad_mem, getD_of_ge _ false bad (hlen_pre.symm ▸ hbad_ge)⟩, by decide⟩
      · cases hin : (gateAt C j).inputs with
        | nil =>
          rw [hin] at hbad_mem
          simp at hbad_mem
        | cons u rest =>
          cases rest with
          | nil =>
            rw [hin] at hbad_mem
            have hub : bad = u := by simpa using hbad_mem
            subst hub
            apply hreduce_const j hjs false
            intro x hx
            have hlen_pre : (wiresAux (C.gates.take j) x).length = raw + j := by
              rw [wiresAux_length, hx, List.length_take]; omega
            dsimp only
            rw [hop, hin]
            simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
              id_eq, Bool.or_false]
            exact getD_of_ge _ false bad (hlen_pre.symm ▸ hbad_ge)
          | cons v rest2 =>
            cases rest2 with
            | nil =>
              by_cases hu : u < raw + j
              · have hv : raw + j ≤ v := by
                  rw [hin] at hbad_mem
                  simp at hbad_mem
                  rcases hbad_mem with rfl | rfl
                  · omega
                  · exact hbad_ge
                apply hreduce_copy j hjs u hu
                intro x hx
                have hlen_pre : (wiresAux (C.gates.take j) x).length = raw + j := by
                  rw [wiresAux_length, hx, List.length_take]; omega
                dsimp only
                rw [hop, hin]
                simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
                  id_eq, Bool.or_false]
                rw [getD_of_ge _ false v (hlen_pre.symm ▸ hv), Bool.or_false]
              · by_cases hv : v < raw + j
                · apply hreduce_copy j hjs v hv
                  intro x hx
                  have hlen_pre : (wiresAux (C.gates.take j) x).length = raw + j := by
                    rw [wiresAux_length, hx, List.length_take]; omega
                  dsimp only
                  rw [hop, hin]
                  simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
                    id_eq, Bool.or_false]
                  rw [getD_of_ge _ false u (hlen_pre.symm ▸ Nat.le_of_not_lt hu), Bool.false_or]
                · apply hreduce_const j hjs false
                  intro x hx
                  have hlen_pre : (wiresAux (C.gates.take j) x).length = raw + j := by
                    rw [wiresAux_length, hx, List.length_take]; omega
                  dsimp only
                  rw [hop, hin]
                  simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
                    id_eq, Bool.or_false]
                  rw [getD_of_ge _ false u (hlen_pre.symm ▸ Nat.le_of_not_lt hu),
                    getD_of_ge _ false v (hlen_pre.symm ▸ Nat.le_of_not_lt hv), Bool.or_false]
            | cons _ _ =>
              have hle := hgm.2
              rw [hin] at hle
              simp at hle

theorem wiresAux_mono_skip (u0 : ℕ) (gs : List Gate) (w1 w2 : List Bool)
    (hmono : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ u0 ∉ g.inputs)
    (hlen : w1.length = w2.length)
    (hle : ∀ w, w ≠ u0 → w1.getD w false = true → w2.getD w false = true) :
    (wiresAux gs w1).length = (wiresAux gs w2).length ∧
      (∀ w, w ≠ u0 → (wiresAux gs w1).getD w false = true →
        (wiresAux gs w2).getD w false = true) := by
  induction gs generalizing w1 w2 with
  | nil => exact ⟨hlen, hle⟩
  | cons g gs ih =>
    rw [wiresAux_cons, wiresAux_cons]
    obtain ⟨hgop, hgun⟩ := hmono g (List.mem_cons_self ..)
    have hgs : ∀ g' ∈ gs, (g'.op = GateOp.and ∨ g'.op = GateOp.or) ∧ u0 ∉ g'.inputs :=
      fun g' hg' => hmono g' (List.mem_cons_of_mem _ hg')
    have hstep :
        g.op.eval (g.inputs.map fun i => w1.getD i false) = true →
        g.op.eval (g.inputs.map fun i => w2.getD i false) = true := by
      rcases hgop with hop | hop
      · simp only [hop, GateOp.eval, List.all_eq_true, List.mem_map, id_eq]
        intro h b hb
        rcases hb with ⟨i, hi, rfl⟩
        exact hle i (fun heq => hgun (heq ▸ hi)) (h _ ⟨i, hi, rfl⟩)
      · simp only [hop, GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
        rintro ⟨_, ⟨i, hi, h1⟩, rfl⟩
        exact ⟨true, ⟨i, hi, hle i (fun heq => hgun (heq ▸ hi)) h1⟩, rfl⟩
    apply ih
    · exact hgs
    · simp [hlen]
    · intro w hw h1
      by_cases hlt : w < w1.length
      · rw [getD_append_left w1 _ false w hlt] at h1
        rw [getD_append_left w2 _ false w (hlen ▸ hlt)]
        exact hle w hw h1
      · by_cases heq : w = w1.length
        · subst heq
          rw [getD_append_right w1 _ false w1.length (le_refl _)] at h1
          rw [hlen, getD_append_right w2 _ false w2.length (le_refl _)]
          simp only [Nat.sub_self, List.getD_cons_zero] at h1 ⊢
          exact hstep h1
        · rw [getD_of_ge (w1 ++ _) false w (by simp; omega)] at h1
          cases h1

theorem oneEach_length {n m : ℕ} (u : Fin n) (v : Fin m) :
    (oneEach u v).length = n + m := by
  simp [oneEach]

theorem oneEach_getD_left {n m : ℕ} (u : Fin n) (v : Fin m) (i : ℕ) (hi : i < n) :
    (oneEach u v).getD i false = decide (i = u.val) := by
  unfold oneEach
  rw [getD_append_left _ _ false i (by simp [hi])]
  simp [List.getD_eq_getElem?_getD, hi, Fin.ext_iff]

theorem oneEach_getD_right {n m : ℕ} (u : Fin n) (v : Fin m) (j : ℕ) (hj : j < m) :
    (oneEach u v).getD (n + j) false = decide (j = v.val) := by
  unfold oneEach
  rw [getD_append_right _ _ false (n + j) (by simp)]
  have hsub : n + j - (List.ofFn fun i : Fin n => decide (i = u)).length = j := by simp
  rw [hsub]
  simp [List.getD_eq_getElem?_getD, hj, Fin.ext_iff]

theorem noFour_symm {n m : ℕ} (G : Fin n → Fin m → Bool)
    (hno4 : ∀ a b : Fin n, a ≠ b →
      ((Finset.univ.filter fun v : Fin m => G a v = false) ∩
       (Finset.univ.filter fun v : Fin m => G b v = false)).card ≤ 1) :
    ∀ c d : Fin m, c ≠ d →
      ((Finset.univ.filter fun u : Fin n => G u c = false) ∩
       (Finset.univ.filter fun u : Fin n => G u d = false)).card ≤ 1 := by
  intro c d hcd
  by_contra hgt
  have h1lt : 1 < ((Finset.univ.filter fun u : Fin n => G u c = false) ∩
      (Finset.univ.filter fun u : Fin n => G u d = false)).card := by omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp h1lt
  simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  have hsub : ({c, d} : Finset (Fin m)) ⊆
      (Finset.univ.filter fun v : Fin m => G a v = false) ∩
      (Finset.univ.filter fun v : Fin m => G b v = false) := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl <;> simp [ha, hb]
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_pair hcd] at hcard
  have hle := hno4 a b hab
  omega

theorem dims_zero_or_ge_three {n m : ℕ} (G : Fin n → Fin m → Bool)
    (hdR : ∀ a : Fin n, 2 ≤ (Finset.univ.filter fun v : Fin m => G a v = false).card)
    (hdC : ∀ c : Fin m, 2 ≤ (Finset.univ.filter fun u : Fin n => G u c = false).card)
    (hno4 : ∀ a b : Fin n, a ≠ b →
      ((Finset.univ.filter fun v : Fin m => G a v = false) ∩
       (Finset.univ.filter fun v : Fin m => G b v = false)).card ≤ 1) :
    (n = 0 ∧ m = 0) ∨ (3 ≤ n ∧ 3 ≤ m) := by
  by_cases hn0 : n = 0
  · left
    refine ⟨hn0, ?_⟩
    by_contra hm0
    have h2 := hdC ⟨0, Nat.pos_of_ne_zero hm0⟩
    have hle : (Finset.univ.filter fun u : Fin n => G u ⟨0, Nat.pos_of_ne_zero hm0⟩ = false).card ≤ n := by
      simpa using Finset.card_filter_le (Finset.univ : Finset (Fin n)) _
    omega
  by_cases hm0 : m = 0
  · exfalso
    have h2 := hdR ⟨0, Nat.pos_of_ne_zero hn0⟩
    have hle : (Finset.univ.filter fun v : Fin m => G ⟨0, Nat.pos_of_ne_zero hn0⟩ v = false).card ≤ m := by
      simpa using Finset.card_filter_le (Finset.univ : Finset (Fin m)) _
    omega
  right
  have hn2 : 2 ≤ n := by
    have h2 := hdC ⟨0, Nat.pos_of_ne_zero hm0⟩
    have hle : (Finset.univ.filter fun u : Fin n => G u ⟨0, Nat.pos_of_ne_zero hm0⟩ = false).card ≤ n := by
      simpa using Finset.card_filter_le (Finset.univ : Finset (Fin n)) _
    omega
  have hm2 : 2 ≤ m := by
    have h2 := hdR ⟨0, Nat.pos_of_ne_zero hn0⟩
    have hle : (Finset.univ.filter fun v : Fin m => G ⟨0, Nat.pos_of_ne_zero hn0⟩ v = false).card ≤ m := by
      simpa using Finset.card_filter_le (Finset.univ : Finset (Fin m)) _
    omega
  have hn3 : 3 ≤ n := by
    by_contra hlt
    have hn_eq : n = 2 := by omega
    let a0 : Fin n := ⟨0, by omega⟩
    let a1 : Fin n := ⟨1, by omega⟩
    have hne : a0 ≠ a1 := by intro h; simp [a0, a1] at h
    have hall : ∀ c : Fin m, G a0 c = false ∧ G a1 c = false := by
      intro c
      have hc := hdC c
      have hsub : (Finset.univ.filter fun u : Fin n => G u c = false) = Finset.univ := by
        apply Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
        simpa [hn_eq] using hc
      have h0 : a0 ∈ Finset.univ.filter (fun u : Fin n => G u c = false) := by
        rw [hsub]; exact Finset.mem_univ _
      have h1 : a1 ∈ Finset.univ.filter (fun u : Fin n => G u c = false) := by
        rw [hsub]; exact Finset.mem_univ _
      exact ⟨(Finset.mem_filter.mp h0).2, (Finset.mem_filter.mp h1).2⟩
    have hinter : (Finset.univ.filter fun v : Fin m => G a0 v = false) ∩
        (Finset.univ.filter fun v : Fin m => G a1 v = false) = Finset.univ := by
      ext v
      simp [hall v]
    have hle := hno4 a0 a1 hne
    rw [hinter] at hle
    simp at hle
    omega
  have hm3 : 3 ≤ m := by
    have hno4C := noFour_symm G hno4
    by_contra hlt
    have hm_eq : m = 2 := by omega
    let c0 : Fin m := ⟨0, by omega⟩
    let c1 : Fin m := ⟨1, by omega⟩
    have hne : c0 ≠ c1 := by intro h; simp [c0, c1] at h
    have hall : ∀ a : Fin n, G a c0 = false ∧ G a c1 = false := by
      intro a
      have ha := hdR a
      have hsub : (Finset.univ.filter fun v : Fin m => G a v = false) = Finset.univ := by
        apply Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
        simpa [hm_eq] using ha
      have h0 : c0 ∈ Finset.univ.filter (fun v : Fin m => G a v = false) := by
        rw [hsub]; exact Finset.mem_univ _
      have h1 : c1 ∈ Finset.univ.filter (fun v : Fin m => G a v = false) := by
        rw [hsub]; exact Finset.mem_univ _
      exact ⟨(Finset.mem_filter.mp h0).2, (Finset.mem_filter.mp h1).2⟩
    have hinter : (Finset.univ.filter fun u : Fin n => G u c0 = false) ∩
        (Finset.univ.filter fun u : Fin n => G u c1 = false) = Finset.univ := by
      ext u
      simp [hall u]
    have hle := hno4C c0 c1 hne
    rw [hinter] at hle
    simp at hle
    omega
  exact ⟨hn3, hm3⟩

theorem not_const_of_graph {n m : ℕ} (G : Fin n → Fin m → Bool)
    (hn3 : 3 ≤ n) (hm3 : 3 ≤ m)
    (hdR : ∀ a : Fin n, 2 ≤ (Finset.univ.filter fun v : Fin m => G a v = false).card)
    (hno4 : ∀ a b : Fin n, a ≠ b →
      ((Finset.univ.filter fun v : Fin m => G a v = false) ∩
       (Finset.univ.filter fun v : Fin m => G b v = false)).card ≤ 1)
    (b : Bool) (hconst : ∀ u v, G u v = b) : False := by
  cases b
  · let a0 : Fin n := ⟨0, by omega⟩
    let a1 : Fin n := ⟨1, by omega⟩
    have hne : a0 ≠ a1 := by intro h; simp [a0, a1] at h
    have hinter : (Finset.univ.filter fun v : Fin m => G a0 v = false) ∩
        (Finset.univ.filter fun v : Fin m => G a1 v = false) = Finset.univ := by
      ext v; simp [hconst]
    have hle := hno4 a0 a1 hne
    rw [hinter] at hle
    simp at hle
    omega
  · have h2 := hdR ⟨0, by omega⟩
    have hempty : (Finset.univ.filter fun v : Fin m => G ⟨0, by omega⟩ v = false) = ∅ := by
      ext v; simp [hconst]
    rw [hempty] at h2
    simp at h2

theorem not_single_input_of_graph {n m : ℕ} (G : Fin n → Fin m → Bool)
    (hn3 : 3 ≤ n) (hm3 : 3 ≤ m)
    (hno4 : ∀ a b : Fin n, a ≠ b →
      ((Finset.univ.filter fun v : Fin m => G a v = false) ∩
       (Finset.univ.filter fun v : Fin m => G b v = false)).card ≤ 1)
    (i : ℕ) (hi : i < n + m)
    (hsingle : ∀ u v, G u v = (oneEach u v).getD i false) : False := by
  by_cases hin : i < n
  · have htwo : 2 ≤ (Finset.univ.erase (⟨i, hin⟩ : Fin n)).card := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _)]
      simp; omega
    obtain ⟨a1, ha1, a2, ha2, hne⟩ :=
      Finset.one_lt_card.mp (by omega : 1 < (Finset.univ.erase (⟨i, hin⟩ : Fin n)).card)
    have ha1' : a1.val ≠ i := fun h => (Finset.mem_erase.mp ha1).1 (Fin.ext h)
    have ha2' : a2.val ≠ i := fun h => (Finset.mem_erase.mp ha2).1 (Fin.ext h)
    have hf1 : ∀ v, G a1 v = false := by
      intro v; rw [hsingle, oneEach_getD_left a1 v i hin]; simp [Ne.symm ha1']
    have hf2 : ∀ v, G a2 v = false := by
      intro v; rw [hsingle, oneEach_getD_left a2 v i hin]; simp [Ne.symm ha2']
    have hinter : (Finset.univ.filter fun v : Fin m => G a1 v = false) ∩
        (Finset.univ.filter fun v : Fin m => G a2 v = false) = Finset.univ := by
      ext v; simp [hf1, hf2]
    have hle := hno4 a1 a2 hne
    rw [hinter] at hle
    simp at hle
    omega
  · have hno4C := noFour_symm G hno4
    have hj : i - n < m := by omega
    have htwo : 2 ≤ (Finset.univ.erase (⟨i - n, hj⟩ : Fin m)).card := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _)]
      simp; omega
    obtain ⟨c1, hc1, c2, hc2, hne⟩ :=
      Finset.one_lt_card.mp (by omega : 1 < (Finset.univ.erase (⟨i - n, hj⟩ : Fin m)).card)
    have hc1' : c1.val ≠ i - n := fun h => (Finset.mem_erase.mp hc1).1 (Fin.ext h)
    have hc2' : c2.val ≠ i - n := fun h => (Finset.mem_erase.mp hc2).1 (Fin.ext h)
    have hieq : n + (i - n) = i := by omega
    have hf1 : ∀ u, G u c1 = false := by
      intro u
      rw [hsingle, ← hieq, oneEach_getD_right u c1 (i - n) hj]
      simp [Ne.symm hc1']
    have hf2 : ∀ u, G u c2 = false := by
      intro u
      rw [hsingle, ← hieq, oneEach_getD_right u c2 (i - n) hj]
      simp [Ne.symm hc2']
    have hinter : (Finset.univ.filter fun u : Fin n => G u c1 = false) ∩
        (Finset.univ.filter fun u : Fin n => G u c2 = false) = Finset.univ := by
      ext u; simp [hf1, hf2]
    have hle := hno4C c1 c2 hne
    rw [hinter] at hle
    simp at hle
    omega

theorem all_raw_read {n m : ℕ} (G : Fin n → Fin m → Bool) (C : Circuit)
    (hn3 : 3 ≤ n) (hm3 : 3 ≤ m)
    (hdR : ∀ a : Fin n, 2 ≤ (Finset.univ.filter fun v : Fin m => G a v = false).card)
    (hdC : ∀ c : Fin m, 2 ≤ (Finset.univ.filter fun u : Fin n => G u c = false).card)
    (hno4 : ∀ a b : Fin n, a ≠ b →
      ((Finset.univ.filter fun v : Fin m => G a v = false) ∩
       (Finset.univ.filter fun v : Fin m => G b v = false)).card ≤ 1)
    (hmono : Monotone2 C)
    (hrep : Represents G C)
    (hout : n + m ≤ C.output) :
    ∀ w < n + m, 1 ≤ readsIn C (Finset.range C.size) w := by
  intro w hw
  by_contra hlt
  have hzero : readsIn C (Finset.range C.size) w = 0 := by omega
  have hun : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ w ∉ g.inputs := by
    intro g hg
    refine ⟨(hmono g hg).1, ?_⟩
    intro hmem
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
    have hcnt : 0 < (gateAt C j).inputs.count w := by
      rw [gateAt_eq_getElem C j hj]
      exact List.count_pos_iff.mpr hmem
    have hle : (gateAt C j).inputs.count w ≤ readsIn C (Finset.range C.size) w := by
      unfold readsIn
      exact Finset.single_le_sum (f := fun t => (gateAt C t).inputs.count w)
        (fun _ _ => Nat.zero_le _)
        (Finset.mem_range.mpr (show j < C.size from hj))
    omega
  have hne_out : C.output ≠ w := by omega
  by_cases hwn : w < n
  · let u0 : Fin n := ⟨w, hwn⟩
    have hle_row : ∀ (u : Fin n) (v : Fin m), G u0 v = true → G u v = true := by
      intro u v htrue
      have h1 : (wiresAux C.gates (oneEach u0 v)).getD C.output false = true := by
        rw [← circuit_eval_eq, hrep u0 v]; exact htrue
      have h2 := (wiresAux_mono_skip w C.gates (oneEach u0 v) (oneEach u v) hun
        (by rw [oneEach_length, oneEach_length]) ?_).2 C.output hne_out h1
      · rw [← circuit_eval_eq, hrep u v] at h2; exact h2
      · intro k hkw hk1
        by_cases hkn : k < n
        · rw [oneEach_getD_left u0 v k hkn] at hk1
          simp only [decide_eq_true_eq] at hk1
          exact absurd hk1 hkw
        · by_cases hkm : k < n + m
          · have hkeq : k = n + (k - n) := by omega
            rw [hkeq, oneEach_getD_right u0 v (k - n) (by omega)] at hk1
            rw [hkeq, oneEach_getD_right u v (k - n) (by omega)]
            exact hk1
          · rw [getD_of_ge (oneEach u0 v) false k (by rw [oneEach_length]; omega)] at hk1
            cases hk1
    let u1 : Fin n := if u0.val = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩
    have hne : u1 ≠ u0 := by
      intro h
      dsimp only [u1] at h
      split_ifs at h with h0
      · have := congrArg Fin.val h; simp at this; omega
      · have := congrArg Fin.val h; simp at this; exact h0 this.symm
    have hsub : (Finset.univ.filter fun v : Fin m => G u1 v = false) ⊆
        (Finset.univ.filter fun v : Fin m => G u0 v = false) ∩
        (Finset.univ.filter fun v : Fin m => G u1 v = false) := by
      intro v hv
      simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
      refine ⟨?_, hv⟩
      cases h0 : G u0 v
      · rfl
      · have ht := hle_row u1 v h0
        rw [hv] at ht
        cases ht
    have hcard := (hdR u1).trans (Finset.card_le_card hsub)
    have hle := hno4 u0 u1 hne.symm
    omega
  · have hno4C := noFour_symm G hno4
    let v0 : Fin m := ⟨w - n, by omega⟩
    have hweq : w = n + v0.val := by simp [v0]; omega
    have hle_col : ∀ (u : Fin n) (v : Fin m), G u v0 = true → G u v = true := by
      intro u v htrue
      have h1 : (wiresAux C.gates (oneEach u v0)).getD C.output false = true := by
        rw [← circuit_eval_eq, hrep u v0]; exact htrue
      have h2 := (wiresAux_mono_skip w C.gates (oneEach u v0) (oneEach u v) hun
        (by rw [oneEach_length, oneEach_length]) ?_).2 C.output hne_out h1
      · rw [← circuit_eval_eq, hrep u v] at h2; exact h2
      · intro k hkw hk1
        by_cases hkn : k < n
        · rw [oneEach_getD_left u v0 k hkn] at hk1
          rw [oneEach_getD_left u v k hkn]
          exact hk1
        · by_cases hkm : k < n + m
          · have hkeq : k = n + (k - n) := by omega
            rw [hkeq, oneEach_getD_right u v0 (k - n) (by omega)] at hk1
            simp only [decide_eq_true_eq] at hk1
            have : k = w := by omega
            exact absurd this hkw
          · rw [getD_of_ge (oneEach u v0) false k (by rw [oneEach_length]; omega)] at hk1
            cases hk1
    let v1 : Fin m := if v0.val = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩
    have hne : v1 ≠ v0 := by
      intro h
      dsimp only [v1] at h
      split_ifs at h with h0
      · have := congrArg Fin.val h; simp at this; omega
      · have := congrArg Fin.val h; simp at this; exact h0 this.symm
    have hsub : (Finset.univ.filter fun u : Fin n => G u v1 = false) ⊆
        (Finset.univ.filter fun u : Fin n => G u v0 = false) ∩
        (Finset.univ.filter fun u : Fin n => G u v1 = false) := by
      intro u hu
      simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
      refine ⟨?_, hu⟩
      cases h0 : G u v0
      · rfl
      · have ht := hle_col u v1 h0
        rw [hu] at ht
        cases ht
    have hcard := (hdC v1).trans (Finset.card_le_card hsub)
    have hle := hno4C v0 v1 hne.symm
    omega

theorem sum_count_eq_length (S : Finset ℕ) (l : List ℕ) (hl : ∀ x ∈ l, x ∈ S) :
    ∑ w ∈ S, l.count w = l.length := by
  induction l with
  | nil => simp
  | cons a tl ih =>
    have ha : a ∈ S := hl a (List.mem_cons_self ..)
    have htl : ∀ x ∈ tl, x ∈ S := fun x hx => hl x (List.mem_cons_of_mem _ hx)
    simp only [List.count_cons, beq_iff_eq, Finset.sum_add_distrib, List.length_cons]
    rw [ih htl]
    have h1 : ∑ w ∈ S, (if a == w then 1 else 0) = 1 := by
      simp [beq_iff_eq, ha]
    have h2 : (∑ w ∈ S, if a = w then 1 else 0) = 1 := by
      simp [Finset.sum_ite_eq, ha]
    have h3 : (∑ w ∈ S, if w = a then 1 else 0) = 1 := by
      simp [Finset.sum_ite_eq', ha]
    omega

theorem handshaking (N : ℕ) (hN : 1 ≤ N) (C : Circuit)
    (hshape : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hback : ReadsBack N C)
    (hsz : 0 < C.size)
    (hraw : ∀ w < N, 1 ≤ readsIn C (Finset.range C.size) w)
    (hused : ∀ j < C.size, j + 1 < C.size → 0 < readsIn C (Finset.range C.size) (N + j)) :
    let reads := readsIn C (Finset.range C.size)
    let shared := (Finset.range (N + C.size)).filter (fun w => 2 ≤ reads w)
    let D := ∑ w ∈ shared, (reads w - 1)
    C.size = N - 1 + D ∧
      (∑ w ∈ shared, reads w) = D + shared.card ∧
      shared.card ≤ D := by
  dsimp only
  let reads := readsIn C (Finset.range C.size)
  let shared := (Finset.range (N + C.size)).filter (fun w => 2 ≤ reads w)
  let D := ∑ w ∈ shared, (reads w - 1)
  change C.size = N - 1 + D ∧ (∑ w ∈ shared, reads w) = D + shared.card ∧ shared.card ≤ D
  have hlen_sz : C.gates.length = C.size := rfl
  have hsum_all : ∑ w ∈ Finset.range (N + C.size), reads w = 2 * C.size := by
    change ∑ w ∈ Finset.range (N + C.size),
      ∑ j ∈ Finset.range C.size, (gateAt C j).inputs.count w = 2 * C.size
    rw [Finset.sum_comm]
    have heach : ∀ j ∈ Finset.range C.size,
        ∑ w ∈ Finset.range (N + C.size), (gateAt C j).inputs.count w = 2 := by
      intro j hj
      have hj' : j < C.gates.length := Finset.mem_range.mp hj
      rw [sum_count_eq_length]
      · rw [gateAt_eq_getElem C j hj']
        exact (hshape C.gates[j] (List.getElem_mem hj')).2
      · intro i hi
        exact Finset.mem_range.mpr (Nat.lt_trans (hback j hj' i hi) (by omega))
    rw [Finset.sum_congr rfl heach]
    simp [mul_comm]
  have hlast_zero : reads (N + C.size - 1) = 0 := by
    change ∑ j ∈ Finset.range C.size, (gateAt C j).inputs.count (N + C.size - 1) = 0
    apply Finset.sum_eq_zero
    intro j hj
    have hj' : j < C.gates.length := Finset.mem_range.mp hj
    rw [List.count_eq_zero]
    intro hmem
    have hlt := hback j hj' _ hmem
    omega
  have hlast_not_mem : N + C.size - 1 ∉ shared := by
    intro hm
    have h2 := (Finset.mem_filter.mp hm).2
    omega
  have hsub_shared : shared ⊆ Finset.range (N + C.size - 1) := by
    intro w hw
    have hr := Finset.mem_range.mp (Finset.mem_filter.mp hw).1
    have hne : w ≠ N + C.size - 1 := fun h => hlast_not_mem (h ▸ hw)
    exact Finset.mem_range.mpr (by omega)
  have hpos_init : ∀ w ∈ Finset.range (N + C.size - 1), 1 ≤ reads w := by
    intro w hw
    have hwlt := Finset.mem_range.mp hw
    by_cases hwn : w < N
    · exact hraw w hwn
    · have hj : w - N < C.size := by omega
      have hj1 : w - N + 1 < C.size := by omega
      have hweq : N + (w - N) = w := by omega
      have hp := hused (w - N) hj hj1
      rw [hweq] at hp
      exact hp
  have hsum_init : ∑ w ∈ Finset.range (N + C.size - 1), reads w = 2 * C.size := by
    have hsplit : Finset.range (N + C.size) =
        insert (N + C.size - 1) (Finset.range (N + C.size - 1)) := by
      conv_lhs => rw [show N + C.size = (N + C.size - 1) + 1 by omega]
      exact Finset.range_add_one
    rw [hsplit, Finset.sum_insert (by simp)] at hsum_all
    omega
  have hones : ∀ w ∈ Finset.range (N + C.size - 1) \ shared, reads w = 1 := by
    intro w hw
    obtain ⟨hr, hns⟩ := Finset.mem_sdiff.mp hw
    have hge := hpos_init w hr
    have hlt : ¬ (2 ≤ reads w) := by
      intro h2
      apply hns
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by have := Finset.mem_range.mp hr; omega), h2⟩
    omega
  have hsum_split : ∑ w ∈ Finset.range (N + C.size - 1), reads w =
      ∑ w ∈ shared, reads w + ∑ w ∈ Finset.range (N + C.size - 1) \ shared, reads w := by
    rw [← Finset.sum_sdiff hsub_shared, add_comm]
  have hsum_ones : ∑ w ∈ Finset.range (N + C.size - 1) \ shared, reads w =
      (Finset.range (N + C.size - 1) \ shared).card := by
    rw [Finset.sum_congr rfl hones]
    simp
  have hcard_sdiff : (Finset.range (N + C.size - 1) \ shared).card + shared.card =
      N + C.size - 1 := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub_shared, Finset.card_range]
    have hle := Finset.card_le_card hsub_shared
    rw [Finset.card_range] at hle
    omega
  have hD_add : D + shared.card = ∑ w ∈ shared, reads w := by
    calc D + shared.card
        = (∑ w ∈ shared, (reads w - 1)) + ∑ _w ∈ shared, 1 := by simp [D]
      _ = ∑ w ∈ shared, (reads w - 1 + 1) := by rw [← Finset.sum_add_distrib]
      _ = ∑ w ∈ shared, reads w := by
          apply Finset.sum_congr rfl
          intro w hw
          have h2 := (Finset.mem_filter.mp hw).2
          omega
  have hcard_le_D : shared.card ≤ D := by
    calc shared.card = ∑ _w ∈ shared, 1 := by simp
      _ ≤ ∑ w ∈ shared, (reads w - 1) := by
        apply Finset.sum_le_sum
        intro w hw
        have h2 := (Finset.mem_filter.mp hw).2
        omega
  refine ⟨?_, hD_add.symm, hcard_le_D⟩
  omega

theorem deg_le_other_minus_one {n m : ℕ} (G : Fin n → Fin m → Bool)
    (hdR : ∀ a : Fin n, 2 ≤ (Finset.univ.filter fun v : Fin m => G a v = false).card)
    (hno4 : ∀ a b : Fin n, a ≠ b →
      ((Finset.univ.filter fun v : Fin m => G a v = false) ∩
       (Finset.univ.filter fun v : Fin m => G b v = false)).card ≤ 1)
    (c : Fin m) :
    (Finset.univ.filter fun u : Fin n => G u c = false).card ≤ m - 1 := by
  classical
  let nc := Finset.univ.filter fun u : Fin n => G u c = false
  have hex : ∀ u ∈ nc, ∃ v ∈ (Finset.univ.erase c : Finset (Fin m)), G u v = false := by
    intro u hu
    have h2 := hdR u
    have hne : ((Finset.univ.filter fun v : Fin m => G u v = false).erase c).Nonempty := by
      apply Finset.card_pos.mp
      have := Finset.card_erase_le (s := Finset.univ.filter fun v : Fin m => G u v = false) (a := c)
      have hge := Finset.pred_card_le_card_erase (s := Finset.univ.filter fun v : Fin m => G u v = false) (a := c)
      omega
    obtain ⟨v, hv⟩ := hne
    obtain ⟨hvc, hvf⟩ := Finset.mem_erase.mp hv
    exact ⟨v, Finset.mem_erase.mpr ⟨hvc, Finset.mem_univ v⟩, (Finset.mem_filter.mp hvf).2⟩
  choose f hf_mem hf_false using hex
  have hinj : ∀ a (ha : a ∈ nc) b (hb : b ∈ nc), f a ha = f b hb → a = b := by
    intro a ha b hb heq
    by_contra hab
    have hvc : f a ha ≠ c := (Finset.mem_erase.mp (hf_mem a ha)).1
    have hsub : ({c, f a ha} : Finset (Fin m)) ⊆
        (Finset.univ.filter fun v : Fin m => G a v = false) ∩
        (Finset.univ.filter fun v : Fin m => G b v = false) := by
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl
      · simp [(Finset.mem_filter.mp ha).2, (Finset.mem_filter.mp hb).2]
      · exact Finset.mem_inter.mpr
          ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf_false a ha⟩,
           Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [heq]; exact hf_false b hb⟩⟩
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_pair hvc.symm] at hcard
    have hle := hno4 a b hab
    omega
  have hle : nc.card ≤ (Finset.univ.erase c : Finset (Fin m)).card :=
    Finset.card_le_card_of_injOn (fun a => if ha : a ∈ nc then f a ha else c)
      (fun a ha => by
        have ha' : a ∈ nc := ha
        simp only [ha', dite_true]
        exact hf_mem a ha')
      (fun a ha b hb h => by
        have ha' : a ∈ nc := ha
        have hb' : b ∈ nc := hb
        simp only [ha', hb', dite_true] at h
        exact hinj a ha' b hb' h)
  rw [Finset.card_erase_of_mem (Finset.mem_univ c)] at hle
  simpa [nc] using hle

theorem pair_count_rows {n m : ℕ} (G : Fin n → Fin m → Bool)
    (hno4 : ∀ a b : Fin n, a ≠ b →
      ((Finset.univ.filter fun v : Fin m => G a v = false) ∩
       (Finset.univ.filter fun v : Fin m => G b v = false)).card ≤ 1) :
    ∑ a : Fin n,
      (Finset.univ.filter fun v : Fin m => G a v = false).card *
        ((Finset.univ.filter fun v : Fin m => G a v = false).card - 1) ≤ m * (m - 1) := by
  let nbr := fun a : Fin n => Finset.univ.filter fun v : Fin m => G a v = false
  have hdisj : Set.PairwiseDisjoint (Finset.univ : Finset (Fin n)) (fun a => (nbr a).offDiag) := by
    intro a _ b _ hab
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro p hpa hpb
    rw [Finset.mem_offDiag] at hpa hpb
    have hsub : ({p.1, p.2} : Finset (Fin m)) ⊆ nbr a ∩ nbr b := by
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl
      · exact Finset.mem_inter.mpr ⟨hpa.1, hpb.1⟩
      · exact Finset.mem_inter.mpr ⟨hpa.2.1, hpb.2.1⟩
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_pair hpa.2.2] at hcard
    have hle : (nbr a ∩ nbr b).card ≤ 1 := hno4 a b hab
    omega
  have hbi : (Finset.univ.biUnion fun a : Fin n => (nbr a).offDiag) ⊆
      (Finset.univ : Finset (Fin m)).offDiag := by
    intro p hp
    rcases Finset.mem_biUnion.mp hp with ⟨a, _, hpa⟩
    rw [Finset.mem_offDiag] at hpa ⊢
    exact ⟨Finset.mem_univ _, Finset.mem_univ _, hpa.2.2⟩
  have hcard_le := Finset.card_le_card hbi
  rw [Finset.card_biUnion hdisj] at hcard_le
  have hoff : ∀ s : Finset (Fin m), s.offDiag.card = s.card * (s.card - 1) := by
    intro s
    rw [Finset.offDiag_card]
    cases h : s.card with
    | zero => simp
    | succ k =>
      have hk : (k + 1) * (k + 1) = (k + 1) * k + (k + 1) := by ring
      have hsub : (k + 1) * (k + 1) - (k + 1) = (k + 1) * k := by omega
      simpa using hsub
  simpa [hoff] using hcard_le

theorem card_bool_split {α : Type*} [Fintype α] (f : α → Bool) :
    (Finset.univ.filter fun x => f x = true).card +
    (Finset.univ.filter fun x => f x = false).card = Fintype.card α := by
  classical
  have hu : (Finset.univ.filter fun x => f x = true) ∪
      (Finset.univ.filter fun x => f x = false) = Finset.univ := by
    ext x
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    cases f x <;> simp
  have hdj : Disjoint (Finset.univ.filter fun x => f x = true)
      (Finset.univ.filter fun x => f x = false) := by
    rw [Finset.disjoint_left]
    intro x h1 h2
    have h1' := (Finset.mem_filter.mp h1).2
    have h2' := (Finset.mem_filter.mp h2).2
    rw [h1'] at h2'
    cases h2'
  rw [← Finset.card_union_of_disjoint hdj, hu, Finset.card_univ]

theorem fewR_le_one_of_ge_eight {n m : ℕ} (G : Fin n → Fin m → Bool)
    (hm : 8 ≤ m)
    (hno4 : ∀ a b : Fin n, a ≠ b →
      ((Finset.univ.filter fun v : Fin m => G a v = false) ∩
       (Finset.univ.filter fun v : Fin m => G b v = false)).card ≤ 1) :
    (Finset.univ.filter fun r : Fin n =>
      (Finset.univ.filter fun v : Fin m => G r v = true).card ≤ 3).card ≤ 1 := by
  by_contra hgt
  let S := Finset.univ.filter fun r : Fin n =>
    (Finset.univ.filter fun v : Fin m => G r v = true).card ≤ 3
  change ¬ (S.card ≤ 1) at hgt
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < S.card)
  have hpa := (Finset.mem_filter.mp ha).2
  have hpb := (Finset.mem_filter.mp hb).2
  have hcomp : ∀ r : Fin n,
      (Finset.univ.filter fun v : Fin m => G r v = true).card +
      (Finset.univ.filter fun v : Fin m => G r v = false).card = m := by
    intro r
    simpa using card_bool_split (fun v : Fin m => G r v)
  have hna : m - 3 ≤ (Finset.univ.filter fun v : Fin m => G a v = false).card := by
    have := hcomp a; omega
  have hnb : m - 3 ≤ (Finset.univ.filter fun v : Fin m => G b v = false).card := by
    have := hcomp b; omega
  have hu := Finset.card_union_add_card_inter
    (Finset.univ.filter fun v : Fin m => G a v = false)
    (Finset.univ.filter fun v : Fin m => G b v = false)
  have hule : ((Finset.univ.filter fun v : Fin m => G a v = false) ∪
      (Finset.univ.filter fun v : Fin m => G b v = false)).card ≤ m := by
    simpa using Finset.card_le_univ
      ((Finset.univ.filter fun v : Fin m => G a v = false) ∪
       (Finset.univ.filter fun v : Fin m => G b v = false))
  have hile := hno4 a b hab
  omega

theorem few_sum_le_two_of_m_le_seven {n m : ℕ} (G : Fin n → Fin m → Bool)
    (hN : 17 ≤ n + m) (hm7 : m ≤ 7)
    (hdR : ∀ a : Fin n, 2 ≤ (Finset.univ.filter fun v : Fin m => G a v = false).card)
    (hno4 : ∀ a b : Fin n, a ≠ b →
      ((Finset.univ.filter fun v : Fin m => G a v = false) ∩
       (Finset.univ.filter fun v : Fin m => G b v = false)).card ≤ 1) :
    (Finset.univ.filter fun r : Fin n =>
      (Finset.univ.filter fun v : Fin m => G r v = true).card ≤ 3).card +
    (Finset.univ.filter fun c : Fin m =>
      (Finset.univ.filter fun u : Fin n => G u c = true).card ≤ 3).card ≤ 2 := by
  have hn10 : 10 ≤ n := by omega
  have hfewC_zero : (Finset.univ.filter fun c : Fin m =>
      (Finset.univ.filter fun u : Fin n => G u c = true).card ≤ 3).card = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro c _ hle
    have hcomp : (Finset.univ.filter fun u : Fin n => G u c = true).card +
        (Finset.univ.filter fun u : Fin n => G u c = false).card = n := by
      simpa using card_bool_split (fun u : Fin n => G u c)
    have hdeg := deg_le_other_minus_one G hdR hno4 c
    omega
  rw [hfewC_zero, Nat.add_zero]
  let fewR := Finset.univ.filter fun r : Fin n =>
    (Finset.univ.filter fun v : Fin m => G r v = true).card ≤ 3
  let nbr := fun r : Fin n => Finset.univ.filter fun v : Fin m => G r v = false
  have hpc : ∑ a : Fin n, (nbr a).card * ((nbr a).card - 1) ≤ m * (m - 1) :=
    pair_count_rows G hno4
  have hcompR : ∀ r : Fin n,
      (Finset.univ.filter fun v : Fin m => G r v = true).card + (nbr r).card = m := by
    intro r
    simpa [nbr] using card_bool_split (fun v : Fin m => G r v)
  have h2n : 2 * n ≤ m * (m - 1) := by
    calc 2 * n = ∑ _a : Fin n, 2 := by simp [mul_comm]
      _ ≤ ∑ a : Fin n, (nbr a).card * ((nbr a).card - 1) := by
        apply Finset.sum_le_sum
        intro a _
        have h2 : 2 ≤ (nbr a).card := hdR a
        have h1 : 1 ≤ (nbr a).card - 1 := by omega
        calc 2 = 2 * 1 := by ring
          _ ≤ (nbr a).card * ((nbr a).card - 1) := Nat.mul_le_mul h2 h1
      _ ≤ m * (m - 1) := hpc
  have hm6 : 6 ≤ m := by
    by_contra hlt
    have hm5 : m ≤ 5 := by omega
    have : m * (m - 1) ≤ 20 := by
      interval_cases m <;> decide
    omega
  have hsplit : ∑ a : Fin n, (nbr a).card * ((nbr a).card - 1) =
      ∑ a ∈ fewR, (nbr a).card * ((nbr a).card - 1) +
      ∑ a ∈ Finset.univ \ fewR, (nbr a).card * ((nbr a).card - 1) := by
    rw [← Finset.sum_sdiff (Finset.subset_univ fewR), add_comm]
  have hrest : 2 * (n - fewR.card) ≤
      ∑ a ∈ Finset.univ \ fewR, (nbr a).card * ((nbr a).card - 1) := by
    have hcard_sd : (Finset.univ \ fewR).card = n - fewR.card := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.subset_univ fewR)]
      simp
    calc 2 * (n - fewR.card) = ∑ _a ∈ Finset.univ \ fewR, 2 := by simp [hcard_sd, mul_comm]
      _ ≤ ∑ a ∈ Finset.univ \ fewR, (nbr a).card * ((nbr a).card - 1) := by
        apply Finset.sum_le_sum
        intro a _
        have h2 : 2 ≤ (nbr a).card := hdR a
        have h1 : 1 ≤ (nbr a).card - 1 := by omega
        calc 2 = 2 * 1 := by ring
          _ ≤ (nbr a).card * ((nbr a).card - 1) := Nat.mul_le_mul h2 h1
  have hfew_le_n : fewR.card ≤ n := by simpa using Finset.card_le_univ fewR
  change fewR.card ≤ 2
  by_cases hm_eq : m = 6
  · have hn11 : 11 ≤ n := by omega
    have hfew_sum : 6 * fewR.card ≤ ∑ a ∈ fewR, (nbr a).card * ((nbr a).card - 1) := by
      calc 6 * fewR.card = ∑ _a ∈ fewR, 6 := by simp [mul_comm]
        _ ≤ ∑ a ∈ fewR, (nbr a).card * ((nbr a).card - 1) := by
          apply Finset.sum_le_sum
          intro a ha
          have hp := (Finset.mem_filter.mp ha).2
          have hc := hcompR a
          have h3 : 3 ≤ (nbr a).card := by omega
          have h2 : 2 ≤ (nbr a).card - 1 := by omega
          calc 6 = 3 * 2 := by ring
            _ ≤ (nbr a).card * ((nbr a).card - 1) := Nat.mul_le_mul h3 h2
    have hpc30 : ∑ a : Fin n, (nbr a).card * ((nbr a).card - 1) ≤ 30 := by
      calc ∑ a : Fin n, (nbr a).card * ((nbr a).card - 1) ≤ m * (m - 1) := hpc
        _ = 30 := by rw [hm_eq]
    omega
  · have hm_eq7 : m = 7 := by omega
    have hfew_sum : 12 * fewR.card ≤ ∑ a ∈ fewR, (nbr a).card * ((nbr a).card - 1) := by
      calc 12 * fewR.card = ∑ _a ∈ fewR, 12 := by simp [mul_comm]
        _ ≤ ∑ a ∈ fewR, (nbr a).card * ((nbr a).card - 1) := by
          apply Finset.sum_le_sum
          intro a ha
          have hp := (Finset.mem_filter.mp ha).2
          have hc := hcompR a
          have h4 : 4 ≤ (nbr a).card := by omega
          have h3 : 3 ≤ (nbr a).card - 1 := by omega
          calc 12 = 4 * 3 := by ring
            _ ≤ (nbr a).card * ((nbr a).card - 1) := Nat.mul_le_mul h4 h3
    have hpc42 : ∑ a : Fin n, (nbr a).card * ((nbr a).card - 1) ≤ 42 := by
      calc ∑ a : Fin n, (nbr a).card * ((nbr a).card - 1) ≤ m * (m - 1) := hpc
        _ = 42 := by rw [hm_eq7]
    omega

theorem few_sum_le_two {n m : ℕ} (G : Fin n → Fin m → Bool)
    (hN : 17 ≤ n + m)
    (hdR : ∀ a : Fin n, 2 ≤ (Finset.univ.filter fun v : Fin m => G a v = false).card)
    (hdC : ∀ c : Fin m, 2 ≤ (Finset.univ.filter fun u : Fin n => G u c = false).card)
    (hno4 : ∀ a b : Fin n, a ≠ b →
      ((Finset.univ.filter fun v : Fin m => G a v = false) ∩
       (Finset.univ.filter fun v : Fin m => G b v = false)).card ≤ 1) :
    (Finset.univ.filter fun r : Fin n =>
      (Finset.univ.filter fun v : Fin m => G r v = true).card ≤ 3).card +
    (Finset.univ.filter fun c : Fin m =>
      (Finset.univ.filter fun u : Fin n => G u c = true).card ≤ 3).card ≤ 2 := by
  by_cases hm7 : m ≤ 7
  · exact few_sum_le_two_of_m_le_seven G hN hm7 hdR hno4
  by_cases hn7 : n ≤ 7
  · have hno4C := noFour_symm G hno4
    have h := few_sum_le_two_of_m_le_seven (fun c r => G r c) (by omega) hn7 hdC hno4C
    omega
  · have h1 := fewR_le_one_of_ge_eight G (by omega) hno4
    have h2 := fewR_le_one_of_ge_eight (fun c r => G r c) (by omega) (noFour_symm G hno4)
    omega

theorem biUnion_card_eq_sum (L : List (Finset ℕ))
    (hdisj : L.Pairwise Disjoint) :
    (L.toFinset.biUnion fun S => S).card = (L.map Finset.card).sum := by
  induction L with
  | nil => simp
  | cons A tl ih =>
    rw [List.pairwise_cons] at hdisj
    rw [List.toFinset_cons, Finset.biUnion_insert, List.map_cons, List.sum_cons]
    have hdj : Disjoint A (tl.toFinset.biUnion fun S => S) := by
      rw [Finset.disjoint_biUnion_right]
      intro B hB
      exact hdisj.1 B (List.mem_toFinset.mp hB)
    rw [Finset.card_union_of_disjoint hdj, ih hdisj.2]

theorem sum_inter_le_card (L : List (Finset ℕ)) (U : Finset ℕ)
    (hdisj : L.Pairwise Disjoint) :
    (L.map fun S => (S ∩ U).card).sum ≤ U.card := by
  have hsub : ∀ K : List (Finset ℕ), K.Pairwise Disjoint →
      (K.map fun S => (S ∩ U).card).sum = ((K.toFinset.biUnion fun S => S) ∩ U).card := by
    intro K
    induction K with
    | nil => intro _; simp
    | cons A tl ih =>
      intro hd
      rw [List.pairwise_cons] at hd
      rw [List.map_cons, List.sum_cons, List.toFinset_cons, Finset.biUnion_insert,
        Finset.union_inter_distrib_right]
      have hdj : Disjoint (A ∩ U) ((tl.toFinset.biUnion fun S => S) ∩ U) := by
        apply Disjoint.mono Finset.inter_subset_left Finset.inter_subset_left
        rw [Finset.disjoint_biUnion_right]
        intro B hB
        exact hd.1 B (List.mem_toFinset.mp hB)
      rw [Finset.card_union_of_disjoint hdj, ih hd.2]
  rw [hsub L hdisj]
  exact Finset.card_le_card Finset.inter_subset_right

theorem list_sum_le_of_forall {α : Type*} (L : List α) (f g : α → ℕ)
    (h : ∀ x ∈ L, f x ≤ g x) :
    (L.map f).sum ≤ (L.map g).sum := by
  induction L with
  | nil => simp
  | cons a tl ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (h a (List.mem_cons_self ..))
      (ih fun x hx => h x (List.mem_cons_of_mem _ hx))

theorem split_block {n m : ℕ} (S : Finset ℕ) (hS : S ⊆ Finset.range (n + m)) :
    let R : Finset (Fin n) := Finset.univ.filter (fun r => r.val ∈ S)
    let B : Finset (Fin m) := Finset.univ.filter (fun c => n + c.val ∈ S)
    R.image (fun r => r.val) ∪ B.image (fun c => n + c.val) = S ∧
      S.card = R.card + B.card := by
  dsimp only
  let R : Finset (Fin n) := Finset.univ.filter (fun r => r.val ∈ S)
  let B : Finset (Fin m) := Finset.univ.filter (fun c => n + c.val ∈ S)
  have heq : R.image (fun r => r.val) ∪ B.image (fun c => n + c.val) = S := by
    ext w
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
      R, B]
    constructor
    · rintro (⟨r, hr, rfl⟩ | ⟨c, hc, rfl⟩) <;> assumption
    · intro hw
      have hlt := Finset.mem_range.mp (hS hw)
      by_cases hwn : w < n
      · exact Or.inl ⟨⟨w, hwn⟩, hw, rfl⟩
      · exact Or.inr ⟨⟨w - n, by omega⟩,
          by simpa [Nat.add_sub_cancel' (Nat.le_of_not_lt hwn)] using hw,
          by simp; omega⟩
  have hdj : Disjoint (R.image (fun r => r.val)) (B.image (fun c => n + c.val)) := by
    rw [Finset.disjoint_left]
    intro w h1 h2
    rcases Finset.mem_image.mp h1 with ⟨r, _, rfl⟩
    rcases Finset.mem_image.mp h2 with ⟨c, _, hc⟩
    omega
  have hcard : S.card = R.card + B.card := by
    rw [← heq, Finset.card_union_of_disjoint hdj,
      Finset.card_image_of_injective _ Fin.val_injective,
      Finset.card_image_of_injective _ (fun a b h => Fin.ext (by omega))]
  exact ⟨heq, hcard⟩

theorem block_few_card {n m : ℕ} (G : Fin n → Fin m → Bool)
    (S : Finset ℕ) (_hS : S ⊆ Finset.range (n + m)) :
    let R : Finset (Fin n) := Finset.univ.filter (fun r => r.val ∈ S)
    let B : Finset (Fin m) := Finset.univ.filter (fun c => n + c.val ∈ S)
    let fewR_all := Finset.univ.filter (fun r : Fin n =>
      (Finset.univ.filter fun v : Fin m => G r v = true).card ≤ 3)
    let fewC_all := Finset.univ.filter (fun c : Fin m =>
      (Finset.univ.filter fun u : Fin n => G u c = true).card ≤ 3)
    let fewWires := fewR_all.image (fun r => r.val) ∪ fewC_all.image (fun c => n + c.val)
    (R.filter fun r => (Finset.univ.filter fun v : Fin m => G r v = true).card ≤ 3).card +
    (B.filter fun c => (Finset.univ.filter fun u : Fin n => G u c = true).card ≤ 3).card =
      (S ∩ fewWires).card := by
  dsimp only
  let R : Finset (Fin n) := Finset.univ.filter (fun r => r.val ∈ S)
  let B : Finset (Fin m) := Finset.univ.filter (fun c => n + c.val ∈ S)
  let fewR := R.filter fun r => (Finset.univ.filter fun v : Fin m => G r v = true).card ≤ 3
  let fewC := B.filter fun c => (Finset.univ.filter fun u : Fin n => G u c = true).card ≤ 3
  let fewR_all := Finset.univ.filter (fun r : Fin n =>
    (Finset.univ.filter fun v : Fin m => G r v = true).card ≤ 3)
  let fewC_all := Finset.univ.filter (fun c : Fin m =>
    (Finset.univ.filter fun u : Fin n => G u c = true).card ≤ 3)
  let fewWires := fewR_all.image (fun r => r.val) ∪ fewC_all.image (fun c => n + c.val)
  have heq : fewR.image (fun r => r.val) ∪ fewC.image (fun c => n + c.val) = S ∩ fewWires := by
    ext w
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_image, Finset.mem_filter,
      Finset.mem_univ, true_and, fewR, fewC, R, B, fewWires, fewR_all, fewC_all]
    constructor
    · rintro (⟨r, ⟨hrS, hr3⟩, rfl⟩ | ⟨c, ⟨hcS, hc3⟩, rfl⟩)
      · exact ⟨hrS, Or.inl ⟨r, hr3, rfl⟩⟩
      · exact ⟨hcS, Or.inr ⟨c, hc3, rfl⟩⟩
    · rintro ⟨hwS, ⟨r, hr3, rfl⟩ | ⟨c, hc3, rfl⟩⟩
      · exact Or.inl ⟨r, ⟨hwS, hr3⟩, rfl⟩
      · exact Or.inr ⟨c, ⟨hwS, hc3⟩, rfl⟩
  have hdj : Disjoint (fewR.image (fun r => r.val)) (fewC.image (fun c => n + c.val)) := by
    rw [Finset.disjoint_left]
    intro w h1 h2
    rcases Finset.mem_image.mp h1 with ⟨r, _, rfl⟩
    rcases Finset.mem_image.mp h2 with ⟨c, _, hc⟩
    omega
  rw [← heq, Finset.card_union_of_disjoint hdj,
    Finset.card_image_of_injective _ Fin.val_injective,
    Finset.card_image_of_injective _ (fun a b h => Fin.ext (by omega))]

theorem main : ∀ (n m : ℕ) (G : Fin n → Fin m → Bool) (C : Circuit),
    let nbrR := fun (sourceRow : Fin n) => Finset.univ.filter (fun destCol : Fin m => G sourceRow destCol = false)
    let nbrC := fun (sourceCol : Fin m) => Finset.univ.filter (fun destRow : Fin n => G destRow sourceCol = false)
    (∀ a, 2 ≤ (nbrR a).card) → (∀ c, 2 ≤ (nbrC c).card) →
    (∀ a b, a ≠ b → ((nbrR a) ∩ (nbrR b)).card ≤ 1) →
    Monotone2 C →
    Represents G C →
    11 * (n + m) ≤ 10 * C.size + 16 ∧
    (17 ≤ n + m → 11 * (n + m) ≤ 10 * C.size + 12) ∧
    ((∀ a, 3 ≤ (nbrR a).card) → (∀ c, 3 ≤ (nbrC c).card) →
      11 * (n + m) ≤ 10 * C.size + 8) := by
  intro n m G C0 nbrR nbrC hdR hdC hno4 hmono0 hrep0
  rcases dims_zero_or_ge_three G hdR hdC hno4 with ⟨rfl, rfl⟩ | ⟨hn3, hm3⟩
  · refine ⟨by omega, by omega, fun _ _ => by omega⟩
  let N := n + m
  rcases simplify_mono N C0.size C0 rfl hmono0 with
    ⟨b, hb⟩ | ⟨i, hi, hfi⟩ | ⟨C, hsz_le, hev, hmono, hshape, hback, hsz_pos, hout_eq, hused⟩
  · exfalso
    exact not_const_of_graph G hn3 hm3 hdR hno4 b
      (fun u v => (hrep0 u v).symm.trans (hb (oneEach u v) (oneEach_length u v)))
  · exfalso
    exact not_single_input_of_graph G hn3 hm3 hno4 i hi
      (fun u v => (hrep0 u v).symm.trans (hfi (oneEach u v) (oneEach_length u v)))
  have hrep : Represents G C := fun u v =>
    (hev (oneEach u v) (oneEach_length u v)).trans (hrep0 u v)
  have hraw : ∀ w < N, 1 ≤ readsIn C (Finset.range C.size) w :=
    all_raw_read G C hn3 hm3 hdR hdC hno4 hmono hrep (by omega)
  let gates := Finset.range C.size
  let gate := gateAt C
  let reads := readsIn C gates
  let neg := @Finset.filter ℕ (fun k => (gate k).op = GateOp.not)
    (fun k => Classical.propDecidable ((gate k).op = GateOp.not)) gates
  let shared := (Finset.range (N + C.size)).filter (fun w => 2 ≤ reads w)
  let sharedGates := gates.filter (fun k => 2 ≤ reads (N + k))
  let sharedRaw := (Finset.range N).filter (fun w => 2 ≤ reads w)
  let markedReads := ∑ w ∈ shared, reads w
  let once := (Finset.range N).filter (fun w => reads w = 1)
  let D := ∑ w ∈ shared, (reads w - 1)
  have hneg0 : neg.card = 0 := by
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro k hk
    have hk' := (@Finset.mem_filter ℕ (fun k => (gate k).op = GateOp.not)
      (fun k => Classical.propDecidable _) gates k).mp hk
    have hlt : k < C.gates.length := Finset.mem_range.mp hk'.1
    have hgop := (hshape C.gates[k] (List.getElem_mem hlt)).1
    have hnot : (gateAt C k).op = GateOp.not := hk'.2
    rw [gateAt_eq_getElem C k hlt] at hnot
    rcases hgop with h | h <;> rw [h] at hnot <;> cases hnot
  obtain ⟨hsize_eq, hmr_eq, hsh_le_D⟩ :=
    handshaking N (by omega) C hshape hback hsz_pos hraw hused
  change C.size = N - 1 + D at hsize_eq
  change markedReads = D + shared.card at hmr_eq
  change shared.card ≤ D at hsh_le_D
  have hshape24 : ∀ g ∈ C.gates,
      ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∨
      (g.op = GateOp.not ∧ g.inputs.length = 1) :=
    fun g hg => Or.inl (hshape g hg)
  obtain ⟨pure, chains, e, hpure_le, hchains_le, he_pos, hdisj, hcov, hpure_ok, hchains_ok⟩ :=
    PEqualNP.Outside.L_meta_25644 N C hshape24 hback hsz_pos hout_eq hused
  dsimp only at hpure_le hchains_le he_pos hdisj hcov hpure_ok hchains_ok
  change pure.length + e ≤ sharedGates.card + neg.card + 1 at hpure_le
  change chains.length + e ≤ 2 * (markedReads + neg.card) at hchains_le
  change 0 < markedReads + neg.card → 0 < e at he_pos
  change (pure ++ chains).toFinset.biUnion (fun S => S) = once at hcov
  rw [hneg0, Nat.add_zero] at hpure_le hchains_le he_pos
  have hsh_split : shared = sharedRaw ∪ sharedGates.image (fun k => N + k) := by
    ext w
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_range,
      shared, sharedRaw, sharedGates, gates]
    constructor
    · rintro ⟨hwlt, h2⟩
      by_cases hwn : w < N
      · exact Or.inl ⟨hwn, h2⟩
      · exact Or.inr ⟨w - N, ⟨by omega, by simpa [Nat.add_sub_cancel' (Nat.le_of_not_lt hwn)] using h2⟩,
          by omega⟩
    · rintro (⟨hwn, h2⟩ | ⟨k, ⟨hk, h2⟩, rfl⟩)
      · exact ⟨by omega, h2⟩
      · exact ⟨by omega, h2⟩
  have hsh_disj : Disjoint sharedRaw (sharedGates.image (fun k => N + k)) := by
    rw [Finset.disjoint_left]
    intro w h1 h2
    have hlt := Finset.mem_range.mp (Finset.mem_filter.mp h1).1
    rcases Finset.mem_image.mp h2 with ⟨k, _, rfl⟩
    omega
  have hsh_card : shared.card = sharedRaw.card + sharedGates.card := by
    rw [hsh_split, Finset.card_union_of_disjoint hsh_disj,
      Finset.card_image_of_injective _ (fun a b h => by omega)]
  have honce_add : once.card + sharedRaw.card = N := by
    have hu : once ∪ sharedRaw = Finset.range N := by
      ext w
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_range, once, sharedRaw]
      constructor
      · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
      · intro h
        have h1 : 1 ≤ reads w := hraw w h
        by_cases h2 : 2 ≤ reads w
        · exact Or.inr ⟨h, h2⟩
        · exact Or.inl ⟨h, by omega⟩
    have hdj : Disjoint once sharedRaw := by
      rw [Finset.disjoint_left]
      intro w h1 h2
      have := (Finset.mem_filter.mp h1).2
      have := (Finset.mem_filter.mp h2).2
      omega
    rw [← Finset.card_union_of_disjoint hdj, hu, Finset.card_range]
  have hblock_sub : ∀ S ∈ pure ++ chains, S ⊆ Finset.range N := by
    intro S hS w hw
    have hmem : w ∈ once := by
      rw [← hcov]
      exact Finset.mem_biUnion.mpr ⟨S, List.mem_toFinset.mpr hS, hw⟩
    exact (Finset.mem_filter.mp hmem).1
  let fewR_all := Finset.univ.filter (fun r : Fin n =>
    (Finset.univ.filter fun v : Fin m => G r v = true).card ≤ 3)
  let fewC_all := Finset.univ.filter (fun c : Fin m =>
    (Finset.univ.filter fun u : Fin n => G u c = true).card ≤ 3)
  let fewWires := fewR_all.image (fun r => r.val) ∪ fewC_all.image (fun c => n + c.val)
  have hfewWires_card : fewWires.card = fewR_all.card + fewC_all.card := by
    have hdj : Disjoint (fewR_all.image (fun r => r.val)) (fewC_all.image (fun c => n + c.val)) := by
      rw [Finset.disjoint_left]
      intro w h1 h2
      rcases Finset.mem_image.mp h1 with ⟨r, _, rfl⟩
      rcases Finset.mem_image.mp h2 with ⟨c, _, hc⟩
      omega
    rw [Finset.card_union_of_disjoint hdj,
      Finset.card_image_of_injective _ Fin.val_injective,
      Finset.card_image_of_injective _ (fun a b h => Fin.ext (by omega))]
  have hblock_bounds : ∀ S ∈ pure ++ chains,
      S.card ≤ 2 + 2 * (S ∩ fewWires).card ∧
      S.card ≤ 6 ∧
      ((∀ a, 3 ≤ (nbrR a).card) → (∀ c, 3 ≤ (nbrC c).card) → S.card ≤ 2) := by
    intro S hS
    have hSsub := hblock_sub S hS
    obtain ⟨hS_eq, hS_card⟩ := split_block S hSsub
    let R : Finset (Fin n) := Finset.univ.filter (fun r => r.val ∈ S)
    let B : Finset (Fin m) := Finset.univ.filter (fun c => n + c.val ∈ S)
    change R.image (fun r => r.val) ∪ B.image (fun c => n + c.val) = S at hS_eq
    change S.card = R.card + B.card at hS_card
    have htree : ∃ (E : Finset ℕ) (region : Finset ℕ) (root : ℕ),
        E.card ≤ 1 ∧
        let wires := S ∪ region.image (fun k => N + k)
        let localReads := readsIn C region
        region ⊆ gates ∧ root ∈ wires ∧ localReads root = 0 ∧
        (∀ b ∈ E, b ∉ wires ∧ b < root ∧ localReads b = 1) ∧
        (∀ j ∈ region,
          ((gate j).op = GateOp.and ∨ (gate j).op = GateOp.or) ∧
          (gate j).inputs.length = 2 ∧ ∀ w ∈ (gate j).inputs, w ∈ wires ∨ w ∈ E) ∧
        (∀ w ∈ wires, w ≠ root → localReads w = 1 ∧ reads w = 1 ∧ C.output ≠ w) := by
      rcases List.mem_append.mp hS with hp | hc
      · rcases (hpure_ok S hp).2 with ⟨region, root, h1, h2, h3, h4, h5, h6⟩
        exact ⟨∅, region, root, by simp, h1, h2, h3, h4, h5, h6⟩
      · rcases (hchains_ok S hc).2 with ⟨b, region, root, h1, h2, h3, h4, h5, h6⟩
        exact ⟨{b}, region, root, by simp, h1, h2, h3, h4, h5, h6⟩
    rcases htree with ⟨E, region, root, hEcard, hreg_sub, hroot_mem, hroot0, hEprop, hreg_prop, hwire_prop⟩
    have h25615 := PEqualNP.Outside.L_meta_25615 n m G C R B region E root
      hdR hdC hno4 hmono hback hrep hreg_sub (by rwa [hS_eq]) hEcard
      (by intro w hw; rw [hS_eq]; exact hEprop w hw)
      (by intro k hk; rw [hS_eq]; exact hreg_prop k hk)
      hroot0
      (by intro w hw; rw [hS_eq] at hw; exact hwire_prop w hw)
    dsimp only at h25615
    rcases h25615 with ⟨hb1, ⟨hbR3, hbB3⟩, _, hbdeg3⟩
    have hfew_eq := block_few_card G S hSsub
    dsimp only at hfew_eq
    refine ⟨?_, by omega, ?_⟩
    · rw [hS_card, ← hfew_eq]
      exact hb1
    · intro h3R h3C
      obtain ⟨hR1, hB1⟩ := hbdeg3 h3R h3C
      omega
  have hD_pos : 1 ≤ D ∨ N ≤ 6 := by
    by_cases hD0 : D = 0
    · right
      have hsh0 : shared.card = 0 := by omega
      have hsr0 : sharedRaw.card = 0 := by omega
      have hsg0 : sharedGates.card = 0 := by omega
      have hmr0 : markedReads = 0 := by omega
      have hq0 : chains.length = 0 := by omega
      have hp1 : pure.length ≤ 1 := by omega
      have honce_le : once.card ≤ 6 * (pure ++ chains).length := by
        rw [← hcov, biUnion_card_eq_sum _ hdisj]
        calc ((pure ++ chains).map Finset.card).sum
            ≤ ((pure ++ chains).map fun _ => 6).sum :=
              list_sum_le_of_forall _ _ _ (fun S hS => (hblock_bounds S hS).2.1)
          _ = 6 * (pure ++ chains).length := by simp [mul_comm]
      rw [List.length_append] at honce_le
      omega
    · left; omega
  have hbase_le : 1 ≤ D → 2 * (pure.length + chains.length) + sharedRaw.card + 2 ≤ 10 * D := by
    intro hD1
    have hmr_pos : 0 < markedReads := by omega
    have he1 : 1 ≤ e := he_pos hmr_pos
    omega
  have hbound3 : (∀ a, 3 ≤ (nbrR a).card) → (∀ c, 3 ≤ (nbrC c).card) →
      11 * N ≤ 10 * C0.size + 8 := by
    intro h3R h3C
    have hD1 : 1 ≤ D := by
      by_contra hlt
      have hD0 : D = 0 := by omega
      have hsh0 : shared.card = 0 := by omega
      have hsr0 : sharedRaw.card = 0 := by omega
      have hsg0 : sharedGates.card = 0 := by omega
      have hmr0 : markedReads = 0 := by omega
      have honce_le : once.card ≤ 2 * (pure ++ chains).length := by
        rw [← hcov, biUnion_card_eq_sum _ hdisj]
        calc ((pure ++ chains).map Finset.card).sum
            ≤ ((pure ++ chains).map fun _ => 2).sum :=
              list_sum_le_of_forall _ _ _ (fun S hS => (hblock_bounds S hS).2.2 h3R h3C)
          _ = 2 * (pure ++ chains).length := by simp [mul_comm]
      rw [List.length_append] at honce_le
      omega
    have honce_le : once.card ≤ 2 * (pure.length + chains.length) := by
      rw [← hcov, biUnion_card_eq_sum _ hdisj]
      calc ((pure ++ chains).map Finset.card).sum
          ≤ ((pure ++ chains).map fun _ => 2).sum :=
            list_sum_le_of_forall _ _ _ (fun S hS => (hblock_bounds S hS).2.2 h3R h3C)
        _ = 2 * (pure ++ chains).length := by simp [mul_comm]
        _ = 2 * (pure.length + chains.length) := by rw [List.length_append]
    have hbase := hbase_le hD1
    omega
  have hbound2 : 17 ≤ N → 11 * N ≤ 10 * C0.size + 12 := by
    intro hN17
    have hD1 : 1 ≤ D := by omega
    have hfew2 : fewWires.card ≤ 2 := by
      rw [hfewWires_card]
      exact few_sum_le_two G hN17 hdR hdC hno4
    have honce_le : once.card ≤ 2 * (pure.length + chains.length) + 2 * fewWires.card := by
      rw [← hcov, biUnion_card_eq_sum _ hdisj]
      have h1 : ((pure ++ chains).map Finset.card).sum ≤
          ((pure ++ chains).map fun S => 2 + 2 * (S ∩ fewWires).card).sum :=
        list_sum_le_of_forall _ _ _ (fun S hS => (hblock_bounds S hS).1)
      have h2 : ((pure ++ chains).map fun S => 2 + 2 * (S ∩ fewWires).card).sum =
          2 * (pure ++ chains).length + 2 * ((pure ++ chains).map fun S => (S ∩ fewWires).card).sum := by
        induction (pure ++ chains) with
        | nil => simp
        | cons A tl ih =>
          simp only [List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
          omega
      have h3 := sum_inter_le_card (pure ++ chains) fewWires hdisj
      rw [List.length_append] at h2
      omega
    have hbase := hbase_le hD1
    omega
  have hbound1 : 11 * N ≤ 10 * C0.size + 16 := by
    by_cases hN17 : 17 ≤ N
    · have := hbound2 hN17; omega
    · by_cases hN6 : N ≤ 6
      · omega
      · have hD1 : 1 ≤ D := by omega
        omega
  exact ⟨hbound1, hbound2, hbound3⟩

end PEqualNP.Outside.L_meta_25646_aux

theorem PEqualNP.Outside.L_meta_25646 : (∀ (n m : ℕ) (G : Fin n → Fin m → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit),
  let nbrR := fun (sourceRow : Fin n) => Finset.univ.filter (fun destCol : Fin m => G sourceRow destCol = false)
  let nbrC := fun (sourceCol : Fin m) => Finset.univ.filter (fun destRow : Fin n => G destRow sourceCol = false)
  (∀ a, 2 ≤ (nbrR a).card) → (∀ c, 2 ≤ (nbrC c).card) →
  (∀ a b, a ≠ b → ((nbrR a) ∩ (nbrR b)).card ≤ 1) →
  PEqualNP.MetaComplexity.Monotone2 C →
  PEqualNP.Represents.Represents G C →
  11 * (n + m) ≤ 10 * C.size + 16 ∧
  (17 ≤ n + m → 11 * (n + m) ≤ 10 * C.size + 12) ∧
  ((∀ a, 3 ≤ (nbrR a).card) → (∀ c, 3 ≤ (nbrC c).card) →
    11 * (n + m) ≤ 10 * C.size + 8)) :=
  PEqualNP.Outside.L_meta_25646_aux.main
