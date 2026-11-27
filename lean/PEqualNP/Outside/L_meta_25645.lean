import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.L_meta_25577
import PEqualNP.Outside.L_meta_25578
import PEqualNP.Outside.L_meta_25644

namespace PEqualNP.Outside.L_meta_25645_aux

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

theorem gateAt_eq_getElem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]

theorem list_split_at {α : Type*} (l : List α) (j : ℕ) (hj : j < l.length) :
    l = l.take j ++ l[j] :: l.drop (j + 1) := by
  have h1 := (List.take_append_drop j l).symm
  rw [List.drop_eq_getElem_cons hj] at h1
  exact h1

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

noncomputable def isNot (g : Gate) : Bool :=
  @decide (g.op = GateOp.not) (Classical.propDecidable _)

noncomputable def notCount (gs : List Gate) : ℕ :=
  gs.countP isNot

noncomputable def binCount (gs : List Gate) : ℕ :=
  gs.countP (fun g => !isNot g)

theorem notCount_add_binCount (gs : List Gate) :
    notCount gs + binCount gs = gs.length := by
  induction gs with
  | nil => simp [notCount, binCount]
  | cons g gs ih =>
    simp only [notCount, binCount, List.countP_cons, List.length_cons] at ih ⊢
    cases isNot g <;> simp <;> omega

theorem isNot_and (ins : List ℕ) : isNot ⟨GateOp.and, ins⟩ = false := by
  unfold isNot
  simp

theorem isNot_or (ins : List ℕ) : isNot ⟨GateOp.or, ins⟩ = false := by
  unfold isNot
  simp

theorem isNot_not (ins : List ℕ) : isNot ⟨GateOp.not, ins⟩ = true := by
  unfold isNot
  simp

theorem notCount_append (l1 l2 : List Gate) :
    notCount (l1 ++ l2) = notCount l1 + notCount l2 := by
  simp [notCount, List.countP_append]

theorem binCount_append (l1 l2 : List Gate) :
    binCount (l1 ++ l2) = binCount l1 + binCount l2 := by
  simp [binCount, List.countP_append]

theorem notCount_singleton (g : Gate) :
    notCount [g] = if isNot g then 1 else 0 := by
  simp [notCount]

theorem binCount_singleton (g : Gate) :
    binCount [g] = if isNot g then 0 else 1 := by
  unfold binCount
  cases h : isNot g <;> simp [h]

def GoodShape (C : Circuit) : Prop :=
  ∀ g ∈ C.gates,
    ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∨
    (g.op = GateOp.not ∧ g.inputs.length = 1)

inductive WireVal where
  | const (b : Bool)
  | wire (idx : ℕ)

def evalWireVal (W : List Bool) : WireVal → Bool
  | WireVal.const b => b
  | WireVal.wire u => W.getD u false

def lookupEnv (env : List WireVal) (i : ℕ) : WireVal :=
  env.getD i (WireVal.const false)

def foldStep (raw : ℕ) (st : List WireVal × List Gate) (g : Gate) : List WireVal × List Gate :=
  let env := st.1
  let acc := st.2
  let nextW := raw + acc.length
  match g.op with
  | GateOp.not =>
    match g.inputs with
    | [] => (env ++ [WireVal.const true], acc)
    | i :: _ =>
      match lookupEnv env i with
      | WireVal.const b => (env ++ [WireVal.const (!b)], acc)
      | WireVal.wire u => (env ++ [WireVal.wire nextW], acc ++ [⟨GateOp.not, [u]⟩])
  | GateOp.and =>
    match g.inputs with
    | [] => (env ++ [WireVal.const true], acc)
    | [i] => (env ++ [lookupEnv env i], acc)
    | [i1, i2] =>
      match lookupEnv env i1, lookupEnv env i2 with
      | WireVal.const false, _ => (env ++ [WireVal.const false], acc)
      | _, WireVal.const false => (env ++ [WireVal.const false], acc)
      | WireVal.const true, v => (env ++ [v], acc)
      | v, WireVal.const true => (env ++ [v], acc)
      | WireVal.wire u1, WireVal.wire u2 =>
        (env ++ [WireVal.wire nextW], acc ++ [⟨GateOp.and, [u1, u2]⟩])
    | _ => (env ++ [WireVal.const false], acc)
  | GateOp.or =>
    match g.inputs with
    | [] => (env ++ [WireVal.const false], acc)
    | [i] => (env ++ [lookupEnv env i], acc)
    | [i1, i2] =>
      match lookupEnv env i1, lookupEnv env i2 with
      | WireVal.const true, _ => (env ++ [WireVal.const true], acc)
      | _, WireVal.const true => (env ++ [WireVal.const true], acc)
      | WireVal.const false, v => (env ++ [v], acc)
      | v, WireVal.const false => (env ++ [v], acc)
      | WireVal.wire u1, WireVal.wire u2 =>
        (env ++ [WireVal.wire nextW], acc ++ [⟨GateOp.or, [u1, u2]⟩])
    | _ => (env ++ [WireVal.const false], acc)
  | _ => (env ++ [WireVal.const false], acc)

def FoldStateOK (raw : ℕ) (gs : List Gate) (env : List WireVal) (acc : List Gate) : Prop :=
  env.length = raw + gs.length ∧
  (∀ v ∈ env, ∀ u, v = WireVal.wire u → u < raw + acc.length) ∧
  GoodShape ⟨acc, 0⟩ ∧
  ReadsBack raw ⟨acc, 0⟩ ∧
  notCount acc ≤ notCount gs ∧
  binCount acc ≤ binCount gs ∧
  ∀ x : List Bool, x.length = raw →
    ∀ w : ℕ, evalWireVal (wiresAux acc x) (lookupEnv env w) = (wiresAux gs x).getD w false

theorem lookupEnv_wire_lt {raw : ℕ} {env : List WireVal} {acc : List Gate}
    (hbound : ∀ v ∈ env, ∀ u, v = WireVal.wire u → u < raw + acc.length)
    {i u : ℕ} (hl : lookupEnv env i = WireVal.wire u) :
    u < raw + acc.length := by
  by_cases hi : i < env.length
  · have hmem : env.getD i (WireVal.const false) ∈ env := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
      exact List.getElem_mem hi
    exact hbound _ hmem u hl
  · have hge : env.length ≤ i := Nat.le_of_not_lt hi
    have hf : lookupEnv env i = WireVal.const false := getD_of_ge env (WireVal.const false) i hge
    rw [hf] at hl
    cases hl

theorem readsBack_append_one (raw : ℕ) (acc : List Gate) (g : Gate)
    (hback : ReadsBack raw ⟨acc, 0⟩)
    (hg : ∀ i ∈ g.inputs, i < raw + acc.length) :
    ReadsBack raw ⟨acc ++ [g], 0⟩ := by
  intro j hj i hi
  simp only [List.length_append, List.length_singleton] at hj
  by_cases hlt : j < acc.length
  · have hgat : gateAt ⟨acc ++ [g], 0⟩ j = gateAt ⟨acc, 0⟩ j := by
      unfold gateAt
      exact getD_append_left acc [g] ⟨GateOp.or, []⟩ j hlt
    rw [hgat] at hi
    exact hback j hlt i hi
  · have heq : j = acc.length := by omega
    subst heq
    have hgat : gateAt ⟨acc ++ [g], 0⟩ acc.length = g := by
      unfold gateAt
      rw [getD_append_right acc [g] ⟨GateOp.or, []⟩ acc.length (le_refl _)]
      simp
    rw [hgat] at hi
    exact hg i hi

theorem eval_preserve_append_no_gate {raw : ℕ} {env : List WireVal} {acc gs : List Gate}
    {v : WireVal} {g : Gate}
    (hlen : env.length = raw + gs.length)
    (heval : ∀ x : List Bool, x.length = raw →
      ∀ w : ℕ, evalWireVal (wiresAux acc x) (lookupEnv env w) = (wiresAux gs x).getD w false)
    (hnew : ∀ x : List Bool, x.length = raw →
      evalWireVal (wiresAux acc x) v =
      g.op.eval (g.inputs.map fun i => (wiresAux gs x).getD i false)) :
    ∀ x : List Bool, x.length = raw →
      ∀ w : ℕ, evalWireVal (wiresAux acc x) (lookupEnv (env ++ [v]) w) =
        (wiresAux (gs ++ [g]) x).getD w false := by
  intro x hx w
  have hwlen : (wiresAux gs x).length = env.length := by
    rw [wiresAux_length, hx, hlen]
  rw [wiresAux_append, wiresAux_cons, wiresAux_nil]
  by_cases hlt : w < env.length
  · unfold lookupEnv
    rw [getD_append_left env [v] _ w hlt,
      getD_append_left (wiresAux gs x) _ false w (hwlen.symm ▸ hlt)]
    exact heval x hx w
  · by_cases heq : w = env.length
    · subst heq
      unfold lookupEnv
      rw [getD_append_right env [v] _ env.length (le_refl _),
        ← hwlen, getD_append_right (wiresAux gs x) _ false (wiresAux gs x).length (le_refl _)]
      simp only [Nat.sub_self, List.getD_cons_zero]
      exact hnew x hx
    · have hge1 : (env ++ [v]).length ≤ w := by simp; omega
      have hge2 : (wiresAux gs x ++
          [g.op.eval (g.inputs.map fun i => (wiresAux gs x).getD i false)]).length ≤ w := by
        simp [hwlen]; omega
      unfold lookupEnv
      rw [getD_of_ge (env ++ [v]) _ w hge1, getD_of_ge _ false w hge2]
      rfl

theorem eval_preserve_append_gate {raw : ℕ} {env : List WireVal} {acc gs : List Gate}
    {g g' : Gate}
    (hlen : env.length = raw + gs.length)
    (hbound : ∀ v ∈ env, ∀ u, v = WireVal.wire u → u < raw + acc.length)
    (heval : ∀ x : List Bool, x.length = raw →
      ∀ w : ℕ, evalWireVal (wiresAux acc x) (lookupEnv env w) = (wiresAux gs x).getD w false)
    (hnew : ∀ x : List Bool, x.length = raw →
      g'.op.eval (g'.inputs.map fun i => (wiresAux acc x).getD i false) =
      g.op.eval (g.inputs.map fun i => (wiresAux gs x).getD i false)) :
    ∀ x : List Bool, x.length = raw →
      ∀ w : ℕ,
        evalWireVal (wiresAux (acc ++ [g']) x) (lookupEnv (env ++ [WireVal.wire (raw + acc.length)]) w) =
        (wiresAux (gs ++ [g]) x).getD w false := by
  intro x hx w
  have hwlen : (wiresAux gs x).length = env.length := by
    rw [wiresAux_length, hx, hlen]
  have halen : (wiresAux acc x).length = raw + acc.length := by
    rw [wiresAux_length, hx]
  rw [wiresAux_append, wiresAux_cons, wiresAux_nil,
    wiresAux_append, wiresAux_cons, wiresAux_nil]
  by_cases hlt : w < env.length
  · unfold lookupEnv
    rw [getD_append_left env _ _ w hlt,
      getD_append_left (wiresAux gs x) _ false w (hwlen.symm ▸ hlt)]
    have hold := heval x hx w
    cases hlu : lookupEnv env w with
    | const b =>
      unfold lookupEnv at hold hlu
      rw [hlu] at hold ⊢
      exact hold
    | wire u =>
      have hu : u < raw + acc.length := lookupEnv_wire_lt hbound hlu
      unfold lookupEnv at hold hlu
      rw [hlu] at hold ⊢
      dsimp only [evalWireVal] at hold ⊢
      rw [getD_append_left (wiresAux acc x) _ false u (halen.symm ▸ hu)]
      exact hold
  · by_cases heq : w = env.length
    · subst heq
      unfold lookupEnv
      rw [getD_append_right env _ _ env.length (le_refl _),
        ← hwlen, getD_append_right (wiresAux gs x) _ false (wiresAux gs x).length (le_refl _)]
      simp only [Nat.sub_self, List.getD_cons_zero, evalWireVal]
      rw [← halen, getD_append_right (wiresAux acc x) _ false (wiresAux acc x).length (le_refl _)]
      simp only [Nat.sub_self, List.getD_cons_zero]
      exact hnew x hx
    · have hge1 : (env ++ [WireVal.wire (raw + acc.length)]).length ≤ w := by simp; omega
      have hge2 : (wiresAux gs x ++
          [g.op.eval (g.inputs.map fun i => (wiresAux gs x).getD i false)]).length ≤ w := by
        simp [hwlen]; omega
      unfold lookupEnv
      rw [getD_of_ge (env ++ _) _ w hge1, getD_of_ge _ false w hge2]
      rfl

theorem foldStep_ok (raw : ℕ) (gs : List Gate) (env : List WireVal) (acc : List Gate) (g : Gate)
    (hok : FoldStateOK raw gs env acc)
    (hfan : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    let st' := foldStep raw (env, acc) g
    FoldStateOK raw (gs ++ [g]) st'.1 st'.2 := by
  rcases hok with ⟨hlen, hbound, hshape, hback, hnot, hbin, heval⟩
  have hgop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not := by
    simpa using hfan.1
  have hno_gate : ∀ v : WireVal,
      (∀ u, v = WireVal.wire u → u < raw + acc.length) →
      (∀ x : List Bool, x.length = raw →
        evalWireVal (wiresAux acc x) v =
        g.op.eval (g.inputs.map fun i => (wiresAux gs x).getD i false)) →
      FoldStateOK raw (gs ++ [g]) (env ++ [v]) acc := by
    intro v hv hnew
    refine ⟨by simp [hlen]; omega, ?_, hshape, hback, ?_, ?_,
      eval_preserve_append_no_gate hlen heval hnew⟩
    · intro v' hv' u hu
      rcases List.mem_append.mp hv' with h1 | h2
      · exact hbound v' h1 u hu
      · rw [List.mem_singleton.mp h2] at hu
        exact hv u hu
    · rw [notCount_append]; omega
    · rw [binCount_append]; omega
  have hwith_gate : ∀ g' : Gate,
      (((g'.op = GateOp.and ∨ g'.op = GateOp.or) ∧ g'.inputs.length = 2) ∨
       (g'.op = GateOp.not ∧ g'.inputs.length = 1)) →
      (∀ i ∈ g'.inputs, i < raw + acc.length) →
      isNot g' = isNot g →
      (∀ x : List Bool, x.length = raw →
        g'.op.eval (g'.inputs.map fun i => (wiresAux acc x).getD i false) =
        g.op.eval (g.inputs.map fun i => (wiresAux gs x).getD i false)) →
      FoldStateOK raw (gs ++ [g]) (env ++ [WireVal.wire (raw + acc.length)]) (acc ++ [g']) := by
    intro g' hg's hg'in hsame hnew
    refine ⟨by simp [hlen]; omega, ?_, ?_, readsBack_append_one raw acc g' hback hg'in, ?_, ?_,
      eval_preserve_append_gate hlen hbound heval hnew⟩
    · intro v' hv' u hu
      simp only [List.length_append, List.length_singleton]
      rcases List.mem_append.mp hv' with h1 | h2
      · exact Nat.lt_trans (hbound v' h1 u hu) (by omega)
      · rw [List.mem_singleton.mp h2] at hu
        cases hu
        omega
    · intro h hh
      rcases List.mem_append.mp hh with h1 | h2
      · exact hshape h h1
      · rw [List.mem_singleton.mp h2]
        exact hg's
    · rw [notCount_append, notCount_append, notCount_singleton, notCount_singleton, hsame]
      omega
    · rw [binCount_append, binCount_append, binCount_singleton, binCount_singleton, hsame]
      omega
  rcases hgop with hop | hop | hop
  · cases hin : g.inputs with
    | nil =>
      dsimp only [foldStep]
      rw [hop, hin]
      dsimp only
      apply hno_gate (WireVal.const true) (fun _ h => by cases h)
      intro x _
      simp [hop, hin, GateOp.eval, evalWireVal]
    | cons i1 rest =>
      cases rest with
      | nil =>
        dsimp only [foldStep]
        rw [hop, hin]
        dsimp only
        apply hno_gate (lookupEnv env i1) (fun u hu => lookupEnv_wire_lt hbound hu)
        intro x hx
        rw [heval x hx i1]
        simp [hop, hin, GateOp.eval]
      | cons i2 rest2 =>
        cases rest2 with
        | nil =>
          dsimp only [foldStep]
          rw [hop, hin]
          dsimp only
          cases h1 : lookupEnv env i1 with
          | const b1 =>
            cases b1 with
            | false =>
              dsimp only
              apply hno_gate (WireVal.const false) (fun _ h => by cases h)
              intro x hx
              have he1 := heval x hx i1
              rw [h1] at he1
              rw [hop, hin]
              dsimp only [GateOp.eval, evalWireVal, List.map, List.all, id_eq] at he1 ⊢
              rw [← he1]; rfl
            | true =>
              cases h2 : lookupEnv env i2 with
              | const b2 =>
                cases b2 with
                | false =>
                  dsimp only
                  apply hno_gate (WireVal.const false) (fun _ h => by cases h)
                  intro x hx
                  have he2 := heval x hx i2
                  rw [h2] at he2
                  rw [hop, hin]
                  dsimp only [GateOp.eval, evalWireVal, List.map, List.all, id_eq] at he2 ⊢
                  rw [← he2]; simp
                | true =>
                  dsimp only
                  apply hno_gate (WireVal.const true) (fun _ h => by cases h)
                  intro x hx
                  have he1 := heval x hx i1
                  have he2 := heval x hx i2
                  rw [h1] at he1
                  rw [h2] at he2
                  rw [hop, hin]
                  dsimp only [GateOp.eval, evalWireVal, List.map, List.all, id_eq] at he1 he2 ⊢
                  rw [← he1, ← he2]; rfl
              | wire u2 =>
                dsimp only
                apply hno_gate (WireVal.wire u2) (fun u hu => by cases hu; exact lookupEnv_wire_lt hbound h2)
                intro x hx
                have he1 := heval x hx i1
                have he2 := heval x hx i2
                rw [h1] at he1
                rw [h2] at he2
                rw [hop, hin]
                dsimp only [GateOp.eval, evalWireVal, List.map, List.all, id_eq] at he1 he2 ⊢
                rw [← he1, ← he2]; simp
          | wire u1 =>
            cases h2 : lookupEnv env i2 with
            | const b2 =>
              cases b2 with
              | false =>
                dsimp only
                apply hno_gate (WireVal.const false) (fun _ h => by cases h)
                intro x hx
                have he2 := heval x hx i2
                rw [h2] at he2
                rw [hop, hin]
                dsimp only [GateOp.eval, evalWireVal, List.map, List.all, id_eq] at he2 ⊢
                rw [← he2]; simp
              | true =>
                dsimp only
                apply hno_gate (WireVal.wire u1) (fun u hu => by cases hu; exact lookupEnv_wire_lt hbound h1)
                intro x hx
                have he1 := heval x hx i1
                have he2 := heval x hx i2
                rw [h1] at he1
                rw [h2] at he2
                rw [hop, hin]
                dsimp only [GateOp.eval, evalWireVal, List.map, List.all, id_eq] at he1 he2 ⊢
                rw [← he1, ← he2]; simp
            | wire u2 =>
              dsimp only
              apply hwith_gate ⟨GateOp.and, [u1, u2]⟩
                (Or.inl ⟨Or.inl rfl, rfl⟩)
                (fun i hi => by
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
                  rcases hi with rfl | rfl
                  · exact lookupEnv_wire_lt hbound h1
                  · exact lookupEnv_wire_lt hbound h2)
                (by unfold isNot; rw [hop])
              intro x hx
              have he1 := heval x hx i1
              have he2 := heval x hx i2
              rw [h1] at he1
              rw [h2] at he2
              rw [hop, hin]
              dsimp only [GateOp.eval, evalWireVal, List.map, List.all, id_eq] at he1 he2 ⊢
              rw [← he1, ← he2]
        | cons _ _ =>
          have hle := hfan.2
          rw [hin] at hle
          simp at hle
  · cases hin : g.inputs with
    | nil =>
      dsimp only [foldStep]
      rw [hop, hin]
      dsimp only
      apply hno_gate (WireVal.const false) (fun _ h => by cases h)
      intro x _
      simp [hop, hin, GateOp.eval, evalWireVal]
    | cons i1 rest =>
      cases rest with
      | nil =>
        dsimp only [foldStep]
        rw [hop, hin]
        dsimp only
        apply hno_gate (lookupEnv env i1) (fun u hu => lookupEnv_wire_lt hbound hu)
        intro x hx
        rw [heval x hx i1]
        simp [hop, hin, GateOp.eval]
      | cons i2 rest2 =>
        cases rest2 with
        | nil =>
          dsimp only [foldStep]
          rw [hop, hin]
          dsimp only
          cases h1 : lookupEnv env i1 with
          | const b1 =>
            cases b1 with
            | true =>
              dsimp only
              apply hno_gate (WireVal.const true) (fun _ h => by cases h)
              intro x hx
              have he1 := heval x hx i1
              rw [h1] at he1
              rw [hop, hin]
              dsimp only [GateOp.eval, evalWireVal, List.map, List.any, id_eq] at he1 ⊢
              rw [← he1]; rfl
            | false =>
              cases h2 : lookupEnv env i2 with
              | const b2 =>
                cases b2 with
                | true =>
                  dsimp only
                  apply hno_gate (WireVal.const true) (fun _ h => by cases h)
                  intro x hx
                  have he2 := heval x hx i2
                  rw [h2] at he2
                  rw [hop, hin]
                  dsimp only [GateOp.eval, evalWireVal, List.map, List.any, id_eq] at he2 ⊢
                  rw [← he2]; simp
                | false =>
                  dsimp only
                  apply hno_gate (WireVal.const false) (fun _ h => by cases h)
                  intro x hx
                  have he1 := heval x hx i1
                  have he2 := heval x hx i2
                  rw [h1] at he1
                  rw [h2] at he2
                  rw [hop, hin]
                  dsimp only [GateOp.eval, evalWireVal, List.map, List.any, id_eq] at he1 he2 ⊢
                  rw [← he1, ← he2]; rfl
              | wire u2 =>
                dsimp only
                apply hno_gate (WireVal.wire u2) (fun u hu => by cases hu; exact lookupEnv_wire_lt hbound h2)
                intro x hx
                have he1 := heval x hx i1
                have he2 := heval x hx i2
                rw [h1] at he1
                rw [h2] at he2
                rw [hop, hin]
                dsimp only [GateOp.eval, evalWireVal, List.map, List.any, id_eq] at he1 he2 ⊢
                rw [← he1, ← he2]; simp
          | wire u1 =>
            cases h2 : lookupEnv env i2 with
            | const b2 =>
              cases b2 with
              | true =>
                dsimp only
                apply hno_gate (WireVal.const true) (fun _ h => by cases h)
                intro x hx
                have he2 := heval x hx i2
                rw [h2] at he2
                rw [hop, hin]
                dsimp only [GateOp.eval, evalWireVal, List.map, List.any, id_eq] at he2 ⊢
                rw [← he2]; simp
              | false =>
                dsimp only
                apply hno_gate (WireVal.wire u1) (fun u hu => by cases hu; exact lookupEnv_wire_lt hbound h1)
                intro x hx
                have he1 := heval x hx i1
                have he2 := heval x hx i2
                rw [h1] at he1
                rw [h2] at he2
                rw [hop, hin]
                dsimp only [GateOp.eval, evalWireVal, List.map, List.any, id_eq] at he1 he2 ⊢
                rw [← he1, ← he2]; simp
            | wire u2 =>
              dsimp only
              apply hwith_gate ⟨GateOp.or, [u1, u2]⟩
                (Or.inl ⟨Or.inr rfl, rfl⟩)
                (fun i hi => by
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
                  rcases hi with rfl | rfl
                  · exact lookupEnv_wire_lt hbound h1
                  · exact lookupEnv_wire_lt hbound h2)
                (by unfold isNot; rw [hop])
              intro x hx
              have he1 := heval x hx i1
              have he2 := heval x hx i2
              rw [h1] at he1
              rw [h2] at he2
              rw [hop, hin]
              dsimp only [GateOp.eval, evalWireVal, List.map, List.any, id_eq] at he1 he2 ⊢
              rw [← he1, ← he2]
        | cons _ _ =>
          have hle := hfan.2
          rw [hin] at hle
          simp at hle
  · cases hin : g.inputs with
    | nil =>
      dsimp only [foldStep]
      rw [hop, hin]
      dsimp only
      apply hno_gate (WireVal.const true) (fun _ h => by cases h)
      intro x _
      simp [hop, hin, GateOp.eval, evalWireVal]
    | cons i1 rest =>
      dsimp only [foldStep]
      rw [hop, hin]
      dsimp only
      cases h1 : lookupEnv env i1 with
      | const b1 =>
        dsimp only
        apply hno_gate (WireVal.const (!b1)) (fun _ h => by cases h)
        intro x hx
        have he1 := heval x hx i1
        rw [h1] at he1
        rw [hop, hin]
        dsimp only [GateOp.eval, evalWireVal, List.map, List.headD] at he1 ⊢
        rw [← he1]
      | wire u1 =>
        dsimp only
        apply hwith_gate ⟨GateOp.not, [u1]⟩
          (Or.inr ⟨rfl, rfl⟩)
          (fun i hi => by
            simp only [List.mem_singleton] at hi
            subst hi
            exact lookupEnv_wire_lt hbound h1)
          (by unfold isNot; rw [hop])
        intro x hx
        have he1 := heval x hx i1
        rw [h1] at he1
        rw [hop, hin]
        dsimp only [GateOp.eval, evalWireVal, List.map, List.headD] at he1 ⊢
        rw [← he1]

theorem fold_const_all (raw : ℕ) (C : Circuit) (hfan : FanInTwo C) :
    (∃ b : Bool, ∀ x : List Bool, x.length = raw → C.eval x = b) ∨
    (∃ i < raw, ∀ x : List Bool, x.length = raw → C.eval x = x.getD i false) ∨
    (∃ C1 : Circuit,
      (∀ x : List Bool, x.length = raw → C1.eval x = C.eval x) ∧
      GoodShape C1 ∧
      ReadsBack raw C1 ∧
      raw ≤ C1.output ∧
      C1.output < raw + C1.size ∧
      notCount C1.gates ≤ notCount C.gates ∧
      binCount C1.gates ≤ binCount C.gates) := by
  have hrun : ∀ gs : List Gate,
      (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
      ∃ env acc, FoldStateOK raw gs env acc := by
    intro gs
    induction gs using List.reverseRecOn with
    | nil =>
      intro _
      refine ⟨(List.range raw).map WireVal.wire, [], ?_⟩
      refine ⟨by simp, ?_, fun g hg => by simp at hg, fun j hj => by simp at hj,
        by simp [notCount], by simp [binCount], ?_⟩
      · intro v hv u hu
        rcases List.mem_map.mp hv with ⟨k, hk, hkv⟩
        rw [← hkv] at hu
        cases hu
        simp only [List.mem_range] at hk
        simp [hk]
      · intro x hx w
        by_cases hw : w < raw
        · have hlu : lookupEnv ((List.range raw).map WireVal.wire) w = WireVal.wire w := by
            unfold lookupEnv
            simp [List.getD_eq_getElem?_getD, hw]
          rw [hlu]
          rfl
        · have hge : ((List.range raw).map WireVal.wire).length ≤ w := by simp; omega
          have hlu : lookupEnv ((List.range raw).map WireVal.wire) w = WireVal.const false :=
            getD_of_ge _ _ w hge
          rw [hlu]
          symm
          exact getD_of_ge x false w (by omega)
    | append_singleton gs g ih =>
      intro hgs
      obtain ⟨env, acc, hok⟩ := ih (fun g' hg' => hgs g' (List.mem_append_left _ hg'))
      have hg := hgs g (List.mem_append_right _ (List.mem_singleton_self g))
      exact ⟨(foldStep raw (env, acc) g).1, (foldStep raw (env, acc) g).2,
        foldStep_ok raw gs env acc g hok hg⟩
  obtain ⟨env, acc, hlen, hbound, hshape, hback, hnot, hbin, heval⟩ := hrun C.gates hfan
  cases hlu : lookupEnv env C.output with
  | const b =>
    left
    refine ⟨b, fun x hx => ?_⟩
    have h1 := heval x hx C.output
    rw [hlu] at h1
    exact h1.symm
  | wire u =>
    have hu_lt : u < raw + acc.length := lookupEnv_wire_lt hbound hlu
    by_cases hlt : u < raw
    · right; left
      refine ⟨u, hlt, fun x hx => ?_⟩
      have h1 := heval x hx C.output
      rw [hlu] at h1
      dsimp only [evalWireVal] at h1
      rw [wiresAux_getD_lt acc x u (hx.symm ▸ hlt)] at h1
      exact h1.symm
    · right; right
      refine ⟨⟨acc, u⟩, ?_, hshape, hback, show raw ≤ u by omega, hu_lt, hnot, hbin⟩
      intro x hx
      have h1 := heval x hx C.output
      rw [hlu] at h1
      exact h1

def shift (jw w : ℕ) : ℕ :=
  if jw < w then w - 1 else w

theorem shift_lt {jw w : ℕ} (h : w < jw) : shift jw w = w := by
  simp [shift, Nat.not_lt.mpr (Nat.le_of_lt h)]

theorem shift_gt {jw w : ℕ} (h : jw < w) : shift jw w = w - 1 := by
  simp [shift, h]

def remapUnused (jw : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (shift jw)⟩

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
      rw [shift_gt hjw]
      have hsub : Wold.length - 1 = Wnew.length := by omega
      rw [hsub, getD_append_right Wnew [b] false Wnew.length (le_refl _),
        getD_append_right Wold [b] false Wold.length (le_refl _)]
      simp
    · have hge1 : (Wold ++ [b]).length ≤ w := by simp; omega
      have hge2 : (Wnew ++ [b]).length ≤ shift jw w := by
        unfold shift
        split_ifs <;> (simp; omega)
      rw [getD_of_ge (Wnew ++ [b]) false _ hge2, getD_of_ge (Wold ++ [b]) false _ hge1]

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
    let b := g.op.eval (g.inputs.map fun i => Wold.getD i false)
    obtain ⟨hl', hj', hi'⟩ := step_inv jw Wold Wnew b hlen hjw hinv
    exact ih _ _ hgs hl' hj' hi'

theorem notCount_map_remapUnused (jw : ℕ) (l : List Gate) :
    notCount (l.map (remapUnused jw)) = notCount l := by
  induction l with
  | nil => simp [notCount]
  | cons g gs ih =>
    simp only [List.map_cons, notCount, List.countP_cons] at ih ⊢
    have : isNot (remapUnused jw g) = isNot g := rfl
    rw [this, ih]

theorem binCount_map_remapUnused (jw : ℕ) (l : List Gate) :
    binCount (l.map (remapUnused jw)) = binCount l := by
  induction l with
  | nil => simp [binCount]
  | cons g gs ih =>
    simp only [List.map_cons, binCount, List.countP_cons] at ih ⊢
    have : isNot (remapUnused jw g) = isNot g := rfl
    rw [this, ih]

theorem prune_unused (raw : ℕ) :
    ∀ (s : ℕ) (C : Circuit), C.size = s →
      GoodShape C → ReadsBack raw C → raw ≤ C.output → C.output < raw + s →
      ∃ C' : Circuit,
        (∀ x : List Bool, x.length = raw → C'.eval x = C.eval x) ∧
        GoodShape C' ∧
        ReadsBack raw C' ∧
        0 < C'.size ∧
        C'.output + 1 = raw + C'.size ∧
        (∀ j < C'.size, j + 1 < C'.size → 0 < readsIn C' (Finset.range C'.size) (raw + j)) ∧
        notCount C'.gates ≤ notCount C.gates ∧
        binCount C'.gates ≤ binCount C.gates := by
  intro s
  induction s using Nat.strong_induction_on with
  | ind s ih =>
    intro C hsize hshape hback hout_lo hout_hi
    have hglen : C.gates.length = s := hsize
    by_cases hout_last : C.output + 1 < raw + s
    · let k := C.output - raw + 1
      let C1 : Circuit := ⟨C.gates.take k, C.output⟩
      have hklt : k < s := by omega
      have hsz1 : C1.size = k := by
        show (C.gates.take k).length = k
        rw [List.length_take]; omega
      have hshape1 : GoodShape C1 := fun g hg => hshape g (List.mem_of_mem_take hg)
      have hback1 : ReadsBack raw C1 := by
        intro j hj i hi
        have hlt : j < k := hsz1 ▸ hj
        have hgat : gateAt C1 j = gateAt C j := by
          simp only [gateAt, C1, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hlt]
        rw [hgat] at hi
        exact hback j (by omega) i hi
      have hev1 : ∀ x : List Bool, x.length = raw → C1.eval x = C.eval x := by
        intro x hx
        rw [circuit_eval_eq, circuit_eval_eq]
        have hsplit := (List.take_append_drop k C.gates).symm
        conv_rhs =>
          rw [hsplit, wiresAux_append, wiresAux_getD_lt _ _ _
            (by rw [wiresAux_length, hx, List.length_take]; omega)]
      have hsplit_g := (List.take_append_drop k C.gates).symm
      have hnot1 : notCount C1.gates ≤ notCount C.gates := by
        conv_rhs => rw [hsplit_g, notCount_append]
        exact Nat.le_add_right _ _
      have hbin1 : binCount C1.gates ≤ binCount C.gates := by
        conv_rhs => rw [hsplit_g, binCount_append]
        exact Nat.le_add_right _ _
      obtain ⟨C', hev', hsh', hbk', hsz', hout', hused', hnt', hbn'⟩ :=
        ih k hklt C1 hsz1 hshape1 hback1 hout_lo (show C.output < raw + k by omega)
      exact ⟨C', fun x hx => (hev' x hx).trans (hev1 x hx), hsh', hbk', hsz', hout', hused',
        hnt'.trans hnot1, hbn'.trans hbin1⟩
    · have hout_eq : C.output + 1 = raw + s := by omega
      have hs_pos : 0 < s := by omega
      by_cases hused : ∀ j < s, j + 1 < s → 0 < readsIn C (Finset.range s) (raw + j)
      · exact ⟨C, fun _ _ => rfl, hshape, hback, hsize.symm ▸ hs_pos, hsize.symm ▸ hout_eq,
          hsize.symm ▸ hused, le_refl _, le_refl _⟩
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
        have hshape1 : GoodShape C1 := by
          intro g hg
          rcases List.mem_append.mp hg with hp | hq
          · exact hshape g (List.mem_of_mem_take hp)
          · rcases List.mem_map.mp hq with ⟨g0, hg0, rfl⟩
            simpa [remapUnused] using hshape g0 (List.mem_of_mem_drop hg0)
        have hun : ∀ g ∈ post, jw ∉ g.inputs := by
          intro g hg hmem
          obtain ⟨k, hk, hgk⟩ := List.getElem_of_mem hg
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
        have hback1 : ReadsBack raw C1 := by
          intro k hk i hi
          have hk' : k < s - 1 := hsz1 ▸ hk
          have hpre_len : pre.length = j := by simp [pre, List.length_take, hglen]; omega
          by_cases hkj : k < j
          · have hgat : gateAt C1 k = gateAt C k := by
              have h1 : gateAt C1 k = pre.getD k ⟨GateOp.or, []⟩ := by
                simp only [gateAt, C1]
                exact getD_append_left pre _ _ k (by omega)
              rw [h1]
              simp only [gateAt, pre, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hkj]
            rw [hgat] at hi
            exact hback k (by omega) i hi
          · have hidx : k - j < post.length := by
              simp [post, List.length_drop, hglen]; omega
            have hgat : gateAt C1 k = remapUnused jw (gateAt C (k + 1)) := by
              have h1 : gateAt C1 k = (post.map (remapUnused jw)).getD (k - j) ⟨GateOp.or, []⟩ := by
                simp only [gateAt, C1]
                rw [getD_append_right pre _ _ k (by omega), hpre_len]
              rw [h1, List.getD_eq_getElem?_getD, List.getElem?_map,
                List.getElem?_eq_getElem hidx]
              simp only [Option.map_some, Option.getD_some, post, List.getElem_drop]
              congr 1
              rw [gateAt_eq_getElem C (k + 1) (by omega)]
              congr 1
              omega
            rw [hgat] at hi
            rcases List.mem_map.mp hi with ⟨w, hwm, rfl⟩
            have hwlt : w < raw + (k + 1) := hback (k + 1) (by omega) w hwm
            have hwne : w ≠ jw := by
              intro heq
              subst heq
              have hgmem : gateAt C (k + 1) ∈ post := by
                rw [gateAt_eq_getElem C (k + 1) (by omega)]
                have : C.gates[k + 1]'(by omega) = post[k - j]'hidx := by
                  simp [post, List.getElem_drop, show j + 1 + (k - j) = k + 1 by omega]
                rw [this]
                exact List.getElem_mem hidx
              exact hun _ hgmem hwm
            unfold shift
            split_ifs <;> omega
        have hco : C.output ≠ jw := by omega
        have hout_lo1 : raw ≤ C1.output := by
          dsimp only [C1, shift]
          split_ifs <;> omega
        have hout_hi1 : C1.output < raw + (s - 1) := by
          dsimp only [C1, shift]
          split_ifs <;> omega
        have hsplit_g := list_split_at C.gates j (hglen.symm ▸ hjs)
        have hnot1 : notCount C1.gates ≤ notCount C.gates := by
          dsimp only [C1]
          rw [notCount_append, notCount_map_remapUnused]
          have hnc : notCount C.gates =
              notCount pre + (if isNot C.gates[j] then 1 else 0) + notCount post := by
            conv_lhs => rw [hsplit_g]
            simp only [notCount, pre, post, List.countP_append, List.countP_cons]
            omega
          omega
        have hbin1 : binCount C1.gates ≤ binCount C.gates := by
          dsimp only [C1]
          rw [binCount_append, binCount_map_remapUnused]
          have hbc : binCount C.gates =
              binCount pre + (if !isNot C.gates[j] then 1 else 0) + binCount post := by
            conv_lhs => rw [hsplit_g]
            simp only [binCount, pre, post, List.countP_append, List.countP_cons]
            omega
          omega
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
        obtain ⟨C', hev', hsh', hbk', hsz', hout', hused', hnt', hbn'⟩ :=
          ih (s - 1) (by omega) C1 hsz1 hshape1 hback1 hout_lo1 hout_hi1
        exact ⟨C', fun x hx => (hev' x hx).trans (hev1 x hx), hsh', hbk', hsz', hout', hused',
          hnt'.trans hnot1, hbn'.trans hbin1⟩

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

theorem noFour_symm {n m : ℕ} (G : Fin n → Fin m → Bool) (edge : Bool)
    (hno4 : ∀ a b : Fin n, a ≠ b →
      ((Finset.univ.filter fun v : Fin m => G a v = edge) ∩
       (Finset.univ.filter fun v : Fin m => G b v = edge)).card ≤ 1) :
    ∀ c d : Fin m, c ≠ d →
      ((Finset.univ.filter fun u : Fin n => G u c = edge) ∩
       (Finset.univ.filter fun u : Fin n => G u d = edge)).card ≤ 1 := by
  intro c d hcd
  by_contra hgt
  have h1lt : 1 < ((Finset.univ.filter fun u : Fin n => G u c = edge) ∩
      (Finset.univ.filter fun u : Fin n => G u d = edge)).card := by omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp h1lt
  simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  have hsub : ({c, d} : Finset (Fin m)) ⊆
      (Finset.univ.filter fun v : Fin m => G a v = edge) ∩
      (Finset.univ.filter fun v : Fin m => G b v = edge) := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl <;> simp [ha, hb]
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_pair hcd] at hcard
  have hle := hno4 a b hab
  omega

theorem dims_zero_or_ge_three {n m : ℕ} (G : Fin n → Fin m → Bool) (edge : Bool)
    (hdR : ∀ a : Fin n, 2 ≤ (Finset.univ.filter fun v : Fin m => G a v = edge).card)
    (hdC : ∀ c : Fin m, 2 ≤ (Finset.univ.filter fun u : Fin n => G u c = edge).card)
    (hno4 : ∀ a b : Fin n, a ≠ b →
      ((Finset.univ.filter fun v : Fin m => G a v = edge) ∩
       (Finset.univ.filter fun v : Fin m => G b v = edge)).card ≤ 1) :
    (n = 0 ∧ m = 0) ∨ (3 ≤ n ∧ 3 ≤ m) := by
  by_cases hn0 : n = 0
  · left
    refine ⟨hn0, ?_⟩
    by_contra hm0
    have h2 := hdC ⟨0, Nat.pos_of_ne_zero hm0⟩
    have hle : (Finset.univ.filter fun u : Fin n => G u ⟨0, Nat.pos_of_ne_zero hm0⟩ = edge).card ≤ n := by
      simpa using Finset.card_filter_le (Finset.univ : Finset (Fin n)) _
    omega
  by_cases hm0 : m = 0
  · exfalso
    have h2 := hdR ⟨0, Nat.pos_of_ne_zero hn0⟩
    have hle : (Finset.univ.filter fun v : Fin m => G ⟨0, Nat.pos_of_ne_zero hn0⟩ v = edge).card ≤ m := by
      simpa using Finset.card_filter_le (Finset.univ : Finset (Fin m)) _
    omega
  right
  have hn2 : 2 ≤ n := by
    have h2 := hdC ⟨0, Nat.pos_of_ne_zero hm0⟩
    have hle : (Finset.univ.filter fun u : Fin n => G u ⟨0, Nat.pos_of_ne_zero hm0⟩ = edge).card ≤ n := by
      simpa using Finset.card_filter_le (Finset.univ : Finset (Fin n)) _
    omega
  have hm2 : 2 ≤ m := by
    have h2 := hdR ⟨0, Nat.pos_of_ne_zero hn0⟩
    have hle : (Finset.univ.filter fun v : Fin m => G ⟨0, Nat.pos_of_ne_zero hn0⟩ v = edge).card ≤ m := by
      simpa using Finset.card_filter_le (Finset.univ : Finset (Fin m)) _
    omega
  have hn3 : 3 ≤ n := by
    by_contra hlt
    have hn_eq : n = 2 := by omega
    let a0 : Fin n := ⟨0, by omega⟩
    let a1 : Fin n := ⟨1, by omega⟩
    have hne : a0 ≠ a1 := by intro h; simp [a0, a1] at h
    have hall : ∀ c : Fin m, G a0 c = edge ∧ G a1 c = edge := by
      intro c
      have hc := hdC c
      have hsub : (Finset.univ.filter fun u : Fin n => G u c = edge) = Finset.univ := by
        apply Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
        simpa [hn_eq] using hc
      have h0 : a0 ∈ Finset.univ.filter (fun u : Fin n => G u c = edge) := by
        rw [hsub]; exact Finset.mem_univ _
      have h1 : a1 ∈ Finset.univ.filter (fun u : Fin n => G u c = edge) := by
        rw [hsub]; exact Finset.mem_univ _
      exact ⟨(Finset.mem_filter.mp h0).2, (Finset.mem_filter.mp h1).2⟩
    have hinter : (Finset.univ.filter fun v : Fin m => G a0 v = edge) ∩
        (Finset.univ.filter fun v : Fin m => G a1 v = edge) = Finset.univ := by
      ext v; simp [hall v]
    have hle := hno4 a0 a1 hne
    rw [hinter] at hle
    simp at hle
    omega
  have hm3 : 3 ≤ m := by
    have hno4C := noFour_symm G edge hno4
    by_contra hlt
    have hm_eq : m = 2 := by omega
    let c0 : Fin m := ⟨0, by omega⟩
    let c1 : Fin m := ⟨1, by omega⟩
    have hne : c0 ≠ c1 := by intro h; simp [c0, c1] at h
    have hall : ∀ a : Fin n, G a c0 = edge ∧ G a c1 = edge := by
      intro a
      have ha := hdR a
      have hsub : (Finset.univ.filter fun v : Fin m => G a v = edge) = Finset.univ := by
        apply Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
        simpa [hm_eq] using ha
      have h0 : c0 ∈ Finset.univ.filter (fun v : Fin m => G a v = edge) := by
        rw [hsub]; exact Finset.mem_univ _
      have h1 : c1 ∈ Finset.univ.filter (fun v : Fin m => G a v = edge) := by
        rw [hsub]; exact Finset.mem_univ _
      exact ⟨(Finset.mem_filter.mp h0).2, (Finset.mem_filter.mp h1).2⟩
    have hinter : (Finset.univ.filter fun u : Fin n => G u c0 = edge) ∩
        (Finset.univ.filter fun u : Fin n => G u c1 = edge) = Finset.univ := by
      ext u; simp [hall u]
    have hle := hno4C c0 c1 hne
    rw [hinter] at hle
    simp at hle
    omega
  exact ⟨hn3, hm3⟩

theorem not_const_of_graph {n m : ℕ} (G : Fin n → Fin m → Bool) (edge : Bool)
    (hn3 : 3 ≤ n) (hm3 : 3 ≤ m)
    (hdR : ∀ a : Fin n, 2 ≤ (Finset.univ.filter fun v : Fin m => G a v = edge).card)
    (hno4 : ∀ a b : Fin n, a ≠ b →
      ((Finset.univ.filter fun v : Fin m => G a v = edge) ∩
       (Finset.univ.filter fun v : Fin m => G b v = edge)).card ≤ 1)
    (b : Bool) (hconst : ∀ u v, G u v = b) : False := by
  by_cases hbe : b = edge
  · subst hbe
    let a0 : Fin n := ⟨0, by omega⟩
    let a1 : Fin n := ⟨1, by omega⟩
    have hne : a0 ≠ a1 := by intro h; simp [a0, a1] at h
    have hinter : (Finset.univ.filter fun v : Fin m => G a0 v = b) ∩
        (Finset.univ.filter fun v : Fin m => G a1 v = b) = Finset.univ := by
      ext v; simp [hconst]
    have hle := hno4 a0 a1 hne
    rw [hinter] at hle
    simp at hle
    omega
  · have h2 := hdR ⟨0, by omega⟩
    have hempty : (Finset.univ.filter fun v : Fin m => G ⟨0, by omega⟩ v = edge) = ∅ := by
      ext v; simp [hconst, hbe]
    rw [hempty] at h2
    simp at h2

theorem not_single_input_of_graph {n m : ℕ} (G : Fin n → Fin m → Bool) (edge : Bool)
    (hn3 : 3 ≤ n) (hm3 : 3 ≤ m)
    (hdR : ∀ a : Fin n, 2 ≤ (Finset.univ.filter fun v : Fin m => G a v = edge).card)
    (hdC : ∀ c : Fin m, 2 ≤ (Finset.univ.filter fun u : Fin n => G u c = edge).card)
    (hno4 : ∀ a b : Fin n, a ≠ b →
      ((Finset.univ.filter fun v : Fin m => G a v = edge) ∩
       (Finset.univ.filter fun v : Fin m => G b v = edge)).card ≤ 1)
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
    cases edge
    · have hinter : (Finset.univ.filter fun v : Fin m => G a1 v = false) ∩
          (Finset.univ.filter fun v : Fin m => G a2 v = false) = Finset.univ := by
        ext v; simp [hf1, hf2]
      have hle := hno4 a1 a2 hne
      rw [hinter] at hle
      simp at hle
      omega
    · have h2 := hdR a1
      have hempty : (Finset.univ.filter fun v : Fin m => G a1 v = true) = ∅ := by
        ext v; simp [hf1]
      rw [hempty] at h2
      simp at h2
  · have hno4C := noFour_symm G edge hno4
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
    cases edge
    · have hinter : (Finset.univ.filter fun u : Fin n => G u c1 = false) ∩
          (Finset.univ.filter fun u : Fin n => G u c2 = false) = Finset.univ := by
        ext u; simp [hf1, hf2]
      have hle := hno4C c1 c2 hne
      rw [hinter] at hle
      simp at hle
      omega
    · have h2 := hdC c1
      have hempty : (Finset.univ.filter fun u : Fin n => G u c1 = true) = ∅ := by
        ext u; simp [hf1]
      rw [hempty] at h2
      simp at h2

theorem wiresAux_agree_skip2 (u1 u2 : ℕ) (gs : List Gate) (w1 w2 : List Bool)
    (hun : ∀ g ∈ gs, u1 ∉ g.inputs ∧ u2 ∉ g.inputs)
    (hlen : w1.length = w2.length)
    (hagree : ∀ w, w ≠ u1 → w ≠ u2 → w1.getD w false = w2.getD w false) :
    (wiresAux gs w1).length = (wiresAux gs w2).length ∧
      (∀ w, w ≠ u1 → w ≠ u2 → (wiresAux gs w1).getD w false = (wiresAux gs w2).getD w false) := by
  induction gs generalizing w1 w2 with
  | nil => exact ⟨hlen, hagree⟩
  | cons g gs ih =>
    rw [wiresAux_cons, wiresAux_cons]
    obtain ⟨hu1, hu2⟩ := hun g (List.mem_cons_self ..)
    have hgs : ∀ g' ∈ gs, u1 ∉ g'.inputs ∧ u2 ∉ g'.inputs :=
      fun g' hg' => hun g' (List.mem_cons_of_mem _ hg')
    have hbit :
        g.op.eval (g.inputs.map fun i => w1.getD i false) =
        g.op.eval (g.inputs.map fun i => w2.getD i false) := by
      congr 1
      apply List.map_congr_left
      intro i hi
      exact hagree i (fun h => hu1 (h ▸ hi)) (fun h => hu2 (h ▸ hi))
    rw [hbit]
    apply ih _ _ hgs (by simp [hlen])
    intro w hw1 hw2
    by_cases hlt : w < w1.length
    · rw [getD_append_left w1 _ false w hlt, getD_append_left w2 _ false w (hlen ▸ hlt)]
      exact hagree w hw1 hw2
    · by_cases heq : w = w1.length
      · subst heq
        rw [getD_append_right w1 _ false w1.length (le_refl _),
          hlen, getD_append_right w2 _ false w2.length (le_refl _)]
      · rw [getD_of_ge (w1 ++ _) false w (by simp; omega),
          getD_of_ge (w2 ++ _) false w (by simp; omega)]

theorem unread_le_two {n m : ℕ} (G : Fin n → Fin m → Bool) (edge : Bool) (C : Circuit)
    (hdR : ∀ a : Fin n, 2 ≤ (Finset.univ.filter fun v : Fin m => G a v = edge).card)
    (hdC : ∀ c : Fin m, 2 ≤ (Finset.univ.filter fun u : Fin n => G u c = edge).card)
    (hno4 : ∀ a b : Fin n, a ≠ b →
      ((Finset.univ.filter fun v : Fin m => G a v = edge) ∩
       (Finset.univ.filter fun v : Fin m => G b v = edge)).card ≤ 1)
    (hrep : Represents G C)
    (hout : n + m ≤ C.output) :
    ((Finset.range (n + m)).filter (fun w => readsIn C (Finset.range C.size) w = 0)).card ≤ 2 := by
  have hun_of_zero : ∀ w, readsIn C (Finset.range C.size) w = 0 →
      ∀ g ∈ C.gates, w ∉ g.inputs := by
    intro w hz g hg hmem
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
    have hcnt : 0 < (gateAt C j).inputs.count w := by
      rw [gateAt_eq_getElem C j hj]
      exact List.count_pos_iff.mpr hmem
    have hle : (gateAt C j).inputs.count w ≤ readsIn C (Finset.range C.size) w := by
      unfold readsIn
      exact Finset.single_le_sum (f := fun t => (gateAt C t).inputs.count w)
        (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (show j < C.size from hj))
    omega
  let urR := (Finset.range n).filter (fun w => readsIn C (Finset.range C.size) w = 0)
  let urC := (Finset.range m).filter (fun j => readsIn C (Finset.range C.size) (n + j) = 0)
  have hR1 : urR.card ≤ 1 := by
    by_contra hgt
    obtain ⟨w1, hw1, w2, hw2, hne⟩ := Finset.one_lt_card.mp (by omega : 1 < urR.card)
    obtain ⟨hw1lt, hw1z⟩ := Finset.mem_filter.mp hw1
    obtain ⟨hw2lt, hw2z⟩ := Finset.mem_filter.mp hw2
    have hw1_lt : w1 < n := Finset.mem_range.mp hw1lt
    have hw2_lt : w2 < n := Finset.mem_range.mp hw2lt
    let a1 : Fin n := ⟨w1, hw1_lt⟩
    let a2 : Fin n := ⟨w2, hw2_lt⟩
    have ha_ne : a1 ≠ a2 := fun h => hne (congrArg Fin.val h)
    have hsame : ∀ v : Fin m, G a1 v = G a2 v := by
      intro v
      rw [← hrep a1 v, ← hrep a2 v, circuit_eval_eq, circuit_eval_eq]
      have hskip := (wiresAux_agree_skip2 w1 w2 C.gates (oneEach a1 v) (oneEach a2 v)
        (fun g hg => ⟨hun_of_zero w1 hw1z g hg, hun_of_zero w2 hw2z g hg⟩)
        (by rw [oneEach_length, oneEach_length]) ?_).2 C.output (by omega) (by omega)
      · exact hskip
      · intro k hk1 hk2
        by_cases hkn : k < n
        · rw [oneEach_getD_left a1 v k hkn, oneEach_getD_left a2 v k hkn]
          simp [a1, a2, hk1, hk2]
        · by_cases hkm : k < n + m
          · have hkeq : k = n + (k - n) := by omega
            rw [hkeq, oneEach_getD_right a1 v (k - n) (by omega),
              oneEach_getD_right a2 v (k - n) (by omega)]
          · rw [getD_of_ge (oneEach a1 v) false k (by rw [oneEach_length]; omega),
              getD_of_ge (oneEach a2 v) false k (by rw [oneEach_length]; omega)]
    have heq : (Finset.univ.filter fun v : Fin m => G a1 v = edge) ∩
        (Finset.univ.filter fun v : Fin m => G a2 v = edge) =
        (Finset.univ.filter fun v : Fin m => G a1 v = edge) := by
      ext v; simp [hsame v]
    have hle := hno4 a1 a2 ha_ne
    rw [heq] at hle
    have h2 := hdR a1
    omega
  have hC1 : urC.card ≤ 1 := by
    have hno4C := noFour_symm G edge hno4
    by_contra hgt
    obtain ⟨j1, hj1, j2, hj2, hne⟩ := Finset.one_lt_card.mp (by omega : 1 < urC.card)
    obtain ⟨hj1lt, hj1z⟩ := Finset.mem_filter.mp hj1
    obtain ⟨hj2lt, hj2z⟩ := Finset.mem_filter.mp hj2
    have hj1_lt : j1 < m := Finset.mem_range.mp hj1lt
    have hj2_lt : j2 < m := Finset.mem_range.mp hj2lt
    let c1 : Fin m := ⟨j1, hj1_lt⟩
    let c2 : Fin m := ⟨j2, hj2_lt⟩
    have hc_ne : c1 ≠ c2 := fun h => hne (congrArg Fin.val h)
    have hsame : ∀ u : Fin n, G u c1 = G u c2 := by
      intro u
      rw [← hrep u c1, ← hrep u c2, circuit_eval_eq, circuit_eval_eq]
      have hskip := (wiresAux_agree_skip2 (n + j1) (n + j2) C.gates (oneEach u c1) (oneEach u c2)
        (fun g hg => ⟨hun_of_zero (n + j1) hj1z g hg, hun_of_zero (n + j2) hj2z g hg⟩)
        (by rw [oneEach_length, oneEach_length]) ?_).2 C.output (by omega) (by omega)
      · exact hskip
      · intro k hk1 hk2
        by_cases hkn : k < n
        · rw [oneEach_getD_left u c1 k hkn, oneEach_getD_left u c2 k hkn]
        · by_cases hkm : k < n + m
          · have hkeq : k = n + (k - n) := by omega
            have h1 : k - n ≠ j1 := by omega
            have h2 : k - n ≠ j2 := by omega
            rw [hkeq, oneEach_getD_right u c1 (k - n) (by omega),
              oneEach_getD_right u c2 (k - n) (by omega)]
            simp [c1, c2, h1, h2]
          · rw [getD_of_ge (oneEach u c1) false k (by rw [oneEach_length]; omega),
              getD_of_ge (oneEach u c2) false k (by rw [oneEach_length]; omega)]
    have heq : (Finset.univ.filter fun u : Fin n => G u c1 = edge) ∩
        (Finset.univ.filter fun u : Fin n => G u c2 = edge) =
        (Finset.univ.filter fun u : Fin n => G u c1 = edge) := by
      ext u; simp [hsame u]
    have hle := hno4C c1 c2 hc_ne
    rw [heq] at hle
    have h2 := hdC c1
    omega
  have hsub : (Finset.range (n + m)).filter (fun w => readsIn C (Finset.range C.size) w = 0) ⊆
      urR ∪ urC.image (fun j => n + j) := by
    intro w hw
    obtain ⟨hwlt, hwz⟩ := Finset.mem_filter.mp hw
    have hwlt' := Finset.mem_range.mp hwlt
    by_cases hwn : w < n
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hwn, hwz⟩)
    · apply Finset.mem_union_right
      refine Finset.mem_image.mpr ⟨w - n, ?_, by omega⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),
        by simpa [Nat.add_sub_cancel' (Nat.le_of_not_lt hwn)] using hwz⟩
  calc ((Finset.range (n + m)).filter (fun w => readsIn C (Finset.range C.size) w = 0)).card
      ≤ (urR ∪ urC.image (fun j => n + j)).card := Finset.card_le_card hsub
    _ ≤ urR.card + (urC.image (fun j => n + j)).card := Finset.card_union_le _ _
    _ ≤ urR.card + urC.card := Nat.add_le_add_left Finset.card_image_le _
    _ ≤ 2 := by omega

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

theorem unread_zero_of_mono {n m : ℕ} (G : Fin n → Fin m → Bool) (edge : Bool) (C : Circuit)
    (hn3 : 3 ≤ n) (hm3 : 3 ≤ m)
    (hdR : ∀ a : Fin n, 2 ≤ (Finset.univ.filter fun v : Fin m => G a v = edge).card)
    (hdC : ∀ c : Fin m, 2 ≤ (Finset.univ.filter fun u : Fin n => G u c = edge).card)
    (hno4 : ∀ a b : Fin n, a ≠ b →
      ((Finset.univ.filter fun v : Fin m => G a v = edge) ∩
       (Finset.univ.filter fun v : Fin m => G b v = edge)).card ≤ 1)
    (hmono : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hrep : Represents G C)
    (hout : n + m ≤ C.output) :
    ((Finset.range (n + m)).filter (fun w => readsIn C (Finset.range C.size) w = 0)).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro w hw hzero
  have hwlt := Finset.mem_range.mp hw
  have hun : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ w ∉ g.inputs := by
    intro g hg
    refine ⟨hmono g hg, ?_⟩
    intro hmem
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
    have hcnt : 0 < (gateAt C j).inputs.count w := by
      rw [gateAt_eq_getElem C j hj]
      exact List.count_pos_iff.mpr hmem
    have hle : (gateAt C j).inputs.count w ≤ readsIn C (Finset.range C.size) w := by
      unfold readsIn
      exact Finset.single_le_sum (f := fun t => (gateAt C t).inputs.count w)
        (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (show j < C.size from hj))
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
    cases edge
    · have hsub : (Finset.univ.filter fun v : Fin m => G u1 v = false) ⊆
          (Finset.univ.filter fun v : Fin m => G u0 v = false) ∩
          (Finset.univ.filter fun v : Fin m => G u1 v = false) := by
        intro v hv
        simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
        refine ⟨?_, hv⟩
        cases h0 : G u0 v
        · rfl
        · have ht := hle_row u1 v h0; rw [hv] at ht; cases ht
      have hcard := (hdR u1).trans (Finset.card_le_card hsub)
      have hle := hno4 u0 u1 hne.symm
      omega
    · have hsub : (Finset.univ.filter fun v : Fin m => G u0 v = true) ⊆
          (Finset.univ.filter fun v : Fin m => G u0 v = true) ∩
          (Finset.univ.filter fun v : Fin m => G u1 v = true) := by
        intro v hv
        simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
        exact ⟨hv, hle_row u1 v hv⟩
      have hcard := (hdR u0).trans (Finset.card_le_card hsub)
      have hle := hno4 u0 u1 hne.symm
      omega
  · have hno4C := noFour_symm G edge hno4
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
    cases edge
    · have hsub : (Finset.univ.filter fun u : Fin n => G u v1 = false) ⊆
          (Finset.univ.filter fun u : Fin n => G u v0 = false) ∩
          (Finset.univ.filter fun u : Fin n => G u v1 = false) := by
        intro u hu
        simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
        refine ⟨?_, hu⟩
        cases h0 : G u v0
        · rfl
        · have ht := hle_col u v1 h0; rw [hu] at ht; cases ht
      have hcard := (hdC v1).trans (Finset.card_le_card hsub)
      have hle := hno4C v0 v1 hne.symm
      omega
    · have hsub : (Finset.univ.filter fun u : Fin n => G u v0 = true) ⊆
          (Finset.univ.filter fun u : Fin n => G u v0 = true) ∩
          (Finset.univ.filter fun u : Fin n => G u v1 = true) := by
        intro u hu
        simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
        exact ⟨hu, hle_col u v1 hu⟩
      have hcard := (hdC v0).trans (Finset.card_le_card hsub)
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
    have h3 : (∑ w ∈ S, if a = w then 1 else 0) = 1 := by
      simp [Finset.sum_ite_eq, ha]
    omega

theorem sum_range_countP {α : Type*} (l : List α) (d : α) (p : α → Bool) :
    (∑ k ∈ Finset.range l.length, if p (l.getD k d) then 1 else 0) = l.countP p := by
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton l a ih =>
    rw [List.length_append, List.length_singleton, Finset.range_add_one,
      Finset.sum_insert (by simp), List.countP_append, List.countP_singleton]
    have hlast : (l ++ [a]).getD l.length d = a := by
      rw [getD_append_right l [a] d l.length (le_refl _)]
      simp
    have hrest : ∑ k ∈ Finset.range l.length, (if p ((l ++ [a]).getD k d) then 1 else 0) =
        ∑ k ∈ Finset.range l.length, (if p (l.getD k d) then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [getD_append_left l [a] d k (Finset.mem_range.mp hk)]
    rw [hlast, hrest, ih]
    cases p a
    · simp
    · simp; omega

theorem neg_card_eq_notCount (C : Circuit) :
    (@Finset.filter ℕ (fun k => (gateAt C k).op = GateOp.not)
      (fun k => Classical.propDecidable ((gateAt C k).op = GateOp.not))
      (Finset.range C.size)).card = notCount C.gates := by
  rw [Finset.card_filter]
  have heq : ∀ k ∈ Finset.range C.size,
      (@ite ℕ ((gateAt C k).op = GateOp.not)
        (Classical.propDecidable ((gateAt C k).op = GateOp.not)) 1 0) =
      if isNot (C.gates.getD k ⟨GateOp.or, []⟩) then 1 else 0 := by
    intro k _
    unfold isNot gateAt
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd (@decide_eq_true _ (Classical.propDecidable _) h1) h2
    · exact absurd (@of_decide_eq_true _ (Classical.propDecidable _) h2) h1
    · rfl
  rw [Finset.sum_congr rfl heq]
  exact sum_range_countP C.gates ⟨GateOp.or, []⟩ isNot

theorem handshaking_not (N : ℕ) (C : Circuit)
    (hshape : GoodShape C)
    (hback : ReadsBack N C)
    (hsz : 0 < C.size)
    (hused : ∀ j < C.size, j + 1 < C.size → 0 < readsIn C (Finset.range C.size) (N + j)) :
    let reads := readsIn C (Finset.range C.size)
    let shared := (Finset.range (N + C.size)).filter (fun w => 2 ≤ reads w)
    let unreadRaw := (Finset.range N).filter (fun w => reads w = 0)
    let D := ∑ w ∈ shared, (reads w - 1)
    binCount C.gates + unreadRaw.card + 1 = N + D ∧
      (∑ w ∈ shared, reads w) = D + shared.card ∧
      shared.card ≤ D := by
  dsimp only
  let reads := readsIn C (Finset.range C.size)
  let shared := (Finset.range (N + C.size)).filter (fun w => 2 ≤ reads w)
  let unreadRaw := (Finset.range N).filter (fun w => reads w = 0)
  let D := ∑ w ∈ shared, (reads w - 1)
  change binCount C.gates + unreadRaw.card + 1 = N + D ∧
    (∑ w ∈ shared, reads w) = D + shared.card ∧ shared.card ≤ D
  have hlen_sz : C.gates.length = C.size := rfl
  have hsum_all : ∑ w ∈ Finset.range (N + C.size), reads w =
      2 * binCount C.gates + notCount C.gates := by
    change ∑ w ∈ Finset.range (N + C.size),
      ∑ j ∈ Finset.range C.size, (gateAt C j).inputs.count w =
      2 * binCount C.gates + notCount C.gates
    rw [Finset.sum_comm]
    have heach : ∀ j ∈ Finset.range C.size,
        ∑ w ∈ Finset.range (N + C.size), (gateAt C j).inputs.count w =
        if isNot (C.gates.getD j ⟨GateOp.or, []⟩) then 1 else 2 := by
      intro j hj
      have hj' : j < C.gates.length := Finset.mem_range.mp hj
      rw [sum_count_eq_length]
      · rw [gateAt_eq_getElem C j hj']
        have hget : C.gates.getD j ⟨GateOp.or, []⟩ = C.gates[j] := gateAt_eq_getElem C j hj'
        rw [hget]
        rcases hshape C.gates[j] (List.getElem_mem hj') with ⟨hop, hlen2⟩ | ⟨hop, hlen1⟩
        · have hnotf : isNot C.gates[j] = false := by
            unfold isNot
            rcases hop with h | h <;> simp [h]
          simp [hnotf, hlen2]
        · have hnott : isNot C.gates[j] = true := by
            unfold isNot
            simp [hop]
          simp [hnott, hlen1]
      · intro i hi
        exact Finset.mem_range.mpr (Nat.lt_trans (hback j hj' i hi) (by omega))
    rw [Finset.sum_congr rfl heach]
    have hsplit_sum :
        (∑ j ∈ Finset.range C.size, if isNot (C.gates.getD j ⟨GateOp.or, []⟩) then 1 else 2) =
        (∑ j ∈ Finset.range C.size, if isNot (C.gates.getD j ⟨GateOp.or, []⟩) then 1 else 0) +
        2 * (∑ j ∈ Finset.range C.size, if !isNot (C.gates.getD j ⟨GateOp.or, []⟩) then 1 else 0) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      cases isNot (C.gates.getD j ⟨GateOp.or, []⟩) <;> simp
    rw [hsplit_sum]
    have h1 := sum_range_countP C.gates ⟨GateOp.or, []⟩ isNot
    have h2 := sum_range_countP C.gates ⟨GateOp.or, []⟩ (fun g => !isNot g)
    rw [← hlen_sz, h1, h2]
    change notCount C.gates + 2 * binCount C.gates = 2 * binCount C.gates + notCount C.gates
    omega
  have hlast_zero : reads (N + C.size - 1) = 0 := by
    change ∑ j ∈ Finset.range C.size, (gateAt C j).inputs.count (N + C.size - 1) = 0
    apply Finset.sum_eq_zero
    intro j hj
    have hj' : j < C.gates.length := Finset.mem_range.mp hj
    rw [List.count_eq_zero]
    intro hmem
    have hlt := hback j hj' _ hmem
    omega
  have hsum_init : ∑ w ∈ Finset.range (N + C.size - 1), reads w =
      2 * binCount C.gates + notCount C.gates := by
    have hsplit : Finset.range (N + C.size) =
        insert (N + C.size - 1) (Finset.range (N + C.size - 1)) := by
      conv_lhs => rw [show N + C.size = (N + C.size - 1) + 1 by omega]
      exact Finset.range_add_one
    rw [hsplit, Finset.sum_insert (by simp)] at hsum_all
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
  have hsub_unread : unreadRaw ⊆ Finset.range (N + C.size - 1) := by
    intro w hw
    have hr := Finset.mem_range.mp (Finset.mem_filter.mp hw).1
    exact Finset.mem_range.mpr (by omega)
  have hdj_su : Disjoint shared unreadRaw := by
    rw [Finset.disjoint_left]
    intro w h1 h2
    have := (Finset.mem_filter.mp h1).2
    have := (Finset.mem_filter.mp h2).2
    omega
  have hsub_union : shared ∪ unreadRaw ⊆ Finset.range (N + C.size - 1) :=
    Finset.union_subset hsub_shared hsub_unread
  have hones : ∀ w ∈ Finset.range (N + C.size - 1) \ (shared ∪ unreadRaw), reads w = 1 := by
    intro w hw
    obtain ⟨hr, hns⟩ := Finset.mem_sdiff.mp hw
    have hwlt := Finset.mem_range.mp hr
    have hnot_sh : ¬ (2 ≤ reads w) := by
      intro h2
      apply hns
      exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), h2⟩)
    have hpos : 1 ≤ reads w := by
      by_cases hwn : w < N
      · by_contra h0
        apply hns
        exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hwn, by omega⟩)
      · have hj : w - N < C.size := by omega
        have hj1 : w - N + 1 < C.size := by omega
        have hweq : N + (w - N) = w := by omega
        have hp := hused (w - N) hj hj1
        rw [hweq] at hp
        exact hp
    omega
  have hsum_unread : ∑ w ∈ unreadRaw, reads w = 0 := by
    apply Finset.sum_eq_zero
    intro w hw
    exact (Finset.mem_filter.mp hw).2
  have hsum_split : ∑ w ∈ Finset.range (N + C.size - 1), reads w =
      ∑ w ∈ shared, reads w + (Finset.range (N + C.size - 1) \ (shared ∪ unreadRaw)).card := by
    rw [← Finset.sum_sdiff hsub_union, add_comm, Finset.sum_union hdj_su, hsum_unread, Nat.add_zero]
    congr 1
    rw [Finset.sum_congr rfl hones]
    simp
  have hcard_sdiff : (Finset.range (N + C.size - 1) \ (shared ∪ unreadRaw)).card +
      shared.card + unreadRaw.card = N + C.size - 1 := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub_union, Finset.card_range,
      Finset.card_union_of_disjoint hdj_su]
    have hle := Finset.card_le_card hsub_union
    rw [Finset.card_range, Finset.card_union_of_disjoint hdj_su] at hle
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
  have hbn := notCount_add_binCount C.gates
  refine ⟨?_, hD_add.symm, hcard_le_D⟩
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

theorem main : ∀ (n m d : ℕ) (G : Fin n → Fin m → Bool) (edge : Bool)
    (C : Circuit),
    let nbrR := fun (a : Fin n) => Finset.univ.filter (fun v : Fin m => G a v = edge)
    let nbrC := fun (c : Fin m) => Finset.univ.filter (fun u : Fin n => G u c = edge)
    2 ≤ d →
    (∀ a, 2 ≤ (nbrR a).card ∧ (nbrR a).card ≤ d) →
    (∀ c, 2 ≤ (nbrC c).card ∧ (nbrC c).card ≤ d) →
    (∀ a b, a ≠ b → ((nbrR a) ∩ (nbrR b)).card ≤ 1) →
    FanInTwo C → Represents G C →
    let negs := C.gates.countP (fun g => @decide (g.op = GateOp.not) (Classical.propDecidable _))
    (28 * d + 1) * (n + m) + 12 * d * negs ≤ 28 * d * C.size + 78 * d + 2 := by
  intro n m d G edge C0 nbrR nbrC hd2 hdR hdC hno4 hfan0 hrep0 negs
  have hdR2 : ∀ a, 2 ≤ (nbrR a).card := fun a => (hdR a).1
  have hdC2 : ∀ c, 2 ≤ (nbrC c).card := fun c => (hdC c).1
  have hnegs_eq : negs = notCount C0.gates := rfl
  have hC0_split : notCount C0.gates + binCount C0.gates = C0.size := notCount_add_binCount C0.gates
  rcases dims_zero_or_ge_three G edge hdR2 hdC2 hno4 with ⟨rfl, rfl⟩ | ⟨hn3, hm3⟩
  · have hle : negs ≤ C0.size := by omega
    have h1 : 12 * d * negs ≤ 28 * d * negs := Nat.mul_le_mul_right negs (by omega)
    have h2 : 28 * d * negs ≤ 28 * d * C0.size := Nat.mul_le_mul_left (28 * d) hle
    omega
  let N := n + m
  rcases fold_const_all N C0 hfan0 with
    ⟨b, hb⟩ | ⟨i, hi, hfi⟩ | ⟨C1, hev1, hsh1, hbk1, hout_lo1, hout_hi1, hnot1, hbin1⟩
  · exfalso
    exact not_const_of_graph G edge hn3 hm3 hdR2 hno4 b
      (fun u v => (hrep0 u v).symm.trans (hb (oneEach u v) (oneEach_length u v)))
  · exfalso
    exact not_single_input_of_graph G edge hn3 hm3 hdR2 hdC2 hno4 i hi
      (fun u v => (hrep0 u v).symm.trans (hfi (oneEach u v) (oneEach_length u v)))
  obtain ⟨C, hev2, hshape, hback, hsz_pos, hout_eq, hused, hnot2, hbin2⟩ :=
    prune_unused N C1.size C1 rfl hsh1 hbk1 hout_lo1 hout_hi1
  have hrep : Represents G C := fun u v =>
    (hev2 (oneEach u v) (oneEach_length u v)).trans
      ((hev1 (oneEach u v) (oneEach_length u v)).trans (hrep0 u v))
  have hnot_le : notCount C.gates ≤ notCount C0.gates := hnot2.trans hnot1
  have hbin_le : binCount C.gates ≤ binCount C0.gates := hbin2.trans hbin1
  let gates := Finset.range C.size
  let gate := gateAt C
  let reads := readsIn C gates
  let neg := @Finset.filter ℕ (fun k => (gate k).op = GateOp.not)
    (fun k => Classical.propDecidable ((gate k).op = GateOp.not)) gates
  let shared := (Finset.range (N + C.size)).filter (fun w => 2 ≤ reads w)
  let sharedGates := gates.filter (fun k => 2 ≤ reads (N + k))
  let sharedRaw := (Finset.range N).filter (fun w => 2 ≤ reads w)
  let unreadRaw := (Finset.range N).filter (fun w => reads w = 0)
  let markedReads := ∑ w ∈ shared, reads w
  let once := (Finset.range N).filter (fun w => reads w = 1)
  let D := ∑ w ∈ shared, (reads w - 1)
  have hneg_eq : neg.card = notCount C.gates := neg_card_eq_notCount C
  have hu2 : unreadRaw.card ≤ 2 := unread_le_two G edge C hdR2 hdC2 hno4 hrep (by omega)
  obtain ⟨hhand, hmr_eq, hsh_le_D⟩ := handshaking_not N C hshape hback hsz_pos hused
  change binCount C.gates + unreadRaw.card + 1 = N + D at hhand
  change markedReads = D + shared.card at hmr_eq
  change shared.card ≤ D at hsh_le_D
  obtain ⟨pure, chains, e, hpure_le, hchains_le, he_pos, hdisj, hcov, hpure_ok, hchains_ok⟩ :=
    PEqualNP.Outside.L_meta_25644 N C hshape hback hsz_pos hout_eq hused
  dsimp only at hpure_le hchains_le he_pos hdisj hcov hpure_ok hchains_ok
  change pure.length + e ≤ sharedGates.card + neg.card + 1 at hpure_le
  change chains.length + e ≤ 2 * (markedReads + neg.card) at hchains_le
  change 0 < markedReads + neg.card → 0 < e at he_pos
  change (pure ++ chains).toFinset.biUnion (fun S => S) = once at hcov
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
  have hN_part : once.card + sharedRaw.card + unreadRaw.card = N := by
    have hu : once ∪ sharedRaw ∪ unreadRaw = Finset.range N := by
      ext w
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_range, once, sharedRaw, unreadRaw]
      constructor
      · rintro ((⟨h, _⟩ | ⟨h, _⟩) | ⟨h, _⟩) <;> exact h
      · intro h
        by_cases h0 : reads w = 0
        · exact Or.inr ⟨h, h0⟩
        · by_cases h2 : 2 ≤ reads w
          · exact Or.inl (Or.inr ⟨h, h2⟩)
          · exact Or.inl (Or.inl ⟨h, by omega⟩)
    have hd1 : Disjoint once sharedRaw := by
      rw [Finset.disjoint_left]
      intro w h1 h2
      have := (Finset.mem_filter.mp h1).2
      have := (Finset.mem_filter.mp h2).2
      omega
    have hd2' : Disjoint (once ∪ sharedRaw) unreadRaw := by
      rw [Finset.disjoint_left]
      intro w h1 h2
      have h2' := (Finset.mem_filter.mp h2).2
      rcases Finset.mem_union.mp h1 with ha | hb
      · have := (Finset.mem_filter.mp ha).2; omega
      · have := (Finset.mem_filter.mp hb).2; omega
    rw [← Finset.card_union_of_disjoint hd1, ← Finset.card_union_of_disjoint hd2', hu,
      Finset.card_range]
  have hblock_sub : ∀ S ∈ pure ++ chains, S ⊆ Finset.range N := by
    intro S hS w hw
    have hmem : w ∈ once := by
      rw [← hcov]
      exact Finset.mem_biUnion.mpr ⟨S, List.mem_toFinset.mpr hS, hw⟩
    exact (Finset.mem_filter.mp hmem).1
  have hcap_pure : ∀ S ∈ pure, S.card ≤ 4 * d := by
    intro S hS
    have hSsub := hblock_sub S (List.mem_append_left _ hS)
    obtain ⟨hS_eq, hS_card⟩ := split_block S hSsub
    let R : Finset (Fin n) := Finset.univ.filter (fun r => r.val ∈ S)
    let B : Finset (Fin m) := Finset.univ.filter (fun c => n + c.val ∈ S)
    change R.image (fun r => r.val) ∪ B.image (fun c => n + c.val) = S at hS_eq
    change S.card = R.card + B.card at hS_card
    rcases (hpure_ok S hS).2 with ⟨region, root, hreg_sub, hroot_mem, hroot0, hEprop, hreg_prop, hwire_prop⟩
    have h578 := PEqualNP.Outside.L_meta_25578 n m G C R B region ∅ root
      hback hrep hreg_sub (by rwa [hS_eq]) (by simp)
      (by intro w hw; simp at hw)
      (by intro k hk; rw [hS_eq]; exact hreg_prop k hk)
      hroot0
      (by intro w hw; rw [hS_eq] at hw; exact hwire_prop w hw)
    dsimp only at h578
    simp only [Finset.card_empty, Nat.add_zero] at h578
    have h577 := (PEqualNP.Outside.L_meta_25577 d 2 hd2 (le_refl 2)).1 n m G edge R B
      ⟨hdR, hdC, hno4, h578.1, h578.2.1, h578.2.2⟩
    have hcap : max (2 * d * 2) (2 * (d * (2 - 1)) + 2 * (d * (2 - 1) / 2)) ≤ 4 * d := by omega
    omega
  have hcap_chain : ∀ S ∈ chains, S.card ≤ 6 * d := by
    intro S hS
    have hSsub := hblock_sub S (List.mem_append_right _ hS)
    obtain ⟨hS_eq, hS_card⟩ := split_block S hSsub
    let R : Finset (Fin n) := Finset.univ.filter (fun r => r.val ∈ S)
    let B : Finset (Fin m) := Finset.univ.filter (fun c => n + c.val ∈ S)
    change R.image (fun r => r.val) ∪ B.image (fun c => n + c.val) = S at hS_eq
    change S.card = R.card + B.card at hS_card
    rcases (hchains_ok S hS).2 with ⟨b, region, root, hreg_sub, hroot_mem, hroot0, hEprop, hreg_prop, hwire_prop⟩
    have h578 := PEqualNP.Outside.L_meta_25578 n m G C R B region {b} root
      hback hrep hreg_sub (by rwa [hS_eq]) (by simp)
      (by intro w hw; rw [hS_eq]; exact hEprop w hw)
      (by intro k hk; rw [hS_eq]; exact hreg_prop k hk)
      hroot0
      (by intro w hw; rw [hS_eq] at hw; exact hwire_prop w hw)
    dsimp only at h578
    simp only [Finset.card_singleton] at h578
    have h577 := (PEqualNP.Outside.L_meta_25577 d 3 hd2 (by omega)).1 n m G edge R B
      ⟨hdR, hdC, hno4, h578.1, h578.2.1, h578.2.2⟩
    have hcap : max (2 * d * 3) (2 * (d * (3 - 1)) + 2 * (d * (3 - 1) / 2)) ≤ 6 * d := by omega
    omega
  have honce_le : once.card ≤ 4 * d * pure.length + 6 * d * chains.length := by
    rw [← hcov, biUnion_card_eq_sum _ hdisj, List.map_append, List.sum_append]
    have hp : (pure.map Finset.card).sum ≤ 4 * d * pure.length := by
      calc (pure.map Finset.card).sum
          ≤ (pure.map fun _ => 4 * d).sum := list_sum_le_of_forall _ _ _ hcap_pure
        _ = 4 * d * pure.length := by simp [mul_comm]
    have hq : (chains.map Finset.card).sum ≤ 6 * d * chains.length := by
      calc (chains.map Finset.card).sum
          ≤ (chains.map fun _ => 6 * d).sum := list_sum_le_of_forall _ _ _ hcap_chain
        _ = 6 * d * chains.length := by simp [mul_comm]
    exact Nat.add_le_add hp hq
  have hrestore : (28 * d + 1) * N ≤ 28 * d * binCount C.gates + 16 * d * notCount C.gates + 78 * d + 2 →
      (28 * d + 1) * N + 12 * d * negs ≤ 28 * d * C0.size + 78 * d + 2 := by
    intro hmain
    have h1 : 28 * d * binCount C.gates ≤ 28 * d * binCount C0.gates :=
      Nat.mul_le_mul_left (28 * d) hbin_le
    have h2 : 16 * d * notCount C.gates ≤ 16 * d * notCount C0.gates :=
      Nat.mul_le_mul_left (16 * d) hnot_le
    have h3 : 28 * d * C0.size = 28 * d * binCount C0.gates + 28 * d * notCount C0.gates := by
      rw [← hC0_split, Nat.mul_add, add_comm]
    have h4 : 16 * d * notCount C0.gates + 12 * d * negs = 28 * d * notCount C0.gates := by
      rw [hnegs_eq]; ring
    linarith
  apply hrestore
  by_cases hpos : 0 < markedReads + neg.card
  · have he1 : 1 ≤ e := he_pos hpos
    have hmul_p : 4 * d * (pure.length + e) ≤ 4 * d * (sharedGates.card + neg.card + 1) :=
      Nat.mul_le_mul_left (4 * d) hpure_le
    have hmul_q : 6 * d * (chains.length + e) ≤ 6 * d * (2 * (markedReads + neg.card)) :=
      Nat.mul_le_mul_left (6 * d) hchains_le
    have hmul_sh : 16 * d * (sharedRaw.card + sharedGates.card) ≤ 16 * d * D :=
      Nat.mul_le_mul_left (16 * d) (hsh_card ▸ hsh_le_D)
    have hsr_le : sharedRaw.card ≤ 4 * d * sharedRaw.card := by
      calc sharedRaw.card = 1 * sharedRaw.card := (Nat.one_mul _).symm
        _ ≤ 4 * d * sharedRaw.card := Nat.mul_le_mul_right _ (by omega)
    have he_mul : 10 * d ≤ 10 * d * e := by
      calc 10 * d = 10 * d * 1 := (Nat.mul_one _).symm
        _ ≤ 10 * d * e := Nat.mul_le_mul_left _ he1
    have hu_mul : (28 * d + 1) * unreadRaw.card ≤ (28 * d + 1) * 2 :=
      Nat.mul_le_mul_left (28 * d + 1) hu2
    have hhand_mul : 28 * d * (binCount C.gates + unreadRaw.card + 1) = 28 * d * (N + D) :=
      congrArg (fun t => 28 * d * t) hhand
    have hmr_mul : 12 * d * markedReads = 12 * d * D + 12 * d * sharedRaw.card + 12 * d * sharedGates.card := by
      rw [hmr_eq, hsh_card]; ring
    rw [hneg_eq] at hmul_p hmul_q
    linarith
  · have hmr0 : markedReads = 0 := by omega
    have hneg0 : neg.card = 0 := by omega
    have hnot0 : notCount C.gates = 0 := by omega
    have hD0 : D = 0 := by omega
    have hsh0 : shared.card = 0 := by omega
    have hsr0 : sharedRaw.card = 0 := by omega
    have hsg0 : sharedGates.card = 0 := by omega
    have hq0 : chains.length = 0 := by omega
    have hp1 : pure.length ≤ 1 := by omega
    have hmonoC : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
      intro g hg
      rcases hshape g hg with ⟨hop, _⟩ | ⟨hop, _⟩
      · exact hop
      · exfalso
        have hpos_not : 0 < notCount C.gates := by
          unfold notCount
          rw [List.countP_pos_iff]
          exact ⟨g, hg, by unfold isNot; simp [hop]⟩
        omega
    have hu0 : unreadRaw.card = 0 :=
      unread_zero_of_mono G edge C hn3 hm3 hdR2 hdC2 hno4 hmonoC hrep (by omega)
    have hN_le : N ≤ 4 * d := by
      have hp4 : 4 * d * pure.length ≤ 4 * d * 1 := Nat.mul_le_mul_left (4 * d) hp1
      rw [hq0, Nat.mul_zero, Nat.add_zero] at honce_le
      omega
    have hB_eq : binCount C.gates + 1 = N := by omega
    have hB_exp : 28 * d * binCount C.gates + 28 * d = 28 * d * N := by
      have hB_mul : 28 * d * (binCount C.gates + 1) = 28 * d * N :=
        congrArg (fun t => 28 * d * t) hB_eq
      rw [← hB_mul]; ring
    have hN_exp : (28 * d + 1) * N = 28 * d * N + N := by ring
    omega

end PEqualNP.Outside.L_meta_25645_aux

theorem PEqualNP.Outside.L_meta_25645 : (∀ (n m d : ℕ) (G : Fin n → Fin m → Bool) (edge : Bool)
    (C : PEqualNP.CircuitLowerBounds.Circuit),
  let nbrR := fun (a : Fin n) => Finset.univ.filter (fun v : Fin m => G a v = edge)
  let nbrC := fun (c : Fin m) => Finset.univ.filter (fun u : Fin n => G u c = edge)
  2 ≤ d →
  (∀ a, 2 ≤ (nbrR a).card ∧ (nbrR a).card ≤ d) →
  (∀ c, 2 ≤ (nbrC c).card ∧ (nbrC c).card ≤ d) →
  (∀ a b, a ≠ b → ((nbrR a) ∩ (nbrR b)).card ≤ 1) →
  PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.Represents.Represents G C →
  let negs := C.gates.countP (fun g => @decide (g.op = PEqualNP.CircuitLowerBounds.GateOp.not) (Classical.propDecidable _))
  (28 * d + 1) * (n + m) + 12 * d * negs ≤ 28 * d * C.size + 78 * d + 2) :=
  PEqualNP.Outside.L_meta_25645_aux.main
