import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25444

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents PEqualNP.EdgeOwnership

def gateStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl gateStep x := rfl

lemma getD_append_left {α : Type*} (a b : List α) (i : ℕ) (d : α) (h : i < a.length) :
    (a ++ b).getD i d = a.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma getD_append_right {α : Type*} (a b : List α) (i : ℕ) (d : α) (h : a.length ≤ i) :
    (a ++ b).getD i d = b.getD (i - a.length) d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

lemma getD_eq_default {α : Type*} (a : List α) (i : ℕ) (d : α) (h : a.length ≤ i) :
    a.getD i d = d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

lemma list_any_congr {α : Type*} (l : List α) (f g : α → Bool) (h : ∀ x ∈ l, f x = g x) :
    l.any f = l.any g := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.any_cons]
    rw [h a (by simp), ih (fun x hx => h x (by simp [hx]))]

lemma list_map_congr {α β : Type*} (l : List α) (f g : α → β) (h : ∀ x ∈ l, f x = g x) :
    l.map f = l.map g := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.map_cons]
    rw [h a (by simp), ih (fun x hx => h x (by simp [hx]))]

lemma foldl_gateStep_length (gs : List Gate) (x : List Bool) :
    (gs.foldl gateStep x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, gateStep, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_gateStep_getD_lt (gs : List Gate) (x : List Bool) (i : ℕ) (h : i < x.length) :
    (gs.foldl gateStep x).getD i false = x.getD i false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    have h1 : i < (gateStep x g).length := by
      simp only [gateStep, List.length_append, List.length_singleton]
      omega
    rw [List.foldl_cons, ih (gateStep x g) h1]
    exact getD_append_left x _ i false h

lemma foldl_gateStep_getD_add (gs : List Gate) (x : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl gateStep x).getD (x.length + j) false =
      (gs.getD j ⟨GateOp.and, []⟩).op.eval
        ((gs.getD j ⟨GateOp.and, []⟩).inputs.map
          fun i => ((gs.take j).foldl gateStep x).getD i false) := by
  induction gs generalizing x j with
  | nil => simp at hj
  | cons g0 gs ih =>
    cases j with
    | zero =>
      simp only [Nat.add_zero, List.foldl_cons, List.take_zero, List.foldl_nil,
        List.getD_cons_zero]
      have h1 : x.length < (gateStep x g0).length := by
        simp only [gateStep, List.length_append, List.length_singleton]
        omega
      rw [foldl_gateStep_getD_lt gs (gateStep x g0) x.length h1]
      simp only [gateStep]
      rw [getD_append_right x _ x.length false (Nat.le_refl _)]
      simp
    | succ k =>
      have hk : k < gs.length := by
        simp only [List.length_cons] at hj
        omega
      have hlen : (gateStep x g0).length = x.length + 1 := by
        simp [gateStep]
      have hidx : x.length + (k + 1) = (gateStep x g0).length + k := by omega
      rw [List.foldl_cons, hidx, ih (gateStep x g0) k hk]
      simp [List.take_succ_cons]

lemma oneEach_length {n m : ℕ} (u : Fin n) (v : Fin m) :
    (oneEach u v).length = n + m := by
  simp [oneEach]

lemma oneEach_getD_left {n m : ℕ} (u : Fin n) (v : Fin m) (w : ℕ) (hw : w < n) :
    (oneEach u v).getD w false = decide (⟨w, hw⟩ = u) := by
  unfold oneEach
  rw [getD_append_left _ _ w false (by simp [hw])]
  simp [List.getD_eq_getElem?_getD, hw]

lemma oneEach_getD_right {n m : ℕ} (u : Fin n) (v : Fin m) (w : ℕ) (h1 : n ≤ w) (h2 : w < n + m) :
    (oneEach u v).getD w false = decide (⟨w - n, by omega⟩ = v) := by
  unfold oneEach
  rw [getD_append_right _ _ w false (by simp [h1])]
  have hsub : w - n < m := by omega
  simp [List.getD_eq_getElem?_getD, hsub]

def orChain (nextWire acc : ℕ) : List ℕ → List Gate × ℕ
  | [] => ([], acc)
  | b :: rest =>
    let res := orChain (nextWire + 1) nextWire rest
    (⟨GateOp.or, [acc, b]⟩ :: res.1, res.2)

lemma orChain_len (ws : List ℕ) (nextWire acc : ℕ) :
    (orChain nextWire acc ws).1.length = ws.length := by
  induction ws generalizing nextWire acc with
  | nil => rfl
  | cons b rest ih => simp [orChain, ih]

lemma orChain_out_lt (ws : List ℕ) (nextWire acc : ℕ) (hacc : acc < nextWire) :
    (orChain nextWire acc ws).2 < nextWire + ws.length := by
  induction ws generalizing nextWire acc with
  | nil =>
    simp only [orChain, List.length_nil]
    omega
  | cons b rest ih =>
    simp only [orChain, List.length_cons]
    have h := ih (nextWire + 1) nextWire (by omega)
    omega

lemma orChain_fanInTwo (ws : List ℕ) (nextWire acc : ℕ) :
    ∀ g ∈ (orChain nextWire acc ws).1,
      g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  induction ws generalizing nextWire acc with
  | nil =>
    intro g hg
    simp [orChain] at hg
  | cons b rest ih =>
    intro g hg
    simp only [orChain, List.mem_cons] at hg
    rcases hg with rfl | hg
    · exact ⟨by simp, by simp⟩
    · exact ih (nextWire + 1) nextWire g hg

lemma orChain_eval (ws : List ℕ) (w : List Bool) (acc : ℕ)
    (hws : ∀ b ∈ ws, b < w.length) :
    ((orChain w.length acc ws).1.foldl gateStep w).getD (orChain w.length acc ws).2 false =
      (w.getD acc false || ws.any (fun b => w.getD b false)) := by
  induction ws generalizing w acc with
  | nil => simp [orChain]
  | cons a rest ih =>
    simp only [orChain, List.foldl_cons, List.any_cons]
    let g : Gate := ⟨GateOp.or, [acc, a]⟩
    let w1 := gateStep w g
    have hw1_len : w1.length = w.length + 1 := by simp [w1, gateStep]
    have hws1 : ∀ b ∈ rest, b < w1.length := by
      intro b hb
      have := hws b (by simp [hb])
      omega
    have hih := ih w1 w.length hws1
    rw [hw1_len] at hih
    change ((orChain (w.length + 1) w.length rest).1.foldl gateStep w1).getD
      (orChain (w.length + 1) w.length rest).2 false = _
    rw [hih]
    have hacc1 : w1.getD w.length false = (w.getD acc false || w.getD a false) := by
      simp only [w1, gateStep]
      rw [getD_append_right w _ w.length false (Nat.le_refl _)]
      simp [g, GateOp.eval]
    have hrest : rest.any (fun b => w1.getD b false) = rest.any (fun b => w.getD b false) := by
      apply list_any_congr
      intro b hb
      exact getD_append_left w _ b false (hws b (by simp [hb]))
    rw [hacc1, hrest, Bool.or_assoc]

def remapWire (n m shift dead wU wW : ℕ) (U : Finset (Fin n)) (W : Finset (Fin m))
    (u0 : Fin n) (v0 : Fin m) (w : ℕ) : ℕ :=
  if h1 : w < n then
    let u : Fin n := ⟨w, h1⟩
    if u = u0 then wU
    else if u ∈ U then dead
    else w
  else if h2 : w < n + m then
    let v : Fin m := ⟨w - n, by omega⟩
    if v = v0 then wW
    else if v ∈ W then dead
    else w
  else
    w + shift

def remapGate (f : ℕ → ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map f⟩

lemma foldl_coneStep_length (K : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep K) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, coneStep, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_coneStep_getD_lt (K : ℕ) (gs : List Gate) (cs : List (List ℕ)) (i : ℕ)
    (h : i < cs.length) :
    (gs.foldl (coneStep K) cs).getD i [] = cs.getD i [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    have h1 : i < (coneStep K cs g).length := by
      simp only [coneStep, List.length_append, List.length_singleton]
      omega
    rw [List.foldl_cons, ih (coneStep K cs g) h1]
    exact getD_append_left cs _ i [] h

lemma foldl_coneStep_getD_add (K : ℕ) (gs : List Gate) (cs : List (List ℕ)) (j : ℕ)
    (hj : j < gs.length) :
    (gs.foldl (coneStep K) cs).getD (cs.length + j) [] =
      let prev := (gs.take j).foldl (coneStep K) cs
      let g := gs.getD j ⟨GateOp.and, []⟩
      (g.inputs.filter (fun w => decide (K ≤ w ∧ w < K + (cs.length + j)))).flatMap
        (fun w => (w - K) :: prev.getD (w - K) []) := by
  induction gs generalizing cs j with
  | nil => simp at hj
  | cons g0 gs ih =>
    cases j with
    | zero =>
      simp only [Nat.add_zero, List.foldl_cons, List.take_zero, List.foldl_nil,
        List.getD_cons_zero]
      have h1 : cs.length < (coneStep K cs g0).length := by
        simp only [coneStep, List.length_append, List.length_singleton]
        omega
      rw [foldl_coneStep_getD_lt K gs (coneStep K cs g0) cs.length h1]
      simp only [coneStep]
      rw [getD_append_right cs _ cs.length [] (Nat.le_refl _)]
      simp
    | succ k =>
      have hk : k < gs.length := by
        simp only [List.length_cons] at hj
        omega
      have hlen : (coneStep K cs g0).length = cs.length + 1 := by
        simp [coneStep]
      have hidx : cs.length + (k + 1) = (coneStep K cs g0).length + k := by omega
      rw [List.foldl_cons, hidx, ih (coneStep K cs g0) k hk]
      simp only [List.take_succ_cons, List.foldl_cons, List.getD_cons_succ]

def TransCone (cs : List (List ℕ)) : Prop :=
  ∀ j < cs.length, ∀ i ∈ cs.getD j [], i < j ∧ ∀ a ∈ cs.getD i [], a ∈ cs.getD j []

lemma coneStep_trans (K : ℕ) (cs : List (List ℕ)) (g : Gate) (h : TransCone cs) :
    TransCone (coneStep K cs g) := by
  intro j hj i hi
  simp only [coneStep, List.length_append, List.length_singleton] at hj
  by_cases hlt : j < cs.length
  · rw [coneStep] at hi ⊢
    rw [getD_append_left cs _ j [] hlt] at hi ⊢
    obtain ⟨hij, hsub⟩ := h j hlt i hi
    refine ⟨hij, ?_⟩
    intro a ha
    rw [getD_append_left cs _ i [] (by omega)] at ha
    exact hsub a ha
  · have hjeq : j = cs.length := by omega
    subst hjeq
    rw [coneStep] at hi ⊢
    rw [getD_append_right cs _ cs.length [] (Nat.le_refl _)] at hi ⊢
    simp only [Nat.sub_self, List.getD_cons_zero, List.mem_flatMap, List.mem_filter,
      decide_eq_true_eq, List.mem_cons] at hi ⊢
    obtain ⟨w, ⟨hw_in, hw1, hw2⟩, rfl | hi_sub⟩ := hi
    · have hsub : w - K < cs.length := by omega
      refine ⟨hsub, ?_⟩
      intro a ha
      rw [getD_append_left cs _ (w - K) [] hsub] at ha
      exact ⟨w, ⟨hw_in, hw1, hw2⟩, Or.inr ha⟩
    · have hsub : w - K < cs.length := by omega
      obtain ⟨hi_lt, htrans⟩ := h (w - K) hsub i hi_sub
      refine ⟨by omega, ?_⟩
      intro a ha
      rw [getD_append_left cs _ i [] (by omega)] at ha
      exact ⟨w, ⟨hw_in, hw1, hw2⟩, Or.inr (htrans a ha)⟩

lemma foldl_coneStep_trans (K : ℕ) (gs : List Gate) (cs : List (List ℕ)) (h : TransCone cs) :
    TransCone (gs.foldl (coneStep K) cs) := by
  induction gs generalizing cs with
  | nil => exact h
  | cons g gs ih =>
    rw [List.foldl_cons]
    exact ih (coneStep K cs g) (coneStep_trans K cs g h)

lemma cones_trans (K : ℕ) (C : Circuit) : TransCone (cones K C) := by
  unfold cones
  apply foldl_coneStep_trans
  intro j hj
  simp at hj

lemma inCone_of_input (K : ℕ) (C : Circuit) (g : ℕ) (hg : g < C.gates.length)
    (w : ℕ) (hw_in : w ∈ (C.gates.getD g ⟨GateOp.and, []⟩).inputs)
    (hw1 : K ≤ w) (hw2 : w < K + g) :
    InCone K C (w - K) g := by
  unfold InCone cones
  have h := foldl_coneStep_getD_add K C.gates [] g hg
  simp only [List.length_nil, Nat.zero_add] at h
  rw [h]
  simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq, List.mem_cons]
  exact ⟨w, ⟨hw_in, hw1, hw2⟩, Or.inl rfl⟩

lemma inCone_trans (K : ℕ) (C : Circuit) (a b c : ℕ)
    (hab : InCone K C a b) (hbc : InCone K C b c) :
    InCone K C a c := by
  unfold InCone at hab hbc ⊢
  by_cases hc : c < (cones K C).length
  · exact (cones_trans K C c hc b hbc).2 a hab
  · rw [getD_eq_default (cones K C) c [] (by omega)] at hbc
    simp at hbc

lemma twin_eq {n m : ℕ} (A : Fin n → Fin m → Bool)
    (U : Finset (Fin n)) (W : Finset (Fin m)) (u0 : Fin n) (v0 : Fin m)
    (hA_U : ∀ u ∈ U, ∀ v : Fin m, A u v = A u0 v)
    (hA_W : ∀ v ∈ W, ∀ u : Fin n, A u v = A u v0)
    (u : Fin n) (v : Fin m) :
    A (if u ∈ U then u0 else u) (if v ∈ W then v0 else v) = A u v := by
  by_cases hu : u ∈ U <;> by_cases hv : v ∈ W
  · simp only [hu, hv, ↓reduceIte]
    rw [← hA_U u hu v0, ← hA_W v hv u]
  · simp only [hu, hv, ↓reduceIte]
    rw [← hA_U u hu v]
  · simp only [hu, hv, ↓reduceIte]
    rw [← hA_W v hv u]
  · simp [hu, hv]

lemma part_a (n m : ℕ) (A : Fin n → Fin m → Bool) (U : Finset (Fin n)) (W : Finset (Fin m))
    (u0 : Fin n) (v0 : Fin m) (C : Circuit)
    (hu0 : u0 ∈ U) (hv0 : v0 ∈ W)
    (hA_U : ∀ u ∈ U, ∀ v : Fin m, A u v = A u0 v)
    (hA_W : ∀ v ∈ W, ∀ u : Fin n, A u v = A u v0)
    (hFan : FanInTwo C)
    (hAgree : ∀ (u : Fin n) (v : Fin m), (u ∉ U ∨ u = u0) → (v ∉ W ∨ v = v0) →
      C.eval (oneEach u v) = A u v) :
    ∃ C2 : Circuit, FanInTwo C2 ∧ C2.size ≤ C.size + (U.card - 1) + (W.card - 1) ∧
      Represents A C2 := by
  let us : List ℕ := ((U.erase u0).toList).map Fin.val
  let ws : List ℕ := ((W.erase v0).toList).map (fun v => n + v.val)
  have hus_len : us.length = U.card - 1 := by
    simp [us, Finset.card_erase_of_mem hu0]
  have hws_len : ws.length = W.card - 1 := by
    simp [ws, Finset.card_erase_of_mem hv0]
  let chainU := orChain (n + m) u0.val us
  let chainW := orChain (n + m + us.length) (n + v0.val) ws
  let prefixGates : List Gate := chainU.1 ++ chainW.1
  let shift : ℕ := prefixGates.length
  have hshift : shift = us.length + ws.length := by
    simp [shift, prefixGates, chainU, chainW, orChain_len]
  let wU : ℕ := chainU.2
  let wW : ℕ := chainW.2
  have hwU_lt : wU < n + m + us.length := by
    apply orChain_out_lt
    omega
  have hwW_lt : wW < n + m + shift := by
    have h : wW < n + m + us.length + ws.length :=
      orChain_out_lt ws (n + m + us.length) (n + v0.val) (by omega)
    omega
  let dead : ℕ := n + m + shift + C.gates.length
  let remap : ℕ → ℕ := remapWire n m shift dead wU wW U W u0 v0
  let C2 : Circuit := ⟨prefixGates ++ C.gates.map (remapGate remap), remap C.output⟩
  refine ⟨C2, ?_, ?_, ?_⟩
  · intro g hg
    simp only [C2, prefixGates, List.mem_append, List.mem_map] at hg
    rcases hg with (hg | hg) | ⟨g0, hg0, rfl⟩
    · exact orChain_fanInTwo us (n + m) u0.val g hg
    · exact orChain_fanInTwo ws (n + m + us.length) (n + v0.val) g hg
    · obtain ⟨hop, hlen⟩ := hFan g0 hg0
      exact ⟨hop, by simp [remapGate, hlen]⟩
  · simp only [Circuit.size, C2, List.length_append, List.length_map]
    omega
  · intro u v
    let u' : Fin n := if u ∈ U then u0 else u
    let v' : Fin m := if v ∈ W then v0 else v
    let x : List Bool := oneEach u v
    let x' : List Bool := oneEach u' v'
    let xU : List Bool := chainU.1.foldl gateStep x
    let xPre : List Bool := prefixGates.foldl gateStep x
    have hx_len : x.length = n + m := oneEach_length u v
    have hx'_len : x'.length = n + m := oneEach_length u' v'
    have hxU_len : xU.length = n + m + us.length := by
      simp [xU, foldl_gateStep_length, hx_len, chainU, orChain_len]
    have hxPre_eq : xPre = chainW.1.foldl gateStep xU := by
      simp [xPre, prefixGates, xU, List.foldl_append]
    have hxPre_len : xPre.length = n + m + shift := by
      simp [xPre, foldl_gateStep_length, hx_len, shift]
    have hus_lt : ∀ b ∈ us, b < x.length := by
      intro b hb
      simp only [us, List.mem_map] at hb
      obtain ⟨a, _, rfl⟩ := hb
      omega
    have hws_lt : ∀ b ∈ ws, b < xU.length := by
      intro b hb
      simp only [ws, List.mem_map] at hb
      obtain ⟨a, _, rfl⟩ := hb
      omega
    have hxU_wU : xU.getD wU false = decide (u ∈ U) := by
      have h1 : xU.getD wU false = (x.getD u0.val false || us.any (fun b => x.getD b false)) := by
        have h := orChain_eval us x u0.val hus_lt
        rw [hx_len] at h
        exact h
      rw [h1]
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.or_eq_true, List.any_eq_true, decide_eq_true_eq]
      constructor
      · rintro (h0 | ⟨b, hb, hxb⟩)
        · rw [oneEach_getD_left u v u0.val u0.isLt, decide_eq_true_eq] at h0
          have : u0 = u := Fin.ext (by simpa using congrArg Fin.val h0)
          subst this
          exact hu0
        · simp only [us, List.mem_map, Finset.mem_toList, Finset.mem_erase] at hb
          obtain ⟨a, ⟨_, haU⟩, rfl⟩ := hb
          rw [oneEach_getD_left u v a.val a.isLt, decide_eq_true_eq] at hxb
          have : a = u := Fin.ext (by simpa using congrArg Fin.val hxb)
          subst this
          exact haU
      · intro huU
        by_cases heq : u = u0
        · left
          rw [oneEach_getD_left u v u0.val u0.isLt, decide_eq_true_eq]
          exact Fin.ext (by simp [heq])
        · right
          refine ⟨u.val, ?_, ?_⟩
          · simp only [us, List.mem_map, Finset.mem_toList, Finset.mem_erase]
            exact ⟨u, ⟨heq, huU⟩, rfl⟩
          · rw [oneEach_getD_left u v u.val u.isLt, decide_eq_true_eq]
    have hxPre_wU : xPre.getD wU false = decide (u ∈ U) := by
      rw [hxPre_eq, foldl_gateStep_getD_lt chainW.1 xU wU (by omega), hxU_wU]
    have hxPre_wW : xPre.getD wW false = decide (v ∈ W) := by
      have h1 : xPre.getD wW false =
          (xU.getD (n + v0.val) false || ws.any (fun b => xU.getD b false)) := by
        rw [hxPre_eq]
        have h := orChain_eval ws xU (n + v0.val) hws_lt
        rw [hxU_len] at h
        exact h
      rw [h1]
      have hv0_eq : xU.getD (n + v0.val) false = x.getD (n + v0.val) false :=
        foldl_gateStep_getD_lt chainU.1 x (n + v0.val) (by omega)
      have hws_any : ws.any (fun b => xU.getD b false) = ws.any (fun b => x.getD b false) := by
        apply list_any_congr
        intro b hb
        simp only [ws, List.mem_map] at hb
        obtain ⟨a, _, rfl⟩ := hb
        exact foldl_gateStep_getD_lt chainU.1 x (n + a.val) (by omega)
      rw [hv0_eq, hws_any]
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.or_eq_true, List.any_eq_true, decide_eq_true_eq]
      constructor
      · rintro (h0 | ⟨b, hb, hxb⟩)
        · rw [oneEach_getD_right u v (n + v0.val) (by omega) (by omega), decide_eq_true_eq] at h0
          have : v0 = v := Fin.ext (by simpa using congrArg Fin.val h0)
          subst this
          exact hv0
        · simp only [ws, List.mem_map, Finset.mem_toList, Finset.mem_erase] at hb
          obtain ⟨a, ⟨_, haW⟩, rfl⟩ := hb
          rw [oneEach_getD_right u v (n + a.val) (by omega) (by omega), decide_eq_true_eq] at hxb
          have : a = v := Fin.ext (by simpa using congrArg Fin.val hxb)
          subst this
          exact haW
      · intro hvW
        by_cases heq : v = v0
        · left
          rw [oneEach_getD_right u v (n + v0.val) (by omega) (by omega), decide_eq_true_eq]
          exact Fin.ext (by simp [heq])
        · right
          refine ⟨n + v.val, ?_, ?_⟩
          · simp only [ws, List.mem_map, Finset.mem_toList, Finset.mem_erase]
            exact ⟨v, ⟨heq, hvW⟩, rfl⟩
          · rw [oneEach_getD_right u v (n + v.val) (by omega) (by omega), decide_eq_true_eq]
            exact Fin.ext (by simp)
    have hbase : ∀ i : ℕ, xPre.getD (remap i) false = x'.getD i false := by
      intro i
      simp only [remap, remapWire]
      split_ifs with h1 h2 h3 h4 h5 h6
      · rw [hxPre_wU, oneEach_getD_left u' v' i h1]
        apply Bool.eq_iff_iff.mpr
        simp only [decide_eq_true_eq]
        constructor
        · intro huU
          simp only [u', huU, ↓reduceIte]
          exact h2
        · intro hEq
          by_cases huU : u ∈ U
          · exact huU
          · simp only [u', huU, ↓reduceIte] at hEq
            have : u = u0 := hEq.symm.trans h2
            subst this
            exact absurd hu0 huU
      · rw [getD_eq_default xPre dead false (by omega), oneEach_getD_left u' v' i h1]
        symm
        rw [decide_eq_false_iff_not]
        intro hEq
        by_cases huU : u ∈ U
        · simp only [u', huU, ↓reduceIte] at hEq
          exact h2 hEq
        · simp only [u', huU, ↓reduceIte] at hEq
          rw [hEq] at h3
          exact huU h3
      · rw [foldl_gateStep_getD_lt prefixGates x i (by omega),
          oneEach_getD_left u v i h1, oneEach_getD_left u' v' i h1]
        apply Bool.eq_iff_iff.mpr
        simp only [decide_eq_true_eq]
        by_cases huU : u ∈ U
        · simp only [u', huU, ↓reduceIte]
          constructor
          · intro hEq
            rw [← hEq] at huU
            exact absurd huU h3
          · intro hEq
            exact absurd hEq h2
        · simp only [u', huU, ↓reduceIte]
      · rw [hxPre_wW, oneEach_getD_right u' v' i (by omega) h4]
        apply Bool.eq_iff_iff.mpr
        simp only [decide_eq_true_eq]
        constructor
        · intro hvW
          simp only [v', hvW, ↓reduceIte]
          exact h5
        · intro hEq
          by_cases hvW : v ∈ W
          · exact hvW
          · simp only [v', hvW, ↓reduceIte] at hEq
            have : v = v0 := hEq.symm.trans h5
            subst this
            exact absurd hv0 hvW
      · rw [getD_eq_default xPre dead false (by omega), oneEach_getD_right u' v' i (by omega) h4]
        symm
        rw [decide_eq_false_iff_not]
        intro hEq
        by_cases hvW : v ∈ W
        · simp only [v', hvW, ↓reduceIte] at hEq
          exact h5 hEq
        · simp only [v', hvW, ↓reduceIte] at hEq
          rw [hEq] at h6
          exact hvW h6
      · rw [foldl_gateStep_getD_lt prefixGates x i (by omega),
          oneEach_getD_right u v i (by omega) h4, oneEach_getD_right u' v' i (by omega) h4]
        apply Bool.eq_iff_iff.mpr
        simp only [decide_eq_true_eq]
        by_cases hvW : v ∈ W
        · simp only [v', hvW, ↓reduceIte]
          constructor
          · intro hEq
            rw [← hEq] at hvW
            exact absurd hvW h6
          · intro hEq
            exact absurd hEq h5
        · simp only [v', hvW, ↓reduceIte]
      · rw [getD_eq_default xPre (i + shift) false (by omega),
          getD_eq_default x' i false (by omega)]
    have hsim : ∀ gs : List Gate, gs.length ≤ C.gates.length →
        ∀ i : ℕ,
          ((gs.map (remapGate remap)).foldl gateStep xPre).getD (remap i) false =
            (gs.foldl gateStep x').getD i false := by
      intro gs
      induction gs using List.reverseRecOn with
      | nil =>
        intro _ i
        exact hbase i
      | append_singleton gs g ih =>
        intro hlen i
        have hlen_gs : gs.length ≤ C.gates.length := by
          simp only [List.length_append, List.length_singleton] at hlen
          omega
        have hih := ih hlen_gs
        let w1 := (gs.map (remapGate remap)).foldl gateStep xPre
        let w2 := gs.foldl gateStep x'
        have hw1_len : w1.length = n + m + shift + gs.length := by
          simp [w1, foldl_gateStep_length, hxPre_len]
        have hw2_len : w2.length = n + m + gs.length := by
          simp [w2, foldl_gateStep_length, hx'_len]
        simp only [List.map_append, List.map_singleton, List.foldl_append, List.foldl_cons,
          List.foldl_nil]
        change (gateStep w1 (remapGate remap g)).getD (remap i) false =
          (gateStep w2 g).getD i false
        have hval : (remapGate remap g).op.eval
            ((remapGate remap g).inputs.map fun j => w1.getD j false) =
            g.op.eval (g.inputs.map fun j => w2.getD j false) := by
          simp only [remapGate, List.map_map]
          congr 1
          apply list_map_congr
          intro j _
          exact hih j
        by_cases hilt : i < n + m
        · have hri : remap i < w1.length ∨ remap i = dead := by
            simp only [remap, remapWire]
            split_ifs
            · left; omega
            · right; rfl
            · left; omega
            · left; omega
            · right; rfl
            · left; omega
          rcases hri with hlt1 | hdead
          · rw [gateStep, getD_append_left w1 _ (remap i) false hlt1,
              gateStep, getD_append_left w2 _ i false (by omega)]
            exact hih i
          · rw [hdead]
            have hge1 : (gateStep w1 (remapGate remap g)).length ≤ dead := by
              simp only [gateStep, List.length_append, List.length_singleton]
              simp only [List.length_append, List.length_singleton] at hlen
              omega
            rw [getD_eq_default _ dead false hge1,
              gateStep, getD_append_left w2 _ i false (by omega), ← hih i, hdead,
              getD_eq_default w1 dead false (by omega)]
        · have hri : remap i = i + shift := by
            simp only [remap, remapWire]
            split_ifs <;> omega
          rw [hri]
          by_cases hi2 : i < w2.length
          · rw [gateStep, getD_append_left w1 _ (i + shift) false (by omega),
              gateStep, getD_append_left w2 _ i false hi2, ← hri]
            exact hih i
          · by_cases hiEq : i = w2.length
            · have hi1 : i + shift = w1.length := by omega
              rw [hi1, hiEq, gateStep, gateStep,
                getD_append_right w1 _ w1.length false (Nat.le_refl _),
                getD_append_right w2 _ w2.length false (Nat.le_refl _)]
              simp only [Nat.sub_self, List.getD_cons_zero]
              exact hval
            · have hge1 : (gateStep w1 (remapGate remap g)).length ≤ i + shift := by
                simp only [gateStep, List.length_append, List.length_singleton]
                omega
              have hge2 : (gateStep w2 g).length ≤ i := by
                simp only [gateStep, List.length_append, List.length_singleton]
                omega
              rw [getD_eq_default _ (i + shift) false hge1, getD_eq_default _ i false hge2]
    have heval : C2.eval x = C.eval x' := by
      simp only [Circuit.eval, wires_eq_foldl, C2, List.foldl_append]
      exact hsim C.gates (Nat.le_refl _) C.output
    rw [heval]
    have hu'_ok : u' ∉ U ∨ u' = u0 := by
      by_cases huU : u ∈ U
      · right; simp [u', huU]
      · left; simp [u', huU]
    have hv'_ok : v' ∉ W ∨ v' = v0 := by
      by_cases hvW : v ∈ W
      · right; simp [v', hvW]
      · left; simp [v', hvW]
    rw [hAgree u' v' hu'_ok hv'_ok]
    exact twin_eq A U W u0 v0 hA_U hA_W u v

lemma part_b (n m : ℕ) (A : Fin n → Fin m → Bool) (U : Finset (Fin n)) (W : Finset (Fin m))
    (u0 : Fin n) (v0 : Fin m) (C : Circuit)
    (hu0 : u0 ∈ U) (hv0 : v0 ∈ W)
    (hA_U : ∀ u ∈ U, ∀ v : Fin m, A u v = A u0 v)
    (hA_W : ∀ v ∈ W, ∀ u : Fin n, A u v = A u v0)
    (hAgree : ∀ (u : Fin n) (v : Fin m), (u ∉ U ∨ u = u0) → (v ∉ W ∨ v = v0) →
      C.eval (oneEach u v) = A u v)
    (hUnread : ∀ w : ℕ, ((∃ u ∈ U, w = u.val) ∨ (∃ v ∈ W, w = n + v.val)) →
      C.output ≠ w ∧ ∀ g < C.gates.length,
        (C.output = n + m + g ∨ (n + m ≤ C.output ∧ InCone (n + m) C g (C.output - (n + m)))) →
        w ∉ (C.gates.getD g ⟨GateOp.and, []⟩).inputs) :
    Represents A C := by
  intro u v
  let u' : Fin n := if u ∈ U then u0 else u
  let v' : Fin m := if v ∈ W then v0 else v
  let x : List Bool := oneEach u v
  let x' : List Bool := oneEach u' v'
  have hx_len : x.length = n + m := oneEach_length u v
  have hx'_len : x'.length = n + m := oneEach_length u' v'
  have hinput_eq : ∀ w < n + m,
      ¬ ((∃ a ∈ U, w = a.val) ∨ (∃ b ∈ W, w = n + b.val)) →
      x.getD w false = x'.getD w false := by
    intro w hw hnot
    by_cases h1 : w < n
    · have haU : (⟨w, h1⟩ : Fin n) ∉ U := fun hmem => hnot (Or.inl ⟨⟨w, h1⟩, hmem, rfl⟩)
      rw [oneEach_getD_left u v w h1, oneEach_getD_left u' v' w h1]
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      by_cases huU : u ∈ U
      · simp only [u', huU, ↓reduceIte]
        constructor
        · intro hEq; rw [← hEq] at huU; exact absurd huU haU
        · intro hEq; rw [← hEq] at hu0; exact absurd hu0 haU
      · simp only [u', huU, ↓reduceIte]
    · have hbW : (⟨w - n, by omega⟩ : Fin m) ∉ W :=
        fun hmem => hnot (Or.inr ⟨⟨w - n, by omega⟩, hmem, by simp; omega⟩)
      rw [oneEach_getD_right u v w (by omega) hw, oneEach_getD_right u' v' w (by omega) hw]
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      by_cases hvW : v ∈ W
      · simp only [v', hvW, ↓reduceIte]
        constructor
        · intro hEq; rw [← hEq] at hvW; exact absurd hvW hbW
        · intro hEq; rw [← hEq] at hv0; exact absurd hv0 hbW
      · simp only [v', hvW, ↓reduceIte]
  have heval : C.eval x = C.eval x' := by
    simp only [Circuit.eval, wires_eq_foldl]
    by_cases hout1 : C.output < n + m
    · rw [foldl_gateStep_getD_lt C.gates x C.output (by omega),
        foldl_gateStep_getD_lt C.gates x' C.output (by omega)]
      exact hinput_eq C.output hout1 (fun hmem => (hUnread C.output hmem).1 rfl)
    · by_cases hout2 : C.output < n + m + C.gates.length
      · let g0 : ℕ := C.output - (n + m)
        have hg0_lt : g0 < C.gates.length := by omega
        have hout_eq : C.output = n + m + g0 := by omega
        have hcone_eq : ∀ g : ℕ, g < C.gates.length → (g = g0 ∨ InCone (n + m) C g g0) →
            (C.gates.foldl gateStep x).getD (n + m + g) false =
              (C.gates.foldl gateStep x').getD (n + m + g) false := by
          intro g
          induction g using Nat.strong_induction_on with
          | ind g ih =>
            intro hg_lt hg_cone
            have hx_g := foldl_gateStep_getD_add C.gates x g hg_lt
            have hx'_g := foldl_gateStep_getD_add C.gates x' g hg_lt
            rw [hx_len] at hx_g
            rw [hx'_len] at hx'_g
            rw [hx_g, hx'_g]
            congr 1
            apply list_map_congr
            intro w hw_in
            by_cases hw1 : w < n + m
            · rw [foldl_gateStep_getD_lt (C.gates.take g) x w (by omega),
                foldl_gateStep_getD_lt (C.gates.take g) x' w (by omega)]
              apply hinput_eq w hw1
              intro hmem
              have hnot := (hUnread w hmem).2 g hg_lt
              apply hnot _ hw_in
              rcases hg_cone with rfl | hinc
              · exact Or.inl hout_eq
              · exact Or.inr ⟨by omega, hinc⟩
            · by_cases hw2 : w < n + m + g
              · let i : ℕ := w - (n + m)
                have hi_lt : i < g := by omega
                have hw_eq : w = n + m + i := by omega
                have htake_x : ((C.gates.take g).foldl gateStep x).getD w false =
                    (C.gates.foldl gateStep x).getD (n + m + i) false := by
                  have hsplit : C.gates = C.gates.take g ++ C.gates.drop g :=
                    (List.take_append_drop g C.gates).symm
                  conv_rhs => rw [hsplit, List.foldl_append]
                  have hlen_t : ((C.gates.take g).foldl gateStep x).length = n + m + g := by
                    rw [foldl_gateStep_length, hx_len, List.length_take]
                    omega
                  rw [← hw_eq, foldl_gateStep_getD_lt (C.gates.drop g) _ w (by omega)]
                have htake_x' : ((C.gates.take g).foldl gateStep x').getD w false =
                    (C.gates.foldl gateStep x').getD (n + m + i) false := by
                  have hsplit : C.gates = C.gates.take g ++ C.gates.drop g :=
                    (List.take_append_drop g C.gates).symm
                  conv_rhs => rw [hsplit, List.foldl_append]
                  have hlen_t : ((C.gates.take g).foldl gateStep x').length = n + m + g := by
                    rw [foldl_gateStep_length, hx'_len, List.length_take]
                    omega
                  rw [← hw_eq, foldl_gateStep_getD_lt (C.gates.drop g) _ w (by omega)]
                rw [htake_x, htake_x']
                have hi_in_g : InCone (n + m) C i g :=
                  inCone_of_input (n + m) C g hg_lt w hw_in (by omega) hw2
                have hi_cone : i = g0 ∨ InCone (n + m) C i g0 := by
                  rcases hg_cone with rfl | hinc
                  · exact Or.inr hi_in_g
                  · exact Or.inr (inCone_trans (n + m) C i g g0 hi_in_g hinc)
                exact ih i hi_lt (by omega) hi_cone
              · have hlen_t1 : ((C.gates.take g).foldl gateStep x).length ≤ w := by
                  rw [foldl_gateStep_length, hx_len, List.length_take]
                  omega
                have hlen_t2 : ((C.gates.take g).foldl gateStep x').length ≤ w := by
                  rw [foldl_gateStep_length, hx'_len, List.length_take]
                  omega
                rw [getD_eq_default _ w false hlen_t1, getD_eq_default _ w false hlen_t2]
        rw [hout_eq]
        exact hcone_eq g0 hg0_lt (Or.inl rfl)
      · have hlen1 : (C.gates.foldl gateStep x).length ≤ C.output := by
          rw [foldl_gateStep_length, hx_len]
          omega
        have hlen2 : (C.gates.foldl gateStep x').length ≤ C.output := by
          rw [foldl_gateStep_length, hx'_len]
          omega
        rw [getD_eq_default _ C.output false hlen1, getD_eq_default _ C.output false hlen2]
  rw [heval]
  have hu'_ok : u' ∉ U ∨ u' = u0 := by
    by_cases huU : u ∈ U
    · right; simp [u', huU]
    · left; simp [u', huU]
  have hv'_ok : v' ∉ W ∨ v' = v0 := by
    by_cases hvW : v ∈ W
    · right; simp [v', hvW]
    · left; simp [v', hvW]
  rw [hAgree u' v' hu'_ok hv'_ok]
  exact twin_eq A U W u0 v0 hA_U hA_W u v

end PEqualNP.Outside.L_meta_25444

theorem PEqualNP.Outside.L_meta_25444 : (∀ (n m : ℕ) (A : Fin n → Fin m → Bool) (U : Finset (Fin n)) (W : Finset (Fin m)) (u0 : Fin n) (v0 : Fin m) (C : PEqualNP.CircuitLowerBounds.Circuit), u0 ∈ U → v0 ∈ W → (∀ u ∈ U, ∀ v : Fin m, A u v = A u0 v) → (∀ v ∈ W, ∀ u : Fin n, A u v = A u v0) → PEqualNP.MetaComplexity.FanInTwo C → (∀ (u : Fin n) (v : Fin m), (u ∉ U ∨ u = u0) → (v ∉ W ∨ v = v0) → C.eval (PEqualNP.Represents.oneEach u v) = A u v) → (∃ C2 : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C2 ∧ C2.size ≤ C.size + (U.card - 1) + (W.card - 1) ∧ PEqualNP.Represents.Represents A C2) ∧ ((∀ w : ℕ, ((∃ u ∈ U, w = u.val) ∨ (∃ v ∈ W, w = n + v.val)) → C.output ≠ w ∧ ∀ g < C.gates.length, (C.output = n + m + g ∨ (n + m ≤ C.output ∧ PEqualNP.EdgeOwnership.InCone (n + m) C g (C.output - (n + m)))) → w ∉ (C.gates.getD g ⟨PEqualNP.CircuitLowerBounds.GateOp.and, []⟩).inputs) → PEqualNP.Represents.Represents A C)) := by
  intro n m A U W u0 v0 C hu0 hv0 hA_U hA_W hFan hAgree
  exact ⟨PEqualNP.Outside.L_meta_25444.part_a n m A U W u0 v0 C hu0 hv0 hA_U hA_W hFan hAgree,
    PEqualNP.Outside.L_meta_25444.part_b n m A U W u0 v0 C hu0 hv0 hA_U hA_W hAgree⟩
