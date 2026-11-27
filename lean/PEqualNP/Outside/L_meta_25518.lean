import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25518_aux

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (FanInTwo Monotone2)
open PEqualNP.MetaComplexity.NestedCover (ReadsBack gateAt)
open PEqualNP.NotBracket (notCount)

private theorem list_any_congr {α : Type _} {xs : List α} {f g : α → Bool}
    (h : ∀ a ∈ xs, f a = g a) : xs.any f = xs.any g := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
    simp only [List.any_cons, h a List.mem_cons_self, ih (fun b hb => h b (List.mem_cons_of_mem a hb))]

private theorem filter_nonempty_sum {α β : Type _} (f : α → List β) (xs : List α) :
    ((xs.filter fun a => decide (f a ≠ [])).map fun a => (f a).length).sum =
      (xs.map fun a => (f a).length).sum := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
    by_cases h : f a = []
    · simp only [List.filter_cons, h, ne_eq, not_true_eq_false, decide_false, List.map_cons, List.sum_cons, List.length_nil, Nat.zero_add]; exact ih
    · simp only [List.filter_cons, h, ne_eq, not_false_eq_true, decide_true, ↓reduceIte, List.map_cons, List.sum_cons]; rw [ih]

private theorem length_le_sum_length {α β : Type _} (xs : List (α × List β))
    (h : ∀ p ∈ xs, p.2 ≠ []) : xs.length ≤ (xs.map fun p => p.2.length).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    have h1 : 1 ≤ x.2.length := List.length_pos_of_ne_nil (h x List.mem_cons_self)
    have h2 := ih (fun p hp => h p (List.mem_cons_of_mem x hp))
    omega

private theorem map_toList_sum {α : Type _} [DecidableEq α] (s : Finset α) (f : α → ℕ) :
    (s.toList.map f).sum = ∑ x ∈ s, f x := by
  change ((s.toList : Multiset α).map f).sum = (s.val.map f).sum
  rw [Finset.coe_toList]

private theorem card_filter_add_not {α : Type _} [DecidableEq α] (s : Finset α) (p : α → Prop) [DecidablePred p] :
    (s.filter p).card + (s.filter fun x => ¬ p x).card = s.card := by
  rw [← Finset.card_union_of_disjoint]
  · congr 1; ext x; simp; tauto
  · rw [Finset.disjoint_left]; intro x h1 h2; simp at h1 h2; exact h2.2 h1.2

private def readGate (w : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

private theorem foldl_snoc_keeps {α β : Type _} (F : List α → β → α) (gs : List β) (init : List α) :
    init <+: gs.foldl (fun R g => R ++ [F R g]) init := by
  induction gs generalizing init with
  | nil => exact List.prefix_refl _
  | cons g gs ih => exact (List.prefix_append init [F init g]).trans (ih _)

private theorem foldl_snoc_length {α β : Type _} (F : List α → β → α) (gs : List β) (init : List α) :
    (gs.foldl (fun R g => R ++ [F R g]) init).length = init.length + gs.length := by
  induction gs generalizing init with
  | nil => simp
  | cons g gs ih => simp [ih]; omega

private theorem getD_of_prefix {α : Type _} {P L : List α} (h : P <+: L) {i : ℕ} (hi : i < P.length)
    (d : α) : L.getD i d = P.getD i d := by
  obtain ⟨t, rfl⟩ := h
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private theorem wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length :=
  foldl_snoc_length readGate C.gates x

private theorem wires_low (C : Circuit) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (C.wires x).getD i false = x.getD i false :=
  getD_of_prefix (foldl_snoc_keeps readGate C.gates x) hi false

private theorem wires_past (C : Circuit) (x : List Bool) (i : ℕ) (hi : x.length + C.gates.length ≤ i) :
    (C.wires x).getD i false = false := by
  apply List.getD_eq_default
  rw [wires_length]; exact hi

private theorem wires_append_prefix (gs1 gs2 : List Gate) (x : List Bool) :
    (Circuit.mk gs1 0).wires x <+: (Circuit.mk (gs1 ++ gs2) 0).wires x := by
  simp only [Circuit.wires, List.foldl_append]
  exact foldl_snoc_keeps readGate gs2 _

private theorem wires_append_getD (gs1 gs2 : List Gate) (x : List Bool) (i : ℕ)
    (hi : i < x.length + gs1.length) :
    ((Circuit.mk (gs1 ++ gs2) 0).wires x).getD i false =
      ((Circuit.mk gs1 0).wires x).getD i false := by
  apply getD_of_prefix (wires_append_prefix gs1 gs2 x)
  rw [wires_length]; exact hi

private theorem wires_snoc_eq (gs : List Gate) (g : Gate) (x : List Bool) :
    ((Circuit.mk (gs ++ [g]) 0).wires x).getD (x.length + gs.length) false =
      readGate ((Circuit.mk gs 0).wires x) g := by
  have h1 : (Circuit.mk (gs ++ [g]) 0).wires x =
      (Circuit.mk gs 0).wires x ++ [readGate ((Circuit.mk gs 0).wires x) g] := by
    simp only [Circuit.wires, List.foldl_append, List.foldl_cons, List.foldl_nil, readGate]
  rw [h1]
  have hlen : ((Circuit.mk gs 0).wires x).length = x.length + gs.length := wires_length _ _
  rw [← hlen]
  simp [List.getD_eq_getElem?_getD]

private theorem foldl_snoc_split {α β : Type _} (F : List α → β → α) (gs : List β) (init : List α)
    (j : ℕ) (hj : j < gs.length) (d : α) :
    (gs.foldl (fun R g => R ++ [F R g]) init).getD (init.length + j) d
      = F ((gs.take j).foldl (fun R g => R ++ [F R g]) init) gs[j] ∧
    ((gs.take j).foldl (fun R g => R ++ [F R g]) init) <+:
      gs.foldl (fun R g => R ++ [F R g]) init ∧
    ((gs.take j).foldl (fun R g => R ++ [F R g]) init).length = init.length + j := by
  have hsplit : gs = gs.take j ++ gs[j] :: gs.drop (j + 1) := by simp
  set P := (gs.take j).foldl (fun R g => R ++ [F R g]) init with hP
  have hPl : P.length = init.length + j := by
    rw [hP, foldl_snoc_length F]; simp; omega
  have hpre : (P ++ [F P gs[j]]) <+: gs.foldl (fun R g => R ++ [F R g]) init := by
    conv_rhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
    exact foldl_snoc_keeps F _ _
  refine ⟨?_, (List.prefix_append P _).trans hpre, hPl⟩
  rw [getD_of_prefix hpre (by simp; omega), ← hPl]
  simp

private theorem wires_gate (N : ℕ) (C : Circuit) (x : List Bool) (hx : x.length = N)
    (hback : ReadsBack N C) (j : ℕ) (hj : j < C.gates.length) :
    (C.wires x).getD (N + j) false =
      (C.gates[j]).op.eval ((C.gates[j]).inputs.map fun i => (C.wires x).getD i false) := by
  obtain ⟨value, pre, len⟩ := foldl_snoc_split readGate C.gates x j hj false
  have hval : (C.wires x).getD (N + j) false =
      readGate ((C.gates.take j).foldl (fun R g => R ++ [readGate R g]) x) C.gates[j] := by
    rw [← hx]; exact value
  rw [hval]
  unfold readGate
  congr 1
  apply List.map_congr_left
  intro i hi
  have hlt : i < N + j := by
    have hb := hback j hj i
    rw [gateAt, List.getD_eq_getElem _ _ hj] at hb
    exact hb hi
  have hpl : ((C.gates.take j).foldl (fun R g => R ++ [readGate R g]) x).length = N + j := by
    rw [len, hx]
  exact (getD_of_prefix pre (by omega) false).symm

private def relocW (n w : ℕ) : ℕ := if w < n then w else w + n
private def relocG (n : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (relocW n)⟩

private theorem relocW_ne_raw (n w : ℕ) (i : Fin n) : relocW n w ≠ n + i.val := by
  unfold relocW; split_ifs <;> omega

private def rawCount (r : ℕ) (gs : List Gate) : ℕ := (gs.map fun g => g.inputs.count r).sum

private theorem rawCount_append (r : ℕ) (gs1 gs2 : List Gate) :
    rawCount r (gs1 ++ gs2) = rawCount r gs1 + rawCount r gs2 := by
  simp [rawCount, List.map_append, List.sum_append]

private theorem rawCount_zero_iff (r : ℕ) (gs : List Gate) :
    rawCount r gs = 0 ↔ ∀ g ∈ gs, r ∉ g.inputs := by
  unfold rawCount
  rw [List.sum_eq_zero_iff]
  simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, List.count_eq_zero]

private theorem notCount_append (gs1 gs2 : List Gate) :
    notCount ⟨gs1 ++ gs2, 0⟩ = notCount ⟨gs1, 0⟩ + notCount ⟨gs2, 0⟩ := by
  simp [notCount, List.filter_append]

private theorem readsBack_snoc (N : ℕ) (gs : List Gate) (g : Gate)
    (hrb : ReadsBack N ⟨gs, 0⟩) (hg : ∀ a ∈ g.inputs, a < N + gs.length) :
    ReadsBack N ⟨gs ++ [g], 0⟩ := by
  intro j hj a ha
  change j < (gs ++ [g]).length at hj
  change a ∈ ((gs ++ [g]).getD j ⟨.or, []⟩).inputs at ha
  by_cases hlt : j < gs.length
  · rw [List.getD_append _ _ _ _ hlt] at ha
    exact hrb j hlt a ha
  · have hjeq : j = gs.length := by simp at hj; omega
    subst hjeq
    rw [List.getD_append_right _ _ _ _ le_rfl] at ha
    simp only [Nat.sub_self, List.getD_cons_zero] at ha
    exact hg a ha

private theorem fanInTwo_snoc (gs : List Gate) (g : Gate)
    (hfan : FanInTwo ⟨gs, 0⟩)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hlen : g.inputs.length ≤ 2) :
    FanInTwo ⟨gs ++ [g], 0⟩ := by
  intro g' hg'
  rcases List.mem_append.mp hg' with h1 | h2
  · exact hfan g' h1
  · rw [List.mem_singleton.mp h2]; exact ⟨hop, hlen⟩

private theorem relocD_props (n : ℕ) (D : Circuit) (hmono : Monotone2 D) (hrb : ReadsBack n D) :
    let gs := D.gates.map (relocG n)
    gs.length = D.gates.length ∧
    FanInTwo ⟨gs, 0⟩ ∧
    ReadsBack (n + n) ⟨gs, 0⟩ ∧
    notCount ⟨gs, 0⟩ = 0 ∧
    (∀ g ∈ gs, g.op ≠ .not) ∧
    (∀ i : Fin n, rawCount (n + i.val) gs = 0) ∧
    (∀ (x y : List Bool), x.length = n → y.length = n →
      ∀ w < n + D.gates.length,
        ((Circuit.mk gs 0).wires (x ++ y)).getD (relocW n w) false = (D.wires x).getD w false) := by
  let gs := D.gates.map (relocG n)
  have hrb' : ReadsBack (n + n) ⟨gs, 0⟩ := by
    intro j hj a ha
    have hj' : j < D.gates.length := by simpa [gs] using hj
    have hgj : gateAt ⟨gs, 0⟩ j = relocG n D.gates[j] := by
      unfold gateAt
      rw [List.getD_eq_getElem _ _ hj, List.getElem_map]
    rw [hgj] at ha
    simp only [relocG, List.mem_map] at ha
    obtain ⟨w, hw, rfl⟩ := ha
    have hbw := hrb j hj' w
    rw [gateAt, List.getD_eq_getElem _ _ hj'] at hbw
    have hlt := hbw hw
    unfold relocW; split_ifs <;> omega
  have hno_not : ∀ g ∈ gs, g.op ≠ .not := by
    intro g hg hop
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
    have hm := (hmono g0 hg0).1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
    rcases hm with h | h <;> simp [relocG, h] at hop
  refine ⟨by simp, ?_, hrb', ?_, hno_not, ?_, ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
    have hm := hmono g0 hg0
    refine ⟨?_, by simp [relocG, hm.2]⟩
    have h1 := hm.1
    simp only [relocG, Set.mem_insert_iff, Set.mem_singleton_iff] at h1 ⊢
    tauto
  · unfold notCount
    simp only [List.length_eq_zero_iff, List.filter_eq_nil_iff, decide_eq_true_eq]
    exact hno_not
  · intro i
    rw [rawCount_zero_iff]
    intro g hg hmem
    obtain ⟨g0, _, rfl⟩ := List.mem_map.mp hg
    simp only [relocG, List.mem_map] at hmem
    obtain ⟨w, _, hw⟩ := hmem
    exact relocW_ne_raw n w i hw
  · intro x y hx hy w hw
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      by_cases hlt : w < n
      · have hrw : relocW n w = w := by simp [relocW, hlt]
        rw [hrw, wires_low _ (x ++ y) w (by simp [hx, hy]; omega), wires_low _ x w (by omega)]
        simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : w < x.length)]
      · let j := w - n
        have hj : j < D.gates.length := by omega
        have hrw : relocW n w = (n + n) + j := by unfold relocW; simp [hlt]; omega
        have hwj : w = n + j := by omega
        rw [hrw, hwj]
        rw [wires_gate (n + n) ⟨gs, 0⟩ (x ++ y) (by simp [hx, hy]) hrb' j (by simpa [gs] using hj)]
        rw [wires_gate n D x hx hrb j hj]
        have hgj : gs[j]'(by simpa [gs] using hj) = relocG n D.gates[j] := by simp [gs]
        change (gs[j]'(by simpa [gs] using hj)).op.eval _ = _
        rw [hgj]
        simp only [relocG, List.map_map]
        congr 1
        apply List.map_congr_left
        intro a ha
        have halt : a < n + j := by
          have hb := hrb j hj a
          rw [gateAt, List.getD_eq_getElem _ _ hj] at hb
          exact hb ha
        exact ih a (by omega) (by omega)

private def orFoldAux (N : ℕ) (gs : List Gate) (acc : ℕ) : List ℕ → List Gate × ℕ
  | [] => (gs, acc)
  | w :: rest => orFoldAux N (gs ++ [⟨.or, [acc, w]⟩]) (N + gs.length) rest

private def orFold (N : ℕ) (gs : List Gate) : List ℕ → List Gate × ℕ
  | [] => (gs, 0)
  | w :: rest => orFoldAux N gs w rest

private theorem orFoldAux_props (N : ℕ) (rest : List ℕ) :
    ∀ (gs : List Gate) (acc : ℕ),
      FanInTwo ⟨gs, 0⟩ →
      ReadsBack N ⟨gs, 0⟩ →
      acc < N + gs.length →
      (∀ w ∈ rest, w < N + gs.length) →
      let res := orFoldAux N gs acc rest
      ∃ ext : List Gate,
        res.1 = gs ++ ext ∧
        ext.length = rest.length ∧
        FanInTwo ⟨res.1, 0⟩ ∧
        ReadsBack N ⟨res.1, 0⟩ ∧
        notCount ⟨ext, 0⟩ = 0 ∧
        (∀ g ∈ ext, g.op ≠ .not) ∧
        res.2 < N + res.1.length ∧
        (rest = [] ∧ res.2 = acc ∨ rest ≠ [] ∧ N + gs.length ≤ res.2) ∧
        (∀ r : ℕ, r < N → rawCount r ext + (if res.2 = r then 1 else 0) = (acc :: rest).count r) ∧
        (∀ x : List Bool, x.length = N →
          ((Circuit.mk res.1 0).wires x).getD res.2 false =
            (acc :: rest).any (fun w => ((Circuit.mk gs 0).wires x).getD w false)) := by
  induction rest with
  | nil =>
    intro gs acc hfan hrb hacc _
    refine ⟨[], by simp [orFoldAux], rfl, hfan, hrb, by simp [notCount], by simp,
      hacc, Or.inl ⟨rfl, rfl⟩, ?_, ?_⟩
    · intro r _
      simp only [orFoldAux, rawCount, List.map_nil, List.sum_nil, Nat.zero_add, List.count_singleton]
      by_cases h : acc = r
      · subst h; simp
      · simp [h, Ne.symm h]
    · intro x _; simp [orFoldAux]
  | cons w rest ih =>
    intro gs acc hfan hrb hacc hrest
    let wNew := N + gs.length
    let g : Gate := ⟨.or, [acc, w]⟩
    have hfan1 : FanInTwo ⟨gs ++ [g], 0⟩ := fanInTwo_snoc gs g hfan (by simp [g]) (by simp [g])
    have hrb1 : ReadsBack N ⟨gs ++ [g], 0⟩ := readsBack_snoc N gs g hrb (by
      intro a ha
      simp only [g, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with ha | ha
      · rw [ha]; exact hacc
      · rw [ha]; exact hrest w List.mem_cons_self)
    have hrest1 : ∀ u ∈ rest, u < N + (gs ++ [g]).length := by
      intro u hu
      have := hrest u (List.mem_cons_of_mem w hu)
      simp; omega
    obtain ⟨ext', heq, hlen', hfan', hrb', hnot', hnonot', hout', hpos', hrc', heval'⟩ :=
      ih (gs ++ [g]) wNew hfan1 hrb1 (by simp [wNew]) hrest1
    have hge_out : N + gs.length ≤ (orFoldAux N (gs ++ [g]) wNew rest).2 := by
      rcases hpos' with ⟨_, h2⟩ | ⟨_, h2⟩
      · rw [h2]
      · simp at h2; omega
    refine ⟨g :: ext', by simpa [orFoldAux, List.append_assoc] using heq, by simp [hlen'],
      hfan', hrb', ?_, ?_, hout', Or.inr ⟨by simp, hge_out⟩, ?_, ?_⟩
    · unfold notCount at hnot' ⊢; simp [g, hnot']
    · intro g' hg'
      rcases List.mem_cons.mp hg' with rfl | hg''
      · simp [g]
      · exact hnonot' g' hg''
    · intro r hr
      have h1 : rawCount r (g :: ext') = g.inputs.count r + rawCount r ext' := by simp [rawCount]
      have hrc := hrc' r hr
      have hne_new : wNew ≠ r := by dsimp [wNew]; omega
      have hne_out : (orFoldAux N (gs ++ [g]) wNew rest).2 ≠ r := by omega
      have hne_out' : (orFoldAux N (gs ++ [⟨.or, [acc, w]⟩]) (N + gs.length) rest).2 ≠ r := hne_out
      simp only [orFoldAux, hne_out, hne_out', ↓reduceIte, Nat.add_zero] at hrc ⊢
      rw [h1, hrc]
      have hg_cnt : g.inputs.count r = (if acc = r then 1 else 0) + (if w = r then 1 else 0) := by
        simp only [g, List.count_cons, List.count_nil, beq_iff_eq]
        by_cases h1 : acc = r <;> by_cases h2 : w = r <;> simp [h1, h2]
      have hn_cnt : (wNew :: rest).count r = rest.count r := by
        simp [List.count_cons, beq_iff_eq, hne_new]
      have ha_cnt : (acc :: w :: rest).count r = (if acc = r then 1 else 0) + (if w = r then 1 else 0) + rest.count r := by
        simp only [List.count_cons, beq_iff_eq]
        by_cases h1 : acc = r <;> by_cases h2 : w = r <;> simp [h1, h2] <;> omega
      omega
    · intro x hx
      have hev := heval' x hx
      have hwNew_val : ((Circuit.mk (gs ++ [g]) 0).wires x).getD wNew false =
          (((Circuit.mk gs 0).wires x).getD acc false || ((Circuit.mk gs 0).wires x).getD w false) := by
        dsimp [wNew]
        rw [← hx, wires_snoc_eq gs g x]
        simp [readGate, g, GateOp.eval]
      have hrest_any : rest.any (fun u => ((Circuit.mk (gs ++ [g]) 0).wires x).getD u false) =
          rest.any (fun u => ((Circuit.mk gs 0).wires x).getD u false) :=
        list_any_congr fun u hu =>
          wires_append_getD gs [g] x u (by rw [hx]; exact hrest u (List.mem_cons_of_mem w hu))
      change ((Circuit.mk (orFoldAux N (gs ++ [g]) wNew rest).1 0).wires x).getD
          (orFoldAux N (gs ++ [g]) wNew rest).2 false = _
      rw [hev]
      simp only [List.any_cons, hwNew_val, hrest_any, Bool.or_assoc]

private theorem orFold_props (N : ℕ) (ws : List ℕ) (hne : ws ≠ [])
    (gs : List Gate) (hfan : FanInTwo ⟨gs, 0⟩) (hrb : ReadsBack N ⟨gs, 0⟩)
    (hlt : ∀ w ∈ ws, w < N + gs.length) :
    let res := orFold N gs ws
    ∃ ext : List Gate,
      res.1 = gs ++ ext ∧
      ext.length + 1 = ws.length ∧
      FanInTwo ⟨res.1, 0⟩ ∧
      ReadsBack N ⟨res.1, 0⟩ ∧
      notCount ⟨ext, 0⟩ = 0 ∧
      (∀ g ∈ ext, g.op ≠ .not) ∧
      res.2 < N + res.1.length ∧
      (∀ r : ℕ, r < N → rawCount r ext + (if res.2 = r then 1 else 0) = ws.count r) ∧
      (∀ x : List Bool, x.length = N →
        ((Circuit.mk res.1 0).wires x).getD res.2 false =
          ws.any (fun w => ((Circuit.mk gs 0).wires x).getD w false)) := by
  cases ws with
  | nil => exact absurd rfl hne
  | cons w rest =>
    obtain ⟨ext, heq, hlen, hfan', hrb', hnot, hnonot, hout, _, hrc, heval⟩ :=
      orFoldAux_props N rest gs w hfan hrb (hlt w List.mem_cons_self)
        (fun u hu => hlt u (List.mem_cons_of_mem w hu))
    exact ⟨ext, heq, by simp [hlen], hfan', hrb', hnot, hnonot, hout, hrc, heval⟩

private def buildGroups (n : ℕ) (leadWire : Fin n → ℕ) (gs : List Gate) :
    List (Fin n × List (Fin n)) → List Gate × List ℕ
  | [] => (gs, [])
  | (idx, peers) :: rest =>
    let (gs1, wPeers) := orFold (n + n) gs (peers.map fun j => j.val)
    let wGrp := (n + n) + gs1.length
    let gs2 := gs1 ++ [⟨.and, [leadWire idx, wPeers]⟩]
    let (gs3, ws) := buildGroups n leadWire gs2 rest
    (gs3, wGrp :: ws)

private theorem buildGroups_props (n : ℕ) (leadWire : Fin n → ℕ)
    (hlead_lt : ∀ i : Fin n, leadWire i < n + n)
    (groups : List (Fin n × List (Fin n)))
    (hne : ∀ p ∈ groups, p.2 ≠ []) :
    ∀ (gs : List Gate),
      FanInTwo ⟨gs, 0⟩ →
      ReadsBack (n + n) ⟨gs, 0⟩ →
      let res := buildGroups n leadWire gs groups
      ∃ ext : List Gate,
        res.1 = gs ++ ext ∧
        ext.length = (groups.map fun p => p.2.length).sum ∧
        res.2.length = groups.length ∧
        FanInTwo ⟨res.1, 0⟩ ∧
        ReadsBack (n + n) ⟨res.1, 0⟩ ∧
        notCount ⟨ext, 0⟩ = 0 ∧
        (∀ g ∈ ext, g.op ≠ .not) ∧
        (∀ w ∈ res.2, n + n ≤ w ∧ w < (n + n) + res.1.length) ∧
        (∀ i : Fin n, rawCount (n + i.val) ext = (groups.map fun p => leadWire p.1).count (n + i.val)) ∧
        (∀ x : List Bool, x.length = n + n →
          res.2.any (fun w => ((Circuit.mk res.1 0).wires x).getD w false) =
            groups.any (fun p =>
              x.getD (leadWire p.1) false && p.2.any (fun j => x.getD j.val false))) := by
  induction groups with
  | nil =>
    intro gs hfan hrb
    refine ⟨[], by simp [buildGroups], by simp, by simp [buildGroups], hfan, hrb,
      by simp [notCount], by simp, by simp [buildGroups], by simp [rawCount], by simp [buildGroups]⟩
  | cons hd tl ih =>
    rcases hd with ⟨idx, peers⟩
    intro gs hfan hrb
    have hpeers_ne : peers ≠ [] := hne (idx, peers) List.mem_cons_self
    have hmap_ne : peers.map (fun j : Fin n => j.val) ≠ [] := by simp [hpeers_ne]
    have hmap_lt : ∀ w ∈ peers.map (fun j : Fin n => j.val), w < (n + n) + gs.length := by
      intro w hw; obtain ⟨j, _, rfl⟩ := List.mem_map.mp hw; omega
    obtain ⟨ext1, heq1, hlen1, hfan1, hrb1, hnot1, hnonot1, hout1, hrc1, heval1⟩ :=
      orFold_props (n + n) (peers.map fun j => j.val) hmap_ne gs hfan hrb hmap_lt
    set gs1 := (orFold (n + n) gs (peers.map fun j => j.val)).1
    set wPeers := (orFold (n + n) gs (peers.map fun j => j.val)).2
    let wGrp := (n + n) + gs1.length
    let gAnd : Gate := ⟨.and, [leadWire idx, wPeers]⟩
    let gs2 := gs1 ++ [gAnd]
    have hfan2 : FanInTwo ⟨gs2, 0⟩ := fanInTwo_snoc gs1 gAnd hfan1 (by simp [gAnd]) (by simp [gAnd])
    have hrb2 : ReadsBack (n + n) ⟨gs2, 0⟩ := readsBack_snoc (n + n) gs1 gAnd hrb1 (by
      intro a ha
      simp only [gAnd, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · have := hlead_lt idx; omega
      · exact hout1)
    obtain ⟨ext2, heq2, hlen2, hwlen2, hfan3, hrb3, hnot2, hnonot2, hwb2, hrc2, heval2⟩ :=
      ih (fun p hp => hne p (List.mem_cons_of_mem _ hp)) gs2 hfan2 hrb2
    have hgs3_eq : (buildGroups n leadWire gs2 tl).1 = gs ++ (ext1 ++ [gAnd] ++ ext2) := by
      rw [heq2]; simp [gs2, heq1, List.append_assoc]
    have hpeers_len : (peers.map fun j : Fin n => j.val).length = peers.length := List.length_map _
    refine ⟨ext1 ++ [gAnd] ++ ext2, ?_, ?_, ?_, hfan3, hrb3, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [buildGroups, gs2, gs1, gAnd, wPeers] using hgs3_eq
    · simp only [List.length_append, List.length_singleton, List.map_cons, List.sum_cons]
      omega
    · simp [buildGroups, gs2, gs1, gAnd, wPeers, hwlen2]
    · rw [notCount_append, notCount_append, hnot1, hnot2]; simp [notCount, gAnd]
    · intro g hg
      simp only [List.mem_append, List.mem_singleton] at hg
      rcases hg with (h1 | rfl) | h2
      · exact hnonot1 g h1
      · simp [gAnd]
      · exact hnonot2 g h2
    · intro w hw
      simp only [buildGroups, gs2, gs1, gAnd, wPeers, List.mem_cons] at hw
      rcases hw with rfl | hw'
      · change n + n ≤ wGrp ∧ wGrp < n + n + (buildGroups n leadWire gs2 tl).1.length
        refine ⟨by dsimp [wGrp]; omega, ?_⟩
        rw [hgs3_eq]; simp [wGrp, heq1]
      · exact hwb2 w hw'
    · intro i
      rw [rawCount_append, rawCount_append, hrc2 i]
      have hrc1i := hrc1 (n + i.val) (by omega)
      have hcnt0 : (peers.map fun j : Fin n => j.val).count (n + i.val) = 0 := by
        rw [List.count_eq_zero]
        simp only [List.mem_map, not_exists, not_and]
        intro j _ hj; omega
      rw [hcnt0] at hrc1i
      have hrc1_0 : rawCount (n + i.val) ext1 = 0 := by omega
      have hwP_ne : wPeers ≠ n + i.val := by
        intro heq; rw [heq] at hrc1i; simp at hrc1i
      have hgAnd_rc : rawCount (n + i.val) [gAnd] = if leadWire idx = n + i.val then 1 else 0 := by
        simp only [rawCount, gAnd, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          Nat.add_zero, List.count_cons, List.count_nil, beq_iff_eq, hwP_ne, ↓reduceIte]
        by_cases h : leadWire idx = n + i.val
        · simp [h]
        · simp [h, Ne.symm h]
      rw [hrc1_0, hgAnd_rc]
      simp only [List.map_cons, List.count_cons, beq_iff_eq]
      by_cases h : leadWire idx = n + i.val
      · simp [h]; omega
      · simp [h, Ne.symm h]
    · intro x hx
      have hev1 := heval1 x hx
      have hev2 := heval2 x hx
      have hlead_val : ((Circuit.mk gs1 0).wires x).getD (leadWire idx) false = x.getD (leadWire idx) false :=
        wires_low _ x (leadWire idx) (by rw [hx]; exact hlead_lt idx)
      have hwGrp_val2 : ((Circuit.mk gs2 0).wires x).getD wGrp false =
          (x.getD (leadWire idx) false && peers.any (fun j => x.getD j.val false)) := by
        dsimp [wGrp, gs2]
        rw [← hx, wires_snoc_eq gs1 gAnd x]
        simp only [readGate, gAnd, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
          Bool.and_true, hlead_val]
        congr 1
        rw [hev1, List.any_map]
        exact list_any_congr fun j _ => wires_low _ x j.val (by rw [hx]; omega)
      have hwGrp_val3 : ((Circuit.mk (buildGroups n leadWire gs2 tl).1 0).wires x).getD wGrp false =
          ((Circuit.mk gs2 0).wires x).getD wGrp false := by
        rw [heq2]
        exact wires_append_getD gs2 ext2 x wGrp (by rw [hx]; simp [wGrp, gs2])
      change (((Circuit.mk (buildGroups n leadWire gs2 tl).1 0).wires x).getD wGrp false ||
          (buildGroups n leadWire gs2 tl).2.any (fun w => ((Circuit.mk (buildGroups n leadWire gs2 tl).1 0).wires x).getD w false)) = _
      rw [hwGrp_val3, hwGrp_val2, hev2]
      rfl

private theorem solve (n : ℕ) (G : Fin n → Fin n → Bool) (T : Finset (Fin n)) (D : Circuit)
    (hDmono : Monotone2 D) (hDrb : ReadsBack n D)
    (hDeval : ∀ u v, D.eval (List.ofFn (fun index : Fin n => decide (index = u ∨ index = v))) = (G u v && G v u))
    (hcov : ∀ i j, G i j = true → G j i = false → i ∈ T ∨ j ∈ T) :
    let paired := fun (u v : Fin n) => List.ofFn (fun index : Fin n => decide (index = u ∨ index = v))
    let a := (Finset.univ.filter (fun p : Fin n × Fin n => G p.1 p.2 = true ∧ G p.2 p.1 = false)).card
    ∃ E : Circuit,
      FanInTwo E ∧
      ReadsBack (n + n) E ∧
      notCount E ≤ 1 ∧
      (∀ g ∈ E.gates, g.op = .not → g.inputs.length = 1) ∧
      E.output < (n + n) + E.size ∧
      E.size ≤ D.size + a + min a (2 * T.card) + T.card + 1 ∧
      (∀ i : Fin n, (E.gates.map (fun g => g.inputs.count (n + i.val))).sum ≤ 2) ∧
      (∀ i : Fin n, i ∉ T → E.output ≠ n + i.val ∧ ∀ g ∈ E.gates, n + i.val ∉ g.inputs) ∧
      ∀ u v, E.eval (paired u v ++ List.ofFn (fun raw : Fin n => decide (raw = u ∧ raw ∈ T))) = G u v := by
  classical
  intro paired a
  let asym := Finset.univ.filter (fun p : Fin n × Fin n => G p.1 p.2 = true ∧ G p.2 p.1 = false)
  let Tlist : List (Fin n) := T.toList
  have hT_nodup : Tlist.Nodup := Finset.nodup_toList T
  have hT_len : Tlist.length = T.card := Finset.length_toList T
  have hT_mem : ∀ i : Fin n, i ∈ Tlist ↔ i ∈ T := fun i => Finset.mem_toList
  let srcPeers (i : Fin n) : List (Fin n) := (Finset.univ.filter (fun j : Fin n => G i j = true ∧ G j i = false)).toList
  let tgtPeers (j : Fin n) : List (Fin n) := (Finset.univ.filter (fun i : Fin n => i ∉ T ∧ G i j = true ∧ G j i = false)).toList
  let srcGroups : List (Fin n × List (Fin n)) :=
    (Tlist.filter (fun i => decide (srcPeers i ≠ []))).map (fun i => (i, srcPeers i))
  let tgtGroups : List (Fin n × List (Fin n)) :=
    (Tlist.filter (fun j => decide (tgtPeers j ≠ []))).map (fun j => (j, tgtPeers j))
  have hsrc_ne : ∀ p ∈ srcGroups, p.2 ≠ [] := by
    intro p hp
    simp only [srcGroups, List.mem_map, List.mem_filter, decide_eq_true_eq] at hp
    obtain ⟨i, ⟨_, hne⟩, rfl⟩ := hp; exact hne
  have htgt_ne : ∀ p ∈ tgtGroups, p.2 ≠ [] := by
    intro p hp
    simp only [tgtGroups, List.mem_map, List.mem_filter, decide_eq_true_eq] at hp
    obtain ⟨j, ⟨_, hne⟩, rfl⟩ := hp; exact hne
  have hsrc_len_le : srcGroups.length ≤ T.card := by
    dsimp [srcGroups]; rw [List.length_map, ← hT_len]; exact List.length_filter_le _ _
  have htgt_len_le : tgtGroups.length ≤ T.card := by
    dsimp [tgtGroups]; rw [List.length_map, ← hT_len]; exact List.length_filter_le _ _
  have hsrc_sum : (srcGroups.map fun p => p.2.length).sum = (asym.filter (fun p => p.1 ∈ T)).card := by
    have h1 : (srcGroups.map fun p => p.2.length).sum = (Tlist.map fun i => (srcPeers i).length).sum := by
      dsimp [srcGroups]; rw [List.map_map]; exact filter_nonempty_sum srcPeers Tlist
    rw [h1]
    have h2 : (Tlist.map fun i => (srcPeers i).length).sum =
        ∑ i ∈ T, (Finset.univ.filter (fun j : Fin n => G i j = true ∧ G j i = false)).card := by
      rw [← map_toList_sum T]
      congr 1; apply List.map_congr_left; intro i _; exact Finset.length_toList _
    rw [h2]
    let fSrc (i : Fin n) : Finset (Fin n × Fin n) :=
      (Finset.univ.filter (fun j : Fin n => G i j = true ∧ G j i = false)).image (fun j => (i, j))
    have hcard : asym.filter (fun p => p.1 ∈ T) = T.biUnion fSrc := by
      ext ⟨i, j⟩
      simp only [asym, fSrc, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
        Finset.mem_image, Prod.mk.injEq]
      constructor
      · rintro ⟨⟨h1, h2⟩, hiT⟩; exact ⟨i, hiT, j, ⟨h1, h2⟩, rfl, rfl⟩
      · rintro ⟨i', hi', j', ⟨h1, h2⟩, rfl, rfl⟩; exact ⟨⟨h1, h2⟩, hi'⟩
    rw [hcard, Finset.card_biUnion]
    · apply Finset.sum_congr rfl
      intro i _
      exact (Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).2)).symm
    · intro i1 _ i2 _ hne
      change Disjoint (fSrc i1) (fSrc i2)
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      simp only [fSrc, Finset.mem_image] at hp1 hp2
      obtain ⟨_, _, rfl⟩ := hp1
      obtain ⟨_, _, heq⟩ := hp2
      exact hne (Prod.mk.inj heq).1.symm
  have htgt_sum : (tgtGroups.map fun p => p.2.length).sum = (asym.filter (fun p => p.1 ∉ T)).card := by
    have h1 : (tgtGroups.map fun p => p.2.length).sum = (Tlist.map fun j => (tgtPeers j).length).sum := by
      dsimp [tgtGroups]; rw [List.map_map]; exact filter_nonempty_sum tgtPeers Tlist
    rw [h1]
    have h2 : (Tlist.map fun j => (tgtPeers j).length).sum =
        ∑ j ∈ T, (Finset.univ.filter (fun i : Fin n => i ∉ T ∧ G i j = true ∧ G j i = false)).card := by
      rw [← map_toList_sum T]
      congr 1; apply List.map_congr_left; intro j _; exact Finset.length_toList _
    rw [h2]
    let fTgt (j : Fin n) : Finset (Fin n × Fin n) :=
      (Finset.univ.filter (fun i : Fin n => i ∉ T ∧ G i j = true ∧ G j i = false)).image (fun i => (i, j))
    have hcard : asym.filter (fun p => p.1 ∉ T) = T.biUnion fTgt := by
      ext ⟨i, j⟩
      simp only [asym, fTgt, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
        Finset.mem_image, Prod.mk.injEq]
      constructor
      · rintro ⟨⟨h1, h2⟩, hiT⟩
        have hjT : j ∈ T := (hcov i j h1 h2).resolve_left hiT
        exact ⟨j, hjT, i, ⟨hiT, h1, h2⟩, rfl, rfl⟩
      · rintro ⟨j', _, i', ⟨hiT, h1, h2⟩, rfl, rfl⟩; exact ⟨⟨h1, h2⟩, hiT⟩
    rw [hcard, Finset.card_biUnion]
    · apply Finset.sum_congr rfl
      intro j _
      exact (Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).1)).symm
    · intro j1 _ j2 _ hne
      change Disjoint (fTgt j1) (fTgt j2)
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      simp only [fTgt, Finset.mem_image] at hp1 hp2
      obtain ⟨_, _, rfl⟩ := hp1
      obtain ⟨_, _, heq⟩ := hp2
      exact hne (Prod.mk.inj heq).2.symm
  have hsum_eq_a : (srcGroups.map fun p => p.2.length).sum + (tgtGroups.map fun p => p.2.length).sum = a := by
    rw [hsrc_sum, htgt_sum]
    exact card_filter_add_not asym (fun p => p.1 ∈ T)
  have hsrc_le_sum : srcGroups.length ≤ (srcGroups.map fun p => p.2.length).sum :=
    length_le_sum_length srcGroups hsrc_ne
  have htgt_le_sum : tgtGroups.length ≤ (tgtGroups.map fun p => p.2.length).sum :=
    length_le_sum_length tgtGroups htgt_ne
  have hgrps_le_min : srcGroups.length + tgtGroups.length ≤ min a (2 * T.card) := by omega
  have hsrc_cnt : ∀ i : Fin n,
      (srcGroups.map fun p => n + p.1.val).count (n + i.val) ≤ if i ∈ T then 1 else 0 := by
    intro i
    have hnd : (srcGroups.map fun p => n + p.1.val).Nodup := by
      dsimp [srcGroups]
      rw [List.map_map]
      apply List.Nodup.map (fun x y h => Fin.ext (by dsimp at h; omega))
      exact hT_nodup.filter _
    by_cases hi : i ∈ T
    · simp only [hi, ↓reduceIte]
      exact List.nodup_iff_count_le_one.mp hnd (n + i.val)
    · simp only [hi, ↓reduceIte]
      apply Nat.le_zero.mpr
      rw [List.count_eq_zero]
      simp only [srcGroups, List.mem_map, List.mem_filter, not_exists, not_and]
      intro p ⟨j, ⟨hjT, _⟩, hp⟩ heq
      rw [← hp] at heq
      have hjeq : j = i := Fin.ext (by dsimp at heq; omega)
      subst hjeq
      exact hi ((hT_mem j).mp hjT)
  have htgt_cnt : ∀ i : Fin n, (tgtGroups.map fun p => p.1.val).count (n + i.val) = 0 := by
    intro i
    rw [List.count_eq_zero]
    simp only [List.mem_map, not_exists, not_and]
    intro p _ hp; omega
  have hraw_len : ∀ u : Fin n, (List.ofFn (fun raw : Fin n => decide (raw = u ∧ raw ∈ T))).length = n := by
    intro u; simp
  have hpair_len : ∀ u v : Fin n, (paired u v).length = n := by
    intro u v; simp [paired]
  have hinp_get_lo : ∀ (u v i : Fin n),
      (paired u v ++ List.ofFn (fun raw : Fin n => decide (raw = u ∧ raw ∈ T))).getD i.val false =
        decide (i = u ∨ i = v) := by
    intro u v i
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp [paired]), List.getElem?_ofFn]
    simp [i.isLt]
  have hinp_get_hi : ∀ (u v i : Fin n),
      (paired u v ++ List.ofFn (fun raw : Fin n => decide (raw = u ∧ raw ∈ T))).getD (n + i.val) false =
        decide (i = u ∧ i ∈ T) := by
    intro u v i
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp [paired]), hpair_len u v]
    simp only [Nat.add_sub_cancel_left, List.getElem?_ofFn, i.isLt, ↓reduceDIte, Option.getD_some]
  have hsrc_sem : ∀ u v : Fin n,
      srcGroups.any (fun p =>
        (paired u v ++ List.ofFn (fun raw : Fin n => decide (raw = u ∧ raw ∈ T))).getD (n + p.1.val) false &&
        p.2.any (fun j => (paired u v ++ List.ofFn (fun raw : Fin n => decide (raw = u ∧ raw ∈ T))).getD j.val false)) =
      decide (u ∈ T ∧ G u v = true ∧ G v u = false) := by
    intro u v
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true, Bool.and_eq_true, hinp_get_hi, hinp_get_lo, decide_eq_true_eq]
    constructor
    · rintro ⟨⟨i, js⟩, hp, ⟨rfl, hiT⟩, j, hj, hju | hjv⟩
      · simp only [srcGroups, List.mem_map, List.mem_filter, decide_eq_true_eq, Prod.mk.injEq] at hp
        obtain ⟨i', ⟨_, _⟩, rfl, rfl⟩ := hp
        simp only [srcPeers, Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and] at hj
        subst hju; rw [hj.1] at hj; simp at hj
      · simp only [srcGroups, List.mem_map, List.mem_filter, decide_eq_true_eq, Prod.mk.injEq] at hp
        obtain ⟨i', ⟨_, _⟩, rfl, rfl⟩ := hp
        simp only [srcPeers, Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and] at hj
        subst hjv; exact ⟨hiT, hj.1, hj.2⟩
    · rintro ⟨huT, h1, h2⟩
      have hv_mem : v ∈ srcPeers u := by simp [srcPeers, h1, h2]
      have hne : srcPeers u ≠ [] := List.ne_nil_of_mem hv_mem
      refine ⟨(u, srcPeers u), ?_, ⟨rfl, huT⟩, v, hv_mem, Or.inr rfl⟩
      simp only [srcGroups, List.mem_map, List.mem_filter, decide_eq_true_eq]
      exact ⟨u, ⟨(hT_mem u).mpr huT, hne⟩, rfl⟩
  have htgt_sem : ∀ u v : Fin n,
      (!(Tlist.any (fun t => (paired u v ++ List.ofFn (fun raw : Fin n => decide (raw = u ∧ raw ∈ T))).getD (n + t.val) false)) &&
       tgtGroups.any (fun p =>
         (paired u v ++ List.ofFn (fun raw : Fin n => decide (raw = u ∧ raw ∈ T))).getD p.1.val false &&
         p.2.any (fun i => (paired u v ++ List.ofFn (fun raw : Fin n => decide (raw = u ∧ raw ∈ T))).getD i.val false))) =
      decide (u ∉ T ∧ G u v = true ∧ G v u = false) := by
    intro u v
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.any_eq_false, List.any_eq_true,
      hinp_get_hi, hinp_get_lo, decide_eq_true_eq]
    constructor
    · rintro ⟨hguard, ⟨j, is⟩, hp, hju | hjv, i, hi, hiu | hiv⟩
      · simp only [tgtGroups, List.mem_map, List.mem_filter, decide_eq_true_eq, Prod.mk.injEq] at hp
        obtain ⟨j', ⟨hj'T, _⟩, rfl, rfl⟩ := hp
        exact False.elim (by
          have := hguard j' hj'T
          dsimp at hju
          exact this ⟨hju, (hT_mem j').mp hj'T⟩)
      · simp only [tgtGroups, List.mem_map, List.mem_filter, decide_eq_true_eq, Prod.mk.injEq] at hp
        obtain ⟨j', ⟨hj'T, _⟩, rfl, rfl⟩ := hp
        exact False.elim (by
          have := hguard j' hj'T
          dsimp at hju
          exact this ⟨hju, (hT_mem j').mp hj'T⟩)
      · simp only [tgtGroups, List.mem_map, List.mem_filter, decide_eq_true_eq, Prod.mk.injEq] at hp
        obtain ⟨j', ⟨_, _⟩, rfl, rfl⟩ := hp
        simp only [tgtPeers, Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and] at hi
        rw [← hjv, ← hiu]; exact hi
      · simp only [tgtGroups, List.mem_map, List.mem_filter, decide_eq_true_eq, Prod.mk.injEq] at hp
        obtain ⟨j', ⟨hj'T, _⟩, rfl, rfl⟩ := hp
        simp only [tgtPeers, Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and] at hi
        rw [hiv, ← hjv] at hi
        exact False.elim (hi.1 ((hT_mem j').mp hj'T))
    · rintro ⟨huT, h1, h2⟩
      have hvT : v ∈ T := (hcov u v h1 h2).resolve_left huT
      have hu_mem : u ∈ tgtPeers v := by simp [tgtPeers, huT, h1, h2]
      have hne : tgtPeers v ≠ [] := List.ne_nil_of_mem hu_mem
      refine ⟨fun t _ ⟨htu, htT⟩ => huT (htu ▸ htT), (v, tgtPeers v), ?_, Or.inr rfl, u, hu_mem, Or.inl rfl⟩
      simp only [tgtGroups, List.mem_map, List.mem_filter, decide_eq_true_eq]
      exact ⟨v, ⟨(hT_mem v).mpr hvT, hne⟩, rfl⟩
  let useD := decide (D.output < n + D.gates.length)
  obtain ⟨hDlen, hDfan, hDrb', hDnot, hDnonot, hDrc, hDwire⟩ := relocD_props n D hDmono hDrb
  let gs0 : List Gate := if useD then D.gates.map (relocG n) else []
  have hgs0_len : gs0.length ≤ D.size := by
    dsimp [gs0, Circuit.size]; split_ifs <;> simp [hDlen]
  have hgs0_fan : FanInTwo ⟨gs0, 0⟩ := by dsimp [gs0]; split_ifs; exact hDfan; simp [FanInTwo]
  have hgs0_rb : ReadsBack (n + n) ⟨gs0, 0⟩ := by dsimp [gs0]; split_ifs; exact hDrb'; simp [ReadsBack]
  have hgs0_not : notCount ⟨gs0, 0⟩ = 0 := by dsimp [gs0]; split_ifs; exact hDnot; simp [notCount]
  have hgs0_nonot : ∀ g ∈ gs0, g.op ≠ .not := by dsimp [gs0]; split_ifs; exact hDnonot; simp
  have hgs0_rc : ∀ i : Fin n, rawCount (n + i.val) gs0 = 0 := by
    intro i; dsimp [gs0]; split_ifs; exact hDrc i; simp [rawCount]
  obtain ⟨extS, heqS, hlenS, hwlenS, hfanS, hrbS, hnotS, hnonotS, hwbS, hrcS, hevalS⟩ :=
    buildGroups_props n (fun i => n + i.val) (fun i => by omega) srcGroups hsrc_ne gs0 hgs0_fan hgs0_rb
  set gsS := (buildGroups n (fun i => n + i.val) gs0 srcGroups).1
  set wsS := (buildGroups n (fun i => n + i.val) gs0 srcGroups).2
  obtain ⟨extT, heqT, hlenT, hwlenT, hfanT, hrbT, hnotT, hnonotT, hwbT, hrcT, hevalT⟩ :=
    buildGroups_props n (fun j => j.val) (fun j => by omega) tgtGroups htgt_ne gsS hfanS hrbS
  set gsT := (buildGroups n (fun j => j.val) gsS tgtGroups).1
  set wsT := (buildGroups n (fun j => j.val) gsS tgtGroups).2
  have hfinish : ∀ (gsM : List Gate) (extraW : List ℕ),
      gsM.length ≤ D.size + a + tgtGroups.length + (if tgtGroups = [] then 0 else T.card) →
      FanInTwo ⟨gsM, 0⟩ →
      ReadsBack (n + n) ⟨gsM, 0⟩ →
      notCount ⟨gsM, 0⟩ ≤ (if tgtGroups = [] then 0 else 1) →
      (∀ g ∈ gsM, g.op = .not → g.inputs.length = 1) →
      (∀ i : Fin n, rawCount (n + i.val) gsM ≤ if i ∈ T then 2 else 0) →
      extraW.length ≤ (if tgtGroups = [] then 0 else 1) →
      (∀ w ∈ extraW, n + n ≤ w ∧ w < (n + n) + gsM.length) →
      (∀ u v : Fin n,
        extraW.any (fun w => ((Circuit.mk gsM 0).wires (paired u v ++ List.ofFn (fun raw : Fin n => decide (raw = u ∧ raw ∈ T)))).getD w false) =
          decide (u ∉ T ∧ G u v = true ∧ G v u = false)) →
      (gsT <+: gsM) →
      ∃ E : Circuit,
        FanInTwo E ∧ ReadsBack (n + n) E ∧ notCount E ≤ 1 ∧
        (∀ g ∈ E.gates, g.op = .not → g.inputs.length = 1) ∧
        E.output < (n + n) + E.size ∧
        E.size ≤ D.size + a + min a (2 * T.card) + T.card + 1 ∧
        (∀ i : Fin n, (E.gates.map (fun g => g.inputs.count (n + i.val))).sum ≤ 2) ∧
        (∀ i : Fin n, i ∉ T → E.output ≠ n + i.val ∧ ∀ g ∈ E.gates, n + i.val ∉ g.inputs) ∧
        ∀ u v, E.eval (paired u v ++ List.ofFn (fun raw : Fin n => decide (raw = u ∧ raw ∈ T))) = G u v := by
    intro gsM extraW hMlen hMfan hMrb hMnot hMnot1 hMrc hElen hEwb hEsem hpreTM
    let dW : List ℕ := if useD then [relocW n D.output] else []
    let topW : List ℕ := wsS ++ extraW ++ dW
    have hpreST : gsS <+: gsT := ⟨extT, heqT.symm⟩
    have hpre0S : gs0 <+: gsS := ⟨extS, heqS.symm⟩
    have hpreSM : gsS <+: gsM := List.IsPrefix.trans hpreST hpreTM
    have hpre0M : gs0 <+: gsM := List.IsPrefix.trans hpre0S hpreSM
    have htop_lt : ∀ w ∈ topW, w < (n + n) + gsM.length := by
      intro w hw
      simp only [topW, List.mem_append] at hw
      rcases hw with (h1 | h2) | h3
      · have hlt := (hwbS w h1).2
        have := hpreSM.length_le; omega
      · exact (hEwb w h2).2
      · dsimp [dW] at h3
        split_ifs at h3 with huD
        · rw [List.mem_singleton.mp h3]
          have hDout : D.output < n + D.gates.length := of_decide_eq_true huD
          have hle0 : gs0.length ≤ gsM.length := hpre0M.length_le
          have hgs0e : gs0.length = D.gates.length := by simp [gs0, huD, hDlen]
          unfold relocW; split_ifs <;> omega
        · simp at h3
    have htop_no_raw : ∀ (w : ℕ), w ∈ topW → ∀ i : Fin n, w ≠ n + i.val := by
      intro w hw i
      simp only [topW, List.mem_append] at hw
      rcases hw with (h1 | h2) | h3
      · have := (hwbS w h1).1; omega
      · have := (hEwb w h2).1; omega
      · dsimp [dW] at h3
        split_ifs at h3 with huD
        · rw [List.mem_singleton.mp h3]; exact relocW_ne_raw n D.output i
        · simp at h3
    have htop_sem : ∀ u v : Fin n,
        topW.any (fun w => ((Circuit.mk gsM 0).wires (paired u v ++ List.ofFn (fun raw : Fin n => decide (raw = u ∧ raw ∈ T)))).getD w false) = G u v := by
      intro u v
      let inp := paired u v ++ List.ofFn (fun raw : Fin n => decide (raw = u ∧ raw ∈ T))
      have hinp_len : inp.length = n + n := by simp [inp, hpair_len]
      have hwsS_eq : wsS.any (fun w => ((Circuit.mk gsM 0).wires inp).getD w false) =
          decide (u ∈ T ∧ G u v = true ∧ G v u = false) := by
        obtain ⟨tailM, htailM⟩ := hpreSM
        have hcongr : wsS.any (fun w => ((Circuit.mk gsM 0).wires inp).getD w false) =
            wsS.any (fun w => ((Circuit.mk gsS 0).wires inp).getD w false) :=
          list_any_congr fun w hw => by
            rw [← htailM]
            exact wires_append_getD gsS tailM inp w (by rw [hinp_len]; exact (hwbS w hw).2)
        rw [hcongr, hevalS inp hinp_len, hsrc_sem u v]
      have hdW_eq : dW.any (fun w => ((Circuit.mk gsM 0).wires inp).getD w false) = (G u v && G v u) := by
        dsimp [dW]
        split_ifs with huD
        · simp only [List.any_cons, List.any_nil, Bool.or_false]
          obtain ⟨tail0, htail0⟩ := hpre0M
          have hDout : D.output < n + D.gates.length := of_decide_eq_true huD
          have hrel_lt : relocW n D.output < (n + n) + gs0.length := by
            have : gs0.length = D.gates.length := by simp [gs0, huD, hDlen]
            unfold relocW; split_ifs <;> omega
          rw [← htail0, wires_append_getD gs0 tail0 inp _ (by rw [hinp_len]; exact hrel_lt)]
          have hgs0d : gs0 = D.gates.map (relocG n) := by simp [gs0, huD]
          rw [hgs0d, hDwire (paired u v) _ (hpair_len u v) (hraw_len u) D.output hDout]
          exact hDeval u v
        · simp only [List.any_nil]
          have hge : n + D.gates.length ≤ D.output := by
            have : ¬ D.output < n + D.gates.length := by simpa [useD] using huD
            omega
          have hdev : D.eval (paired u v) = false :=
            wires_past D (paired u v) D.output (by rw [hpair_len u v]; exact hge)
          rw [hDeval u v] at hdev
          exact hdev.symm
      change (wsS ++ extraW ++ dW).any (fun w => ((Circuit.mk gsM 0).wires inp).getD w false) = G u v
      rw [List.any_append, List.any_append, hwsS_eq, hEsem u v, hdW_eq]
      by_cases huT : u ∈ T <;> cases h1 : G u v <;> cases h2 : G v u <;> simp [huT]
    by_cases htop_nil : topW = []
    · refine ⟨⟨[⟨.or, []⟩], n + n⟩, by simp [FanInTwo],
        by
          intro j hj a ha
          have hj0 : j = 0 := by simp at hj; exact hj
          subst hj0
          simp [gateAt] at ha,
        by simp [notCount], by simp, by simp [Circuit.size], by simp [Circuit.size],
        by intro i; simp, by intro i _; exact ⟨by have := i.isLt; dsimp; omega, by simp⟩, ?_⟩
      intro u v
      have hG := htop_sem u v
      rw [htop_nil] at hG
      simp only [List.any_nil] at hG
      rw [← hG]
      let inp := paired u v ++ List.ofFn (fun raw : Fin n => decide (raw = u ∧ raw ∈ T))
      have hlen : inp.length = n + n := by simp [inp, hpair_len]
      have hzero : ((Circuit.mk ([] ++ [⟨.or, []⟩]) 0).wires inp).getD (inp.length + ([] : List Gate).length) false = false := by
        rw [wires_snoc_eq]; rfl
      rw [hlen, List.length_nil, Nat.add_zero, List.nil_append] at hzero
      exact hzero
    · obtain ⟨extF, heqF, hlenF, hfanF, hrbF, hnotF, hnonotF, houtF, hrcF, hevalF⟩ :=
        orFold_props (n + n) topW htop_nil gsM hMfan hMrb htop_lt
      let E : Circuit := ⟨(orFold (n + n) gsM topW).1, (orFold (n + n) gsM topW).2⟩
      have hE_not : notCount E ≤ 1 := by
        change notCount ⟨(orFold (n + n) gsM topW).1, 0⟩ ≤ 1
        rw [heqF, notCount_append, hnotF]
        split_ifs at hMnot <;> omega
      have hE_sz : E.size ≤ D.size + a + min a (2 * T.card) + T.card + 1 := by
        change (orFold (n + n) gsM topW).1.length ≤ _
        rw [heqF, List.length_append]
        have htop_len : topW.length ≤ srcGroups.length + (if tgtGroups = [] then 0 else 1) + 1 := by
          have hdlen : dW.length ≤ 1 := by dsimp [dW]; split_ifs <;> simp
          have : topW.length = wsS.length + extraW.length + dW.length := by simp [topW, Nat.add_assoc]
          omega
        split_ifs at hMlen htop_len <;> omega
      have hE_rc : ∀ i : Fin n, rawCount (n + i.val) E.gates ≤ if i ∈ T then 2 else 0 := by
        intro i
        change rawCount (n + i.val) (orFold (n + n) gsM topW).1 ≤ _
        rw [heqF, rawCount_append]
        have hrcFi := hrcF (n + i.val) (by omega)
        have htop0 : topW.count (n + i.val) = 0 := by
          rw [List.count_eq_zero]
          intro hmem; exact htop_no_raw (n + i.val) hmem i rfl
        rw [htop0] at hrcFi
        have : rawCount (n + i.val) extF = 0 := by omega
        have := hMrc i
        omega
      refine ⟨E, hfanF, hrbF, hE_not, ?_, houtF, hE_sz, ?_, ?_, ?_⟩
      · intro g hg hop
        change g ∈ (orFold (n + n) gsM topW).1 at hg
        rw [heqF] at hg
        rcases List.mem_append.mp hg with h1 | h2
        · exact hMnot1 g h1 hop
        · exact absurd hop (hnonotF g h2)
      · intro i
        have := hE_rc i
        split_ifs at this <;> exact this.trans (by omega)
      · intro i hiT
        have hrc0 : rawCount (n + i.val) E.gates = 0 := by
          have := hE_rc i; simp [hiT] at this; exact this
        have hrcFi := hrcF (n + i.val) (by omega)
        have htop0 : topW.count (n + i.val) = 0 := by
          rw [List.count_eq_zero]
          intro hmem; exact htop_no_raw (n + i.val) hmem i rfl
        rw [htop0] at hrcFi
        refine ⟨?_, (rawCount_zero_iff (n + i.val) E.gates).mp hrc0⟩
        intro hout_eq
        change (orFold (n + n) gsM topW).2 = n + i.val at hout_eq
        rw [hout_eq] at hrcFi; simp at hrcFi
      · intro u v
        have hlen : (paired u v ++ List.ofFn (fun raw : Fin n => decide (raw = u ∧ raw ∈ T))).length = n + n := by
          simp [hpair_len]
        exact (hevalF _ hlen).trans (htop_sem u v)
  by_cases htgt_nil : tgtGroups = []
  · apply hfinish gsT []
    · rw [heqT, heqS, List.length_append, List.length_append, hlenS, hlenT]
      simp only [htgt_nil, ↓reduceIte, List.map_nil, List.sum_nil, List.length_nil] at hsum_eq_a ⊢
      omega
    · exact hfanT
    · exact hrbT
    · rw [heqT, heqS, notCount_append, notCount_append, hgs0_not, hnotS, hnotT]; simp
    · intro g hg hop
      rw [heqT, heqS] at hg
      simp only [List.mem_append] at hg
      rcases hg with (h1 | h2) | h3
      · exact absurd hop (hgs0_nonot g h1)
      · exact absurd hop (hnonotS g h2)
      · exact absurd hop (hnonotT g h3)
    · intro i
      rw [heqT, heqS, rawCount_append, rawCount_append, hgs0_rc i, hrcS i, hrcT i, htgt_cnt i]
      have := hsrc_cnt i
      split_ifs at this ⊢ <;> omega
    · simp
    · simp
    · intro u v
      simp only [List.any_nil]
      have hsem := htgt_sem u v
      rw [htgt_nil] at hsem
      simp only [List.any_nil, Bool.and_false] at hsem
      exact hsem
    · exact List.prefix_refl _
  · have hT_ne : Tlist ≠ [] := by
      intro hnil
      apply htgt_nil
      simp [tgtGroups, hnil]
    have hwsT_ne : wsT ≠ [] := by
      intro hnil
      have : tgtGroups.length = 0 := by rw [← hwlenT, hnil]; simp
      exact htgt_nil (List.eq_nil_of_length_eq_zero this)
    have hTmap_ne : Tlist.map (fun t : Fin n => n + t.val) ≠ [] := by simp [hT_ne]
    have hTmap_lt : ∀ w ∈ Tlist.map (fun t : Fin n => n + t.val), w < (n + n) + gsT.length := by
      intro w hw; obtain ⟨t, _, rfl⟩ := List.mem_map.mp hw; omega
    obtain ⟨extG, heqG, hlenG, hfanG, hrbG, hnotG, hnonotG, houtG, hrcG, hevalG⟩ :=
      orFold_props (n + n) (Tlist.map fun t => n + t.val) hTmap_ne gsT hfanT hrbT hTmap_lt
    set gsG := (orFold (n + n) gsT (Tlist.map fun t => n + t.val)).1
    set wRawT := (orFold (n + n) gsT (Tlist.map fun t => n + t.val)).2
    let wGuard := (n + n) + gsG.length
    let gNot : Gate := ⟨.not, [wRawT]⟩
    let gsN := gsG ++ [gNot]
    have hfanN : FanInTwo ⟨gsN, 0⟩ := fanInTwo_snoc gsG gNot hfanG (by simp [gNot]) (by simp [gNot])
    have hrbN : ReadsBack (n + n) ⟨gsN, 0⟩ := readsBack_snoc (n + n) gsG gNot hrbG (by
      intro a ha; rw [List.mem_singleton.mp ha]; exact houtG)
    have hwsT_ltN : ∀ w ∈ wsT, w < (n + n) + gsN.length := by
      intro w hw
      have := (hwbT w hw).2
      have hlen : gsT.length ≤ gsN.length := by dsimp [gsN]; rw [heqG]; simp
      omega
    obtain ⟨extJ, heqJ, hlenJ, hfanJ, hrbJ, hnotJ, hnonotJ, houtJ, hrcJ, hevalJ⟩ :=
      orFold_props (n + n) wsT hwsT_ne gsN hfanN hrbN hwsT_ltN
    set gsJ := (orFold (n + n) gsN wsT).1
    set wTgtAll := (orFold (n + n) gsN wsT).2
    let wTgtG := (n + n) + gsJ.length
    let gFin : Gate := ⟨.and, [wGuard, wTgtAll]⟩
    let gsM := gsJ ++ [gFin]
    have hfanM : FanInTwo ⟨gsM, 0⟩ := fanInTwo_snoc gsJ gFin hfanJ (by simp [gFin]) (by simp [gFin])
    have hrbM : ReadsBack (n + n) ⟨gsM, 0⟩ := readsBack_snoc (n + n) gsJ gFin hrbJ (by
      intro a ha
      simp only [gFin, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · have hle : gsG.length < gsJ.length := by rw [heqJ]; simp [gsN]
        dsimp [wGuard]; omega
      · exact houtJ)
    have hgsM_eq : gsM = gsT ++ (extG ++ [gNot] ++ extJ ++ [gFin]) := by
      dsimp [gsM]; rw [heqJ]; dsimp [gsN]; rw [heqG]; simp [List.append_assoc]
    apply hfinish gsM [wTgtG]
    · rw [hgsM_eq, heqT, heqS]
      simp only [List.length_append, List.length_singleton, htgt_nil, ↓reduceIte]
      have hTmap_l : (Tlist.map fun t : Fin n => n + t.val).length = T.card := by simp [hT_len]
      omega
    · exact hfanM
    · exact hrbM
    · rw [hgsM_eq, heqT, heqS]
      simp only [notCount_append, hgs0_not, hnotS, hnotT, hnotG, hnotJ, htgt_nil, ↓reduceIte]
      simp [notCount, gNot, gFin]
    · intro g hg hop
      rw [hgsM_eq, heqT, heqS] at hg
      simp only [List.mem_append, List.mem_singleton] at hg
      rcases hg with ((h1 | h2) | h3) | (((h4 | h5) | h6) | h7)
      · exact absurd hop (hgs0_nonot g h1)
      · exact absurd hop (hnonotS g h2)
      · exact absurd hop (hnonotT g h3)
      · exact absurd hop (hnonotG g h4)
      · rw [h5]; rfl
      · exact absurd hop (hnonotJ g h6)
      · rw [h7] at hop; simp [gFin] at hop
    · intro i
      rw [hgsM_eq, heqT, heqS]
      simp only [rawCount_append, hgs0_rc i, hrcS i, hrcT i, htgt_cnt i]
      have hrcGi := hrcG (n + i.val) (by omega)
      have hcntT : (Tlist.map fun t : Fin n => n + t.val).count (n + i.val) = if i ∈ T then 1 else 0 := by
        have hnd : (Tlist.map fun t : Fin n => n + t.val).Nodup :=
          hT_nodup.map (fun x y h => Fin.ext (by omega))
        by_cases hi : i ∈ T
        · simp only [hi, ↓reduceIte]
          have hmem : n + i.val ∈ Tlist.map (fun t : Fin n => n + t.val) :=
            List.mem_map.mpr ⟨i, (hT_mem i).mpr hi, rfl⟩
          rw [List.Nodup.count hnd]; simp [hmem]
        · simp only [hi, ↓reduceIte]
          rw [List.count_eq_zero]
          simp only [List.mem_map, not_exists, not_and]
          intro t ht heq
          have hteq : t = i := Fin.ext (by omega)
          subst hteq; exact hi ((hT_mem t).mp ht)
      have hnot_rc : rawCount (n + i.val) [gNot] = if wRawT = n + i.val then 1 else 0 := by
        simp only [rawCount, gNot, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          Nat.add_zero, List.count_singleton, beq_iff_eq]
      have hrcJi := hrcJ (n + i.val) (by omega)
      have hwsT_0 : wsT.count (n + i.val) = 0 := by
        rw [List.count_eq_zero]
        intro hmem; have := (hwbT _ hmem).1; omega
      rw [hwsT_0] at hrcJi
      have hrcJ_0 : rawCount (n + i.val) extJ = 0 := by omega
      have hwTgtAll_ne : wTgtAll ≠ n + i.val := by
        intro heq; rw [heq] at hrcJi; simp at hrcJi
      have hwGuard_ne : wGuard ≠ n + i.val := by dsimp [wGuard]; omega
      have hfin_rc : rawCount (n + i.val) [gFin] = 0 := by
        simp [rawCount, gFin, hwGuard_ne, hwTgtAll_ne]
      have hsc := hsrc_cnt i
      rw [hnot_rc, hrcJ_0, hfin_rc]
      rw [hcntT] at hrcGi
      split_ifs at hsc hrcGi ⊢ <;> omega
    · simp [htgt_nil]
    · intro w hw
      rw [List.mem_singleton.mp hw]
      refine ⟨by dsimp [wTgtG]; omega, by simp [gsM, wTgtG]⟩
    · intro u v
      let inp := paired u v ++ List.ofFn (fun raw : Fin n => decide (raw = u ∧ raw ∈ T))
      have hinp_len : inp.length = n + n := by simp [inp, hpair_len]
      simp only [List.any_cons, List.any_nil, Bool.or_false]
      dsimp [wTgtG, gsM]
      rw [← hinp_len, wires_snoc_eq gsJ gFin inp]
      simp only [readGate, gFin, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, Bool.and_true]
      have hguard_val : ((Circuit.mk gsJ 0).wires inp).getD wGuard false =
          !(Tlist.any (fun t => inp.getD (n + t.val) false)) := by
        rw [heqJ, wires_append_getD gsN extJ inp wGuard (by rw [hinp_len]; simp [gsN, wGuard])]
        dsimp [wGuard, gsN]
        rw [← hinp_len, wires_snoc_eq gsG gNot inp]
        simp only [readGate, gNot, GateOp.eval, List.map_cons, List.map_nil, List.head?_cons, Option.getD_some]
        congr 1
        rw [hevalG inp hinp_len, List.any_map]
        exact list_any_congr fun t _ => wires_low _ inp (n + t.val) (by rw [hinp_len]; omega)
      have htgt_val : ((Circuit.mk gsJ 0).wires inp).getD wTgtAll false =
          tgtGroups.any (fun p => inp.getD p.1.val false && p.2.any (fun i => inp.getD i.val false)) := by
        rw [hevalJ inp hinp_len]
        have hgsN_eq : gsN = gsT ++ (extG ++ [gNot]) := by dsimp [gsN]; rw [heqG, List.append_assoc]
        have hcongr : wsT.any (fun w => ((Circuit.mk gsN 0).wires inp).getD w false) =
            wsT.any (fun w => ((Circuit.mk gsT 0).wires inp).getD w false) :=
          list_any_congr fun w hw => by
            rw [hgsN_eq]
            exact wires_append_getD gsT _ inp w (by rw [hinp_len]; exact (hwbT w hw).2)
        rw [hcongr, hevalT inp hinp_len]
      rw [hguard_val, htgt_val]
      exact htgt_sem u v
    · exact ⟨extG ++ [gNot] ++ extJ ++ [gFin], hgsM_eq.symm⟩

end PEqualNP.Outside.L_meta_25518_aux

theorem PEqualNP.Outside.L_meta_25518 : (∀ (n : ℕ) (G : Fin n → Fin n → Bool) (T : Finset (Fin n))
    (D : PEqualNP.CircuitLowerBounds.Circuit),
  let paired := fun (u v : Fin n) => List.ofFn (fun index : Fin n => decide (index = u ∨ index = v))
  let a := (Finset.univ.filter (fun p : Fin n × Fin n =>
    G p.1 p.2 = true ∧ G p.2 p.1 = false)).card
  PEqualNP.MetaComplexity.Monotone2 D →
  PEqualNP.MetaComplexity.NestedCover.ReadsBack n D →
  (∀ u v, D.eval (paired u v) = (G u v && G v u)) →
  (∀ i j, G i j = true → G j i = false → i ∈ T ∨ j ∈ T) →
  ∃ E : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo E ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + n) E ∧
    PEqualNP.NotBracket.notCount E ≤ 1 ∧
    (∀ g ∈ E.gates, g.op = .not → g.inputs.length = 1) ∧
    E.output < (n + n) + E.size ∧
    E.size ≤ D.size + a + min a (2 * T.card) + T.card + 1 ∧
    (∀ i : Fin n, (E.gates.map (fun g => g.inputs.count (n + i.val))).sum ≤ 2) ∧
    (∀ i : Fin n, i ∉ T → E.output ≠ n + i.val ∧
      ∀ g ∈ E.gates, n + i.val ∉ g.inputs) ∧
    ∀ u v, E.eval (paired u v ++ List.ofFn (fun raw : Fin n => decide (raw = u ∧ raw ∈ T))) = G u v) :=
  PEqualNP.Outside.L_meta_25518_aux.solve
