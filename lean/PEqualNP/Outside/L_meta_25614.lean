import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25614_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents

private def wireVal (C : Circuit) (inp : List Bool) (w : ℕ) : Bool :=
  (C.wires inp).getD w false

private theorem wires_length (C : Circuit) (inp : List Bool) :
    (C.wires inp).length = inp.length + C.gates.length := by
  unfold Circuit.wires
  suffices h : ∀ (l : List Gate) (acc : List Bool),
      (l.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) acc).length =
        acc.length + l.length by
    exact h C.gates inp
  intro l
  induction l with
  | nil => intro acc; simp
  | cons g l ih =>
    intro acc
    simp only [List.foldl_cons, ih, List.length_append, List.length_cons, List.length_nil]
    omega

private theorem wires_prefix_eq (gs1 gs2 : List Gate) (inp : List Bool) (w : ℕ)
    (hw : w < inp.length + gs1.length) :
    (Circuit.wires ⟨gs1 ++ gs2, 0⟩ inp).getD w false =
      (Circuit.wires ⟨gs1, 0⟩ inp).getD w false := by
  induction gs2 using List.reverseRecOn with
  | nil => simp
  | append_singleton gs2 g ih =>
    rw [← List.append_assoc]
    have hsnoc : Circuit.wires ⟨(gs1 ++ gs2) ++ [g], 0⟩ inp =
        Circuit.wires ⟨gs1 ++ gs2, 0⟩ inp ++
          [g.op.eval (g.inputs.map fun i => (Circuit.wires ⟨gs1 ++ gs2, 0⟩ inp).getD i false)] := by
      unfold Circuit.wires; rw [List.foldl_append]; rfl
    rw [hsnoc]
    have hlen : (Circuit.wires ⟨gs1 ++ gs2, 0⟩ inp).length = inp.length + (gs1 ++ gs2).length :=
      wires_length ⟨gs1 ++ gs2, 0⟩ inp
    have hlt : w < (Circuit.wires ⟨gs1 ++ gs2, 0⟩ inp).length := by
      rw [hlen, List.length_append]; omega
    rw [List.getD_eq_getElem _ _ (by rw [List.length_append]; omega),
      List.getElem_append_left hlt, ← List.getD_eq_getElem _ _ hlt]
    exact ih

private theorem wireVal_input (C : Circuit) (inp : List Bool) {w : ℕ} (hw : w < inp.length) :
    wireVal C inp w = inp.getD w false := by
  unfold wireVal
  have h := wires_prefix_eq [] C.gates inp w (by simpa using hw)
  simpa [Circuit.wires] using h

private theorem wireVal_gate (C : Circuit) (inp : List Bool) {raw j : ℕ}
    (hinp : inp.length = raw) (hj : j < C.gates.length)
    (hrb : ∀ u ∈ (gateAt C j).inputs, u < raw + j) :
    wireVal C inp (raw + j) =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun u => (C.wires inp).getD u false) := by
  unfold wireVal
  have hsplit : C.gates = C.gates.take j ++ [C.gates[j]] ++ C.gates.drop (j + 1) := by
    have h1 : C.gates.take (j + 1) ++ C.gates.drop (j + 1) = C.gates := List.take_append_drop (j + 1) C.gates
    rw [List.take_succ_eq_append_getElem hj] at h1
    exact h1.symm
  have hgt : gateAt C j = C.gates[j] := by
    unfold gateAt; exact List.getD_eq_getElem C.gates _ hj
  have htake_len : (C.gates.take j).length = j := List.length_take_of_le (Nat.le_of_lt hj)
  have hpref1 : (C.wires inp).getD (raw + j) false =
      (Circuit.wires ⟨C.gates.take j ++ [C.gates[j]], 0⟩ inp).getD (raw + j) false := by
    have h := wires_prefix_eq (C.gates.take j ++ [C.gates[j]]) (C.gates.drop (j + 1)) inp (raw + j)
      (by rw [hinp, List.length_append, htake_len]; simp)
    have heq : Circuit.wires ⟨(C.gates.take j ++ [C.gates[j]]) ++ C.gates.drop (j + 1), 0⟩ inp = C.wires inp := by
      unfold Circuit.wires; rw [← hsplit]
    rw [← heq]; exact h
  have hsnoc : Circuit.wires ⟨C.gates.take j ++ [C.gates[j]], 0⟩ inp =
      Circuit.wires ⟨C.gates.take j, 0⟩ inp ++
        [C.gates[j].op.eval (C.gates[j].inputs.map fun i => (Circuit.wires ⟨C.gates.take j, 0⟩ inp).getD i false)] := by
    unfold Circuit.wires; rw [List.foldl_append]; rfl
  have hlen_t : (Circuit.wires ⟨C.gates.take j, 0⟩ inp).length = raw + j := by
    rw [wires_length ⟨C.gates.take j, 0⟩ inp, hinp, htake_len]
  rw [hpref1, hsnoc, List.getD_eq_getElem _ _ (by rw [List.length_append, hlen_t]; simp),
    List.getElem_append_right (by omega)]
  simp only [hlen_t, Nat.sub_self, List.getElem_cons_zero, hgt]
  congr 1
  apply List.map_congr_left
  intro u hu
  have hult : u < raw + j := hrb u (by rwa [hgt])
  have h := wires_prefix_eq (C.gates.take j) ([C.gates[j]] ++ C.gates.drop (j + 1)) inp u
    (by rw [hinp, htake_len]; exact hult)
  have heq : Circuit.wires ⟨C.gates.take j ++ ([C.gates[j]] ++ C.gates.drop (j + 1)), 0⟩ inp = C.wires inp := by
    unfold Circuit.wires; rw [← List.append_assoc, ← hsplit]
  rw [← heq]; exact h.symm

private theorem wireVal_oob (C : Circuit) (inp : List Bool) {w : ℕ}
    (hw : inp.length + C.gates.length ≤ w) : wireVal C inp w = false := by
  unfold wireVal
  rw [List.getD_eq_default]
  rw [wires_length]; exact hw

private theorem gateOp_eval_mono {op : GateOp} (hop : op = GateOp.and ∨ op = GateOp.or)
    {l : List ℕ} {f1 f2 : ℕ → Bool}
    (h : ∀ u ∈ l, f1 u = true → f2 u = true)
    (ht : op.eval (l.map f1) = true) : op.eval (l.map f2) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq] at ht ⊢
    rintro b ⟨u, hu, rfl⟩
    exact h u hu (ht (f1 u) ⟨u, hu, rfl⟩)
  · simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at ht ⊢
    obtain ⟨_, ⟨u, hu, rfl⟩, h1⟩ := ht
    exact ⟨f2 u, ⟨u, hu, rfl⟩, h u hu h1⟩

private theorem readsIn_ge_count (C : Circuit) (G : Finset ℕ) {k : ℕ} (hk : k ∈ G) (w : ℕ) :
    (gateAt C k).inputs.count w ≤ readsIn C G w := by
  unfold readsIn
  exact Finset.single_le_sum (f := fun j => (gateAt C j).inputs.count w) (fun _ _ => Nat.zero_le _) hk

private theorem readsIn_ge_two_of_two (C : Circuit) (G : Finset ℕ) {k1 k2 : ℕ}
    (hk1 : k1 ∈ G) (hk2 : k2 ∈ G) (hne : k1 ≠ k2) (w : ℕ)
    (h1 : w ∈ (gateAt C k1).inputs) (h2 : w ∈ (gateAt C k2).inputs) :
    2 ≤ readsIn C G w := by
  unfold readsIn
  have hsub : ({k1, k2} : Finset ℕ) ⊆ G := by
    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg (f := fun j => (gateAt C j).inputs.count w)
    hsub (fun _ _ _ => Nat.zero_le _)
  rw [Finset.sum_pair hne] at hsum
  have hc1 : 1 ≤ (gateAt C k1).inputs.count w := List.count_pos_iff.mpr h1
  have hc2 : 1 ≤ (gateAt C k2).inputs.count w := List.count_pos_iff.mpr h2
  omega

private theorem exists_reader_of_readsIn_pos (C : Circuit) (G : Finset ℕ) (w : ℕ)
    (hpos : 0 < readsIn C G w) : ∃ k ∈ G, w ∈ (gateAt C k).inputs := by
  by_contra hno
  push Not at hno
  have h0 : readsIn C G w = 0 := by
    unfold readsIn
    apply Finset.sum_eq_zero
    intro k hk
    exact List.count_eq_zero.mpr (hno k hk)
  omega

private theorem gate_children {C : Circuit} {k : ℕ} (hlen : (gateAt C k).inputs.length = 2) :
    ∃ u v, (gateAt C k).inputs = [u, v] := by
  cases h : (gateAt C k).inputs with
  | nil => rw [h] at hlen; simp at hlen
  | cons u rest =>
    cases rest with
    | nil => rw [h] at hlen; simp at hlen
    | cons v rest2 =>
      cases rest2 with
      | nil => exact ⟨u, v, rfl⟩
      | cons _ _ => rw [h] at hlen; simp at hlen

private def subWires (raw : ℕ) (C : Circuit) (region wires : Finset ℕ)
    (hrb : ReadsBack raw C) (hreg : region ⊆ Finset.range C.size) : ℕ → Finset ℕ :=
  WellFounded.fix Nat.lt_wfRel.wf fun w rec =>
    if hw : w ∈ wires then
      if hge : raw ≤ w then
        if hk : w - raw ∈ region then
          insert w (((gateAt C (w - raw)).inputs.attach).foldl
            (fun acc ⟨u, hu⟩ =>
              have hlt : u < w := by
                have hks : w - raw < C.gates.length := Finset.mem_range.mp (hreg hk)
                have := hrb (w - raw) hks u hu
                omega
              acc ∪ rec u hlt) ∅)
        else {w}
      else {w}
    else ∅

private theorem subWires_not_mem (raw : ℕ) (C : Circuit) (region wires : Finset ℕ)
    (hrb : ReadsBack raw C) (hreg : region ⊆ Finset.range C.size) {w : ℕ} (hw : w ∉ wires) :
    subWires raw C region wires hrb hreg w = ∅ := by
  unfold subWires
  rw [WellFounded.fix_eq]
  simp [hw]

private theorem subWires_source (raw : ℕ) (C : Circuit) (region wires : Finset ℕ)
    (hrb : ReadsBack raw C) (hreg : region ⊆ Finset.range C.size) {w : ℕ}
    (hw : w ∈ wires) (hlt : w < raw) :
    subWires raw C region wires hrb hreg w = {w} := by
  unfold subWires
  rw [WellFounded.fix_eq]
  have hnge : ¬ raw ≤ w := by omega
  simp [hw, hnge]

private theorem subWires_gate (raw : ℕ) (C : Circuit) (region wires : Finset ℕ)
    (hrb : ReadsBack raw C) (hreg : region ⊆ Finset.range C.size) {k u v : ℕ}
    (hk : k ∈ region) (hw : raw + k ∈ wires) (hinp : (gateAt C k).inputs = [u, v]) :
    subWires raw C region wires hrb hreg (raw + k) =
      insert (raw + k) (subWires raw C region wires hrb hreg u ∪
        subWires raw C region wires hrb hreg v) := by
  have hge : raw ≤ raw + k := by omega
  have hsub : raw + k - raw = k := Nat.add_sub_cancel_left raw k
  have hfold : ∀ (l : List ℕ) (hl : ∀ x ∈ l, x < raw + k),
      (l.attach.foldl (fun acc x => acc ∪ subWires raw C region wires hrb hreg x.1) ∅) =
      l.foldl (fun acc x => acc ∪ subWires raw C region wires hrb hreg x) ∅ := by
    intro l hl
    suffices hs : ∀ (acc : Finset ℕ),
        (l.attach.foldl (fun a x => a ∪ subWires raw C region wires hrb hreg x.1) acc) =
        l.foldl (fun a x => a ∪ subWires raw C region wires hrb hreg x) acc from hs ∅
    induction l with
    | nil => intro acc; rfl
    | cons a l ih =>
      intro acc
      simp only [List.attach_cons, List.foldl_cons, List.foldl_map]
      exact ih (fun x hx => hl x (List.mem_cons_of_mem _ hx)) _
  conv_lhs => unfold subWires; rw [WellFounded.fix_eq]
  simp only [hw, hge, ↓reduceDIte]
  have hk' : raw + k - raw ∈ region := by rwa [hsub]
  simp only [hk', ↓reduceDIte]
  have hbody : ((gateAt C (raw + k - raw)).inputs.attach.foldl
      (fun acc x => acc ∪ subWires raw C region wires hrb hreg x.1) ∅) =
      subWires raw C region wires hrb hreg u ∪ subWires raw C region wires hrb hreg v := by
    rw [hfold _ (fun x hx => by rw [hsub] at hx; exact hrb k (Finset.mem_range.mp (hreg hk)) x hx),
      hsub, hinp]
    simp
  exact congrArg (insert (raw + k)) hbody

private def evalSub (raw : ℕ) (C : Circuit) (region : Finset ℕ) (entry : ℕ)
    (hrb : ReadsBack raw C) (hreg : region ⊆ Finset.range C.size)
    (inp : List Bool) (e : Bool) : ℕ → Bool :=
  WellFounded.fix Nat.lt_wfRel.wf fun w rec =>
    if w = entry then e
    else if hge : raw ≤ w then
      if hk : w - raw ∈ region then
        let g := gateAt C (w - raw)
        let vals := g.inputs.attach.map (fun ⟨u, hu⟩ =>
          have hlt : u < w := by
            have hks : w - raw < C.gates.length := Finset.mem_range.mp (hreg hk)
            have := hrb (w - raw) hks u hu
            omega
          rec u hlt)
        g.op.eval vals
      else inp.getD w false
    else inp.getD w false

private theorem evalSub_entry (raw : ℕ) (C : Circuit) (region : Finset ℕ) (entry : ℕ)
    (hrb : ReadsBack raw C) (hreg : region ⊆ Finset.range C.size)
    (inp : List Bool) (e : Bool) :
    evalSub raw C region entry hrb hreg inp e entry = e := by
  unfold evalSub; rw [WellFounded.fix_eq]; simp

private theorem evalSub_source (raw : ℕ) (C : Circuit) (region : Finset ℕ) (entry : ℕ)
    (hrb : ReadsBack raw C) (hreg : region ⊆ Finset.range C.size)
    (inp : List Bool) (e : Bool) {w : ℕ} (hne : w ≠ entry) (hlt : w < raw) :
    evalSub raw C region entry hrb hreg inp e w = inp.getD w false := by
  unfold evalSub; rw [WellFounded.fix_eq]
  have hnge : ¬ raw ≤ w := by omega
  simp [hne, hnge]

private theorem evalSub_gate (raw : ℕ) (C : Circuit) (region : Finset ℕ) (entry : ℕ)
    (hrb : ReadsBack raw C) (hreg : region ⊆ Finset.range C.size)
    (inp : List Bool) (e : Bool) {k u v : ℕ}
    (hk : k ∈ region) (hne : raw + k ≠ entry) (hinp : (gateAt C k).inputs = [u, v]) :
    evalSub raw C region entry hrb hreg inp e (raw + k) =
      (gateAt C k).op.eval [evalSub raw C region entry hrb hreg inp e u,
        evalSub raw C region entry hrb hreg inp e v] := by
  have hge : raw ≤ raw + k := by omega
  have hsub : raw + k - raw = k := Nat.add_sub_cancel_left raw k
  have hk' : raw + k - raw ∈ region := by rwa [hsub]
  conv_lhs => unfold evalSub; rw [WellFounded.fix_eq]
  simp only [hne, ↓reduceIte, hge, hk', ↓reduceDIte]
  have hmap : ((gateAt C (raw + k - raw)).inputs.attach.map
      (fun x => evalSub raw C region entry hrb hreg inp e x.1)) =
      (gateAt C (raw + k - raw)).inputs.map (evalSub raw C region entry hrb hreg inp e) := by
    rw [List.map_attach_eq_pmap, List.pmap_eq_map]
  change (gateAt C (raw + k - raw)).op.eval
    ((gateAt C (raw + k - raw)).inputs.attach.map
      (fun x => evalSub raw C region entry hrb hreg inp e x.1)) = _
  rw [hmap, hsub, hinp]
  rfl

set_option maxHeartbeats 800000 in
private theorem main_aux : ∀ (n m : ℕ) (G : Fin n → Fin m → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit)
    (R : Finset (Fin n)) (B : Finset (Fin m)) (region entry : Finset ℕ) (root : ℕ),
  let raw := n + m
  let sources := R.image (fun src => src.val) ∪ B.image (fun dest => n + dest.val)
  let wires := sources ∪ region.image (fun idx => raw + idx)
  let gate := PEqualNP.MetaComplexity.NestedCover.gateAt C
  let localReads := PEqualNP.MetaComplexity.NestedCover.readsIn C region
  let allReads := PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size)
  let extR := fun (i : Fin n) => (Finset.univ \ B).filter (fun outColumn : Fin m => G i outColumn = false)
  let extC := fun (j : Fin m) => (Finset.univ \ R).filter (fun outRow : Fin n => G outRow j = false)
  (∀ a, ∃ c, G a c = false) → (∀ c, ∃ a, G a c = false) →
  PEqualNP.MetaComplexity.Monotone2 C →
  PEqualNP.MetaComplexity.NestedCover.ReadsBack raw C →
  PEqualNP.Represents.Represents G C → region ⊆ Finset.range C.size → root ∈ wires →
  entry.card ≤ 1 → (∀ w ∈ entry, w ∉ wires ∧ w < root ∧ localReads w = 1) →
  (∀ k ∈ region,
    ((gate k).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
     (gate k).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
    (gate k).inputs.length = 2 ∧ ∀ w ∈ (gate k).inputs, w ∈ wires ∨ w ∈ entry) →
  localReads root = 0 →
  (∀ w ∈ wires, w ≠ root → localReads w = 1 ∧ allReads w = 1 ∧ C.output ≠ w) →
  (∀ a ∈ R, ∀ b ∈ R, extR a ⊆ extR b ∨ extR b ⊆ extR a) ∧
  (∀ x ∈ B, ∀ y ∈ B, extC x ⊆ extC y ∨ extC y ⊆ extC x) ∧
  (∀ a ∈ R, ∀ b ∈ R, ∀ x ∈ B, ∀ y ∈ B,
    G a x = true → G b x = true → G b y = true → G a y = true) ∧
  (∀ a ∈ R, ∀ x ∈ B, G a x = true →
    (∀ j ∉ B, G a j = false) ∨ (∀ i ∉ R, G i x = false)) := by
  classical
  intro n m G C R B region entry root raw sources wires gate localReads allReads extR extC
    hzeroR hzeroC hmonoC hrb hrep hreg hrootMem hentryCard hentrySpec hgates hrootRead hpriv
  have hgate_mono_op : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or := by
    intro j hj
    have hgt : gateAt C j = C.gates[j] := by unfold gateAt; exact List.getD_eq_getElem C.gates _ hj
    have hmem : C.gates[j] ∈ C.gates := List.getElem_mem hj
    have hm := (hmonoC C.gates[j] hmem).1
    rw [hgt]
    simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hm
  have hcircuit_mono : ∀ (inp1 inp2 : List Bool), inp1.length = raw → inp2.length = raw →
      (∀ z < raw, inp1.getD z false = true → inp2.getD z false = true) →
      ∀ w, wireVal C inp1 w = true → wireVal C inp2 w = true := by
    intro inp1 inp2 hinp1 hinp2 hle w
    induction w using Nat.strongRecOn with
    | ind w ih =>
      intro ht
      by_cases hw_lt : w < raw
      · rw [wireVal_input C inp1 (by omega)] at ht
        rw [wireVal_input C inp2 (by omega)]
        exact hle w hw_lt ht
      · by_cases hjs : w - raw < C.gates.length
        · have hweq : raw + (w - raw) = w := by omega
          have hg1 := wireVal_gate C inp1 hinp1 hjs (hrb (w - raw) hjs)
          have hg2 := wireVal_gate C inp2 hinp2 hjs (hrb (w - raw) hjs)
          rw [hweq] at hg1 hg2
          rw [hg1] at ht; rw [hg2]
          exact gateOp_eval_mono (hgate_mono_op (w - raw) hjs)
            (fun u hu => ih u (by have := hrb (w - raw) hjs u hu; omega)) ht
        · rw [wireVal_oob C inp1 (by omega)] at ht
          exact False.elim (Bool.noConfusion ht)
  let e0 : ℕ := if h : entry.Nonempty then h.choose else wires.sum id + 1
  have he0_not_mem : e0 ∉ wires := by
    dsimp [e0]
    split_ifs with h
    · exact (hentrySpec h.choose h.choose_spec).1
    · intro hmem
      have hle : wires.sum id + 1 ≤ wires.sum id :=
        Finset.single_le_sum (f := id) (fun _ _ => Nat.zero_le _) hmem
      omega
  have hentry_eq_e0 : ∀ w ∈ entry, w = e0 := by
    intro w hw
    have hne : entry.Nonempty := ⟨w, hw⟩
    dsimp [e0]
    simp only [hne, ↓reduceDIte]
    exact Finset.card_le_one.mp hentryCard w hw hne.choose hne.choose_spec
  have hgates_e0 : ∀ k ∈ region, ∀ w ∈ (gate k).inputs, w ∈ wires ∨ w = e0 := by
    intro k hk w hw
    rcases (hgates k hk).2.2 w hw with hw' | hw'
    · exact Or.inl hw'
    · exact Or.inr (hentry_eq_e0 w hw')
  have hsrc_lt : ∀ w ∈ sources, w < raw := by
    intro w hw
    simp only [sources, Finset.mem_union, Finset.mem_image] at hw
    rcases hw with ⟨a, _, rfl⟩ | ⟨j, _, rfl⟩ <;> omega
  have hwires_split : ∀ w ∈ wires, (w < raw ∧ w ∈ sources) ∨ (raw ≤ w ∧ w - raw ∈ region) := by
    intro w hw
    simp only [wires, Finset.mem_union, Finset.mem_image] at hw
    rcases hw with hs | ⟨k, hk, rfl⟩
    · exact Or.inl ⟨hsrc_lt w hs, hs⟩
    · exact Or.inr ⟨by omega, by simpa using hk⟩
  let S := subWires raw C region wires hrb hreg
  have hS_not_mem : ∀ {w}, w ∉ wires → S w = ∅ := fun hw => subWires_not_mem raw C region wires hrb hreg hw
  have hS_source : ∀ {w}, w ∈ wires → w < raw → S w = {w} := fun hw hlt => subWires_source raw C region wires hrb hreg hw hlt
  have hS_gate : ∀ {k u v}, k ∈ region → raw + k ∈ wires → (gateAt C k).inputs = [u, v] →
      S (raw + k) = insert (raw + k) (S u ∪ S v) := fun hk hw huv => subWires_gate raw C region wires hrb hreg hk hw huv
  have hS_sub : ∀ w, S w ⊆ wires := by
    intro w
    induction w using Nat.strongRecOn with
    | ind w ih =>
      by_cases hw : w ∈ wires
      · rcases hwires_split w hw with ⟨hlt, _⟩ | ⟨hge, hk⟩
        · rw [hS_source hw hlt]
          exact Finset.singleton_subset_iff.mpr hw
        · obtain ⟨_, hlen, _⟩ := hgates (w - raw) hk
          obtain ⟨u, v, huv⟩ := gate_children hlen
          have hweq : raw + (w - raw) = w := by omega
          have hSw : S w = insert w (S u ∪ S v) := by
            have := hS_gate hk (by rwa [hweq]) huv
            simpa [hweq] using this
          rw [hSw]
          have hks : w - raw < C.gates.length := Finset.mem_range.mp (hreg hk)
          have hu_lt : u < w := by have := hrb (w - raw) hks u (by rw [huv]; simp); omega
          have hv_lt : v < w := by have := hrb (w - raw) hks v (by rw [huv]; simp); omega
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_union] at hz
          rcases hz with rfl | hz | hz
          · exact hw
          · exact ih u hu_lt hz
          · exact ih v hv_lt hz
      · rw [hS_not_mem hw]; exact Finset.empty_subset _
  have hS_le : ∀ w z, z ∈ S w → z ≤ w := by
    intro w
    induction w using Nat.strongRecOn with
    | ind w ih =>
      intro z hz
      by_cases hw : w ∈ wires
      · rcases hwires_split w hw with ⟨hlt, _⟩ | ⟨hge, hk⟩
        · rw [hS_source hw hlt] at hz
          simp only [Finset.mem_singleton] at hz; omega
        · obtain ⟨_, hlen, _⟩ := hgates (w - raw) hk
          obtain ⟨u, v, huv⟩ := gate_children hlen
          have hweq : raw + (w - raw) = w := by omega
          have hSw : S w = insert w (S u ∪ S v) := by
            have := hS_gate hk (by rwa [hweq]) huv
            simpa [hweq] using this
          rw [hSw] at hz
          have hks : w - raw < C.gates.length := Finset.mem_range.mp (hreg hk)
          have hu_lt : u < w := by have := hrb (w - raw) hks u (by rw [huv]; simp); omega
          have hv_lt : v < w := by have := hrb (w - raw) hks v (by rw [huv]; simp); omega
          simp only [Finset.mem_insert, Finset.mem_union] at hz
          rcases hz with rfl | hz | hz
          · exact le_rfl
          · exact (ih u hu_lt z hz).trans (Nat.le_of_lt hu_lt)
          · exact (ih v hv_lt z hz).trans (Nat.le_of_lt hv_lt)
      · rw [hS_not_mem hw] at hz; simp at hz
  have hS_self : ∀ w ∈ wires, w ∈ S w := by
    intro w hw
    rcases hwires_split w hw with ⟨hlt, _⟩ | ⟨hge, hk⟩
    · rw [hS_source hw hlt]; simp
    · obtain ⟨_, hlen, _⟩ := hgates (w - raw) hk
      obtain ⟨u, v, huv⟩ := gate_children hlen
      have hweq : raw + (w - raw) = w := by omega
      have hSw : S w = insert w (S u ∪ S v) := by
        have := hS_gate hk (by rwa [hweq]) huv
        simpa [hweq] using this
      rw [hSw]; simp
  let SG (w : ℕ) : Finset ℕ := (S w).filter (fun z => raw ≤ z) |>.image (fun z => z - raw)
  let SL (w : ℕ) : Finset ℕ := (S w).filter (fun z => z < raw)
  have hSG_sub : ∀ w, SG w ⊆ region := by
    intro w k hk
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨hzS, hzge⟩ := Finset.mem_filter.mp hz
    rcases hwires_split z (hS_sub w hzS) with ⟨hlt, _⟩ | ⟨_, hkr⟩
    · omega
    · exact hkr
  have hS_parent : ∀ w z, z ∈ S w → z ≠ w → ∃ k ∈ SG w, z ∈ (gate k).inputs := by
    intro w
    induction w using Nat.strongRecOn with
    | ind w ih =>
      intro z hz hne
      by_cases hw : w ∈ wires
      · rcases hwires_split w hw with ⟨hlt, _⟩ | ⟨hge, hk⟩
        · rw [hS_source hw hlt] at hz
          simp only [Finset.mem_singleton] at hz; exact False.elim (hne hz)
        · obtain ⟨_, hlen, _⟩ := hgates (w - raw) hk
          obtain ⟨u, v, huv⟩ := gate_children hlen
          have hweq : raw + (w - raw) = w := by omega
          have hSw : S w = insert w (S u ∪ S v) := by
            have := hS_gate hk (by rwa [hweq]) huv
            simpa [hweq] using this
          have hks : w - raw < C.gates.length := Finset.mem_range.mp (hreg hk)
          have hu_lt : u < w := by have := hrb (w - raw) hks u (by rw [huv]; simp); omega
          have hv_lt : v < w := by have := hrb (w - raw) hks v (by rw [huv]; simp); omega
          have hkw : w - raw ∈ SG w :=
            Finset.mem_image.mpr ⟨w, Finset.mem_filter.mpr ⟨hS_self w hw, hge⟩, rfl⟩
          have hSGu : SG u ⊆ SG w := by
            intro j hj
            obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hj
            obtain ⟨hyS, hyge⟩ := Finset.mem_filter.mp hy
            exact Finset.mem_image.mpr ⟨y, Finset.mem_filter.mpr ⟨by rw [hSw]; simp [hyS], hyge⟩, rfl⟩
          have hSGv : SG v ⊆ SG w := by
            intro j hj
            obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hj
            obtain ⟨hyS, hyge⟩ := Finset.mem_filter.mp hy
            exact Finset.mem_image.mpr ⟨y, Finset.mem_filter.mpr ⟨by rw [hSw]; simp [hyS], hyge⟩, rfl⟩
          rw [hSw] at hz
          simp only [Finset.mem_insert, Finset.mem_union] at hz
          rcases hz with rfl | hz | hz
          · exact False.elim (hne rfl)
          · by_cases hzu : z = u
            · rw [hzu]; exact ⟨w - raw, hkw, by dsimp [gate]; rw [huv]; simp⟩
            · obtain ⟨j, hj, hzj⟩ := ih u hu_lt z hz hzu
              exact ⟨j, hSGu hj, hzj⟩
          · by_cases hzv : z = v
            · rw [hzv]; exact ⟨w - raw, hkw, by dsimp [gate]; rw [huv]; simp⟩
            · obtain ⟨j, hj, hzj⟩ := ih v hv_lt z hz hzv
              exact ⟨j, hSGv hj, hzj⟩
      · rw [hS_not_mem hw] at hz; simp at hz
  have hRootNotChild : ∀ k ∈ region, root ∉ (gate k).inputs := by
    intro k hk hmem
    have h1 : 1 ≤ readsIn C region root := by
      have hc : 1 ≤ (gate k).inputs.count root := List.count_pos_iff.mpr hmem
      exact hc.trans (readsIn_ge_count C region hk root)
    dsimp only [localReads] at hrootRead
    omega
  have hread1_of_in : ∀ k ∈ region, ∀ u ∈ (gate k).inputs, readsIn C region u = 1 := by
    intro k hk u hu
    rcases (hgates k hk).2.2 u hu with huw | hue
    · have hne : u ≠ root := fun heq => hRootNotChild k hk (heq ▸ hu)
      exact (hpriv u huw hne).1
    · exact (hentrySpec u hue).2.2
  have hchildren_ne : ∀ {k u v : ℕ}, k ∈ region → (gate k).inputs = [u, v] → u ≠ v := by
    intro k u v hk huv heq
    rw [heq] at huv
    have h1 := hread1_of_in k hk v (by rw [huv]; simp)
    have h2 : 2 ≤ readsIn C region v := by
      have hc : (gate k).inputs.count v = 2 := by rw [huv]; simp
      have := readsIn_ge_count C region hk v
      dsimp only [gate] at hc
      omega
    omega
  have hchildren_disj : ∀ {k u v : ℕ}, k ∈ region → (gate k).inputs = [u, v] →
      Disjoint (S u) (S v) := by
    intro k u v hk huv
    rw [Finset.disjoint_left]
    intro z0 hzu0 hzv0
    let I := S u ∩ S v
    have hIne : I.Nonempty := ⟨z0, Finset.mem_inter.mpr ⟨hzu0, hzv0⟩⟩
    let z := I.max' hIne
    have hzI : z ∈ I := Finset.max'_mem I hIne
    obtain ⟨hzu, hzv⟩ := Finset.mem_inter.mp hzI
    have hne_uv : u ≠ v := hchildren_ne hk huv
    have hks : k < C.gates.length := Finset.mem_range.mp (hreg hk)
    have hu_lt : u < raw + k := hrb k hks u (by rw [huv]; simp)
    have hv_lt : v < raw + k := hrb k hks v (by rw [huv]; simp)
    have hzu_ne : z ≠ u := by
      intro heq
      rw [heq] at hzv
      obtain ⟨k', hk', huk'⟩ := hS_parent v u hzv hne_uv
      have hk'_lt : raw + k' ≤ v := by
        obtain ⟨y, hy, hyk⟩ := Finset.mem_image.mp hk'
        obtain ⟨hyS, hyge⟩ := Finset.mem_filter.mp hy
        have hyle := hS_le v y hyS
        omega
      have hkne : k' ≠ k := by omega
      have h2 := readsIn_ge_two_of_two C region (hSG_sub v hk') hk hkne u huk' (by rw [huv]; simp)
      have h1 := hread1_of_in k hk u (by rw [huv]; simp)
      omega
    have hzv_ne : z ≠ v := by
      intro heq
      rw [heq] at hzu
      obtain ⟨k', hk', hvk'⟩ := hS_parent u v hzu hne_uv.symm
      have hk'_lt : raw + k' ≤ u := by
        obtain ⟨y, hy, hyk⟩ := Finset.mem_image.mp hk'
        obtain ⟨hyS, hyge⟩ := Finset.mem_filter.mp hy
        have hyle := hS_le u y hyS
        omega
      have hkne : k' ≠ k := by omega
      have h2 := readsIn_ge_two_of_two C region (hSG_sub u hk') hk hkne v hvk' (by rw [huv]; simp)
      have h1 := hread1_of_in k hk v (by rw [huv]; simp)
      omega
    obtain ⟨k1, hk1, hzk1⟩ := hS_parent u z hzu hzu_ne
    obtain ⟨k2, hk2, hzk2⟩ := hS_parent v z hzv hzv_ne
    have hk12 : k1 = k2 := by
      by_contra hkne
      have h2 := readsIn_ge_two_of_two C region (hSG_sub u hk1) (hSG_sub v hk2) hkne z hzk1 hzk2
      have h1 := hread1_of_in k1 (hSG_sub u hk1) z hzk1
      omega
    rw [← hk12] at hk2
    have hmem1 : raw + k1 ∈ S u := by
      obtain ⟨y, hy, hyk⟩ := Finset.mem_image.mp hk1
      obtain ⟨hyS, hyge⟩ := Finset.mem_filter.mp hy
      have : raw + k1 = y := by omega
      rwa [this]
    have hmem2 : raw + k1 ∈ S v := by
      obtain ⟨y, hy, hyk⟩ := Finset.mem_image.mp hk2
      obtain ⟨hyS, hyge⟩ := Finset.mem_filter.mp hy
      have : raw + k1 = y := by omega
      rwa [this]
    have hle_max : raw + k1 ≤ z := Finset.le_max' I (raw + k1) (Finset.mem_inter.mpr ⟨hmem1, hmem2⟩)
    have hlt_z : z < raw + k1 := hrb k1 (Finset.mem_range.mp (hreg (hSG_sub u hk1))) z hzk1
    omega
  have hSRootEq : S root = wires := by
    apply Finset.Subset.antisymm (hS_sub root)
    have hsub_sub : ∀ x y, y ∈ S x → S y ⊆ S x := by
      intro x
      induction x using Nat.strongRecOn with
      | ind x ihx =>
        intro y hy
        by_cases hx : x ∈ wires
        · rcases hwires_split x hx with ⟨hxlt, _⟩ | ⟨hxge, hxk⟩
          · rw [hS_source hx hxlt] at hy
            simp only [Finset.mem_singleton] at hy; rw [hy]
          · obtain ⟨_, hlen, _⟩ := hgates (x - raw) hxk
            obtain ⟨u, v, huv⟩ := gate_children hlen
            have hxeq : raw + (x - raw) = x := by omega
            have hSx : S x = insert x (S u ∪ S v) := by
              have := hS_gate hxk (by rwa [hxeq]) huv
              simpa [hxeq] using this
            rw [hSx] at hy
            have hxks : x - raw < C.gates.length := Finset.mem_range.mp (hreg hxk)
            have hu_lt : u < x := by have := hrb (x - raw) hxks u (by rw [huv]; simp); omega
            have hv_lt : v < x := by have := hrb (x - raw) hxks v (by rw [huv]; simp); omega
            simp only [Finset.mem_insert, Finset.mem_union] at hy
            rcases hy with rfl | hy | hy
            · exact Finset.Subset.refl _
            · exact (ihx u hu_lt y hy).trans (fun t ht => by rw [hSx]; simp [ht])
            · exact (ihx v hv_lt y hy).trans (fun t ht => by rw [hSx]; simp [ht])
        · rw [hS_not_mem hx] at hy; simp at hy
    have hclimb : ∀ d w, w ∈ wires → wires.sum id - w ≤ d → w ∈ S root := by
      intro d
      induction d with
      | zero =>
        intro w hw hd
        by_cases hwr : w = root
        · rw [hwr]; exact hS_self root hrootMem
        · have h1 : readsIn C region w = 1 := (hpriv w hw hwr).1
          obtain ⟨k, hk, hwk⟩ := exists_reader_of_readsIn_pos C region w (by omega)
          have hkw : raw + k ∈ wires := Finset.mem_union_right _ (Finset.mem_image.mpr ⟨k, hk, rfl⟩)
          have hlt : w < raw + k := hrb k (Finset.mem_range.mp (hreg hk)) w hwk
          have hle_sum : raw + k ≤ wires.sum id := Finset.single_le_sum (f := id) (fun _ _ => Nat.zero_le _) hkw
          omega
      | succ d ih =>
        intro w hw hd
        by_cases hwr : w = root
        · rw [hwr]; exact hS_self root hrootMem
        · have h1 : readsIn C region w = 1 := (hpriv w hw hwr).1
          obtain ⟨k, hk, hwk⟩ := exists_reader_of_readsIn_pos C region w (by omega)
          have hkw : raw + k ∈ wires := Finset.mem_union_right _ (Finset.mem_image.mpr ⟨k, hk, rfl⟩)
          have hlt : w < raw + k := hrb k (Finset.mem_range.mp (hreg hk)) w hwk
          have hle_sum : raw + k ≤ wires.sum id := Finset.single_le_sum (f := id) (fun _ _ => Nat.zero_le _) hkw
          have hpar_in : raw + k ∈ S root := ih (raw + k) hkw (by omega)
          obtain ⟨_, hlen, _⟩ := hgates k hk
          obtain ⟨u, v, huv⟩ := gate_children hlen
          have hSk : S (raw + k) = insert (raw + k) (S u ∪ S v) := hS_gate hk hkw huv
          have hw_in_Sk : w ∈ S (raw + k) := by
            rw [huv] at hwk
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hwk
            rw [hSk]
            rcases hwk with rfl | rfl
            · simp [hS_self w hw]
            · simp [hS_self w hw]
          exact hsub_sub root (raw + k) hpar_in hw_in_Sk
    intro w hw
    exact hclimb (wires.sum id) w hw (by omega)
  have hSLRoot : SL root = sources := by
    ext z
    simp only [SL, hSRootEq, Finset.mem_filter]
    constructor
    · rintro ⟨hz, hlt⟩
      rcases hwires_split z hz with ⟨_, hs⟩ | ⟨hge, _⟩
      · exact hs
      · omega
    · intro hs
      exact ⟨Finset.mem_union_left _ hs, hsrc_lt z hs⟩
  have hSL_gate : ∀ {k u v : ℕ}, k ∈ region → (gate k).inputs = [u, v] →
      SL (raw + k) = SL u ∪ SL v ∧ Disjoint (SL u) (SL v) := by
    intro k u v hk huv
    have hkw : raw + k ∈ wires := Finset.mem_union_right _ (Finset.mem_image.mpr ⟨k, hk, rfl⟩)
    have hSk : S (raw + k) = insert (raw + k) (S u ∪ S v) := hS_gate hk hkw huv
    constructor
    · ext z
      simp only [SL, hSk, Finset.mem_filter, Finset.mem_insert, Finset.mem_union]
      constructor
      · rintro ⟨rfl | h | h, hlt⟩
        · omega
        · exact Or.inl ⟨h, hlt⟩
        · exact Or.inr ⟨h, hlt⟩
      · rintro (⟨h, hlt⟩ | ⟨h, hlt⟩)
        · exact ⟨Or.inr (Or.inl h), hlt⟩
        · exact ⟨Or.inr (Or.inr h), hlt⟩
    · have hd := hchildren_disj hk huv
      exact Finset.disjoint_left.mpr fun z h1 h2 =>
        Finset.disjoint_left.mp hd (Finset.mem_filter.mp h1).1 (Finset.mem_filter.mp h2).1
  let hasE (w : ℕ) : Prop := ∃ k ∈ SG w, e0 ∈ (gate k).inputs
  have hhasE_lt : ∀ w, hasE w → e0 < w := by
    intro w ⟨k, hk, hek⟩
    have hlt : e0 < raw + k := hrb k (Finset.mem_range.mp (hreg (hSG_sub w hk))) e0 hek
    obtain ⟨y, hy, hyk⟩ := Finset.mem_image.mp hk
    obtain ⟨hyS, hyge⟩ := Finset.mem_filter.mp hy
    have hyle := hS_le w y hyS
    omega
  have hhasE_gate : ∀ {k u v : ℕ}, k ∈ region → (gate k).inputs = [u, v] →
      (hasE (raw + k) ↔ u = e0 ∨ v = e0 ∨ hasE u ∨ hasE v) := by
    intro k u v hk huv
    have hkw : raw + k ∈ wires := Finset.mem_union_right _ (Finset.mem_image.mpr ⟨k, hk, rfl⟩)
    have hSk : S (raw + k) = insert (raw + k) (S u ∪ S v) := hS_gate hk hkw huv
    have hSGk : SG (raw + k) = insert k (SG u ∪ SG v) := by
      ext j
      simp only [SG, hSk, Finset.mem_image, Finset.mem_filter, Finset.mem_insert, Finset.mem_union]
      constructor
      · rintro ⟨z, ⟨hz | hz | hz, hzge⟩, rfl⟩
        · left; omega
        · right; left; exact ⟨z, ⟨hz, hzge⟩, rfl⟩
        · right; right; exact ⟨z, ⟨hz, hzge⟩, rfl⟩
      · rintro (rfl | ⟨z, ⟨hz, hzge⟩, rfl⟩ | ⟨z, ⟨hz, hzge⟩, rfl⟩)
        · exact ⟨raw + j, ⟨Or.inl rfl, by omega⟩, by simp⟩
        · exact ⟨z, ⟨Or.inr (Or.inl hz), hzge⟩, rfl⟩
        · exact ⟨z, ⟨Or.inr (Or.inr hz), hzge⟩, rfl⟩
    constructor
    · rintro ⟨j, hj, hej⟩
      rw [hSGk] at hj
      simp only [Finset.mem_insert, Finset.mem_union] at hj
      rcases hj with hjk | hj | hj
      · rw [hjk] at hej; dsimp [gate] at hej; rw [huv] at hej
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hej
        rcases hej with h | h
        · exact Or.inl h.symm
        · exact Or.inr (Or.inl h.symm)
      · exact Or.inr (Or.inr (Or.inl ⟨j, hj, hej⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨j, hj, hej⟩))
    · rintro (hue | hve | ⟨j, hj, hej⟩ | ⟨j, hj, hej⟩)
      · exact ⟨k, by rw [hSGk]; simp, by dsimp [gate]; rw [huv, hue]; simp⟩
      · exact ⟨k, by rw [hSGk]; simp, by dsimp [gate]; rw [huv, hve]; simp⟩
      · exact ⟨j, by rw [hSGk]; simp [hj], hej⟩
      · exact ⟨j, by rw [hSGk]; simp [hj], hej⟩
  have hhasE_disj : ∀ {k u v : ℕ}, k ∈ region → (gate k).inputs = [u, v] →
      ¬ ((u = e0 ∨ hasE u) ∧ (v = e0 ∨ hasE v)) := by
    intro k u v hk huv ⟨hu, hv⟩
    have hks : k < C.gates.length := Finset.mem_range.mp (hreg hk)
    have hu_lt : u < raw + k := hrb k hks u (by rw [huv]; simp)
    have hv_lt : v < raw + k := hrb k hks v (by rw [huv]; simp)
    have hdisjG : Disjoint (SG u) (SG v) := by
      rw [Finset.disjoint_left]
      intro j hj1 hj2
      obtain ⟨y1, hy1, hy1e⟩ := Finset.mem_image.mp hj1
      obtain ⟨y1S, hy1ge⟩ := Finset.mem_filter.mp hy1
      obtain ⟨y2, hy2, hy2e⟩ := Finset.mem_image.mp hj2
      obtain ⟨y2S, hy2ge⟩ := Finset.mem_filter.mp hy2
      have hy12 : y1 = y2 := by omega
      rw [hy12] at y1S
      exact Finset.disjoint_left.mp (hchildren_disj hk huv) y1S y2S
    rcases hu with hue | ⟨k1, hk1, he1⟩
    · have he0_read : readsIn C region e0 = 1 := hread1_of_in k hk e0 (by rw [huv, hue]; simp)
      rcases hv with hve | ⟨k2, hk2, he2⟩
      · exact hchildren_ne hk huv (hue.trans hve.symm)
      · have hk2_lt : raw + k2 ≤ v := by
          obtain ⟨y, hy, hyk⟩ := Finset.mem_image.mp hk2
          obtain ⟨hyS, hyge⟩ := Finset.mem_filter.mp hy
          have := hS_le v y hyS; omega
        have hne : k ≠ k2 := by omega
        have h2 := readsIn_ge_two_of_two C region hk (hSG_sub v hk2) hne e0 (by rw [huv, hue]; simp) he2
        omega
    · have he0_read : readsIn C region e0 = 1 := hread1_of_in k1 (hSG_sub u hk1) e0 he1
      rcases hv with hve | ⟨k2, hk2, he2⟩
      · have hk1_lt : raw + k1 ≤ u := by
          obtain ⟨y, hy, hyk⟩ := Finset.mem_image.mp hk1
          obtain ⟨hyS, hyge⟩ := Finset.mem_filter.mp hy
          have := hS_le u y hyS; omega
        have hne : k1 ≠ k := by omega
        have h2 := readsIn_ge_two_of_two C region (hSG_sub u hk1) hk hne e0 he1 (by rw [huv, hve]; simp)
        omega
      · have hne : k1 ≠ k2 := fun heq => Finset.disjoint_left.mp hdisjG hk1 (heq ▸ hk2)
        have h2 := readsIn_ge_two_of_two C region (hSG_sub u hk1) (hSG_sub v hk2) hne e0 he1 he2
        omega
  let validW (w : ℕ) : Prop := w ∈ wires ∨ w = e0
  have heval_exact : ∀ (inp : List Bool), inp.length = raw → ∀ w ∈ wires,
      evalSub raw C region e0 hrb hreg inp (wireVal C inp e0) w = wireVal C inp w := by
    intro inp hinp w
    induction w using Nat.strongRecOn with
    | ind w ih =>
      intro hw
      have hw_ne : w ≠ e0 := fun heq => he0_not_mem (heq ▸ hw)
      rcases hwires_split w hw with ⟨hlt, _⟩ | ⟨hge, hk⟩
      · rw [evalSub_source raw C region e0 hrb hreg inp _ hw_ne hlt,
          wireVal_input C inp (by omega)]
      · obtain ⟨_, hlen, _⟩ := hgates (w - raw) hk
        obtain ⟨u, v, huv⟩ := gate_children hlen
        have hweq : raw + (w - raw) = w := by omega
        have hks : w - raw < C.gates.length := Finset.mem_range.mp (hreg hk)
        have hu_lt : u < w := by have := hrb (w - raw) hks u (by rw [huv]; simp); omega
        have hv_lt : v < w := by have := hrb (w - raw) hks v (by rw [huv]; simp); omega
        have hEv := evalSub_gate raw C region e0 hrb hreg inp (wireVal C inp e0) hk
          (by rwa [hweq]) huv
        rw [hweq] at hEv
        rw [hEv]
        have hWg := wireVal_gate C inp hinp hks (hrb (w - raw) hks)
        rw [hweq] at hWg
        rw [hWg]
        have hu_eq : evalSub raw C region e0 hrb hreg inp (wireVal C inp e0) u = wireVal C inp u := by
          rcases hgates_e0 (w - raw) hk u (by rw [huv]; simp) with huw | rfl
          · exact ih u hu_lt huw
          · exact evalSub_entry ..
        have hv_eq : evalSub raw C region e0 hrb hreg inp (wireVal C inp e0) v = wireVal C inp v := by
          rcases hgates_e0 (w - raw) hk v (by rw [huv]; simp) with hvw | rfl
          · exact ih v hv_lt hvw
          · exact evalSub_entry ..
        rw [hu_eq, hv_eq, huv]
        rfl
  have heval_mono : ∀ (inp : List Bool) (w : ℕ), w ∈ wires →
      evalSub raw C region e0 hrb hreg inp false w = true →
      evalSub raw C region e0 hrb hreg inp true w = true := by
    intro inp w
    induction w using Nat.strongRecOn with
    | ind w ih =>
      intro hw ht
      have hw_ne : w ≠ e0 := fun heq => he0_not_mem (heq ▸ hw)
      rcases hwires_split w hw with ⟨hlt, _⟩ | ⟨hge, hk⟩
      · rw [evalSub_source raw C region e0 hrb hreg inp _ hw_ne hlt] at ht ⊢
        exact ht
      · obtain ⟨hop, hlen, _⟩ := hgates (w - raw) hk
        obtain ⟨u, v, huv⟩ := gate_children hlen
        have hweq : raw + (w - raw) = w := by omega
        have hks : w - raw < C.gates.length := Finset.mem_range.mp (hreg hk)
        have hu_lt : u < w := by have := hrb (w - raw) hks u (by rw [huv]; simp); omega
        have hv_lt : v < w := by have := hrb (w - raw) hks v (by rw [huv]; simp); omega
        have hEvF := evalSub_gate raw C region e0 hrb hreg inp false hk (by rwa [hweq]) huv
        have hEvT := evalSub_gate raw C region e0 hrb hreg inp true hk (by rwa [hweq]) huv
        rw [hweq] at hEvF hEvT
        rw [hEvF] at ht; rw [hEvT]
        have hu_m : evalSub raw C region e0 hrb hreg inp false u = true →
            evalSub raw C region e0 hrb hreg inp true u = true := by
          rcases hgates_e0 (w - raw) hk u (by rw [huv]; simp) with huw | rfl
          · exact ih u hu_lt huw
          · simp [evalSub_entry]
        have hv_m : evalSub raw C region e0 hrb hreg inp false v = true →
            evalSub raw C region e0 hrb hreg inp true v = true := by
          rcases hgates_e0 (w - raw) hk v (by rw [huv]; simp) with hvw | rfl
          · exact ih v hv_lt hvw
          · simp [evalSub_entry]
        rcases hop with hand | hor
        · simp [gate] at hand
          rw [hand] at ht ⊢
          simp only [GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true, Bool.and_eq_true] at ht ⊢
          exact ⟨hu_m ht.1, hv_m ht.2⟩
        · simp [gate] at hor
          rw [hor] at ht ⊢
          simp only [GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false, Bool.or_eq_true] at ht ⊢
          rcases ht with h | h
          · exact Or.inl (hu_m h)
          · exact Or.inr (hv_m h)
  have heval_mono_inp : ∀ (inp1 inp2 : List Bool) (e : Bool) (w : ℕ), validW w →
      (∀ z ∈ SL w, inp1.getD z false = true → inp2.getD z false = true) →
      evalSub raw C region e0 hrb hreg inp1 e w = true →
      evalSub raw C region e0 hrb hreg inp2 e w = true := by
    intro inp1 inp2 e w
    induction w using Nat.strongRecOn with
    | ind w ih =>
      intro hvw hleaf ht
      rcases hvw with hw | rfl
      · have hw_ne : w ≠ e0 := fun heq => he0_not_mem (heq ▸ hw)
        rcases hwires_split w hw with ⟨hlt, _⟩ | ⟨hge, hk⟩
        · rw [evalSub_source raw C region e0 hrb hreg inp1 _ hw_ne hlt] at ht
          rw [evalSub_source raw C region e0 hrb hreg inp2 _ hw_ne hlt]
          exact hleaf w (Finset.mem_filter.mpr ⟨hS_self w hw, hlt⟩) ht
        · obtain ⟨hop, hlen, _⟩ := hgates (w - raw) hk
          obtain ⟨u, v, huv⟩ := gate_children hlen
          have hweq : raw + (w - raw) = w := by omega
          have hks : w - raw < C.gates.length := Finset.mem_range.mp (hreg hk)
          have hu_lt : u < w := by have := hrb (w - raw) hks u (by rw [huv]; simp); omega
          have hv_lt : v < w := by have := hrb (w - raw) hks v (by rw [huv]; simp); omega
          have hEv1 := evalSub_gate raw C region e0 hrb hreg inp1 e hk (by rwa [hweq]) huv
          have hEv2 := evalSub_gate raw C region e0 hrb hreg inp2 e hk (by rwa [hweq]) huv
          rw [hweq] at hEv1 hEv2
          rw [hEv1] at ht; rw [hEv2]
          have hSL := (hSL_gate hk huv).1; rw [hweq] at hSL
          have hu_m := ih u hu_lt (hgates_e0 (w - raw) hk u (by rw [huv]; simp))
            (fun z hz => hleaf z (by rw [hSL]; simp [hz]))
          have hv_m := ih v hv_lt (hgates_e0 (w - raw) hk v (by rw [huv]; simp))
            (fun z hz => hleaf z (by rw [hSL]; simp [hz]))
          rcases hop with hand | hor
          · simp [gate] at hand
            rw [hand] at ht ⊢
            simp only [GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true, Bool.and_eq_true] at ht ⊢
            exact ⟨hu_m ht.1, hv_m ht.2⟩
          · simp [gate] at hor
            rw [hor] at ht ⊢
            simp only [GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false, Bool.or_eq_true] at ht ⊢
            rcases ht with h | h
            · exact Or.inl (hu_m h)
            · exact Or.inr (hv_m h)
      · rw [evalSub_entry] at ht ⊢; exact ht
  have heval_local : ∀ (inp1 inp2 : List Bool) (e1 e2 : Bool) (w : ℕ), validW w →
      (∀ z ∈ SL w, inp1.getD z false = inp2.getD z false) →
      (w = e0 ∨ hasE w → e1 = e2) →
      evalSub raw C region e0 hrb hreg inp1 e1 w = evalSub raw C region e0 hrb hreg inp2 e2 w := by
    intro inp1 inp2 e1 e2 w
    induction w using Nat.strongRecOn with
    | ind w ih =>
      intro hvw hleaf he
      rcases hvw with hw | rfl
      · have hw_ne : w ≠ e0 := fun heq => he0_not_mem (heq ▸ hw)
        rcases hwires_split w hw with ⟨hlt, _⟩ | ⟨hge, hk⟩
        · rw [evalSub_source raw C region e0 hrb hreg inp1 _ hw_ne hlt,
            evalSub_source raw C region e0 hrb hreg inp2 _ hw_ne hlt]
          exact hleaf w (Finset.mem_filter.mpr ⟨hS_self w hw, hlt⟩)
        · obtain ⟨_, hlen, _⟩ := hgates (w - raw) hk
          obtain ⟨u, v, huv⟩ := gate_children hlen
          have hweq : raw + (w - raw) = w := by omega
          have hks : w - raw < C.gates.length := Finset.mem_range.mp (hreg hk)
          have hu_lt : u < w := by have := hrb (w - raw) hks u (by rw [huv]; simp); omega
          have hv_lt : v < w := by have := hrb (w - raw) hks v (by rw [huv]; simp); omega
          have hEv1 := evalSub_gate raw C region e0 hrb hreg inp1 e1 hk (by rwa [hweq]) huv
          have hEv2 := evalSub_gate raw C region e0 hrb hreg inp2 e2 hk (by rwa [hweq]) huv
          rw [hweq] at hEv1 hEv2; rw [hEv1, hEv2]
          have hSL := (hSL_gate hk huv).1; rw [hweq] at hSL
          have hHE := hhasE_gate hk huv; rw [hweq] at hHE
          have hu_eq : evalSub raw C region e0 hrb hreg inp1 e1 u =
              evalSub raw C region e0 hrb hreg inp2 e2 u :=
            ih u hu_lt (hgates_e0 (w - raw) hk u (by rw [huv]; simp))
              (fun z hz => hleaf z (by rw [hSL]; simp [hz]))
              (fun h => by
                rcases h with rfl | h
                · exact he (Or.inr (hHE.mpr (Or.inl rfl)))
                · exact he (Or.inr (hHE.mpr (Or.inr (Or.inr (Or.inl h))))))
          have hv_eq : evalSub raw C region e0 hrb hreg inp1 e1 v =
              evalSub raw C region e0 hrb hreg inp2 e2 v :=
            ih v hv_lt (hgates_e0 (w - raw) hk v (by rw [huv]; simp))
              (fun z hz => hleaf z (by rw [hSL]; simp [hz]))
              (fun h => by
                rcases h with rfl | h
                · exact he (Or.inr (hHE.mpr (Or.inr (Or.inl rfl))))
                · exact he (Or.inr (hHE.mpr (Or.inr (Or.inr (Or.inr h))))))
          rw [hu_eq, hv_eq]
      · rw [evalSub_entry, evalSub_entry]; exact he (Or.inl rfl)
  have hBeforeRoot : ∀ (inp1 inp2 : List Bool), inp1.length = raw → inp2.length = raw →
      (∀ z < raw, z ∉ sources → inp1.getD z false = inp2.getD z false) →
      ∀ w < root, w ∉ wires → wireVal C inp1 w = wireVal C inp2 w := by
    intro inp1 inp2 hinp1 hinp2 hout w
    induction w using Nat.strongRecOn with
    | ind w ih =>
      intro hwr hwnw
      by_cases hw_lt : w < raw
      · rw [wireVal_input C inp1 (by omega), wireVal_input C inp2 (by omega)]
        exact hout w hw_lt (fun h => hwnw (Finset.mem_union_left _ h))
      · by_cases hjs : w - raw < C.gates.length
        · have hweq : raw + (w - raw) = w := by omega
          have hg1 := wireVal_gate C inp1 hinp1 hjs (hrb (w - raw) hjs)
          have hg2 := wireVal_gate C inp2 hinp2 hjs (hrb (w - raw) hjs)
          rw [hweq] at hg1 hg2
          rw [hg1, hg2]
          have harg : ∀ u ∈ (gateAt C (w - raw)).inputs,
              (C.wires inp1).getD u false = (C.wires inp2).getD u false := by
            intro u hu
            have hu_lt : u < w := by have := hrb (w - raw) hjs u hu; omega
            have hunw : u ∉ wires := by
              intro huw
              have hur : u ≠ root := by omega
              have huS : u ∈ S root := by rwa [hSRootEq]
              obtain ⟨k', hk', huk'⟩ := hS_parent root u huS hur
              have hne_j : w - raw ≠ k' := by
                intro heq; subst heq
                obtain ⟨y, hy, hyk⟩ := Finset.mem_image.mp hk'
                obtain ⟨hyS, hyge⟩ := Finset.mem_filter.mp hy
                have : y = w := by omega
                subst this
                exact hwnw (hS_sub root hyS)
              have h2 := readsIn_ge_two_of_two C (Finset.range C.size)
                (Finset.mem_range.mpr hjs) (hreg (hSG_sub root hk')) hne_j u hu huk'
              have h1 : readsIn C (Finset.range C.size) u = 1 := (hpriv u huw hur).2.1
              omega
            exact ih u hu_lt (by omega) hunw
          congr 1
          apply List.map_congr_left
          exact harg
        · rw [wireVal_oob C inp1 (by omega), wireVal_oob C inp2 (by omega)]
  have hRootMonoEval : ∀ (inp1 inp2 : List Bool), inp1.length = raw → inp2.length = raw →
      (∀ z < raw, z ∉ sources → inp1.getD z false = inp2.getD z false) →
      (wireVal C inp1 root = true → wireVal C inp2 root = true) →
      C.eval inp1 = true → C.eval inp2 = true := by
    intro inp1 inp2 hinp1 hinp2 hout hrootImp
    have hall : ∀ w, (w = root ∨ w ∉ wires) → wireVal C inp1 w = true → wireVal C inp2 w = true := by
      intro w
      induction w using Nat.strongRecOn with
      | ind w ih =>
        intro hcond ht
        rcases hcond with rfl | hwnw
        · exact hrootImp ht
        · by_cases hw_lt : w < raw
          · rw [wireVal_input C inp1 (by omega)] at ht
            rw [wireVal_input C inp2 (by omega), ← hout w hw_lt (fun h => hwnw (Finset.mem_union_left _ h))]
            exact ht
          · by_cases hjs : w - raw < C.gates.length
            · have hweq : raw + (w - raw) = w := by omega
              have hg1 := wireVal_gate C inp1 hinp1 hjs (hrb (w - raw) hjs)
              have hg2 := wireVal_gate C inp2 hinp2 hjs (hrb (w - raw) hjs)
              rw [hweq] at hg1 hg2
              rw [hg1] at ht; rw [hg2]
              refine gateOp_eval_mono (hgate_mono_op (w - raw) hjs) ?_ ht
              intro u hu
              have hu_lt : u < w := by have := hrb (w - raw) hjs u hu; omega
              have huc : u = root ∨ u ∉ wires := by
                by_cases hur : u = root
                · exact Or.inl hur
                · right; intro huw
                  have huS : u ∈ S root := by rwa [hSRootEq]
                  obtain ⟨k', hk', huk'⟩ := hS_parent root u huS hur
                  have hne_j : w - raw ≠ k' := by
                    intro heq; subst heq
                    obtain ⟨y, hy, hyk⟩ := Finset.mem_image.mp hk'
                    obtain ⟨hyS, hyge⟩ := Finset.mem_filter.mp hy
                    have : y = w := by omega
                    subst this
                    exact hwnw (hS_sub root hyS)
                  have h2 := readsIn_ge_two_of_two C (Finset.range C.size)
                    (Finset.mem_range.mpr hjs) (hreg (hSG_sub root hk')) hne_j u hu huk'
                  have h1 : readsIn C (Finset.range C.size) u = 1 := (hpriv u huw hur).2.1
                  omega
              exact ih u hu_lt huc
            · rw [wireVal_oob C inp1 (by omega)] at ht
              exact False.elim (Bool.noConfusion ht)
    have hout_c : C.output = root ∨ C.output ∉ wires := by
      by_cases hor : C.output = root
      · exact Or.inl hor
      · right; intro how
        exact (hpriv C.output how hor).2.2 rfl
    exact hall C.output hout_c
  have honeEach_get : ∀ (r0 : Fin n) (c0 : Fin m) (z : ℕ), z < raw →
      (oneEach r0 c0).getD z false = decide (z = r0.val ∨ z = n + c0.val) := by
    intro r0 c0 z hz
    unfold oneEach
    rw [List.getD_eq_getElem _ _ (by simp; omega)]
    by_cases hzn : z < n
    · rw [List.getElem_append_left (by simp; omega), List.getElem_ofFn]
      have : z ≠ n + c0.val := by omega
      simp [Fin.ext_iff, this, eq_comm]
    · rw [List.getElem_append_right (by simp; omega), List.getElem_ofFn]
      have : z ≠ r0.val := by omega
      simp [Fin.ext_iff, this]
      constructor <;> intro h <;> omega
  let oneRow (a : Fin n) : List Bool := List.ofFn (fun i : Fin raw => decide (i.val = a.val))
  let oneCol (x : Fin m) : List Bool := List.ofFn (fun i : Fin raw => decide (i.val = n + x.val))
  let allFalse : List Bool := List.replicate raw false
  have honeRow_get : ∀ (a : Fin n) (z : ℕ), z < raw → (oneRow a).getD z false = decide (z = a.val) := by
    intro a z hz
    dsimp [oneRow]
    rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_ofFn]
  have honeCol_get : ∀ (x : Fin m) (z : ℕ), z < raw → (oneCol x).getD z false = decide (z = n + x.val) := by
    intro x z hz
    dsimp [oneCol]
    rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_ofFn]
  have hallFalse_get : ∀ (z : ℕ), allFalse.getD z false = false := by
    intro z
    dsimp [allFalse]
    by_cases hz : z < raw
    · rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_replicate]
    · rw [List.getD_eq_default _ _ (by simp; omega)]
  have honeRow_false : ∀ a : Fin n, C.eval (oneRow a) = false := by
    intro a
    obtain ⟨c, hc⟩ := hzeroR a
    cases h : C.eval (oneRow a)
    · rfl
    · have ht := hcircuit_mono (oneRow a) (oneEach a c) (by simp [oneRow]) (by simp [oneEach, raw])
        (fun z hz h1 => by
          rw [honeRow_get a z hz] at h1
          rw [honeEach_get a c z hz]
          simp only [decide_eq_true_eq] at h1 ⊢
          exact Or.inl h1) C.output h
      have hG : G a c = true := by rw [← hrep a c]; exact ht
      rw [hc] at hG; exact Bool.noConfusion hG
  have honeCol_false : ∀ x : Fin m, C.eval (oneCol x) = false := by
    intro x
    obtain ⟨a, ha⟩ := hzeroC x
    cases h : C.eval (oneCol x)
    · rfl
    · have ht := hcircuit_mono (oneCol x) (oneEach a x) (by simp [oneCol]) (by simp [oneEach, raw])
        (fun z hz h1 => by
          rw [honeCol_get x z hz] at h1
          rw [honeEach_get a x z hz]
          simp only [decide_eq_true_eq] at h1 ⊢
          exact Or.inr h1) C.output h
      have hG : G a x = true := by rw [← hrep a x]; exact ht
      rw [ha] at hG; exact Bool.noConfusion hG
  have hmono_total : ∀ (f g : Bool → Bool),
      (f false = true → f true = true) → (g false = true → g true = true) →
      (∀ e, f e = true → g e = true) ∨ (∀ e, g e = true → f e = true) := by
    intro f g hf hg
    cases hf0 : f false <;> cases hf1 : f true <;> cases hg0 : g false <;> cases hg1 : g true
    · left; intro e; cases e <;> simp [hf0, hf1]
    · left; intro e; cases e <;> simp [hf0, hf1]
    · exact False.elim (Bool.noConfusion (hg1.symm.trans (hg hg0)))
    · left; intro e; cases e <;> simp [hf0, hf1]
    · right; intro e; cases e <;> simp [hg0, hg1]
    · left; intro e; cases e <;> simp [hf0, hf1, hg0, hg1]
    · exact False.elim (Bool.noConfusion (hg1.symm.trans (hg hg0)))
    · left; intro e; cases e <;> simp [hg0, hg1]
    · exact False.elim (Bool.noConfusion (hf1.symm.trans (hf hf0)))
    · exact False.elim (Bool.noConfusion (hf1.symm.trans (hf hf0)))
    · exact False.elim (Bool.noConfusion (hf1.symm.trans (hf hf0)))
    · exact False.elim (Bool.noConfusion (hf1.symm.trans (hf hf0)))
    · right; intro e; cases e <;> simp [hg0, hg1]
    · right; intro e; cases e <;> simp [hf0, hf1]
    · exact False.elim (Bool.noConfusion (hg1.symm.trans (hg hg0)))
    · left; intro e; cases e <;> simp [hg0, hg1]
  have hrow_imp_ext : ∀ a ∈ R, ∀ b ∈ R,
      (∀ e : Bool, evalSub raw C region e0 hrb hreg (oneRow a) e root = true →
        evalSub raw C region e0 hrb hreg (oneRow b) e root = true) →
      extR b ⊆ extR a := by
    intro a ha b hb himp j hj
    obtain ⟨hjB, hGbf⟩ := Finset.mem_filter.mp hj
    have hjnotB : j ∉ B := (Finset.mem_sdiff.mp hjB).2
    refine Finset.mem_filter.mpr ⟨hjB, ?_⟩
    cases hGa : G a j
    · rfl
    · have hGb : G b j = true := by
        rw [← hrep b j]
        apply hRootMonoEval (oneEach a j) (oneEach b j) (by simp [oneEach, raw]) (by simp [oneEach, raw])
        · intro z hz hznS
          rw [honeEach_get a j z hz, honeEach_get b j z hz]
          have hza : z ≠ a.val := fun heq => hznS (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a, ha, heq.symm⟩))
          have hzb : z ≠ b.val := fun heq => hznS (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨b, hb, heq.symm⟩))
          simp [hza, hzb]
        · intro ht
          rw [← heval_exact (oneEach a j) (by simp [oneEach, raw]) root hrootMem] at ht
          rw [← heval_exact (oneEach b j) (by simp [oneEach, raw]) root hrootMem]
          have hj_not_src : n + j.val ∉ sources := by
            simp only [sources, Finset.mem_union, Finset.mem_image, not_or]
            constructor
            · rintro ⟨a', _, h⟩; omega
            · rintro ⟨j', hj', h⟩; exact hjnotB (by have : j' = j := Fin.ext (by omega); rwa [← this])
          have h1 := heval_local (oneEach a j) (oneRow a) (wireVal C (oneEach a j) e0)
            (wireVal C (oneEach a j) e0) root (Or.inl hrootMem)
            (fun z hz => by
              rw [hSLRoot] at hz
              have hzlt : z < raw := hsrc_lt z hz
              rw [honeEach_get a j z hzlt, honeRow_get a z hzlt]
              have hzj : z ≠ n + j.val := fun heq => hj_not_src (heq ▸ hz)
              simp [hzj]) (fun _ => rfl)
          have h2 := heval_local (oneEach b j) (oneRow b) (wireVal C (oneEach b j) e0)
            (wireVal C (oneEach b j) e0) root (Or.inl hrootMem)
            (fun z hz => by
              rw [hSLRoot] at hz
              have hzlt : z < raw := hsrc_lt z hz
              rw [honeEach_get b j z hzlt, honeRow_get b z hzlt]
              have hzj : z ≠ n + j.val := fun heq => hj_not_src (heq ▸ hz)
              simp [hzj]) (fun _ => rfl)
          rw [h1] at ht; rw [h2]
          by_cases hhe : hasE root
          · have he_eq : wireVal C (oneEach a j) e0 = wireVal C (oneEach b j) e0 :=
              hBeforeRoot (oneEach a j) (oneEach b j) (by simp [oneEach, raw]) (by simp [oneEach, raw])
                (fun z hz hznS => by
                  rw [honeEach_get a j z hz, honeEach_get b j z hz]
                  have hza : z ≠ a.val := fun heq => hznS (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a, ha, heq.symm⟩))
                  have hzb : z ≠ b.val := fun heq => hznS (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨b, hb, heq.symm⟩))
                  simp [hza, hzb]) e0 (hhasE_lt root hhe) he0_not_mem
            rw [← he_eq]
            exact himp _ ht
          · have ha' := heval_local (oneRow a) (oneRow a) (wireVal C (oneEach a j) e0) false root (Or.inl hrootMem)
              (fun _ _ => rfl) (fun h => by rcases h with rfl | h; exact False.elim (he0_not_mem hrootMem); exact False.elim (hhe h))
            have hb' := heval_local (oneRow b) (oneRow b) (wireVal C (oneEach b j) e0) false root (Or.inl hrootMem)
              (fun _ _ => rfl) (fun h => by rcases h with rfl | h; exact False.elim (he0_not_mem hrootMem); exact False.elim (hhe h))
            rw [ha'] at ht; rw [hb']
            exact himp false ht
        · rw [hrep a j]; exact hGa
      rw [hGbf] at hGb; exact Bool.noConfusion hGb
  have hcol_imp_ext : ∀ x ∈ B, ∀ y ∈ B,
      (∀ e : Bool, evalSub raw C region e0 hrb hreg (oneCol x) e root = true →
        evalSub raw C region e0 hrb hreg (oneCol y) e root = true) →
      extC y ⊆ extC x := by
    intro x hx y hy himp i hi
    obtain ⟨hiR, hGiyf⟩ := Finset.mem_filter.mp hi
    have hinotR : i ∉ R := (Finset.mem_sdiff.mp hiR).2
    refine Finset.mem_filter.mpr ⟨hiR, ?_⟩
    cases hGx : G i x
    · rfl
    · have hGy : G i y = true := by
        rw [← hrep i y]
        apply hRootMonoEval (oneEach i x) (oneEach i y) (by simp [oneEach, raw]) (by simp [oneEach, raw])
        · intro z hz hznS
          rw [honeEach_get i x z hz, honeEach_get i y z hz]
          have hzx : z ≠ n + x.val := fun heq => hznS (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨x, hx, heq.symm⟩))
          have hzy : z ≠ n + y.val := fun heq => hznS (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨y, hy, heq.symm⟩))
          simp [hzx, hzy]
        · intro ht
          rw [← heval_exact (oneEach i x) (by simp [oneEach, raw]) root hrootMem] at ht
          rw [← heval_exact (oneEach i y) (by simp [oneEach, raw]) root hrootMem]
          have hi_not_src : i.val ∉ sources := by
            simp only [sources, Finset.mem_union, Finset.mem_image, not_or]
            constructor
            · rintro ⟨a', ha', h⟩; exact hinotR (by have : a' = i := Fin.ext h; rwa [← this])
            · rintro ⟨j', _, h⟩; omega
          have h1 := heval_local (oneEach i x) (oneCol x) (wireVal C (oneEach i x) e0)
            (wireVal C (oneEach i x) e0) root (Or.inl hrootMem)
            (fun z hz => by
              rw [hSLRoot] at hz
              have hzlt : z < raw := hsrc_lt z hz
              rw [honeEach_get i x z hzlt, honeCol_get x z hzlt]
              have hzi : z ≠ i.val := fun heq => hi_not_src (heq ▸ hz)
              simp [hzi]) (fun _ => rfl)
          have h2 := heval_local (oneEach i y) (oneCol y) (wireVal C (oneEach i y) e0)
            (wireVal C (oneEach i y) e0) root (Or.inl hrootMem)
            (fun z hz => by
              rw [hSLRoot] at hz
              have hzlt : z < raw := hsrc_lt z hz
              rw [honeEach_get i y z hzlt, honeCol_get y z hzlt]
              have hzi : z ≠ i.val := fun heq => hi_not_src (heq ▸ hz)
              simp [hzi]) (fun _ => rfl)
          rw [h1] at ht; rw [h2]
          by_cases hhe : hasE root
          · have he_eq : wireVal C (oneEach i x) e0 = wireVal C (oneEach i y) e0 :=
              hBeforeRoot (oneEach i x) (oneEach i y) (by simp [oneEach, raw]) (by simp [oneEach, raw])
                (fun z hz hznS => by
                  rw [honeEach_get i x z hz, honeEach_get i y z hz]
                  have hzx : z ≠ n + x.val := fun heq => hznS (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨x, hx, heq.symm⟩))
                  have hzy : z ≠ n + y.val := fun heq => hznS (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨y, hy, heq.symm⟩))
                  simp [hzx, hzy]) e0 (hhasE_lt root hhe) he0_not_mem
            rw [← he_eq]
            exact himp _ ht
          · have hx' := heval_local (oneCol x) (oneCol x) (wireVal C (oneEach i x) e0) false root (Or.inl hrootMem)
              (fun _ _ => rfl) (fun h => by rcases h with rfl | h; exact False.elim (he0_not_mem hrootMem); exact False.elim (hhe h))
            have hy' := heval_local (oneCol y) (oneCol y) (wireVal C (oneEach i y) e0) false root (Or.inl hrootMem)
              (fun _ _ => rfl) (fun h => by rcases h with rfl | h; exact False.elim (he0_not_mem hrootMem); exact False.elim (hhe h))
            rw [hx'] at ht; rw [hy']
            exact himp false ht
        · rw [hrep i x]; exact hGx
      rw [hGiyf] at hGy; exact Bool.noConfusion hGy
  have hconc1 : ∀ a ∈ R, ∀ b ∈ R, extR a ⊆ extR b ∨ extR b ⊆ extR a := by
    intro a ha b hb
    rcases hmono_total
      (fun e => evalSub raw C region e0 hrb hreg (oneRow a) e root)
      (fun e => evalSub raw C region e0 hrb hreg (oneRow b) e root)
      (heval_mono (oneRow a) root hrootMem)
      (heval_mono (oneRow b) root hrootMem) with h | h
    · exact Or.inr (hrow_imp_ext a ha b hb h)
    · exact Or.inl (hrow_imp_ext b hb a ha h)
  have hconc2 : ∀ x ∈ B, ∀ y ∈ B, extC x ⊆ extC y ∨ extC y ⊆ extC x := by
    intro x hx y hy
    rcases hmono_total
      (fun e => evalSub raw C region e0 hrb hreg (oneCol x) e root)
      (fun e => evalSub raw C region e0 hrb hreg (oneCol y) e root)
      (heval_mono (oneCol x) root hrootMem)
      (heval_mono (oneCol y) root hrootMem) with h | h
    · exact Or.inr (hcol_imp_ext x hx y hy h)
    · exact Or.inl (hcol_imp_ext y hy x hx h)
  let eConst : Bool := wireVal C allFalse e0
  let E (w : ℕ) (a : Fin n) (x : Fin m) : Bool := evalSub raw C region e0 hrb hreg (oneEach a x) eConst w
  let Er (w : ℕ) (a : Fin n) : Bool := evalSub raw C region e0 hrb hreg (oneRow a) eConst w
  let Ec (w : ℕ) (x : Fin m) : Bool := evalSub raw C region e0 hrb hreg (oneCol x) eConst w
  let E0 (w : ℕ) : Bool := evalSub raw C region e0 hrb hreg allFalse eConst w
  let P (w : ℕ) (a : Fin n) (x : Fin m) : Prop := E w a x = true ∧ Er w a = false ∧ Ec w x = false
  have hinside_out : ∀ a ∈ R, ∀ x ∈ B, ∀ z < raw, z ∉ sources →
      (oneEach a x).getD z false = allFalse.getD z false := by
    intro a ha x hx z hz hznS
    rw [honeEach_get a x z hz, hallFalse_get z]
    have hza : z ≠ a.val := fun heq => hznS (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a, ha, heq.symm⟩))
    have hzx : z ≠ n + x.val := fun heq => hznS (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨x, hx, heq.symm⟩))
    simp [hza, hzx]
  have hrow_out_false : ∀ a ∈ R, ∀ z < raw, z ∉ sources →
      (oneRow a).getD z false = allFalse.getD z false := by
    intro a ha z hz hznS
    rw [honeRow_get a z hz, hallFalse_get z]
    have hza : z ≠ a.val := fun heq => hznS (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a, ha, heq.symm⟩))
    simp [hza]
  have hcol_out_false : ∀ x ∈ B, ∀ z < raw, z ∉ sources →
      (oneCol x).getD z false = allFalse.getD z false := by
    intro x hx z hz hznS
    rw [honeCol_get x z hz, hallFalse_get z]
    have hzx : z ≠ n + x.val := fun heq => hznS (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨x, hx, heq.symm⟩))
    simp [hzx]
  have hERootEq : ∀ a ∈ R, ∀ x ∈ B, E root a x = wireVal C (oneEach a x) root := by
    intro a ha x hx
    rw [← heval_exact (oneEach a x) (by simp [oneEach, raw]) root hrootMem]
    dsimp [E]
    by_cases hhe : hasE root
    · have he_eq : wireVal C (oneEach a x) e0 = eConst :=
        hBeforeRoot (oneEach a x) allFalse (by simp [oneEach, raw]) (by simp [allFalse])
          (hinside_out a ha x hx) e0 (hhasE_lt root hhe) he0_not_mem
      rw [he_eq]
    · exact heval_local (oneEach a x) (oneEach a x) eConst (wireVal C (oneEach a x) e0) root
        (Or.inl hrootMem) (fun _ _ => rfl)
        (fun h => by rcases h with rfl | h; exact False.elim (he0_not_mem hrootMem); exact False.elim (hhe h))
  have hErRootEq : ∀ a ∈ R, Er root a = wireVal C (oneRow a) root := by
    intro a ha
    rw [← heval_exact (oneRow a) (by simp [oneRow]) root hrootMem]
    dsimp [Er]
    by_cases hhe : hasE root
    · have he_eq : wireVal C (oneRow a) e0 = eConst :=
        hBeforeRoot (oneRow a) allFalse (by simp [oneRow]) (by simp [allFalse])
          (hrow_out_false a ha) e0 (hhasE_lt root hhe) he0_not_mem
      rw [he_eq]
    · exact heval_local (oneRow a) (oneRow a) eConst (wireVal C (oneRow a) e0) root
        (Or.inl hrootMem) (fun _ _ => rfl)
        (fun h => by rcases h with rfl | h; exact False.elim (he0_not_mem hrootMem); exact False.elim (hhe h))
  have hEcRootEq : ∀ x ∈ B, Ec root x = wireVal C (oneCol x) root := by
    intro x hx
    rw [← heval_exact (oneCol x) (by simp [oneCol]) root hrootMem]
    dsimp [Ec]
    by_cases hhe : hasE root
    · have he_eq : wireVal C (oneCol x) e0 = eConst :=
        hBeforeRoot (oneCol x) allFalse (by simp [oneCol]) (by simp [allFalse])
          (hcol_out_false x hx) e0 (hhasE_lt root hhe) he0_not_mem
      rw [he_eq]
    · exact heval_local (oneCol x) (oneCol x) eConst (wireVal C (oneCol x) e0) root
        (Or.inl hrootMem) (fun _ _ => rfl)
        (fun h => by rcases h with rfl | h; exact False.elim (he0_not_mem hrootMem); exact False.elim (hhe h))
  have hE0_imp_Er : ∀ w, validW w → ∀ a, E0 w = true → Er w a = true := by
    intro w hvw a ht
    exact heval_mono_inp allFalse (oneRow a) eConst w hvw
      (fun z _ h => by rw [hallFalse_get] at h; exact False.elim (Bool.noConfusion h)) ht
  have hE0_imp_Ec : ∀ w, validW w → ∀ x, E0 w = true → Ec w x = true := by
    intro w hvw x ht
    exact heval_mono_inp allFalse (oneCol x) eConst w hvw
      (fun z _ h => by rw [hallFalse_get] at h; exact False.elim (Bool.noConfusion h)) ht
  have hEr_imp_E : ∀ w, validW w → ∀ a x, Er w a = true → E w a x = true := by
    intro w hvw a x ht
    exact heval_mono_inp (oneRow a) (oneEach a x) eConst w hvw
      (fun z hz h => by
        have hzlt : z < raw := (Finset.mem_filter.mp hz).2
        rw [honeRow_get a z hzlt] at h
        rw [honeEach_get a x z hzlt]
        simp only [decide_eq_true_eq] at h ⊢
        exact Or.inl h) ht
  have hEc_imp_E : ∀ w, validW w → ∀ a x, Ec w x = true → E w a x = true := by
    intro w hvw a x ht
    exact heval_mono_inp (oneCol x) (oneEach a x) eConst w hvw
      (fun z hz h => by
        have hzlt : z < raw := (Finset.mem_filter.mp hz).2
        rw [honeCol_get x z hzlt] at h
        rw [honeEach_get a x z hzlt]
        simp only [decide_eq_true_eq] at h ⊢
        exact Or.inr h) ht
  have hE0_imp_E : ∀ w, validW w → ∀ a x, E0 w = true → E w a x = true :=
    fun w hvw a x ht => hEr_imp_E w hvw a x (hE0_imp_Er w hvw a ht)
  have hE_eq_Ec : ∀ w, validW w → ∀ a x, a.val ∉ SL w → E w a x = Ec w x := by
    intro w hvw a x ha
    exact heval_local (oneEach a x) (oneCol x) eConst eConst w hvw
      (fun z hz => by
        have hzlt : z < raw := (Finset.mem_filter.mp hz).2
        rw [honeEach_get a x z hzlt, honeCol_get x z hzlt]
        have hza : z ≠ a.val := fun heq => ha (heq ▸ hz)
        simp [hza]) (fun _ => rfl)
  have hE_eq_Er : ∀ w, validW w → ∀ a x, n + x.val ∉ SL w → E w a x = Er w a := by
    intro w hvw a x hx
    exact heval_local (oneEach a x) (oneRow a) eConst eConst w hvw
      (fun z hz => by
        have hzlt : z < raw := (Finset.mem_filter.mp hz).2
        rw [honeEach_get a x z hzlt, honeRow_get a z hzlt]
        have hzx : z ≠ n + x.val := fun heq => hx (heq ▸ hz)
        simp [hzx]) (fun _ => rfl)
  have hEr_eq_E0 : ∀ w, validW w → ∀ a, a.val ∉ SL w → Er w a = E0 w := by
    intro w hvw a ha
    exact heval_local (oneRow a) allFalse eConst eConst w hvw
      (fun z hz => by
        have hzlt : z < raw := (Finset.mem_filter.mp hz).2
        rw [honeRow_get a z hzlt, hallFalse_get z]
        have hza : z ≠ a.val := fun heq => ha (heq ▸ hz)
        simp [hza]) (fun _ => rfl)
  have hEc_eq_E0 : ∀ w, validW w → ∀ x, n + x.val ∉ SL w → Ec w x = E0 w := by
    intro w hvw x hx
    exact heval_local (oneCol x) allFalse eConst eConst w hvw
      (fun z hz => by
        have hzlt : z < raw := (Finset.mem_filter.mp hz).2
        rw [honeCol_get x z hzlt, hallFalse_get z]
        have hzx : z ≠ n + x.val := fun heq => hx (heq ▸ hz)
        simp [hzx]) (fun _ => rfl)
  have hP_mem : ∀ w, validW w → ∀ a x, P w a x → a.val ∈ SL w ∧ n + x.val ∈ SL w := by
    intro w hvw a x ⟨hE, hEr, hEc⟩
    constructor
    · by_contra ha
      rw [hE_eq_Ec w hvw a x ha, hEc] at hE
      exact Bool.noConfusion hE
    · by_contra hx
      rw [hE_eq_Er w hvw a x hx, hEr] at hE
      exact Bool.noConfusion hE
  have hP_rect : ∀ w, validW w → ∀ a b x y, P w a x → P w b x → P w b y → P w a y := by
    intro w
    induction w using Nat.strongRecOn with
    | ind w ih =>
      intro hvw a b x y hax hbx hby
      rcases hvw with hw | rfl
      · have hw_ne : w ≠ e0 := fun heq => he0_not_mem (heq ▸ hw)
        rcases hwires_split w hw with ⟨hlt, _⟩ | ⟨hge, hk⟩
        · have h1 := hax.1
          dsimp [E] at h1
          rw [evalSub_source raw C region e0 hrb hreg (oneEach a x) eConst hw_ne hlt,
            honeEach_get a x w hlt] at h1
          simp only [decide_eq_true_eq] at h1
          rcases h1 with hwa | hwx
          · have h2 := hax.2.1
            dsimp [Er] at h2
            rw [evalSub_source raw C region e0 hrb hreg (oneRow a) eConst hw_ne hlt,
              honeRow_get a w hlt, hwa] at h2
            simp at h2
          · have h2 := hax.2.2
            dsimp [Ec] at h2
            rw [evalSub_source raw C region e0 hrb hreg (oneCol x) eConst hw_ne hlt,
              honeCol_get x w hlt, hwx] at h2
            simp at h2
        · obtain ⟨hop, hlen, _⟩ := hgates (w - raw) hk
          obtain ⟨u, v, huv⟩ := gate_children hlen
          have hweq : raw + (w - raw) = w := by omega
          have hks : w - raw < C.gates.length := Finset.mem_range.mp (hreg hk)
          have hu_lt : u < w := by have := hrb (w - raw) hks u (by rw [huv]; simp); omega
          have hv_lt : v < w := by have := hrb (w - raw) hks v (by rw [huv]; simp); omega
          have hvu : validW u := hgates_e0 (w - raw) hk u (by rw [huv]; simp)
          have hvv : validW v := hgates_e0 (w - raw) hk v (by rw [huv]; simp)
          have hdisjSL : Disjoint (SL u) (SL v) := (hSL_gate hk huv).2
          have hgate_ev : ∀ inp, evalSub raw C region e0 hrb hreg inp eConst w =
              (gateAt C (w - raw)).op.eval [evalSub raw C region e0 hrb hreg inp eConst u,
                evalSub raw C region e0 hrb hreg inp eConst v] := by
            intro inp
            have h := evalSub_gate raw C region e0 hrb hreg inp eConst hk (by rwa [hweq]) huv
            rwa [hweq] at h
          rcases hop with hand | hor
          · simp [gate] at hand
            have hEw : ∀ p q, E w p q = (E u p q && E v p q) := fun p q => by
              dsimp [E]; rw [hgate_ev, hand]; simp [GateOp.eval]
            have hErw : ∀ p, Er w p = (Er u p && Er v p) := fun p => by
              dsimp [Er]; rw [hgate_ev, hand]; simp [GateOp.eval]
            have hEcw : ∀ q, Ec w q = (Ec u q && Ec v q) := fun q => by
              dsimp [Ec]; rw [hgate_ev, hand]; simp [GateOp.eval]
            refine ⟨?_, hax.2.1, hby.2.2⟩
            rw [hEw]
            cases h0u : E0 u with
            | true =>
              have huE : ∀ p q, E u p q = true := fun p q => hE0_imp_E u hvu p q h0u
              have huEr : ∀ p, Er u p = true := fun p => hE0_imp_Er u hvu p h0u
              have huEc : ∀ q, Ec u q = true := fun q => hE0_imp_Ec u hvu q h0u
              have hPv : ∀ p q, P w p q → P v p q := fun p q hpq => by
                refine ⟨?_, ?_, ?_⟩
                · have h := hpq.1; rw [hEw, huE] at h; simpa using h
                · have h := hpq.2.1; rw [hErw, huEr] at h; simpa using h
                · have h := hpq.2.2; rw [hEcw, huEc] at h; simpa using h
              have hvay := ih v hv_lt hvv a b x y (hPv a x hax) (hPv b x hbx) (hPv b y hby)
              simp [huE, hvay.1]
            | false =>
              cases h0v : E0 v with
              | true =>
                have hvE : ∀ p q, E v p q = true := fun p q => hE0_imp_E v hvv p q h0v
                have hvEr : ∀ p, Er v p = true := fun p => hE0_imp_Er v hvv p h0v
                have hvEc : ∀ q, Ec v q = true := fun q => hE0_imp_Ec v hvv q h0v
                have hPu : ∀ p q, P w p q → P u p q := fun p q hpq => by
                  refine ⟨?_, ?_, ?_⟩
                  · have h := hpq.1; rw [hEw, hvE] at h; simpa using h
                  · have h := hpq.2.1; rw [hErw, hvEr] at h; simpa using h
                  · have h := hpq.2.2; rw [hEcw, hvEc] at h; simpa using h
                have huay := ih u hu_lt hvu a b x y (hPu a x hax) (hPu b x hbx) (hPu b y hby)
                simp [huay.1, hvE]
              | false =>
                have hcross : ∀ p q, E w p q = true →
                    (p.val ∈ SL u ∧ n + q.val ∈ SL v ∧ Er u p = true ∧ Ec v q = true) ∨
                    (p.val ∈ SL v ∧ n + q.val ∈ SL u ∧ Er v p = true ∧ Ec u q = true) := by
                  intro p q hEwpq
                  rw [hEw, Bool.and_eq_true] at hEwpq
                  obtain ⟨hEu, hEv⟩ := hEwpq
                  have hu_or : p.val ∈ SL u ∨ n + q.val ∈ SL u := by
                    by_contra hno
                    push Not at hno
                    rw [hE_eq_Ec u hvu p q hno.1, hEc_eq_E0 u hvu q hno.2, h0u] at hEu
                    exact Bool.noConfusion hEu
                  have hv_or : p.val ∈ SL v ∨ n + q.val ∈ SL v := by
                    by_contra hno
                    push Not at hno
                    rw [hE_eq_Ec v hvv p q hno.1, hEc_eq_E0 v hvv q hno.2, h0v] at hEv
                    exact Bool.noConfusion hEv
                  rcases hu_or with hpu | hqu
                  · rcases hv_or with hpv | hqv
                    · exact False.elim (Finset.disjoint_left.mp hdisjSL hpu hpv)
                    · left
                      have hqn : n + q.val ∉ SL u := fun h => Finset.disjoint_left.mp hdisjSL h hqv
                      have hpn : p.val ∉ SL v := fun h => Finset.disjoint_left.mp hdisjSL hpu h
                      exact ⟨hpu, hqv, by rw [← hE_eq_Er u hvu p q hqn]; exact hEu,
                        by rw [← hE_eq_Ec v hvv p q hpn]; exact hEv⟩
                  · rcases hv_or with hpv | hqv
                    · right
                      have hpn : p.val ∉ SL u := fun h => Finset.disjoint_left.mp hdisjSL h hpv
                      have hqn : n + q.val ∉ SL v := fun h => Finset.disjoint_left.mp hdisjSL hqu h
                      exact ⟨hpv, hqu, by rw [← hE_eq_Er v hvv p q hqn]; exact hEv,
                        by rw [← hE_eq_Ec u hvu p q hpn]; exact hEu⟩
                    · exact False.elim (Finset.disjoint_left.mp hdisjSL hqu hqv)
                rcases hcross a x hax.1 with ⟨hau, hxv, hEra, _⟩ | ⟨hav, hxu, hEra, _⟩
                · rcases hcross b x hbx.1 with ⟨hbu, _, _, _⟩ | ⟨_, hxu, _, _⟩
                  · rcases hcross b y hby.1 with ⟨_, _, _, hEcy⟩ | ⟨hbv, _, _, _⟩
                    · simp [hEr_imp_E u hvu a y hEra, hEc_imp_E v hvv a y hEcy]
                    · exact False.elim (Finset.disjoint_left.mp hdisjSL hbu hbv)
                  · exact False.elim (Finset.disjoint_left.mp hdisjSL hxu hxv)
                · rcases hcross b x hbx.1 with ⟨_, hxv, _, _⟩ | ⟨hbv, _, _, _⟩
                  · exact False.elim (Finset.disjoint_left.mp hdisjSL hxu hxv)
                  · rcases hcross b y hby.1 with ⟨hbu, _, _, _⟩ | ⟨_, _, _, hEcy⟩
                    · exact False.elim (Finset.disjoint_left.mp hdisjSL hbu hbv)
                    · simp [hEc_imp_E u hvu a y hEcy, hEr_imp_E v hvv a y hEra]
          · simp [gate] at hor
            have hEw : ∀ p q, E w p q = (E u p q || E v p q) := fun p q => by
              dsimp [E]; rw [hgate_ev, hor]; simp [GateOp.eval]
            have hErw : ∀ p, Er w p = (Er u p || Er v p) := fun p => by
              dsimp [Er]; rw [hgate_ev, hor]; simp [GateOp.eval]
            have hEcw : ∀ q, Ec w q = (Ec u q || Ec v q) := fun q => by
              dsimp [Ec]; rw [hgate_ev, hor]; simp [GateOp.eval]
            have hPor : ∀ p q, P w p q → P u p q ∨ P v p q := fun p q ⟨h1, h2, h3⟩ => by
              rw [hEw, Bool.or_eq_true] at h1
              rw [hErw, Bool.or_eq_false_iff] at h2
              rw [hEcw, Bool.or_eq_false_iff] at h3
              rcases h1 with h1 | h1
              · exact Or.inl ⟨h1, h2.1, h3.1⟩
              · exact Or.inr ⟨h1, h2.2, h3.2⟩
            refine ⟨?_, hax.2.1, hby.2.2⟩
            rw [hEw, Bool.or_eq_true]
            rcases hPor a x hax with haxu | haxv
            · have hxu : n + x.val ∈ SL u := (hP_mem u hvu a x haxu).2
              have hbxu : P u b x := by
                rcases hPor b x hbx with h | h
                · exact h
                · exact False.elim (Finset.disjoint_left.mp hdisjSL hxu (hP_mem v hvv b x h).2)
              have hbu : b.val ∈ SL u := (hP_mem u hvu b x hbxu).1
              have hbyu : P u b y := by
                rcases hPor b y hby with h | h
                · exact h
                · exact False.elim (Finset.disjoint_left.mp hdisjSL hbu (hP_mem v hvv b y h).1)
              exact Or.inl (ih u hu_lt hvu a b x y haxu hbxu hbyu).1
            · have hxv : n + x.val ∈ SL v := (hP_mem v hvv a x haxv).2
              have hbxv : P v b x := by
                rcases hPor b x hbx with h | h
                · exact False.elim (Finset.disjoint_left.mp hdisjSL (hP_mem u hvu b x h).2 hxv)
                · exact h
              have hbv : b.val ∈ SL v := (hP_mem v hvv b x hbxv).1
              have hbyv : P v b y := by
                rcases hPor b y hby with h | h
                · exact False.elim (Finset.disjoint_left.mp hdisjSL (hP_mem u hvu b y h).1 hbv)
                · exact h
              exact Or.inr (ih v hv_lt hvv a b x y haxv hbxv hbyv).1
      · have h1 := hax.1
        have h2 := hax.2.1
        dsimp [E] at h1; dsimp [Er] at h2
        rw [evalSub_entry] at h1 h2
        rw [h1] at h2
        exact False.elim (Bool.noConfusion h2)
  have hpos_inside : ∀ a0 ∈ R, ∀ x0 ∈ B, G a0 x0 = true →
      E root a0 x0 = true ∧
      (∀ a ∈ R, Er root a = false) ∧
      (∀ x ∈ B, Ec root x = false) ∧
      E0 root = false ∧
      (∀ a ∈ R, ∀ x ∈ B, G a x = E root a x) := by
    intro a0 ha0 x0 hx0 hG0
    have hE0_true : E root a0 x0 = true := by
      cases h : E root a0 x0
      · have hC : C.eval (oneRow a0) = true := by
          apply hRootMonoEval (oneEach a0 x0) (oneRow a0) (by simp [oneEach, raw]) (by simp [oneRow])
          · intro z hz hznS
            rw [hinside_out a0 ha0 x0 hx0 z hz hznS, hrow_out_false a0 ha0 z hz hznS]
          · intro ht
            rw [← hERootEq a0 ha0 x0 hx0, h] at ht
            exact False.elim (Bool.noConfusion ht)
          · rw [hrep a0 x0]; exact hG0
        rw [honeRow_false a0] at hC; exact False.elim (Bool.noConfusion hC)
      · rfl
    have hEr_all : ∀ a ∈ R, Er root a = false := by
      intro a ha
      cases h : Er root a
      · rfl
      · have hC : C.eval (oneRow a) = true := by
          apply hRootMonoEval (oneEach a0 x0) (oneRow a) (by simp [oneEach, raw]) (by simp [oneRow])
          · intro z hz hznS
            rw [hinside_out a0 ha0 x0 hx0 z hz hznS, hrow_out_false a ha z hz hznS]
          · intro _
            rw [← hErRootEq a ha]; exact h
          · rw [hrep a0 x0]; exact hG0
        rw [honeRow_false a] at hC; exact False.elim (Bool.noConfusion hC)
    have hEc_all : ∀ x ∈ B, Ec root x = false := by
      intro x hx
      cases h : Ec root x
      · rfl
      · have hC : C.eval (oneCol x) = true := by
          apply hRootMonoEval (oneEach a0 x0) (oneCol x) (by simp [oneEach, raw]) (by simp [oneCol])
          · intro z hz hznS
            rw [hinside_out a0 ha0 x0 hx0 z hz hznS, hcol_out_false x hx z hz hznS]
          · intro _
            rw [← hEcRootEq x hx]; exact h
          · rw [hrep a0 x0]; exact hG0
        rw [honeCol_false x] at hC; exact False.elim (Bool.noConfusion hC)
    have hE0_f : E0 root = false := by
      cases h : E0 root
      · rfl
      · have ht := hE0_imp_Er root (Or.inl hrootMem) a0 h
        rw [hEr_all a0 ha0] at ht; exact False.elim (Bool.noConfusion ht)
    have hGeq : ∀ a ∈ R, ∀ x ∈ B, G a x = E root a x := by
      intro a ha x hx
      cases hE : E root a x
      · cases hG : G a x
        · rfl
        · have hC : C.eval (oneRow a) = true := by
            apply hRootMonoEval (oneEach a x) (oneRow a) (by simp [oneEach, raw]) (by simp [oneRow])
            · intro z hz hznS
              rw [hinside_out a ha x hx z hz hznS, hrow_out_false a ha z hz hznS]
            · intro ht
              rw [← hERootEq a ha x hx, hE] at ht
              exact False.elim (Bool.noConfusion ht)
            · rw [hrep a x]; exact hG
          rw [honeRow_false a] at hC; exact False.elim (Bool.noConfusion hC)
      · rw [← hrep a x]
        apply hRootMonoEval (oneEach a0 x0) (oneEach a x) (by simp [oneEach, raw]) (by simp [oneEach, raw])
        · intro z hz hznS
          rw [hinside_out a0 ha0 x0 hx0 z hz hznS, hinside_out a ha x hx z hz hznS]
        · intro _
          rw [← hERootEq a ha x hx]; exact hE
        · rw [hrep a0 x0]; exact hG0
    exact ⟨hE0_true, hEr_all, hEc_all, hE0_f, hGeq⟩
  have hconc3 : ∀ a ∈ R, ∀ b ∈ R, ∀ x ∈ B, ∀ y ∈ B,
      G a x = true → G b x = true → G b y = true → G a y = true := by
    intro a ha b hb x hx y hy hax hbx hby
    obtain ⟨_, hEr_all, hEc_all, _, hGeq⟩ := hpos_inside a ha x hx hax
    have hPax : P root a x := ⟨by rw [← hGeq a ha x hx]; exact hax, hEr_all a ha, hEc_all x hx⟩
    have hPbx : P root b x := ⟨by rw [← hGeq b hb x hx]; exact hbx, hEr_all b hb, hEc_all x hx⟩
    have hPby : P root b y := ⟨by rw [← hGeq b hb y hy]; exact hby, hEr_all b hb, hEc_all y hy⟩
    have hPay := hP_rect root (Or.inl hrootMem) a b x y hPax hPbx hPby
    rw [hGeq a ha y hy]; exact hPay.1
  have hconc4 : ∀ a ∈ R, ∀ x ∈ B, G a x = true →
      (∀ j ∉ B, G a j = false) ∨ (∀ i ∉ R, G i x = false) := by
    intro a ha x hx hGax
    by_contra hboth
    push Not at hboth
    obtain ⟨⟨j, hjB, hGaj_ne⟩, ⟨i, hiR, hGix_ne⟩⟩ := hboth
    have hGaj : G a j = true := by cases h : G a j; exact False.elim (hGaj_ne h); rfl
    have hGix : G i x = true := by cases h : G i x; exact False.elim (hGix_ne h); rfl
    obtain ⟨hEax, hEr_all, hEc_all, hE0_f, _⟩ := hpos_inside a ha x hx hGax
    let inp3 (ba bx : Bool) : List Bool :=
      List.ofFn (fun z : Fin raw => (ba && decide (z.val = a.val)) || (bx && decide (z.val = n + x.val)))
    have hinp3_get : ∀ ba bx z, z < raw →
        (inp3 ba bx).getD z false = ((ba && decide (z = a.val)) || (bx && decide (z = n + x.val))) := by
      intro ba bx z hz
      dsimp [inp3]
      rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_ofFn]
    let F (w : ℕ) (ba bx e : Bool) : Bool := evalSub raw C region e0 hrb hreg (inp3 ba bx) e w
    have hF_ff : ∀ e, F root false false e = evalSub raw C region e0 hrb hreg allFalse e root := fun e =>
      heval_local (inp3 false false) allFalse e e root (Or.inl hrootMem)
        (fun z hz => by
          have hzlt : z < raw := (Finset.mem_filter.mp hz).2
          rw [hinp3_get false false z hzlt, hallFalse_get z]; simp) (fun _ => rfl)
    have hF_tf : ∀ e, F root true false e = evalSub raw C region e0 hrb hreg (oneRow a) e root := fun e =>
      heval_local (inp3 true false) (oneRow a) e e root (Or.inl hrootMem)
        (fun z hz => by
          have hzlt : z < raw := (Finset.mem_filter.mp hz).2
          rw [hinp3_get true false z hzlt, honeRow_get a z hzlt]; simp) (fun _ => rfl)
    have hF_ft : ∀ e, F root false true e = evalSub raw C region e0 hrb hreg (oneCol x) e root := fun e =>
      heval_local (inp3 false true) (oneCol x) e e root (Or.inl hrootMem)
        (fun z hz => by
          have hzlt : z < raw := (Finset.mem_filter.mp hz).2
          rw [hinp3_get false true z hzlt, honeCol_get x z hzlt]; simp) (fun _ => rfl)
    have hF_tt : F root true true eConst = true := by
      have hloc := heval_local (inp3 true true) (oneEach a x) eConst eConst root (Or.inl hrootMem)
        (fun z hz => by
          have hzlt : z < raw := (Finset.mem_filter.mp hz).2
          rw [hinp3_get true true z hzlt, honeEach_get a x z hzlt]
          by_cases h1 : z = a.val <;> by_cases h2 : z = n + x.val <;> simp [h1, h2]) (fun _ => rfl)
      dsimp [F]; rw [hloc]; exact hEax
    have hF_tff_c : F root true false eConst = false := by rw [hF_tf]; exact hEr_all a ha
    have hF_ftf_c : F root false true eConst = false := by rw [hF_ft]; exact hEc_all x hx
    have hF_fff_c : F root false false eConst = false := by rw [hF_ff]; exact hE0_f
    have hj_not_src : n + j.val ∉ sources := by
      simp only [sources, Finset.mem_union, Finset.mem_image, not_or]
      constructor
      · rintro ⟨a', _, h⟩; omega
      · rintro ⟨j', hj', h⟩; exact hjB (by have : j' = j := Fin.ext (by omega); rwa [← this])
    have hi_not_src : i.val ∉ sources := by
      simp only [sources, Finset.mem_union, Finset.mem_image, not_or]
      constructor
      · rintro ⟨a', ha', h⟩; exact hiR (by have : a' = i := Fin.ext h; rwa [← this])
      · rintro ⟨j', _, h⟩; omega
    have hpair_j : ∃ ej : Bool, F root true false ej = true ∧ F root false false ej = false := by
      refine ⟨wireVal C (oneEach a j) e0, ?_, ?_⟩
      · have h1 : wireVal C (oneEach a j) root = F root true false (wireVal C (oneEach a j) e0) := by
          rw [← heval_exact (oneEach a j) (by simp [oneEach, raw]) root hrootMem, hF_tf]
          exact heval_local (oneEach a j) (oneRow a) _ _ root (Or.inl hrootMem)
            (fun z hz => by
              rw [hSLRoot] at hz
              have hzlt : z < raw := hsrc_lt z hz
              rw [honeEach_get a j z hzlt, honeRow_get a z hzlt]
              have hzj : z ≠ n + j.val := fun heq => hj_not_src (heq ▸ hz)
              simp [hzj]) (fun _ => rfl)
        cases hval : F root true false (wireVal C (oneEach a j) e0)
        · have hC : C.eval (oneCol j) = true := by
            apply hRootMonoEval (oneEach a j) (oneCol j) (by simp [oneEach, raw]) (by simp [oneCol])
            · intro z hz hznS
              rw [honeEach_get a j z hz, honeCol_get j z hz]
              have hza : z ≠ a.val := fun heq => hznS (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a, ha, heq.symm⟩))
              simp [hza]
            · intro ht; rw [h1, hval] at ht; exact False.elim (Bool.noConfusion ht)
            · rw [hrep a j]; exact hGaj
          rw [honeCol_false j] at hC; exact False.elim (Bool.noConfusion hC)
        · rfl
      · have h2 : wireVal C (oneCol j) root = F root false false (wireVal C (oneEach a j) e0) := by
          rw [← heval_exact (oneCol j) (by simp [oneCol]) root hrootMem, hF_ff]
          apply heval_local (oneCol j) allFalse _ _ root (Or.inl hrootMem)
          · intro z hz
            rw [hSLRoot] at hz
            have hzlt : z < raw := hsrc_lt z hz
            rw [honeCol_get j z hzlt, hallFalse_get z]
            have hzj : z ≠ n + j.val := fun heq => hj_not_src (heq ▸ hz)
            simp [hzj]
          · intro h
            rcases h with rfl | hhe
            · exact False.elim (he0_not_mem hrootMem)
            · exact hBeforeRoot (oneCol j) (oneEach a j) (by simp [oneCol]) (by simp [oneEach, raw])
                (fun z hz hznS => by
                  rw [honeCol_get j z hz, honeEach_get a j z hz]
                  have hza : z ≠ a.val := fun heq => hznS (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a, ha, heq.symm⟩))
                  simp [hza]) e0 (hhasE_lt root hhe) he0_not_mem
        cases hval : F root false false (wireVal C (oneEach a j) e0)
        · rfl
        · have hC : C.eval (oneCol j) = true := by
            apply hRootMonoEval (oneEach a j) (oneCol j) (by simp [oneEach, raw]) (by simp [oneCol])
            · intro z hz hznS
              rw [honeEach_get a j z hz, honeCol_get j z hz]
              have hza : z ≠ a.val := fun heq => hznS (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a, ha, heq.symm⟩))
              simp [hza]
            · intro _; rw [h2]; exact hval
            · rw [hrep a j]; exact hGaj
          rw [honeCol_false j] at hC; exact False.elim (Bool.noConfusion hC)
    have hpair_i : ∃ ei : Bool, F root false true ei = true ∧ F root false false ei = false := by
      refine ⟨wireVal C (oneEach i x) e0, ?_, ?_⟩
      · have h1 : wireVal C (oneEach i x) root = F root false true (wireVal C (oneEach i x) e0) := by
          rw [← heval_exact (oneEach i x) (by simp [oneEach, raw]) root hrootMem, hF_ft]
          exact heval_local (oneEach i x) (oneCol x) _ _ root (Or.inl hrootMem)
            (fun z hz => by
              rw [hSLRoot] at hz
              have hzlt : z < raw := hsrc_lt z hz
              rw [honeEach_get i x z hzlt, honeCol_get x z hzlt]
              have hzi : z ≠ i.val := fun heq => hi_not_src (heq ▸ hz)
              simp [hzi]) (fun _ => rfl)
        cases hval : F root false true (wireVal C (oneEach i x) e0)
        · have hC : C.eval (oneRow i) = true := by
            apply hRootMonoEval (oneEach i x) (oneRow i) (by simp [oneEach, raw]) (by simp [oneRow])
            · intro z hz hznS
              rw [honeEach_get i x z hz, honeRow_get i z hz]
              have hzx : z ≠ n + x.val := fun heq => hznS (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨x, hx, heq.symm⟩))
              simp [hzx]
            · intro ht; rw [h1, hval] at ht; exact False.elim (Bool.noConfusion ht)
            · rw [hrep i x]; exact hGix
          rw [honeRow_false i] at hC; exact False.elim (Bool.noConfusion hC)
        · rfl
      · have h2 : wireVal C (oneRow i) root = F root false false (wireVal C (oneEach i x) e0) := by
          rw [← heval_exact (oneRow i) (by simp [oneRow]) root hrootMem, hF_ff]
          apply heval_local (oneRow i) allFalse _ _ root (Or.inl hrootMem)
          · intro z hz
            rw [hSLRoot] at hz
            have hzlt : z < raw := hsrc_lt z hz
            rw [honeRow_get i z hzlt, hallFalse_get z]
            have hzi : z ≠ i.val := fun heq => hi_not_src (heq ▸ hz)
            simp [hzi]
          · intro h
            rcases h with rfl | hhe
            · exact False.elim (he0_not_mem hrootMem)
            · exact hBeforeRoot (oneRow i) (oneEach i x) (by simp [oneRow]) (by simp [oneEach, raw])
                (fun z hz hznS => by
                  rw [honeRow_get i z hz, honeEach_get i x z hz]
                  have hzx : z ≠ n + x.val := fun heq => hznS (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨x, hx, heq.symm⟩))
                  simp [hzx]) e0 (hhasE_lt root hhe) he0_not_mem
        cases hval : F root false false (wireVal C (oneEach i x) e0)
        · rfl
        · have hC : C.eval (oneRow i) = true := by
            apply hRootMonoEval (oneEach i x) (oneRow i) (by simp [oneEach, raw]) (by simp [oneRow])
            · intro z hz hznS
              rw [honeEach_get i x z hz, honeRow_get i z hz]
              have hzx : z ≠ n + x.val := fun heq => hznS (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨x, hx, heq.symm⟩))
              simp [hzx]
            · intro _; rw [h2]; exact hval
            · rw [hrep i x]; exact hGix
          rw [honeRow_false i] at hC; exact False.elim (Bool.noConfusion hC)
    obtain ⟨ej, hF_tft_j, hF_fft_j⟩ := hpair_j
    obtain ⟨ei, hF_ftt_i, hF_fft_i⟩ := hpair_i
    have heConst_false : eConst = false ∧ ej = true ∧ ei = true := by
      cases hc : eConst
      · cases hj : ej
        · rw [hc] at hF_tff_c; rw [hj] at hF_tft_j; rw [hF_tff_c] at hF_tft_j; exact False.elim (Bool.noConfusion hF_tft_j)
        · cases hi : ei
          · rw [hc] at hF_ftf_c; rw [hi] at hF_ftt_i; rw [hF_ftf_c] at hF_ftt_i; exact False.elim (Bool.noConfusion hF_ftt_i)
          · exact ⟨rfl, rfl, rfl⟩
      · cases hj : ej
        · rw [hj] at hF_tft_j
          have ht := heval_mono (inp3 true false) root hrootMem hF_tft_j
          rw [hc] at hF_tff_c
          dsimp [F] at hF_tff_c
          rw [hF_tff_c] at ht; exact False.elim (Bool.noConfusion ht)
        · rw [hc] at hF_tff_c; rw [hj] at hF_tft_j; rw [hF_tff_c] at hF_tft_j; exact False.elim (Bool.noConfusion hF_tft_j)
    obtain ⟨hcF, hjT, hiT⟩ := heConst_false
    rw [hcF] at hF_tt hF_tff_c hF_ftf_c hF_fff_c
    rw [hjT] at hF_tft_j hF_fft_j
    rw [hiT] at hF_ftt_i
    have hdepA : ∀ w, validW w → a.val ∉ SL w → ∀ bx e, F w false bx e = F w true bx e := by
      intro w hvw haN bx e
      exact heval_local (inp3 false bx) (inp3 true bx) e e w hvw
        (fun z hz => by
          have hzlt : z < raw := (Finset.mem_filter.mp hz).2
          rw [hinp3_get false bx z hzlt, hinp3_get true bx z hzlt]
          have hza : z ≠ a.val := fun heq => haN (heq ▸ hz)
          simp [hza]) (fun _ => rfl)
    have hdepX : ∀ w, validW w → n + x.val ∉ SL w → ∀ ba e, F w ba false e = F w ba true e := by
      intro w hvw hxN ba e
      exact heval_local (inp3 ba false) (inp3 ba true) e e w hvw
        (fun z hz => by
          have hzlt : z < raw := (Finset.mem_filter.mp hz).2
          rw [hinp3_get ba false z hzlt, hinp3_get ba true z hzlt]
          have hzx : z ≠ n + x.val := fun heq => hxN (heq ▸ hz)
          simp [hzx]) (fun _ => rfl)
    have hdepE : ∀ w, validW w → ¬ (w = e0 ∨ hasE w) → ∀ ba bx, F w ba bx false = F w ba bx true := by
      intro w hvw heN ba bx
      exact heval_local (inp3 ba bx) (inp3 ba bx) false true w hvw (fun _ _ => rfl) (fun h => False.elim (heN h))
    have hno_maj : ∀ w, validW w →
        ¬ (F w true true false = true ∧ F w true false true = true ∧ F w false true true = true ∧
           F w true false false = false ∧ F w false true false = false ∧ F w false false true = false) := by
      intro w
      induction w using Nat.strongRecOn with
      | ind w ih =>
        intro hvw ⟨h110, h101, h011, h100, h010, h001⟩
        rcases hvw with hw | rfl
        · have hw_ne : w ≠ e0 := fun heq => he0_not_mem (heq ▸ hw)
          rcases hwires_split w hw with ⟨hlt, _⟩ | ⟨hge, hk⟩
          · dsimp [F] at h110 h101 h011 h100 h010 h001
            rw [evalSub_source raw C region e0 hrb hreg _ _ hw_ne hlt, hinp3_get _ _ w hlt] at h110 h101 h011 h100 h010 h001
            by_cases hwa : w = a.val
            · simp [hwa] at h100
            · by_cases hwx : w = n + x.val
              · simp [hwx] at h010
              · simp [hwa, hwx] at h110
          · obtain ⟨hop, hlen, _⟩ := hgates (w - raw) hk
            obtain ⟨u, v, huv⟩ := gate_children hlen
            have hweq : raw + (w - raw) = w := by omega
            have hks : w - raw < C.gates.length := Finset.mem_range.mp (hreg hk)
            have hu_lt : u < w := by have := hrb (w - raw) hks u (by rw [huv]; simp); omega
            have hv_lt : v < w := by have := hrb (w - raw) hks v (by rw [huv]; simp); omega
            have hvu : validW u := hgates_e0 (w - raw) hk u (by rw [huv]; simp)
            have hvv : validW v := hgates_e0 (w - raw) hk v (by rw [huv]; simp)
            have hdisjSL : Disjoint (SL u) (SL v) := (hSL_gate hk huv).2
            have hdisjE : ¬ ((u = e0 ∨ hasE u) ∧ (v = e0 ∨ hasE v)) := hhasE_disj hk huv
            have hgate_ev : ∀ ba bx e, F w ba bx e =
                (gateAt C (w - raw)).op.eval [F u ba bx e, F v ba bx e] := by
              intro ba bx e
              dsimp [F]
              have h := evalSub_gate raw C region e0 hrb hreg (inp3 ba bx) e hk (by rwa [hweq]) huv
              rwa [hweq] at h
            rcases hop with hand | hor
            · simp [gate] at hand
              have hFand : ∀ ba bx e, F w ba bx e = (F u ba bx e && F v ba bx e) := fun ba bx e => by
                rw [hgate_ev, hand]; simp [GateOp.eval]
              rw [hFand, Bool.and_eq_true] at h110 h101 h011
              rw [hFand, Bool.and_eq_false_iff] at h100 h010 h001
              have hAX : ∀ z, validW z → F z true false true = true → F z false true true = true →
                  F z false false true = false → a.val ∈ SL z ∧ n + x.val ∈ SL z := by
                intro z hvz ht1 ht2 hf
                constructor
                · by_contra hN; rw [hdepA z hvz hN false true, ht1] at hf; exact Bool.noConfusion hf
                · by_contra hN; rw [hdepX z hvz hN false true, ht2] at hf; exact Bool.noConfusion hf
              have hAE : ∀ z, validW z → F z true true false = true → F z false true true = true →
                  F z false true false = false → a.val ∈ SL z ∧ (z = e0 ∨ hasE z) := by
                intro z hvz ht1 ht2 hf
                constructor
                · by_contra hN; rw [hdepA z hvz hN true false, ht1] at hf; exact Bool.noConfusion hf
                · by_contra hN; rw [hdepE z hvz hN false true, ht2] at hf; exact Bool.noConfusion hf
              have hXE : ∀ z, validW z → F z true true false = true → F z true false true = true →
                  F z true false false = false → n + x.val ∈ SL z ∧ (z = e0 ∨ hasE z) := by
                intro z hvz ht1 ht2 hf
                constructor
                · by_contra hN; rw [hdepX z hvz hN true false, ht1] at hf; exact Bool.noConfusion hf
                · by_contra hN; rw [hdepE z hvz hN true false, ht2] at hf; exact Bool.noConfusion hf
              rcases h100 with hu100 | hv100
              · obtain ⟨hXu, hEu⟩ := hXE u hvu h110.1 h101.1 hu100
                have hu010 : F u false true false = false := by
                  rcases h010 with h | h
                  · exact h
                  · exact False.elim (hdisjE ⟨hEu, (hAE v hvv h110.2 h011.2 h).2⟩)
                have hu001 : F u false false true = false := by
                  rcases h001 with h | h
                  · exact h
                  · exact False.elim (Finset.disjoint_left.mp hdisjSL hXu (hAX v hvv h101.2 h011.2 h).2)
                exact ih u hu_lt hvu ⟨h110.1, h101.1, h011.1, hu100, hu010, hu001⟩
              · obtain ⟨hXv, hEv⟩ := hXE v hvv h110.2 h101.2 hv100
                have hv010 : F v false true false = false := by
                  rcases h010 with h | h
                  · exact False.elim (hdisjE ⟨(hAE u hvu h110.1 h011.1 h).2, hEv⟩)
                  · exact h
                have hv001 : F v false false true = false := by
                  rcases h001 with h | h
                  · exact False.elim (Finset.disjoint_left.mp hdisjSL (hAX u hvu h101.1 h011.1 h).2 hXv)
                  · exact h
                exact ih v hv_lt hvv ⟨h110.2, h101.2, h011.2, hv100, hv010, hv001⟩
            · simp [gate] at hor
              have hFor : ∀ ba bx e, F w ba bx e = (F u ba bx e || F v ba bx e) := fun ba bx e => by
                rw [hgate_ev, hor]; simp [GateOp.eval]
              rw [hFor, Bool.or_eq_true] at h110 h101 h011
              rw [hFor, Bool.or_eq_false_iff] at h100 h010 h001
              have hAX : ∀ z, validW z → F z false true false = false → F z true false false = false →
                  F z true true false = true → a.val ∈ SL z ∧ n + x.val ∈ SL z := by
                intro z hvz hf1 hf2 ht
                constructor
                · by_contra hN; rw [← hdepA z hvz hN true false, hf1] at ht; exact Bool.noConfusion ht
                · by_contra hN; rw [← hdepX z hvz hN true false, hf2] at ht; exact Bool.noConfusion ht
              have hAE : ∀ z, validW z → F z false false true = false → F z true false false = false →
                  F z true false true = true → a.val ∈ SL z ∧ (z = e0 ∨ hasE z) := by
                intro z hvz hf1 hf2 ht
                constructor
                · by_contra hN; rw [← hdepA z hvz hN false true, hf1] at ht; exact Bool.noConfusion ht
                · by_contra hN; rw [← hdepE z hvz hN true false, hf2] at ht; exact Bool.noConfusion ht
              have hXE : ∀ z, validW z → F z false false true = false → F z false true false = false →
                  F z false true true = true → n + x.val ∈ SL z ∧ (z = e0 ∨ hasE z) := by
                intro z hvz hf1 hf2 ht
                constructor
                · by_contra hN; rw [← hdepX z hvz hN false true, hf1] at ht; exact Bool.noConfusion ht
                · by_contra hN; rw [← hdepE z hvz hN false true, hf2] at ht; exact Bool.noConfusion ht
              rcases h110 with hu110 | hv110
              · obtain ⟨hAu, hXu⟩ := hAX u hvu h010.1 h100.1 hu110
                have hu101 : F u true false true = true := by
                  rcases h101 with h | h
                  · exact h
                  · exact False.elim (Finset.disjoint_left.mp hdisjSL hAu (hAE v hvv h001.2 h100.2 h).1)
                have hu011 : F u false true true = true := by
                  rcases h011 with h | h
                  · exact h
                  · exact False.elim (Finset.disjoint_left.mp hdisjSL hXu (hXE v hvv h001.2 h010.2 h).1)
                exact ih u hu_lt hvu ⟨hu110, hu101, hu011, h100.1, h010.1, h001.1⟩
              · obtain ⟨hAv, hXv⟩ := hAX v hvv h010.2 h100.2 hv110
                have hv101 : F v true false true = true := by
                  rcases h101 with h | h
                  · exact False.elim (Finset.disjoint_left.mp hdisjSL (hAE u hvu h001.1 h100.1 h).1 hAv)
                  · exact h
                have hv011 : F v false true true = true := by
                  rcases h011 with h | h
                  · exact False.elim (Finset.disjoint_left.mp hdisjSL (hXE u hvu h001.1 h010.1 h).1 hXv)
                  · exact h
                exact ih v hv_lt hvv ⟨hv110, hv101, hv011, h100.2, h010.2, h001.2⟩
        · dsimp [F] at h110
          rw [evalSub_entry] at h110
          exact Bool.noConfusion h110
    exact hno_maj root (Or.inl hrootMem) ⟨hF_tt, hF_tft_j, hF_ftt_i, hF_tff_c, hF_ftf_c, hF_fft_j⟩
  exact ⟨hconc1, hconc2, hconc3, hconc4⟩

end PEqualNP.Outside.L_meta_25614_aux

theorem PEqualNP.Outside.L_meta_25614 : (∀ (n m : ℕ) (G : Fin n → Fin m → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit)
    (R : Finset (Fin n)) (B : Finset (Fin m)) (region entry : Finset ℕ) (root : ℕ),
  let raw := n + m
  let sources := R.image (fun src => src.val) ∪ B.image (fun dest => n + dest.val)
  let wires := sources ∪ region.image (fun idx => raw + idx)
  let gate := PEqualNP.MetaComplexity.NestedCover.gateAt C
  let localReads := PEqualNP.MetaComplexity.NestedCover.readsIn C region
  let allReads := PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size)
  let extR := fun (i : Fin n) => (Finset.univ \ B).filter (fun outColumn : Fin m => G i outColumn = false)
  let extC := fun (j : Fin m) => (Finset.univ \ R).filter (fun outRow : Fin n => G outRow j = false)
  (∀ a, ∃ c, G a c = false) → (∀ c, ∃ a, G a c = false) →
  PEqualNP.MetaComplexity.Monotone2 C →
  PEqualNP.MetaComplexity.NestedCover.ReadsBack raw C →
  PEqualNP.Represents.Represents G C → region ⊆ Finset.range C.size → root ∈ wires →
  entry.card ≤ 1 → (∀ w ∈ entry, w ∉ wires ∧ w < root ∧ localReads w = 1) →
  (∀ k ∈ region,
    ((gate k).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
     (gate k).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
    (gate k).inputs.length = 2 ∧ ∀ w ∈ (gate k).inputs, w ∈ wires ∨ w ∈ entry) →
  localReads root = 0 →
  (∀ w ∈ wires, w ≠ root → localReads w = 1 ∧ allReads w = 1 ∧ C.output ≠ w) →
  (∀ a ∈ R, ∀ b ∈ R, extR a ⊆ extR b ∨ extR b ⊆ extR a) ∧
  (∀ x ∈ B, ∀ y ∈ B, extC x ⊆ extC y ∨ extC y ⊆ extC x) ∧
  (∀ a ∈ R, ∀ b ∈ R, ∀ x ∈ B, ∀ y ∈ B,
    G a x = true → G b x = true → G b y = true → G a y = true) ∧
  (∀ a ∈ R, ∀ x ∈ B, G a x = true →
    (∀ j ∉ B, G a j = false) ∨ (∀ i ∉ R, G i x = false))) :=
  PEqualNP.Outside.L_meta_25614_aux.main_aux
