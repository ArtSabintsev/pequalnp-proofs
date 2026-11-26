import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

namespace PEqualNP.Outside.L_meta_19062

def evalWires (gs : List Gate) (inp : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) inp

def isMono2 (gs : List Gate) : Prop :=
  ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

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

theorem evalWires_length (gs : List Gate) (inp : List Bool) :
    (evalWires gs inp).length = inp.length + gs.length := by
  obtain ⟨ext, hlen, heq⟩ := foldl_wires_append gs inp
  rw [evalWires, heq, List.length_append, hlen]

theorem evalWires_append_getD_lt (gs1 gs2 : List Gate) (inp : List Bool) {i : ℕ}
    (hi : i < inp.length + gs1.length) :
    (evalWires (gs1 ++ gs2) inp).getD i false = (evalWires gs1 inp).getD i false := by
  rw [evalWires, List.foldl_append]
  obtain ⟨ext, _, heq⟩ := foldl_wires_append gs2 (evalWires gs1 inp)
  change (gs2.foldl _ (evalWires gs1 inp)).getD i false = _
  rw [heq]
  have hlen : (evalWires gs1 inp).length = inp.length + gs1.length := evalWires_length gs1 inp
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : i < (evalWires gs1 inp).length)]

theorem evalWires_snoc (gs : List Gate) (g : Gate) (inp : List Bool) :
    evalWires (gs ++ [g]) inp =
      evalWires gs inp ++ [g.op.eval (g.inputs.map fun i => (evalWires gs inp).getD i false)] := by
  simp [evalWires, List.foldl_append]

theorem evalWires_snoc_last (gs : List Gate) (g : Gate) (inp : List Bool) :
    (evalWires (gs ++ [g]) inp).getD (inp.length + gs.length) false =
      g.op.eval (g.inputs.map fun i => (evalWires gs inp).getD i false) := by
  rw [evalWires_snoc]
  have hlen : (evalWires gs inp).length = inp.length + gs.length := evalWires_length gs inp
  simp [List.getD_eq_getElem?_getD, ← hlen]

theorem evalWires_input (gs : List Gate) (inp : List Bool) {i : ℕ} (hi : i < inp.length) :
    (evalWires gs inp).getD i false = inp.getD i false := by
  have h := evalWires_append_getD_lt [] gs inp (i := i) (by simp [hi])
  simpa [evalWires] using h

theorem isMono2_snoc {gs : List Gate} (hm : isMono2 gs) {op : GateOp} {a b : ℕ}
    (hop : op = GateOp.and ∨ op = GateOp.or) :
    isMono2 (gs ++ [⟨op, [a, b]⟩]) := by
  intro g hg
  simp only [List.mem_append, List.mem_singleton] at hg
  rcases hg with hg | rfl
  · exact hm g hg
  · exact ⟨hop, by simp⟩

theorem gateOp_or_eval (b1 b2 : Bool) : GateOp.eval GateOp.or [b1, b2] = (b1 || b2) := by
  cases b1 <;> cases b2 <;> rfl

theorem gateOp_and_eval (b1 b2 : Bool) : GateOp.eval GateOp.and [b1, b2] = (b1 && b2) := by
  cases b1 <;> cases b2 <;> rfl

theorem oneEach_length {n : ℕ} (u v : Fin n) : (oneEach u v).length = 2 * n := by
  simp [oneEach]; omega

theorem oneEach_getD_left {n : ℕ} (u v : Fin n) {i : ℕ} (hi : i < n) :
    (oneEach u v).getD i false = decide (i = u.val) := by
  simp only [oneEach, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by simp [hi]), List.getElem?_ofFn]
  simp [hi, Fin.ext_iff]

theorem oneEach_getD_right {n : ℕ} (u v : Fin n) {i : ℕ} (hi : i < n) :
    (oneEach u v).getD (n + i) false = decide (i = v.val) := by
  simp only [oneEach, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by simp)]
  simp only [List.length_ofFn, Nat.add_sub_cancel_left, List.getElem?_ofFn, hi, ↓reduceDIte,
    Option.getD_some, Fin.ext_iff]

def buildZ (n : ℕ) (k : ℕ) : List Gate :=
  (List.range k).map fun i => ⟨GateOp.or, [i, n + i]⟩

theorem buildZ_length (n k : ℕ) : (buildZ n k).length = k := by
  simp [buildZ]

theorem buildZ_mono (n k : ℕ) : isMono2 (buildZ n k) := by
  intro g hg
  simp only [buildZ, List.mem_map] at hg
  rcases hg with ⟨i, _, rfl⟩
  exact ⟨Or.inr rfl, by simp⟩

theorem buildZ_eval {n : ℕ} (u v : Fin n) (k : ℕ) (hk : k ≤ n) :
    ∀ i < k, (evalWires (buildZ n k) (oneEach u v)).getD (2 * n + i) false = true ↔
      i = u.val ∨ i = v.val := by
  induction k with
  | zero => intro i hi; omega
  | succ k ih =>
    have hstep : buildZ n (k + 1) = buildZ n k ++ [⟨GateOp.or, [k, n + k]⟩] := by
      simp [buildZ, List.range_succ]
    intro i hi
    rw [hstep]
    by_cases hik : i < k
    · rw [evalWires_append_getD_lt (buildZ n k) [_] (oneEach u v)
        (by rw [oneEach_length, buildZ_length]; omega)]
      exact ih (by omega) i hik
    · have hieq : i = k := by omega
      subst hieq
      have hidx : 2 * n + i = (oneEach u v).length + (buildZ n i).length := by
        rw [oneEach_length, buildZ_length]
      rw [hidx, evalWires_snoc_last]
      simp only [List.map_cons, List.map_nil, gateOp_or_eval, Bool.or_eq_true]
      rw [evalWires_input (buildZ n i) (oneEach u v) (by rw [oneEach_length]; omega),
          evalWires_input (buildZ n i) (oneEach u v) (by rw [oneEach_length]; omega),
          oneEach_getD_left u v (by omega), oneEach_getD_right u v (by omega)]
      simp

def orChain (N : ℕ) (gs : List Gate) (acc : ℕ) : List ℕ → List Gate × ℕ
  | [] => (gs, acc)
  | w :: ws => orChain N (gs ++ [⟨GateOp.or, [acc, w]⟩]) (N + gs.length) ws

theorem orChain_spec (N : ℕ) (gs : List Gate) (acc : ℕ) (ws : List ℕ)
    (hm : isMono2 gs) (hacc : acc < N + gs.length) (hws : ∀ w ∈ ws, w < N + gs.length) :
    let res := orChain N gs acc ws
    (∃ ext, res.1 = gs ++ ext ∧ ext.length = ws.length) ∧
    isMono2 res.1 ∧
    res.2 < N + res.1.length ∧
    ∀ inp : List Bool, inp.length = N →
      ((evalWires res.1 inp).getD res.2 false = true ↔
        (evalWires gs inp).getD acc false = true ∨ ∃ w ∈ ws, (evalWires gs inp).getD w false = true) := by
  induction ws generalizing gs acc with
  | nil =>
    refine ⟨⟨[], by simp [orChain]⟩, hm, hacc, ?_⟩
    intro inp _; simp [orChain]
  | cons w ws ih =>
    let gs1 := gs ++ [⟨GateOp.or, [acc, w]⟩]
    let idx := N + gs.length
    have hm1 : isMono2 gs1 := isMono2_snoc hm (Or.inr rfl)
    have hidx : idx < N + gs1.length := by simp [gs1, idx]
    have hws1 : ∀ w' ∈ ws, w' < N + gs1.length := by
      intro w' hw'
      have h' := hws w' (by simp [hw'])
      simp [gs1]; omega
    obtain ⟨⟨ext, heq, hlen⟩, hm2, houtlt, heval⟩ := ih gs1 idx hm1 hidx hws1
    have hres1 : (orChain N gs acc (w :: ws)).1 = gs ++ (⟨GateOp.or, [acc, w]⟩ :: ext) := by
      show (orChain N gs1 idx ws).1 = _
      rw [heq]; simp [gs1]
    refine ⟨⟨⟨GateOp.or, [acc, w]⟩ :: ext, hres1, by simp [hlen]⟩, hm2, houtlt, ?_⟩
    intro inp hlen_inp
    show (evalWires (orChain N gs1 idx ws).1 inp).getD (orChain N gs1 idx ws).2 false = true ↔ _
    rw [heval inp hlen_inp]
    have hlast : (evalWires gs1 inp).getD idx false = true ↔
        (evalWires gs inp).getD acc false = true ∨ (evalWires gs inp).getD w false = true := by
      have hidx' : idx = inp.length + gs.length := by omega
      rw [hidx', evalWires_snoc_last]
      simp only [List.map_cons, List.map_nil, gateOp_or_eval, Bool.or_eq_true]
    rw [hlast]
    constructor
    · rintro ((ha | hw') | ⟨w', hw'in, hw't⟩)
      · exact Or.inl ha
      · exact Or.inr ⟨w, by simp, hw'⟩
      · have hw'lt := hws w' (by simp [hw'in])
        rw [evalWires_append_getD_lt gs [_] inp (by omega)] at hw't
        exact Or.inr ⟨w', by simp [hw'in], hw't⟩
    · rintro (ha | ⟨w', hw'in, hw't⟩)
      · exact Or.inl (Or.inl ha)
      · simp only [List.mem_cons] at hw'in
        rcases hw'in with rfl | hw'in
        · exact Or.inl (Or.inr hw't)
        · right
          refine ⟨w', hw'in, ?_⟩
          have hw'lt := hws w' (by simp [hw'in])
          rw [evalWires_append_getD_lt gs [_] inp (by omega)]
          exact hw't

def buildOrGroups (N : ℕ) (gs : List Gate) : List (List ℕ) → List Gate × List ℕ
  | [] => (gs, [])
  | [] :: rest => buildOrGroups N gs rest
  | (w0 :: ws) :: rest =>
    let p := orChain N gs w0 ws
    let q := buildOrGroups N p.1 rest
    (q.1, p.2 :: q.2)

theorem buildOrGroups_spec (N : ℕ) (gs : List Gate) (groups : List (List ℕ))
    (hm : isMono2 gs)
    (hgroups : ∀ g ∈ groups, g ≠ [] ∧ ∀ w ∈ g, w < N + gs.length) :
    let res := buildOrGroups N gs groups
    (∃ ext, res.1 = gs ++ ext ∧ ext.length = (groups.map fun g => g.length - 1).sum) ∧
    isMono2 res.1 ∧
    res.2.length = groups.length ∧
    (∀ w ∈ res.2, w < N + res.1.length) ∧
    ∀ inp : List Bool, inp.length = N →
      ∀ k, k < groups.length →
        ((evalWires res.1 inp).getD (res.2.getD k 0) false = true ↔
          ∃ w ∈ groups.getD k [], (evalWires gs inp).getD w false = true) := by
  induction groups generalizing gs with
  | nil =>
    refine ⟨⟨[], by simp [buildOrGroups]⟩, hm, rfl, by simp [buildOrGroups], ?_⟩
    intro inp _ k hk; simp at hk
  | cons g rest ih =>
    have hg := hgroups g (by simp)
    cases g with
    | nil => exact (hg.1 rfl).elim
    | cons w0 ws =>
      have hw0 : w0 < N + gs.length := hg.2 w0 (by simp)
      have hws : ∀ w ∈ ws, w < N + gs.length := fun w hw => hg.2 w (by simp [hw])
      let p := orChain N gs w0 ws
      obtain ⟨⟨ext1, heq1, hlen1⟩, hm1, hout1, heval1⟩ := orChain_spec N gs w0 ws hm hw0 hws
      have hrest : ∀ g' ∈ rest, g' ≠ [] ∧ ∀ w ∈ g', w < N + p.1.length := by
        intro g' hg'
        have h' := hgroups g' (by simp [hg'])
        refine ⟨h'.1, fun w hw => ?_⟩
        have hwlt := h'.2 w hw
        change w < N + p.1.length
        rw [show p.1 = gs ++ ext1 from heq1, List.length_append]; omega
      let q := buildOrGroups N p.1 rest
      obtain ⟨⟨ext2, heq2, hlen2⟩, hm2, hlen_w, hwlt2, heval2⟩ := ih p.1 hm1 hrest
      have hres1 : (buildOrGroups N gs ((w0 :: ws) :: rest)).1 = gs ++ (ext1 ++ ext2) := by
        show q.1 = _
        rw [show q.1 = p.1 ++ ext2 from heq2, show p.1 = gs ++ ext1 from heq1, List.append_assoc]
      have hres2 : (buildOrGroups N gs ((w0 :: ws) :: rest)).2 = p.2 :: q.2 := rfl
      refine ⟨⟨ext1 ++ ext2, hres1, by simp [hlen1, hlen2]⟩, hm2, ?_, ?_, ?_⟩
      · simp only [hres2, List.length_cons]
        exact congrArg Nat.succ hlen_w
      · intro w hw
        rw [hres2, List.mem_cons] at hw
        rcases hw with rfl | hw
        · show p.2 < N + q.1.length
          rw [show q.1 = p.1 ++ ext2 from heq2, List.length_append]
          have : p.2 < N + p.1.length := hout1
          omega
        · exact hwlt2 w hw
      · intro inp hlen_inp k hk
        cases k with
        | zero =>
          simp only [hres2, List.getD_cons_zero]
          show (evalWires q.1 inp).getD p.2 false = true ↔ _
          have hp2_lt : p.2 < inp.length + p.1.length := by
            have : p.2 < N + p.1.length := hout1
            omega
          rw [show q.1 = p.1 ++ ext2 from heq2,
              evalWires_append_getD_lt p.1 ext2 inp hp2_lt]
          rw [heval1 inp hlen_inp]
          simp
        | succ k' =>
          simp only [hres2, List.getD_cons_succ]
          have hk' : k' < rest.length := by simpa using hk
          show (evalWires q.1 inp).getD (q.2.getD k' 0) false = true ↔ _
          rw [heval2 inp hlen_inp k' hk']
          constructor
          · rintro ⟨w, hw, hwt⟩
            have hwlt : w < N + gs.length := (hgroups (rest.getD k' []) (by
              have hmem : rest[k']? = some (rest.getD k' []) := by
                simp [List.getD_eq_getElem?_getD, hk']
              exact List.mem_cons_of_mem _ (List.mem_of_getElem? hmem))).2 w hw
            rw [show p.1 = gs ++ ext1 from heq1,
                evalWires_append_getD_lt gs ext1 inp (by omega)] at hwt
            exact ⟨w, hw, hwt⟩
          · rintro ⟨w, hw, hwt⟩
            have hwlt : w < N + gs.length := (hgroups (rest.getD k' []) (by
              have hmem : rest[k']? = some (rest.getD k' []) := by
                simp [List.getD_eq_getElem?_getD, hk']
              exact List.mem_cons_of_mem _ (List.mem_of_getElem? hmem))).2 w hw
            refine ⟨w, hw, ?_⟩
            rw [show p.1 = gs ++ ext1 from heq1,
                evalWires_append_getD_lt gs ext1 inp (by omega)]
            exact hwt

def th2Step (N : ℕ) (gs : List Gate) (p t : ℕ) : List ℕ → List Gate × ℕ
  | [] => (gs, t)
  | [w] =>
    let gs1 := gs ++ [⟨GateOp.and, [p, w]⟩]
    let a := N + gs.length
    let gs2 := gs1 ++ [⟨GateOp.or, [t, a]⟩]
    (gs2, N + gs1.length)
  | w :: w2 :: rest =>
    let gs1 := gs ++ [⟨GateOp.and, [p, w]⟩]
    let a := N + gs.length
    let gs2 := gs1 ++ [⟨GateOp.or, [t, a]⟩]
    let t' := N + gs1.length
    let gs3 := gs2 ++ [⟨GateOp.or, [p, w]⟩]
    let p' := N + gs2.length
    th2Step N gs3 p' t' (w2 :: rest)

theorem th2Step_spec (N : ℕ) (gs : List Gate) (p t : ℕ) (ws : List ℕ)
    (hne : ws ≠ []) (hm : isMono2 gs)
    (hp : p < N + gs.length) (ht : t < N + gs.length)
    (hws : ∀ w ∈ ws, w < N + gs.length) :
    let res := th2Step N gs p t ws
    (∃ ext, res.1 = gs ++ ext ∧ ext.length = 3 * ws.length - 1) ∧
    isMono2 res.1 ∧
    res.2 < N + res.1.length ∧
    ∀ inp : List Bool, inp.length = N →
      ((evalWires res.1 inp).getD res.2 false = true ↔
        (evalWires gs inp).getD t false = true ∨
        ((evalWires gs inp).getD p false = true ∧ ∃ w ∈ ws, (evalWires gs inp).getD w false = true) ∨
        ∃ i j, i < j ∧ j < ws.length ∧
          (evalWires gs inp).getD (ws.getD i 0) false = true ∧
          (evalWires gs inp).getD (ws.getD j 0) false = true) := by
  induction ws generalizing gs p t with
  | nil => exact (hne rfl).elim
  | cons w tail ih =>
    have hw : w < N + gs.length := hws w (by simp)
    cases tail with
    | nil =>
      let gs1 := gs ++ [⟨GateOp.and, [p, w]⟩]
      let a := N + gs.length
      let gs2 := gs1 ++ [⟨GateOp.or, [t, a]⟩]
      have hm1 : isMono2 gs1 := isMono2_snoc hm (Or.inl rfl)
      have hm2 : isMono2 gs2 := isMono2_snoc hm1 (Or.inr rfl)
      refine ⟨⟨[⟨GateOp.and, [p, w]⟩, ⟨GateOp.or, [t, a]⟩], by simp [th2Step, a], by simp⟩,
        hm2, by simp [th2Step], ?_⟩
      intro inp hlen_inp
      show (evalWires gs2 inp).getD (N + gs1.length) false = true ↔ _
      have hidx2 : N + gs1.length = inp.length + gs1.length := by omega
      have hidx1 : a = inp.length + gs.length := by omega
      rw [hidx2, evalWires_snoc_last]
      simp only [List.map_cons, List.map_nil, gateOp_or_eval, Bool.or_eq_true]
      rw [evalWires_append_getD_lt gs [_] inp (by omega), hidx1, evalWires_snoc_last]
      simp only [List.map_cons, List.map_nil, gateOp_and_eval, Bool.and_eq_true]
      constructor
      · rintro (ht' | ⟨hp', hw'⟩)
        · exact Or.inl ht'
        · exact Or.inr (Or.inl ⟨hp', w, by simp, hw'⟩)
      · rintro (ht' | ⟨hp', w', hw'in, hw'⟩ | ⟨i, j, hij, hj, _, _⟩)
        · exact Or.inl ht'
        · simp only [List.mem_singleton] at hw'in
          subst hw'in
          exact Or.inr ⟨hp', hw'⟩
        · simp at hj; omega
    | cons w2 rest =>
      let gs1 := gs ++ [⟨GateOp.and, [p, w]⟩]
      let a := N + gs.length
      let gs2 := gs1 ++ [⟨GateOp.or, [t, a]⟩]
      let t' := N + gs1.length
      let gs3 := gs2 ++ [⟨GateOp.or, [p, w]⟩]
      let p' := N + gs2.length
      have hm1 : isMono2 gs1 := isMono2_snoc hm (Or.inl rfl)
      have hm2 : isMono2 gs2 := isMono2_snoc hm1 (Or.inr rfl)
      have hm3 : isMono2 gs3 := isMono2_snoc hm2 (Or.inr rfl)
      have hgs3_eq : gs3 = gs ++ [⟨GateOp.and, [p, w]⟩, ⟨GateOp.or, [t, a]⟩, ⟨GateOp.or, [p, w]⟩] := by
        simp [gs3, gs2, gs1]
      have hp' : p' < N + gs3.length := by simp [gs3, gs2, gs1, p']
      have ht' : t' < N + gs3.length := by simp [gs3, gs2, gs1, t']
      have hws' : ∀ w' ∈ w2 :: rest, w' < N + gs3.length := by
        intro w' hw'
        have h' := hws w' (by simp [hw'])
        simp [gs3, gs2, gs1]; omega
      obtain ⟨⟨ext, heq, hlen⟩, hm_res, hout_lt, heval⟩ :=
        ih gs3 p' t' (by simp) hm3 hp' ht' hws'
      have hres1 : (th2Step N gs p t (w :: w2 :: rest)).1 =
          gs ++ ([⟨GateOp.and, [p, w]⟩, ⟨GateOp.or, [t, a]⟩, ⟨GateOp.or, [p, w]⟩] ++ ext) := by
        show (th2Step N gs3 p' t' (w2 :: rest)).1 = _
        rw [heq, hgs3_eq, List.append_assoc]
      refine ⟨⟨_, hres1, by simp [hlen]; omega⟩, hm_res, hout_lt, ?_⟩
      intro inp hlen_inp
      show (evalWires (th2Step N gs3 p' t' (w2 :: rest)).1 inp).getD
        (th2Step N gs3 p' t' (w2 :: rest)).2 false = true ↔ _
      rw [heval inp hlen_inp]
      have eval_t' : (evalWires gs3 inp).getD t' false = true ↔
          (evalWires gs inp).getD t false = true ∨
          ((evalWires gs inp).getD p false = true ∧ (evalWires gs inp).getD w false = true) := by
        rw [evalWires_append_getD_lt gs2 [_] inp (by simp [gs2, gs1, t']; omega)]
        have hidx2 : t' = inp.length + gs1.length := by omega
        have hidx1 : a = inp.length + gs.length := by omega
        rw [hidx2, evalWires_snoc_last]
        simp only [List.map_cons, List.map_nil, gateOp_or_eval, Bool.or_eq_true]
        rw [evalWires_append_getD_lt gs [_] inp (by omega), hidx1, evalWires_snoc_last]
        simp only [List.map_cons, List.map_nil, gateOp_and_eval, Bool.and_eq_true]
      have eval_p' : (evalWires gs3 inp).getD p' false = true ↔
          (evalWires gs inp).getD p false = true ∨ (evalWires gs inp).getD w false = true := by
        have hidx3 : p' = inp.length + gs2.length := by omega
        rw [hidx3, evalWires_snoc_last]
        simp only [List.map_cons, List.map_nil, gateOp_or_eval, Bool.or_eq_true]
        have hgs2_eq : gs2 = gs ++ [⟨GateOp.and, [p, w]⟩, ⟨GateOp.or, [t, a]⟩] := by simp [gs2, gs1]
        rw [hgs2_eq, evalWires_append_getD_lt gs _ inp (by omega),
            evalWires_append_getD_lt gs _ inp (by omega)]
      have eval_old : ∀ u, u < N + gs.length →
          (evalWires gs3 inp).getD u false = (evalWires gs inp).getD u false := by
        intro u hu
        rw [hgs3_eq, evalWires_append_getD_lt gs _ inp (by omega)]
      rw [eval_t', eval_p']
      constructor
      · rintro ((ht_ok | ⟨hp_ok, hw_ok⟩) | ⟨hp_or_w, u, hu_mem, hu_ok⟩ | ⟨i, j, hij, hj, hi_ok, hj_ok⟩)
        · exact Or.inl ht_ok
        · exact Or.inr (Or.inl ⟨hp_ok, w, by simp, hw_ok⟩)
        · rw [eval_old u (hws u (List.mem_cons_of_mem _ hu_mem))] at hu_ok
          rcases hp_or_w with hp_ok | hw_ok
          · exact Or.inr (Or.inl ⟨hp_ok, u, List.mem_cons_of_mem _ hu_mem, hu_ok⟩)
          · obtain ⟨k, hk_lt, hk_eq⟩ := List.getElem_of_mem hu_mem
            right; right
            refine ⟨0, k + 1, Nat.zero_lt_succ k, by simpa using Nat.succ_lt_succ hk_lt, ?_, ?_⟩
            · simpa using hw_ok
            · have hget : (w :: w2 :: rest).getD (k + 1) 0 = u := by
                rw [List.getD_cons_succ, List.getD_eq_getElem?_getD,
                    List.getElem?_eq_getElem hk_lt, Option.getD_some, hk_eq]
              rw [hget]; exact hu_ok
        · right; right
          have hi_lt : i < (w2 :: rest).length := by omega
          have hi_mem : (w2 :: rest).getD i 0 ∈ w2 :: rest := by
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi_lt, Option.getD_some]
            exact List.getElem_mem hi_lt
          have hj_mem : (w2 :: rest).getD j 0 ∈ w2 :: rest := by
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
            exact List.getElem_mem hj
          rw [eval_old _ (hws _ (List.mem_cons_of_mem _ hi_mem))] at hi_ok
          rw [eval_old _ (hws _ (List.mem_cons_of_mem _ hj_mem))] at hj_ok
          exact ⟨i + 1, j + 1, Nat.succ_lt_succ hij, by simpa using Nat.succ_lt_succ hj, hi_ok, hj_ok⟩
      · rintro (ht_ok | ⟨hp_ok, u, hu_mem, hu_ok⟩ | ⟨i, j, hij, hj, hi_ok, hj_ok⟩)
        · exact Or.inl (Or.inl ht_ok)
        · rw [List.mem_cons] at hu_mem
          rcases hu_mem with rfl | hu_mem
          · exact Or.inl (Or.inr ⟨hp_ok, hu_ok⟩)
          · right; left
            refine ⟨Or.inl hp_ok, u, hu_mem, ?_⟩
            rw [eval_old u (hws u (List.mem_cons_of_mem _ hu_mem))]
            exact hu_ok
        · cases i with
          | zero =>
            cases j with
            | zero => omega
            | succ j' =>
              have hj' : j' < (w2 :: rest).length := by simpa using hj
              simp only [List.getD_cons_zero] at hi_ok
              simp only [List.getD_cons_succ] at hj_ok
              have hj_mem : (w2 :: rest).getD j' 0 ∈ w2 :: rest := by
                rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj', Option.getD_some]
                exact List.getElem_mem hj'
              right; left
              refine ⟨Or.inr hi_ok, (w2 :: rest).getD j' 0, hj_mem, ?_⟩
              rw [eval_old _ (hws _ (List.mem_cons_of_mem _ hj_mem))]
              exact hj_ok
          | succ i' =>
            cases j with
            | zero => omega
            | succ j' =>
              have hij' : i' < j' := by omega
              have hj' : j' < (w2 :: rest).length := by simpa using hj
              have hi' : i' < (w2 :: rest).length := by omega
              simp only [List.getD_cons_succ] at hi_ok hj_ok
              have hi_mem : (w2 :: rest).getD i' 0 ∈ w2 :: rest := by
                rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some]
                exact List.getElem_mem hi'
              have hj_mem : (w2 :: rest).getD j' 0 ∈ w2 :: rest := by
                rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj', Option.getD_some]
                exact List.getElem_mem hj'
              right; right
              refine ⟨i', j', hij', hj', ?_, ?_⟩
              · rw [eval_old _ (hws _ (List.mem_cons_of_mem _ hi_mem))]; exact hi_ok
              · rw [eval_old _ (hws _ (List.mem_cons_of_mem _ hj_mem))]; exact hj_ok

def buildTh2 (N : ℕ) (gs : List Gate) : List ℕ → List Gate × ℕ
  | [w0, w1] => (gs ++ [⟨GateOp.and, [w0, w1]⟩], N + gs.length)
  | w0 :: w1 :: w2 :: rest =>
    let gs1 := gs ++ [⟨GateOp.or, [w0, w1]⟩]
    let p := N + gs.length
    let gs2 := gs1 ++ [⟨GateOp.and, [w0, w1]⟩]
    let t := N + gs1.length
    th2Step N gs2 p t (w2 :: rest)
  | _ => (gs, 0)

theorem buildTh2_spec (N : ℕ) (gs : List Gate) (ws : List ℕ)
    (hlen2 : 2 ≤ ws.length) (hm : isMono2 gs)
    (hws : ∀ w ∈ ws, w < N + gs.length) :
    let res := buildTh2 N gs ws
    (∃ ext, res.1 = gs ++ ext ∧ ext.length = 3 * ws.length - 5) ∧
    isMono2 res.1 ∧
    res.2 < N + res.1.length ∧
    ∀ inp : List Bool, inp.length = N →
      ((evalWires res.1 inp).getD res.2 false = true ↔
        ∃ i j, i < j ∧ j < ws.length ∧
          (evalWires gs inp).getD (ws.getD i 0) false = true ∧
          (evalWires gs inp).getD (ws.getD j 0) false = true) := by
  cases ws with
  | nil => simp at hlen2
  | cons w0 t1 =>
    cases t1 with
    | nil => simp at hlen2
    | cons w1 t2 =>
      have hw0 : w0 < N + gs.length := hws w0 (by simp)
      have hw1 : w1 < N + gs.length := hws w1 (by simp)
      cases t2 with
      | nil =>
        refine ⟨⟨[⟨GateOp.and, [w0, w1]⟩], rfl, by simp⟩,
          isMono2_snoc hm (Or.inl rfl), by simp [buildTh2], ?_⟩
        intro inp hlen_inp
        show (evalWires (gs ++ [⟨GateOp.and, [w0, w1]⟩]) inp).getD (N + gs.length) false = true ↔ _
        have hidx : N + gs.length = inp.length + gs.length := by omega
        rw [hidx, evalWires_snoc_last]
        simp only [List.map_cons, List.map_nil, gateOp_and_eval, Bool.and_eq_true]
        constructor
        · rintro ⟨h0, h1⟩
          exact ⟨0, 1, by omega, by simp, by simpa using h0, by simpa using h1⟩
        · rintro ⟨i, j, hij, hj, hi_ok, hj_ok⟩
          simp at hj
          have hi0 : i = 0 := by omega
          have hj1 : j = 1 := by omega
          subst hi0; subst hj1
          exact ⟨by simpa using hi_ok, by simpa using hj_ok⟩
      | cons w2 rest =>
        let gs1 := gs ++ [⟨GateOp.or, [w0, w1]⟩]
        let p := N + gs.length
        let gs2 := gs1 ++ [⟨GateOp.and, [w0, w1]⟩]
        let t := N + gs1.length
        have hm1 : isMono2 gs1 := isMono2_snoc hm (Or.inr rfl)
        have hm2 : isMono2 gs2 := isMono2_snoc hm1 (Or.inl rfl)
        have hgs2_eq : gs2 = gs ++ [⟨GateOp.or, [w0, w1]⟩, ⟨GateOp.and, [w0, w1]⟩] := by
          simp [gs2, gs1]
        have hp : p < N + gs2.length := by simp [gs2, gs1, p]
        have ht : t < N + gs2.length := by simp [gs2, gs1, t]
        have hws' : ∀ w ∈ w2 :: rest, w < N + gs2.length := by
          intro w hw
          have h' := hws w (by simp [hw])
          simp [gs2, gs1]; omega
        obtain ⟨⟨ext, heq, hlen⟩, hm_res, hout_lt, heval⟩ :=
          th2Step_spec N gs2 p t (w2 :: rest) (by simp) hm2 hp ht hws'
        have hres1 : (buildTh2 N gs (w0 :: w1 :: w2 :: rest)).1 =
            gs ++ ([⟨GateOp.or, [w0, w1]⟩, ⟨GateOp.and, [w0, w1]⟩] ++ ext) := by
          show (th2Step N gs2 p t (w2 :: rest)).1 = _
          rw [heq, hgs2_eq, List.append_assoc]
        refine ⟨⟨_, hres1, by simp [hlen]; omega⟩, hm_res, hout_lt, ?_⟩
        intro inp hlen_inp
        show (evalWires (th2Step N gs2 p t (w2 :: rest)).1 inp).getD
          (th2Step N gs2 p t (w2 :: rest)).2 false = true ↔ _
        rw [heval inp hlen_inp]
        have eval_p : (evalWires gs2 inp).getD p false = true ↔
            (evalWires gs inp).getD w0 false = true ∨ (evalWires gs inp).getD w1 false = true := by
          rw [evalWires_append_getD_lt gs1 [_] inp (by simp [gs1, p]; omega)]
          have hidx : p = inp.length + gs.length := by omega
          rw [hidx, evalWires_snoc_last]
          simp only [List.map_cons, List.map_nil, gateOp_or_eval, Bool.or_eq_true]
        have eval_t : (evalWires gs2 inp).getD t false = true ↔
            (evalWires gs inp).getD w0 false = true ∧ (evalWires gs inp).getD w1 false = true := by
          have hidx : t = inp.length + gs1.length := by omega
          rw [hidx, evalWires_snoc_last]
          simp only [List.map_cons, List.map_nil, gateOp_and_eval, Bool.and_eq_true]
          rw [evalWires_append_getD_lt gs [_] inp (by omega),
              evalWires_append_getD_lt gs [_] inp (by omega)]
        have eval_old : ∀ u, u < N + gs.length →
            (evalWires gs2 inp).getD u false = (evalWires gs inp).getD u false := by
          intro u hu
          rw [hgs2_eq, evalWires_append_getD_lt gs _ inp (by omega)]
        rw [eval_p, eval_t]
        constructor
        · rintro (⟨h0, h1⟩ | ⟨h01, u, hu_mem, hu_ok⟩ | ⟨i, j, hij, hj, hi_ok, hj_ok⟩)
          · exact ⟨0, 1, by omega, by simp, by simpa using h0, by simpa using h1⟩
          · rw [eval_old u (hws u (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hu_mem)))] at hu_ok
            obtain ⟨k, hk_lt, hk_eq⟩ := List.getElem_of_mem hu_mem
            have hget : (w0 :: w1 :: w2 :: rest).getD (k + 2) 0 = u := by
              rw [List.getD_cons_succ, List.getD_cons_succ, List.getD_eq_getElem?_getD,
                  List.getElem?_eq_getElem hk_lt, Option.getD_some, hk_eq]
            rcases h01 with h0 | h1
            · refine ⟨0, k + 2, by omega, by simpa using Nat.add_lt_add_right hk_lt 2,
                by simpa using h0, ?_⟩
              rw [hget]; exact hu_ok
            · refine ⟨1, k + 2, by omega, by simpa using Nat.add_lt_add_right hk_lt 2,
                by simpa using h1, ?_⟩
              rw [hget]; exact hu_ok
          · have hi_lt : i < (w2 :: rest).length := by omega
            have hi_mem : (w2 :: rest).getD i 0 ∈ w2 :: rest := by
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi_lt, Option.getD_some]
              exact List.getElem_mem hi_lt
            have hj_mem : (w2 :: rest).getD j 0 ∈ w2 :: rest := by
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
              exact List.getElem_mem hj
            rw [eval_old _ (hws _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hi_mem)))] at hi_ok
            rw [eval_old _ (hws _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hj_mem)))] at hj_ok
            exact ⟨i + 2, j + 2, by omega, by simpa using Nat.add_lt_add_right hj 2, hi_ok, hj_ok⟩
        · rintro ⟨i, j, hij, hj, hi_ok, hj_ok⟩
          match i, j with
          | 0, 1 => exact Or.inl ⟨by simpa using hi_ok, by simpa using hj_ok⟩
          | 0, j' + 2 =>
            have hj' : j' < (w2 :: rest).length := by simpa using hj
            simp only [List.getD_cons_zero] at hi_ok
            simp only [List.getD_cons_succ] at hj_ok
            have hj_mem : (w2 :: rest).getD j' 0 ∈ w2 :: rest := by
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj', Option.getD_some]
              exact List.getElem_mem hj'
            right; left
            refine ⟨Or.inl hi_ok, (w2 :: rest).getD j' 0, hj_mem, ?_⟩
            rw [eval_old _ (hws _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hj_mem)))]; exact hj_ok
          | 1, j' + 2 =>
            have hj' : j' < (w2 :: rest).length := by simpa using hj
            simp only [List.getD_cons_succ, List.getD_cons_zero] at hi_ok
            simp only [List.getD_cons_succ] at hj_ok
            have hj_mem : (w2 :: rest).getD j' 0 ∈ w2 :: rest := by
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj', Option.getD_some]
              exact List.getElem_mem hj'
            right; left
            refine ⟨Or.inr hi_ok, (w2 :: rest).getD j' 0, hj_mem, ?_⟩
            rw [eval_old _ (hws _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hj_mem)))]; exact hj_ok
          | i' + 2, j' + 2 =>
            have hij' : i' < j' := by omega
            have hj' : j' < (w2 :: rest).length := by simpa using hj
            have hi' : i' < (w2 :: rest).length := by omega
            simp only [List.getD_cons_succ] at hi_ok hj_ok
            have hi_mem : (w2 :: rest).getD i' 0 ∈ w2 :: rest := by
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some]
              exact List.getElem_mem hi'
            have hj_mem : (w2 :: rest).getD j' 0 ∈ w2 :: rest := by
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj', Option.getD_some]
              exact List.getElem_mem hj'
            right; right
            refine ⟨i', j', hij', hj', ?_, ?_⟩
            · rw [eval_old _ (hws _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hi_mem)))]; exact hi_ok
            · rw [eval_old _ (hws _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hj_mem)))]; exact hj_ok
          | 0, 0 => omega
          | 1, 0 => omega
          | 1, 1 => omega
          | i' + 2, 0 => omega
          | i' + 2, 1 => omega

theorem sum_map_add_const (L : List (List ℕ)) (hne : ∀ g ∈ L, 1 ≤ g.length) :
    (L.map fun g => g.length - 1).sum + L.length = (L.map List.length).sum := by
  induction L with
  | nil => simp
  | cons g rest ih =>
    have hg : 1 ≤ g.length := hne g (by simp)
    have hih := ih (fun g' hg' => hne g' (by simp [hg']))
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    omega

theorem sum_filter_range (m : ℕ) (f : ℕ → ℕ) (L : List ℕ) (hf : ∀ x ∈ L, f x < m) :
    ((List.range m).map fun k => (L.filter fun x => f x == k).length).sum = L.length := by
  induction L with
  | nil =>
    have h0 : ∀ R : List ℕ, (R.map fun _ => (0 : ℕ)).sum = 0 := by
      intro R; induction R with | nil => rfl | cons _ _ ih => simpa using ih
    simpa using h0 (List.range m)
  | cons a rest ih =>
    have ha : f a < m := hf a (by simp)
    have hih := ih (fun x hx => hf x (by simp [hx]))
    have hinc : ∀ R : List ℕ, R.Nodup → (f a ∈ R →
        (R.map fun k => ((a :: rest).filter fun x => f x == k).length).sum =
          (R.map fun k => (rest.filter fun x => f x == k).length).sum + 1) ∧
        (f a ∉ R →
        (R.map fun k => ((a :: rest).filter fun x => f x == k).length).sum =
          (R.map fun k => (rest.filter fun x => f x == k).length).sum) := by
      intro R hnd
      induction R with
      | nil => exact ⟨by simp, by simp⟩
      | cons k ks ihR =>
        rw [List.nodup_cons] at hnd
        obtain ⟨ih_in, ih_out⟩ := ihR hnd.2
        constructor
        · intro hmem
          rw [List.mem_cons] at hmem
          rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, List.filter_cons]
          rcases hmem with heq | hmem
          · subst heq
            have hnot : f a ∉ ks := hnd.1
            simp only [beq_self_eq_true, ↓reduceIte, List.length_cons]
            rw [ih_out hnot]; omega
          · have hne : (f a == k) = false := by
              rw [beq_eq_false_iff_ne]
              intro heq; exact hnd.1 (heq ▸ hmem)
            simp only [hne, Bool.false_eq_true, ↓reduceIte]
            rw [ih_in hmem]; omega
        · intro hnot
          have hne : (f a == k) = false := by
            rw [beq_eq_false_iff_ne]
            intro heq; exact hnot (by simp [heq])
          have hnot' : f a ∉ ks := fun h => hnot (by simp [h])
          rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, List.filter_cons]
          simp only [hne, Bool.false_eq_true, ↓reduceIte]
          rw [ih_out hnot']
    have hstep := (hinc (List.range m) List.nodup_range).1 (List.mem_range.mpr ha)
    rw [hstep, hih]; simp

theorem crown_circuit (n : ℕ) (hn : 4 ≤ n) :
    RepSizeAtMost (fun u v : Fin n => decide (u ≠ v)) (3 * n + 4 * (Nat.sqrt (n - 1) + 1) - 9) := by
  let c : ℕ := Nat.sqrt (n - 1) + 1
  let r : ℕ := (n + c - 1) / c
  have hsq_le : Nat.sqrt (n - 1) * Nat.sqrt (n - 1) ≤ n - 1 := Nat.sqrt_le (n - 1)
  have hsq_lt : n - 1 < c * c := Nat.lt_succ_sqrt (n - 1)
  have hc_ge2 : 2 ≤ c := by
    by_contra h
    have hs0 : Nat.sqrt (n - 1) = 0 := by omega
    have : c = 1 := by omega
    rw [this] at hsq_lt
    omega
  have hc_lt_n : c < n := by
    by_contra h
    have hle : n - 1 ≤ Nat.sqrt (n - 1) := by omega
    have hmul : (n - 1) * (n - 1) ≤ Nat.sqrt (n - 1) * Nat.sqrt (n - 1) :=
      Nat.mul_le_mul hle hle
    have hmul3 : 3 * (n - 1) ≤ (n - 1) * (n - 1) := Nat.mul_le_mul_right (n - 1) (by omega)
    omega
  have hr_ge2 : 2 ≤ r := by
    show 2 ≤ (n + c - 1) / c
    rw [Nat.le_div_iff_mul_le (by omega)]
    omega
  have hr_le_c : r ≤ c := by
    have hlt : (n + c - 1) / c < c + 1 := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]
      have hmul : (c + 1) * c = c * c + c := by rw [Nat.add_mul, Nat.one_mul]
      omega
    exact Nat.lt_succ_iff.mp hlt
  have hn_le_rc : n ≤ r * c := by
    have hdm : c * r + (n + c - 1) % c = n + c - 1 := Nat.div_add_mod (n + c - 1) c
    have hml : (n + c - 1) % c < c := Nat.mod_lt (n + c - 1) (by omega : 0 < c)
    have hcomm : c * r = r * c := Nat.mul_comm c r
    omega
  have hrow_lt : ∀ i < n, i / c < r := by
    intro i hi
    rw [Nat.div_lt_iff_lt_mul (by omega)]
    omega
  have hrow_ne : ∀ k < r, ∃ i < n, i / c = k := by
    intro k hk
    have hkc_lt : k * c < n := by
      by_contra hge
      have hle : (n + c - 1) / c < k + 1 := by
        rw [Nat.div_lt_iff_lt_mul (by omega)]
        have hmul : (k + 1) * c = k * c + c := by rw [Nat.add_mul, Nat.one_mul]
        omega
      omega
    exact ⟨k * c, hkc_lt, Nat.mul_div_cancel k (by omega)⟩
  have hcol_ne : ∀ j < c, ∃ i < n, i % c = j := by
    intro j hj
    exact ⟨j, by omega, Nat.mod_eq_of_lt hj⟩
  let gs1 := buildZ n n
  have hgs1_len : gs1.length = n := buildZ_length n n
  have hgs1_mono : isMono2 gs1 := buildZ_mono n n
  let rowGroups : List (List ℕ) :=
    (List.range r).map fun k => ((List.range n).filter fun i => i / c == k).map fun i => 2 * n + i
  let colGroups : List (List ℕ) :=
    (List.range c).map fun j => ((List.range n).filter fun i => i % c == j).map fun i => 2 * n + i
  have hrow_groups_ok : ∀ g ∈ rowGroups, g ≠ [] ∧ ∀ w ∈ g, w < 2 * n + gs1.length := by
    intro g hg
    simp only [rowGroups, List.mem_map, List.mem_range] at hg
    rcases hg with ⟨k, hk, rfl⟩
    obtain ⟨i0, hi0, hdiv0⟩ := hrow_ne k hk
    refine ⟨?_, ?_⟩
    · intro hemp
      have hmem : 2 * n + i0 ∈ ((List.range n).filter fun i => i / c == k).map fun i => 2 * n + i := by
        simp only [List.mem_map, List.mem_filter, List.mem_range, beq_iff_eq]
        exact ⟨i0, ⟨hi0, hdiv0⟩, rfl⟩
      rw [hemp] at hmem; cases hmem
    · intro w hw
      simp only [List.mem_map, List.mem_filter, List.mem_range] at hw
      rcases hw with ⟨i, ⟨hi, _⟩, rfl⟩
      omega
  let pRow := buildOrGroups (2 * n) gs1 rowGroups
  obtain ⟨⟨extR, heqR, hlenR⟩, hmR, hlenRw, hwR_lt, hevalR⟩ :=
    buildOrGroups_spec (2 * n) gs1 rowGroups hgs1_mono hrow_groups_ok
  have hcol_groups_ok : ∀ g ∈ colGroups, g ≠ [] ∧ ∀ w ∈ g, w < 2 * n + pRow.1.length := by
    intro g hg
    simp only [colGroups, List.mem_map, List.mem_range] at hg
    rcases hg with ⟨j, hj, rfl⟩
    obtain ⟨i0, hi0, hmod0⟩ := hcol_ne j hj
    refine ⟨?_, ?_⟩
    · intro hemp
      have hmem : 2 * n + i0 ∈ ((List.range n).filter fun i => i % c == j).map fun i => 2 * n + i := by
        simp only [List.mem_map, List.mem_filter, List.mem_range, beq_iff_eq]
        exact ⟨i0, ⟨hi0, hmod0⟩, rfl⟩
      rw [hemp] at hmem; cases hmem
    · intro w hw
      simp only [List.mem_map, List.mem_filter, List.mem_range] at hw
      rcases hw with ⟨i, ⟨hi, _⟩, rfl⟩
      have hpR : pRow.1 = gs1 ++ extR := heqR
      rw [hpR, List.length_append]; omega
  let pCol := buildOrGroups (2 * n) pRow.1 colGroups
  obtain ⟨⟨extC, heqC, hlenC⟩, hmC, hlenCw, hwC_lt, hevalC⟩ :=
    buildOrGroups_spec (2 * n) pRow.1 colGroups hmR hcol_groups_ok
  have hRw_len : pRow.2.length = r := by simpa [rowGroups] using hlenRw
  have hCw_len : pCol.2.length = c := by simpa [colGroups] using hlenCw
  have hRw_lt_pCol : ∀ w ∈ pRow.2, w < 2 * n + pCol.1.length := by
    intro w hw
    have hlt : w < 2 * n + pRow.1.length := hwR_lt w hw
    have hpC : pCol.1 = pRow.1 ++ extC := heqC
    rw [hpC, List.length_append]; omega
  let qRow := buildTh2 (2 * n) pCol.1 pRow.2
  obtain ⟨⟨extTR, heqTR, hlenTR⟩, hmTR, houtTR, hevalTR⟩ :=
    buildTh2_spec (2 * n) pCol.1 pRow.2 (by omega) hmC hRw_lt_pCol
  have hCw_lt_qRow : ∀ w ∈ pCol.2, w < 2 * n + qRow.1.length := by
    intro w hw
    have hlt : w < 2 * n + pCol.1.length := hwC_lt w hw
    have hqR : qRow.1 = pCol.1 ++ extTR := heqTR
    rw [hqR, List.length_append]; omega
  let qCol := buildTh2 (2 * n) qRow.1 pCol.2
  obtain ⟨⟨extTC, heqTC, hlenTC⟩, hmTC, houtTC, hevalTC⟩ :=
    buildTh2_spec (2 * n) qRow.1 pCol.2 (by omega) hmTR hCw_lt_qRow
  let finalGs := qCol.1 ++ [⟨GateOp.or, [qRow.2, qCol.2]⟩]
  let C : Circuit := ⟨finalGs, 2 * n + qCol.1.length⟩
  have hR_sum : (rowGroups.map fun g => g.length - 1).sum + r = n := by
    have h1 := sum_map_add_const rowGroups (fun g hg => Nat.pos_of_ne_zero (List.length_pos_iff.mpr (hrow_groups_ok g hg).1).ne')
    have h2 : (rowGroups.map List.length).sum = n := by
      have hs := sum_filter_range r (fun i => i / c) (List.range n) (fun x hx => hrow_lt x (List.mem_range.mp hx))
      simpa [rowGroups, List.map_map, Function.comp_def] using hs
    have h3 : rowGroups.length = r := by simp [rowGroups]
    omega
  have hC_sum : (colGroups.map fun g => g.length - 1).sum + c = n := by
    have h1 := sum_map_add_const colGroups (fun g hg => Nat.pos_of_ne_zero (List.length_pos_iff.mpr (hcol_groups_ok g hg).1).ne')
    have h2 : (colGroups.map List.length).sum = n := by
      have hs := sum_filter_range c (fun i => i % c) (List.range n) (fun x _ => Nat.mod_lt x (by omega))
      simpa [colGroups, List.map_map, Function.comp_def] using hs
    have h3 : colGroups.length = c := by simp [colGroups]
    omega
  have hmono_final : Monotone2 C := by
    have hm_f : isMono2 finalGs := isMono2_snoc hmTC (Or.inr rfl)
    intro g hg
    obtain ⟨h1, h2⟩ := hm_f g hg
    exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h1, h2⟩
  have hsize_final : C.size ≤ 3 * n + 4 * c - 9 := by
    show finalGs.length ≤ _
    have hlen_f : finalGs.length = qCol.1.length + 1 := by simp [finalGs]
    have hlen_qC : qCol.1.length = qRow.1.length + extTC.length := by
      rw [show qCol.1 = qRow.1 ++ extTC from heqTC, List.length_append]
    have hlen_qR : qRow.1.length = pCol.1.length + extTR.length := by
      rw [show qRow.1 = pCol.1 ++ extTR from heqTR, List.length_append]
    have hlen_pC : pCol.1.length = pRow.1.length + extC.length := by
      rw [show pCol.1 = pRow.1 ++ extC from heqC, List.length_append]
    have hlen_pR : pRow.1.length = gs1.length + extR.length := by
      rw [show pRow.1 = gs1 ++ extR from heqR, List.length_append]
    omega
  refine ⟨C, hmono_final, hsize_final, ?_⟩
  intro u v
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  change (evalWires finalGs (oneEach u v)).getD (2 * n + qCol.1.length) false = true ↔ u ≠ v
  have hlen_inp : (oneEach u v).length = 2 * n := oneEach_length u v
  have hidx_f : 2 * n + qCol.1.length = (oneEach u v).length + qCol.1.length := by omega
  rw [hidx_f, evalWires_snoc_last]
  simp only [List.map_cons, List.map_nil, gateOp_or_eval, Bool.or_eq_true]
  have hqRow_val : (evalWires qCol.1 (oneEach u v)).getD qRow.2 false = true ↔ u.val / c ≠ v.val / c := by
    have hqRow_lt : qRow.2 < 2 * n + qRow.1.length := houtTR
    rw [show qCol.1 = qRow.1 ++ extTC from heqTC,
        evalWires_append_getD_lt qRow.1 extTC (oneEach u v) (by omega),
        hevalTR (oneEach u v) hlen_inp]
    have hrow_k : ∀ k < r, (evalWires pCol.1 (oneEach u v)).getD (pRow.2.getD k 0) false = true ↔
        k = u.val / c ∨ k = v.val / c := by
      intro k hk
      have hwk_lt : pRow.2.getD k 0 < 2 * n + pRow.1.length := by
        have hmem : pRow.2.getD k 0 ∈ pRow.2 := by
          have hk' : k < pRow.2.length := by omega
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk', Option.getD_some]
          exact List.getElem_mem hk'
        exact hwR_lt _ hmem
      rw [show pCol.1 = pRow.1 ++ extC from heqC,
          evalWires_append_getD_lt pRow.1 extC (oneEach u v) (by omega),
          hevalR (oneEach u v) hlen_inp k (by simp [rowGroups]; exact hk)]
      have hgk : rowGroups.getD k [] = ((List.range n).filter fun i => i / c == k).map fun i => 2 * n + i := by
        simp [rowGroups, List.getD_eq_getElem?_getD, hk]
      rw [hgk]
      constructor
      · rintro ⟨w, hw, hwt⟩
        simp only [List.mem_map, List.mem_filter, List.mem_range, beq_iff_eq] at hw
        rcases hw with ⟨i, ⟨hi, hdiv⟩, rfl⟩
        have hzi := (buildZ_eval u v n (Nat.le_refl n) i hi).mp hwt
        rcases hzi with rfl | rfl <;> simp [hdiv]
      · rintro (rfl | rfl)
        · refine ⟨2 * n + u.val, ?_, (buildZ_eval u v n (Nat.le_refl n) u.val u.isLt).mpr (Or.inl rfl)⟩
          simp only [List.mem_map, List.mem_filter, List.mem_range, beq_iff_eq]
          exact ⟨u.val, ⟨u.isLt, rfl⟩, rfl⟩
        · refine ⟨2 * n + v.val, ?_, (buildZ_eval u v n (Nat.le_refl n) v.val v.isLt).mpr (Or.inr rfl)⟩
          simp only [List.mem_map, List.mem_filter, List.mem_range, beq_iff_eq]
          exact ⟨v.val, ⟨v.isLt, rfl⟩, rfl⟩
    constructor
    · rintro ⟨i, j, hij, hj, hi_ok, hj_ok⟩
      rw [hrow_k i (by omega)] at hi_ok
      rw [hrow_k j (by omega)] at hj_ok
      omega
    · intro hne
      have hu_lt : u.val / c < r := hrow_lt u.val u.isLt
      have hv_lt : v.val / c < r := hrow_lt v.val v.isLt
      rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
      · exact ⟨u.val / c, v.val / c, hlt, by omega,
          (hrow_k _ hu_lt).mpr (Or.inl rfl), (hrow_k _ hv_lt).mpr (Or.inr rfl)⟩
      · exact ⟨v.val / c, u.val / c, hgt, by omega,
          (hrow_k _ hv_lt).mpr (Or.inr rfl), (hrow_k _ hu_lt).mpr (Or.inl rfl)⟩
  have hqCol_val : (evalWires qCol.1 (oneEach u v)).getD qCol.2 false = true ↔ u.val % c ≠ v.val % c := by
    rw [hevalTC (oneEach u v) hlen_inp]
    have hcol_j : ∀ j < c, (evalWires qRow.1 (oneEach u v)).getD (pCol.2.getD j 0) false = true ↔
        j = u.val % c ∨ j = v.val % c := by
      intro j hj
      have hwj_lt : pCol.2.getD j 0 < 2 * n + pCol.1.length := by
        have hmem : pCol.2.getD j 0 ∈ pCol.2 := by
          have hj' : j < pCol.2.length := by omega
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj', Option.getD_some]
          exact List.getElem_mem hj'
        exact hwC_lt _ hmem
      rw [show qRow.1 = pCol.1 ++ extTR from heqTR,
          evalWires_append_getD_lt pCol.1 extTR (oneEach u v) (by omega),
          hevalC (oneEach u v) hlen_inp j (by simp [colGroups]; exact hj)]
      have hgj : colGroups.getD j [] = ((List.range n).filter fun i => i % c == j).map fun i => 2 * n + i := by
        simp [colGroups, List.getD_eq_getElem?_getD, hj]
      rw [hgj]
      constructor
      · rintro ⟨w, hw, hwt⟩
        simp only [List.mem_map, List.mem_filter, List.mem_range, beq_iff_eq] at hw
        rcases hw with ⟨i, ⟨hi, hmod⟩, rfl⟩
        rw [show pRow.1 = gs1 ++ extR from heqR,
            evalWires_append_getD_lt gs1 extR (oneEach u v) (by omega)] at hwt
        have hzi := (buildZ_eval u v n (Nat.le_refl n) i hi).mp hwt
        rcases hzi with rfl | rfl <;> simp [hmod]
      · rintro (rfl | rfl)
        · refine ⟨2 * n + u.val, ?_, ?_⟩
          · simp only [List.mem_map, List.mem_filter, List.mem_range, beq_iff_eq]
            exact ⟨u.val, ⟨u.isLt, rfl⟩, rfl⟩
          · rw [show pRow.1 = gs1 ++ extR from heqR,
                evalWires_append_getD_lt gs1 extR (oneEach u v) (by omega)]
            exact (buildZ_eval u v n (Nat.le_refl n) u.val u.isLt).mpr (Or.inl rfl)
        · refine ⟨2 * n + v.val, ?_, ?_⟩
          · simp only [List.mem_map, List.mem_filter, List.mem_range, beq_iff_eq]
            exact ⟨v.val, ⟨v.isLt, rfl⟩, rfl⟩
          · rw [show pRow.1 = gs1 ++ extR from heqR,
                evalWires_append_getD_lt gs1 extR (oneEach u v) (by omega)]
            exact (buildZ_eval u v n (Nat.le_refl n) v.val v.isLt).mpr (Or.inr rfl)
    constructor
    · rintro ⟨i, j, hij, hj, hi_ok, hj_ok⟩
      rw [hcol_j i (by omega)] at hi_ok
      rw [hcol_j j (by omega)] at hj_ok
      omega
    · intro hne
      have hu_lt : u.val % c < c := Nat.mod_lt u.val (by omega)
      have hv_lt : v.val % c < c := Nat.mod_lt v.val (by omega)
      rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
      · exact ⟨u.val % c, v.val % c, hlt, by omega,
          (hcol_j _ hu_lt).mpr (Or.inl rfl), (hcol_j _ hv_lt).mpr (Or.inr rfl)⟩
      · exact ⟨v.val % c, u.val % c, hgt, by omega,
          (hcol_j _ hv_lt).mpr (Or.inr rfl), (hcol_j _ hu_lt).mpr (Or.inl rfl)⟩
  rw [hqRow_val, hqCol_val]
  constructor
  · intro h hor
    subst hor
    rcases h with h | h <;> exact h rfl
  · intro hne
    by_contra h
    have hdiv : u.val / c = v.val / c := by
      by_contra hd; exact h (Or.inl hd)
    have hmod : u.val % c = v.val % c := by
      by_contra hm; exact h (Or.inr hm)
    have hval : u.val = v.val := by
      have hu := Nat.div_add_mod u.val c
      have hv := Nat.div_add_mod v.val c
      rw [hdiv, hmod] at hu
      omega
    exact hne (Fin.ext hval)

end PEqualNP.Outside.L_meta_19062

theorem PEqualNP.Outside.L_meta_19062 : ∀ n : ℕ, 4 ≤ n → PEqualNP.Represents.RepSizeAtMost (fun u v : Fin n => decide (u ≠ v)) (3 * n + 4 * (Nat.sqrt (n - 1) + 1) - 9) :=
  PEqualNP.Outside.L_meta_19062.crown_circuit
