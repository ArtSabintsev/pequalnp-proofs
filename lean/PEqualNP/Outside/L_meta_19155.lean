import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19155

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]

private theorem foldl_step_len (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, step, List.length_append, List.length_cons, List.length_nil]
    omega

private theorem getD_append_left {α : Type} (l₁ l₂ : List α) (d : α) (k : ℕ) (hk : k < l₁.length) :
    (l₁ ++ l₂).getD k d = l₁.getD k d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hk, List.getD_eq_getElem?_getD]

private theorem getD_append_self {α : Type} (l : List α) (v d : α) :
    (l ++ [v]).getD l.length d = v := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _)]
  simp

private theorem getD_oob {α : Type} (l : List α) (k : ℕ) (d : α) (hk : l.length ≤ k) :
    l.getD k d = d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hk]
  rfl

private theorem foldl_step_prefix (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < w.length) :
    (gs.foldl step w).getD k false = w.getD k false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have h1 : k < (step w g).length := by simp [step]; omega
    rw [ih (step w g) h1]
    exact getD_append_left w _ false k hk

private def skipList (n k : ℕ) : List ℕ :=
  List.range k ++ (List.range (n - 1 - k)).map (fun t => k + 1 + t)

private theorem skipList_length (n k : ℕ) (hk : k < n) : (skipList n k).length = n - 1 := by
  simp only [skipList, List.length_append, List.length_range, List.length_map]
  omega

private theorem mem_skipList (n k w : ℕ) (hk : k < n) : w ∈ skipList n k ↔ w < n ∧ w ≠ k := by
  simp only [skipList, List.mem_append, List.mem_range, List.mem_map]
  constructor
  · rintro (h | ⟨t, ht, rfl⟩) <;> omega
  · rintro ⟨hw, hne⟩
    by_cases hlt : w < k
    · exact Or.inl hlt
    · exact Or.inr ⟨w - (k + 1), by omega, by omega⟩

private def orChainAux (base acc : ℕ) : List ℕ → List Gate × ℕ
  | [] => ([], acc)
  | b :: rest =>
    let p := orChainAux (base + 1) base rest
    (⟨GateOp.or, [acc, b]⟩ :: p.1, p.2)

private theorem orChainAux_len (base acc : ℕ) (l : List ℕ) :
    (orChainAux base acc l).1.length = l.length := by
  induction l generalizing base acc with
  | nil => rfl
  | cons b rest ih => simp [orChainAux, ih]

private theorem orChainAux_mono (base acc : ℕ) (l : List ℕ) :
    ∀ g ∈ (orChainAux base acc l).1,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  induction l generalizing base acc with
  | nil => intro g hg; simp [orChainAux] at hg
  | cons b rest ih =>
    intro g hg
    simp only [orChainAux, List.mem_cons] at hg
    rcases hg with rfl | hg
    · exact ⟨Or.inr rfl, by simp⟩
    · exact ih (base + 1) base g hg

private theorem orChainAux_out_lt (base acc : ℕ) (l : List ℕ) (hacc : acc < base) :
    (orChainAux base acc l).2 < base + l.length := by
  induction l generalizing base acc with
  | nil => simp [orChainAux, hacc]
  | cons b rest ih =>
    have h := ih (base + 1) base (by omega)
    simp only [orChainAux, List.length_cons] at h ⊢
    omega

private theorem orChainAux_eval (acc : ℕ) (l : List ℕ) (w : List Bool)
    (hacc : acc < w.length) (hl : ∀ x ∈ l, x < w.length) :
    ((orChainAux w.length acc l).1.foldl step w).getD (orChainAux w.length acc l).2 false =
      (w.getD acc false || l.any (fun x => w.getD x false)) := by
  induction l generalizing acc w with
  | nil => simp [orChainAux]
  | cons b rest ih =>
    let w1 := step w ⟨GateOp.or, [acc, b]⟩
    have hw1len : w1.length = w.length + 1 := by simp [w1, step]
    have hrest_lt : ∀ x ∈ rest, x < w1.length := by
      intro x hx; have := hl x (by simp [hx]); omega
    have hih := ih w.length w1 (by omega) hrest_lt
    rw [hw1len] at hih
    change ((orChainAux (w.length + 1) w.length rest).1.foldl step w1).getD
      (orChainAux (w.length + 1) w.length rest).2 false = _
    rw [hih]
    have hhead : w1.getD w.length false = (w.getD acc false || w.getD b false) := by
      simp [w1, step, getD_append_self, GateOp.eval]
    have hrest : rest.any (fun x => w1.getD x false) = rest.any (fun x => w.getD x false) := by
      apply Bool.eq_iff_iff.mpr
      simp only [List.any_eq_true]
      constructor
      · rintro ⟨x, hx, hxw⟩
        refine ⟨x, hx, ?_⟩
        rwa [show w1.getD x false = w.getD x false from getD_append_left w _ false x (hl x (by simp [hx]))] at hxw
      · rintro ⟨x, hx, hxw⟩
        refine ⟨x, hx, ?_⟩
        rwa [show w1.getD x false = w.getD x false from getD_append_left w _ false x (hl x (by simp [hx]))]
    rw [hhead, hrest, List.any_cons, Bool.or_assoc]

private theorem getD_oneEach {n : ℕ} (u v : Fin n) (k : ℕ) :
    (oneEach u v).getD k false = (decide (k = u.val) || decide (k = n + v.val)) := by
  unfold oneEach
  by_cases h1 : k < n
  · rw [getD_append_left _ _ false k (by simp [h1]), List.getD_eq_getElem?_getD,
      List.getElem?_ofFn, dite_eq_left h1]
    simp only [Option.getD_some]
    have hne : k ≠ n + v.val := by omega
    simp [hne, Fin.ext_iff]
  · by_cases h2 : k < n + n
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp; omega)]
      simp only [List.length_ofFn, List.getElem?_ofFn]
      rw [dite_eq_left (by omega : k - n < n), Option.getD_some]
      have hne : k ≠ u.val := by omega
      simp only [hne, decide_false, Bool.false_or, Fin.ext_iff]
      apply decide_eq_decide.mpr
      omega
    · rw [getD_oob _ k false (by simp; omega)]
      have hne1 : k ≠ u.val := by omega
      have hne2 : k ≠ n + v.val := by omega
      simp [hne1, hne2]

private theorem upper_bound (n : ℕ) (i j : Fin n) (hn : 2 ≤ n) :
    RepSizeAtMost (fun u v : Fin n => decide (u ≠ i) && decide (v ≠ j)) (2 * n - 3) := by
  let rows := skipList n i.val
  let cols := (skipList n j.val).map (fun v => n + v)
  have hrlen : rows.length = n - 1 := skipList_length n i.val i.isLt
  have hclen : cols.length = n - 1 := by simp [cols, skipList_length n j.val j.isLt]
  cases hrows : rows with
  | nil => rw [hrows] at hrlen; simp at hrlen; omega
  | cons r0 rrest =>
    cases hcols : cols with
    | nil => rw [hcols] at hclen; simp at hclen; omega
    | cons c0 crest =>
      have hrrest_len : rrest.length = n - 2 := by rw [hrows] at hrlen; simp at hrlen; omega
      have hcrest_len : crest.length = n - 2 := by rw [hcols] at hclen; simp at hclen; omega
      let rC := orChainAux (2 * n) r0 rrest
      let cC := orChainAux (2 * n + rC.1.length) c0 crest
      let C : Circuit :=
        ⟨rC.1 ++ cC.1 ++ [⟨GateOp.and, [rC.2, cC.2]⟩], 2 * n + rC.1.length + cC.1.length⟩
      have hrb : ∀ x ∈ rows, x < 2 * n := by
        intro x hx; have := (mem_skipList n i.val x i.isLt).mp hx; omega
      have hcb : ∀ x ∈ cols, x < 2 * n + rC.1.length := by
        intro x hx
        simp only [cols, List.mem_map] at hx
        rcases hx with ⟨v, hv, rfl⟩
        have := (mem_skipList n j.val v j.isLt).mp hv
        omega
      have hr0lt : r0 < 2 * n := hrb r0 (by rw [hrows]; simp)
      have hrrest_lt : ∀ x ∈ rrest, x < 2 * n := fun x hx => hrb x (by rw [hrows]; simp [hx])
      have hc0lt : c0 < 2 * n + rC.1.length := hcb c0 (by rw [hcols]; simp)
      have hcrest_lt : ∀ x ∈ crest, x < 2 * n + rC.1.length :=
        fun x hx => hcb x (by rw [hcols]; simp [hx])
      have hrlt : rC.2 < 2 * n + rC.1.length := by
        have := orChainAux_out_lt (2 * n) r0 rrest hr0lt
        rw [orChainAux_len]
        exact this
      refine ⟨C, ?_, ?_, ?_⟩
      · intro g hg
        simp only [C, List.mem_append, List.mem_singleton] at hg
        rcases hg with (hg | hg) | rfl
        · exact orChainAux_mono (2 * n) r0 rrest g hg
        · exact orChainAux_mono (2 * n + rC.1.length) c0 crest g hg
        · exact ⟨Or.inl rfl, by simp⟩
      · change C.gates.length ≤ 2 * n - 3
        simp only [C, List.length_append, List.length_singleton]
        have h1 : rC.1.length = n - 2 := by rw [orChainAux_len, hrrest_len]
        have h2 : cC.1.length = n - 2 := by rw [orChainAux_len, hcrest_len]
        omega
      · intro u v
        let x := oneEach u v
        have hxlen : x.length = 2 * n := by simp [x, oneEach]; omega
        let w1 := rC.1.foldl step x
        have hw1len : w1.length = 2 * n + rC.1.length := by rw [foldl_step_len, hxlen]
        let w2 := cC.1.foldl step w1
        have hw2len : w2.length = 2 * n + rC.1.length + cC.1.length := by
          rw [foldl_step_len, hw1len]
        have hCeval : C.eval x = (w2.getD rC.2 false && w2.getD cC.2 false) := by
          change ((rC.1 ++ cC.1 ++ [({ op := GateOp.and, inputs := [rC.2, cC.2] } : Gate)]).foldl step x).getD
            (2 * n + rC.1.length + cC.1.length) false = _
          rw [List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil]
          change (step w2 { op := GateOp.and, inputs := [rC.2, cC.2] }).getD
            (2 * n + rC.1.length + cC.1.length) false = _
          rw [← hw2len]
          simp [step, getD_append_self, GateOp.eval]
        rw [hCeval]
        have hrval : w1.getD rC.2 false = decide (u ≠ i) := by
          have he := orChainAux_eval r0 rrest x (by rw [hxlen]; exact hr0lt)
            (fun k hk => by rw [hxlen]; exact hrrest_lt k hk)
          rw [hxlen] at he
          change w1.getD rC.2 false = _
          rw [he]
          have hany : (x.getD r0 false || rrest.any fun k => x.getD k false) =
              rows.any (fun k => x.getD k false) := by rw [hrows, List.any_cons]
          rw [hany]
          apply Bool.eq_iff_iff.mpr
          simp only [List.any_eq_true, decide_eq_true_eq, ne_eq]
          constructor
          · rintro ⟨k, hk, hkx⟩
            have hklt := (mem_skipList n i.val k i.isLt).mp hk
            rw [getD_oneEach] at hkx
            simp only [Bool.or_eq_true, decide_eq_true_eq] at hkx
            rcases hkx with rfl | hbad
            · intro heq; exact hklt.2 (congrArg Fin.val heq)
            · omega
          · intro hne
            refine ⟨u.val, (mem_skipList n i.val u.val i.isLt).mpr ⟨u.isLt, fun h => hne (Fin.ext h)⟩, ?_⟩
            rw [getD_oneEach]
            simp
        have hrval2 : w2.getD rC.2 false = decide (u ≠ i) := by
          rw [foldl_step_prefix cC.1 w1 rC.2 (by omega), hrval]
        have hcval : w2.getD cC.2 false = decide (v ≠ j) := by
          have he := orChainAux_eval c0 crest w1 (by rw [hw1len]; exact hc0lt)
            (fun k hk => by rw [hw1len]; exact hcrest_lt k hk)
          rw [hw1len] at he
          change w2.getD cC.2 false = _
          rw [he]
          have hany : (w1.getD c0 false || crest.any fun k => w1.getD k false) =
              cols.any (fun k => w1.getD k false) := by rw [hcols, List.any_cons]
          rw [hany]
          apply Bool.eq_iff_iff.mpr
          simp only [List.any_eq_true, decide_eq_true_eq, ne_eq]
          constructor
          · rintro ⟨k, hk, hkw⟩
            simp only [cols, List.mem_map] at hk
            rcases hk with ⟨t, ht, rfl⟩
            have htlt := (mem_skipList n j.val t j.isLt).mp ht
            rw [foldl_step_prefix rC.1 x (n + t) (by omega), getD_oneEach] at hkw
            simp only [Bool.or_eq_true, decide_eq_true_eq] at hkw
            rcases hkw with hbad | heq
            · omega
            · intro hveq; exact htlt.2 (by have := congrArg Fin.val hveq; omega)
          · intro hne
            refine ⟨n + v.val, List.mem_map.mpr ⟨v.val, (mem_skipList n j.val v.val j.isLt).mpr
              ⟨v.isLt, fun h => hne (Fin.ext h)⟩, rfl⟩, ?_⟩
            rw [foldl_step_prefix rC.1 x (n + v.val) (by omega), getD_oneEach]
            simp
        rw [hrval2, hcval]

private def coneStep (cs : List (Finset ℕ)) (g : Gate) : List (Finset ℕ) :=
  cs ++ [insert cs.length (g.inputs.foldl (fun acc w => if w < cs.length then acc ∪ cs.getD w ∅ else acc) ∅)]

private def wireCones (N : ℕ) (gs : List Gate) : List (Finset ℕ) :=
  gs.foldl coneStep ((List.range N).map fun k => {k})

private theorem foldl_coneStep_len (gs : List Gate) (cs : List (Finset ℕ)) :
    (gs.foldl coneStep cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, coneStep, List.length_append, List.length_cons, List.length_nil]
    omega

private theorem foldl_union_mem (l : List ℕ) (f : ℕ → Finset ℕ) (init : Finset ℕ) (x : ℕ) :
    x ∈ l.foldl (fun acc w => acc ∪ f w) init ↔ x ∈ init ∨ ∃ w ∈ l, x ∈ f w := by
  induction l generalizing init with
  | nil => simp
  | cons a t ih =>
    simp only [List.foldl_cons, ih, Finset.mem_union, List.mem_cons]
    constructor
    · rintro ((h | h) | ⟨w, hw, hxw⟩)
      · exact Or.inl h
      · exact Or.inr ⟨a, Or.inl rfl, h⟩
      · exact Or.inr ⟨w, Or.inr hw, hxw⟩
    · rintro (h | ⟨w, rfl | hw, hxw⟩)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr hxw)
      · exact Or.inr ⟨w, hw, hxw⟩

private theorem cone_bound_and_cover (N : ℕ) (gs : List Gate) :
    ∀ w : ℕ,
      (∀ x ∈ (wireCones N gs).getD w ∅, x < N + gs.length) ∧
      (∀ x ∈ (wireCones N gs).getD w ∅, x ≠ w →
        ∃ j < gs.length, N + j ∈ (wireCones N gs).getD w ∅ ∧ x ∈ (gs.getD j ⟨GateOp.and, []⟩).inputs) := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro w
    simp only [wireCones, List.foldl_nil, List.length_nil, Nat.add_zero]
    by_cases hw : w < N
    · have hget : ((List.range N).map (fun k => ({k} : Finset ℕ))).getD w ∅ = {w} := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hw]
        rfl
      rw [hget]
      refine ⟨fun x hx => by simp at hx; omega, fun x hx hne => by simp at hx; exact absurd hx hne⟩
    · rw [getD_oob _ w ∅ (by simp; omega)]
      exact ⟨fun _ hx => by simp at hx, fun _ hx _ => by simp at hx⟩
  | append_singleton gs g ih =>
    let cs := wireCones N gs
    have hcslen : cs.length = N + gs.length := by
      simp [cs, wireCones, foldl_coneStep_len]
    have hwc : wireCones N (gs ++ [g]) = coneStep cs g := by
      simp [wireCones, cs, List.foldl_append]
    intro w
    rw [hwc]
    by_cases hlt : w < cs.length
    · rw [coneStep, getD_append_left cs _ ∅ w hlt]
      have ⟨hb, hc⟩ := ih w
      refine ⟨fun x hx => by have := hb x hx; simp; omega, fun x hx hne => ?_⟩
      obtain ⟨j, hj, hmem, hin⟩ := hc x hx hne
      refine ⟨j, by simp; omega, hmem, ?_⟩
      rwa [getD_append_left gs [g] _ j hj]
    · by_cases heq : w = cs.length
      · subst heq
        rw [coneStep, getD_append_self]
        have hmem_iff : ∀ x, x ∈ insert cs.length
            (g.inputs.foldl (fun acc u => if u < cs.length then acc ∪ cs.getD u ∅ else acc) ∅) ↔
            x = cs.length ∨ ∃ u ∈ g.inputs, u < cs.length ∧ x ∈ cs.getD u ∅ := by
          intro x
          have hfl : g.inputs.foldl (fun acc u => if u < cs.length then acc ∪ cs.getD u ∅ else acc) ∅ =
              g.inputs.foldl (fun acc u => acc ∪ (if u < cs.length then cs.getD u ∅ else ∅)) ∅ := by
            congr 1; funext acc u; split_ifs <;> simp
          rw [Finset.mem_insert, hfl, foldl_union_mem]
          simp only [Finset.notMem_empty, false_or]
          constructor
          · rintro (rfl | ⟨u, hu, hxu⟩)
            · exact Or.inl rfl
            · split_ifs at hxu with hult
              · exact Or.inr ⟨u, hu, hult, hxu⟩
              · simp at hxu
          · rintro (rfl | ⟨u, hu, hult, hxu⟩)
            · exact Or.inl rfl
            · exact Or.inr ⟨u, hu, by rw [if_pos hult]; exact hxu⟩
        refine ⟨?_, ?_⟩
        · intro x hx
          rcases (hmem_iff x).mp hx with rfl | ⟨u, _, _, hxu⟩
          · simp; omega
          · have := (ih u).1 x hxu; simp; omega
        · intro x hx hne
          rcases (hmem_iff x).mp hx with rfl | ⟨u, hu, hult, hxu⟩
          · exact absurd rfl hne
          · by_cases hxu_eq : x = u
            · subst hxu_eq
              refine ⟨gs.length, by simp, ?_, ?_⟩
              · rw [← hcslen]; exact (hmem_iff cs.length).mpr (Or.inl rfl)
              · rw [getD_append_self]; exact hu
            · obtain ⟨j, hj, hjm, hxin⟩ := (ih u).2 x hxu hxu_eq
              refine ⟨j, by simp; omega, (hmem_iff (N + j)).mpr (Or.inr ⟨u, hu, hult, hjm⟩), ?_⟩
              rwa [getD_append_left gs [g] _ j hj]
      · rw [getD_oob _ w ∅ (by simp [coneStep]; omega)]
        exact ⟨fun _ hx => by simp at hx, fun _ hx _ => by simp at hx⟩

private theorem eval_gate_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l₁ l₂ : List Bool) (h : List.Forall₂ (fun a b => a = true → b = true) l₁ l₂) :
    op.eval l₁ = true → op.eval l₂ = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval]
    induction h with
    | nil => intro _; rfl
    | cons hu _ ih =>
      simp only [List.all_cons, id_eq, Bool.and_eq_true]
      intro ha; exact ⟨hu ha.1, ih ha.2⟩
  · simp only [GateOp.eval]
    induction h with
    | nil => intro hf; exact hf
    | cons hu _ ih =>
      simp only [List.any_cons, id_eq, Bool.or_eq_true]
      rintro (ha | ha)
      · exact Or.inl (hu ha)
      · exact Or.inr (ih ha)

private theorem cone_mono (N : ℕ) (gs : List Gate)
    (hmono : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : List Bool) (hx : x.length = N) (hy : y.length = N) :
    ∀ w : ℕ,
      (∀ k ∈ (wireCones N gs).getD w ∅, k < N → x.getD k false = true → y.getD k false = true) →
      (gs.foldl step x).getD w false = true → (gs.foldl step y).getD w false = true := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro w hagree hxw
    simp only [List.foldl_nil] at hxw ⊢
    by_cases hw : w < N
    · have hget : (wireCones N []).getD w ∅ = {w} := by
        simp only [wireCones, List.foldl_nil]
        rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hw]; rfl
      exact hagree w (by rw [hget]; simp) hw hxw
    · rw [getD_oob x w false (by omega)] at hxw
      exact absurd hxw (by decide)
  | append_singleton gs g ih =>
    have hmono' : ∀ g' ∈ gs, g'.op = GateOp.and ∨ g'.op = GateOp.or :=
      fun g' hg' => hmono g' (by simp [hg'])
    have hgmono : g.op = GateOp.and ∨ g.op = GateOp.or := hmono g (by simp)
    let cs := wireCones N gs
    have hcslen : cs.length = N + gs.length := by simp [cs, wireCones, foldl_coneStep_len]
    have hwc : wireCones N (gs ++ [g]) = coneStep cs g := by
      simp [wireCones, cs, List.foldl_append]
    let wx := gs.foldl step x
    let wy := gs.foldl step y
    have hwxlen : wx.length = N + gs.length := by rw [foldl_step_len, hx]
    have hwylen : wy.length = N + gs.length := by rw [foldl_step_len, hy]
    intro w hagree hxw
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil] at hxw ⊢
    change (step wx g).getD w false = true at hxw
    change (step wy g).getD w false = true
    by_cases hlt : w < N + gs.length
    · rw [hwc, coneStep, getD_append_left cs _ ∅ w (by omega)] at hagree
      rw [step, getD_append_left wx _ false w (by omega)] at hxw
      rw [step, getD_append_left wy _ false w (by omega)]
      exact ih hmono' w hagree hxw
    · by_cases heq : w = N + gs.length
      · subst heq
        rw [← hwxlen] at hxw
        rw [← hwylen]
        simp only [step, getD_append_self] at hxw ⊢
        apply eval_gate_mono g.op hgmono _ _ _ hxw
        rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]
        intro u hu
        by_cases hult : u < N + gs.length
        · apply ih hmono' u
          intro k hk hkN hxk
          apply hagree k _ hkN hxk
          rw [hwc, ← hcslen, coneStep, getD_append_self]
          have hfl : g.inputs.foldl (fun acc v => if v < cs.length then acc ∪ cs.getD v ∅ else acc) ∅ =
              g.inputs.foldl (fun acc v => acc ∪ (if v < cs.length then cs.getD v ∅ else ∅)) ∅ := by
            congr 1; funext acc v; split_ifs <;> simp
          rw [Finset.mem_insert, hfl, foldl_union_mem]
          refine Or.inr (Or.inr ⟨u, hu, ?_⟩)
          rw [if_pos (by omega)]
          exact hk
        · intro hbad
          rw [getD_oob wx u false (by omega)] at hbad
          exact absurd hbad (by decide)
      · rw [getD_oob (step wx g) w false (by simp [step]; omega)] at hxw
        exact absurd hxw (by decide)

private theorem cone_inputs_card_le (N : ℕ) (C : Circuit) (hmono : Monotone2 C) :
    (((wireCones N C.gates).getD C.output ∅).filter (· < N)).card ≤ C.size + 1 := by
  let W := (wireCones N C.gates).getD C.output ∅
  let I := W.filter (· < N)
  let G := W.filter (fun w => ¬ w < N)
  have hdisj : Disjoint I G := Finset.disjoint_filter.mpr (fun _ _ h1 h2 => h2 h1)
  have hunion : I ∪ G = W := by
    ext x; simp only [I, G, Finset.mem_union, Finset.mem_filter]; tauto
  have hWcard : W.card = I.card + G.card := by
    rw [← hunion, Finset.card_union_of_disjoint hdisj]
  have ⟨hWlt, hWcov⟩ := cone_bound_and_cover N C.gates C.output
  have hGsub : G ⊆ Finset.Ico N (N + C.gates.length) := by
    intro x hx
    simp only [G, Finset.mem_filter, Finset.mem_Ico] at hx ⊢
    exact ⟨Nat.le_of_not_lt hx.2, hWlt x hx.1⟩
  have hGle : G.card ≤ C.gates.length := by
    have := Finset.card_le_card hGsub
    simp only [Nat.card_Ico, Nat.add_sub_cancel_left] at this
    exact this
  have herase_sub : W.erase C.output ⊆
      G.biUnion (fun w => (C.gates.getD (w - N) ⟨GateOp.and, []⟩).inputs.toFinset) := by
    intro x hx
    rw [Finset.mem_erase] at hx
    obtain ⟨j, hj, hjm, hxin⟩ := hWcov x hx.2 hx.1
    rw [Finset.mem_biUnion]
    refine ⟨N + j, Finset.mem_filter.mpr ⟨hjm, by omega⟩, ?_⟩
    simpa [Nat.add_sub_cancel_left] using hxin
  have hbi_le : (G.biUnion (fun w => (C.gates.getD (w - N) ⟨GateOp.and, []⟩).inputs.toFinset)).card ≤
      2 * G.card := by
    calc (G.biUnion _).card
        ≤ ∑ w ∈ G, ((C.gates.getD (w - N) ⟨GateOp.and, []⟩).inputs.toFinset).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _w ∈ G, 2 := by
          apply Finset.sum_le_sum
          intro w hw
          have hlt : w - N < C.gates.length := by
            have := Finset.mem_Ico.mp (hGsub hw); omega
          have hmem : C.gates.getD (w - N) ⟨GateOp.and, []⟩ ∈ C.gates := by
            rw [List.getD_eq_getElem _ _ hlt]; exact List.getElem_mem hlt
          exact le_trans (List.toFinset_card_le _) (hmono _ hmem).2
      _ = 2 * G.card := by simp [Nat.mul_comm]
  have herase_ge : W.card - 1 ≤ (W.erase C.output).card := Finset.pred_card_le_card_erase
  have h1 : W.card - 1 ≤ 2 * G.card := le_trans herase_ge (le_trans (Finset.card_le_card herase_sub) hbi_le)
  change I.card ≤ C.gates.length + 1
  omega

private theorem lower_bound (n : ℕ) (i j : Fin n) (hn : 2 ≤ n) :
    ¬ RepSizeAtMost (fun u v : Fin n => decide (u ≠ i) && decide (v ≠ j)) (2 * n - 4) := by
  rintro ⟨C, hmono, hsize, hrep⟩
  let N := 2 * n
  let W := (wireCones N C.gates).getD C.output ∅
  let I := W.filter (· < N)
  have hcard : I.card ≤ C.size + 1 := cone_inputs_card_le N C hmono
  have hmono_op : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or :=
    fun g hg => (hmono g hg).1
  have hne_i : ∃ u0 : Fin n, u0 ≠ i := by
    by_cases h0 : (⟨0, by omega⟩ : Fin n) = i
    · refine ⟨⟨1, by omega⟩, fun heq => ?_⟩
      have hval := congrArg Fin.val (heq.trans h0.symm)
      simp at hval
    · exact ⟨⟨0, by omega⟩, h0⟩
  have hne_j : ∃ v0 : Fin n, v0 ≠ j := by
    by_cases h0 : (⟨0, by omega⟩ : Fin n) = j
    · refine ⟨⟨1, by omega⟩, fun heq => ?_⟩
      have hval := congrArg Fin.val (heq.trans h0.symm)
      simp at hval
    · exact ⟨⟨0, by omega⟩, h0⟩
  obtain ⟨u0, hu0⟩ := hne_i
  obtain ⟨v0, hv0⟩ := hne_j
  have hrow_in : ∀ u : Fin n, u ≠ i → u.val ∈ I := by
    intro u hu
    by_contra hnot
    have hnotW : u.val ∉ W := fun h => hnot (Finset.mem_filter.mpr ⟨h, by omega⟩)
    have htrue : C.eval (oneEach u v0) = true := by rw [hrep u v0]; simp [hu, hv0]
    have hfalse : C.eval (oneEach i v0) = false := by rw [hrep i v0]; simp
    have hstep := cone_mono N C.gates hmono_op (oneEach u v0) (oneEach i v0)
      (by simp [oneEach, N]; omega) (by simp [oneEach, N]; omega) C.output
      (fun k hk _ hxk => by
        rw [getD_oneEach] at hxk ⊢
        simp only [Bool.or_eq_true, decide_eq_true_eq] at hxk ⊢
        rcases hxk with rfl | rfl
        · exact absurd hk hnotW
        · exact Or.inr rfl)
      htrue
    change C.eval (oneEach i v0) = true at hstep
    rw [hfalse] at hstep
    exact absurd hstep (by decide)
  have hcol_in : ∀ v : Fin n, v ≠ j → n + v.val ∈ I := by
    intro v hv
    by_contra hnot
    have hnotW : n + v.val ∉ W := fun h => hnot (Finset.mem_filter.mpr ⟨h, by omega⟩)
    have htrue : C.eval (oneEach u0 v) = true := by rw [hrep u0 v]; simp [hu0, hv]
    have hfalse : C.eval (oneEach u0 j) = false := by rw [hrep u0 j]; simp
    have hstep := cone_mono N C.gates hmono_op (oneEach u0 v) (oneEach u0 j)
      (by simp [oneEach, N]; omega) (by simp [oneEach, N]; omega) C.output
      (fun k hk _ hxk => by
        rw [getD_oneEach] at hxk ⊢
        simp only [Bool.or_eq_true, decide_eq_true_eq] at hxk ⊢
        rcases hxk with rfl | rfl
        · exact Or.inl rfl
        · exact absurd hk hnotW)
      htrue
    change C.eval (oneEach u0 j) = true at hstep
    rw [hfalse] at hstep
    exact absurd hstep (by decide)
  let R : Finset ℕ := (Finset.univ.erase i).image Fin.val
  let K : Finset ℕ := (Finset.univ.erase j).image (fun v : Fin n => n + v.val)
  have hRsub : R ⊆ I := by
    intro x hx
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
    exact hrow_in u (Finset.mem_erase.mp hu).1
  have hKsub : K ⊆ I := by
    intro x hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
    exact hcol_in v (Finset.mem_erase.mp hv).1
  have hRKdisj : Disjoint R K := by
    rw [Finset.disjoint_left]
    intro x hxR hxK
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hxR
    obtain ⟨v, _, hv⟩ := Finset.mem_image.mp hxK
    omega
  have hRcard : R.card = n - 1 := by
    rw [Finset.card_image_of_injective _ Fin.val_injective,
      Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
  have hKcard : K.card = n - 1 := by
    have hinj : Function.Injective (fun v : Fin n => n + v.val) :=
      fun a b h => Fin.ext (Nat.add_left_cancel h)
    rw [Finset.card_image_of_injective _ hinj,
      Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin]
  have hIge : 2 * n - 2 ≤ I.card := by
    have hsub : R ∪ K ⊆ I := Finset.union_subset hRsub hKsub
    have hle := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hRKdisj, hRcard, hKcard] at hle
    omega
  omega

end PEqualNP.Outside.L_meta_19155

theorem PEqualNP.Outside.L_meta_19155 : (∀ (n : ℕ) (i j : Fin n), 2 ≤ n → PEqualNP.Represents.RepSizeAtMost (fun u v : Fin n => decide (u ≠ i) && decide (v ≠ j)) (2 * n - 3) ∧ ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin n => decide (u ≠ i) && decide (v ≠ j)) (2 * n - 4)) :=
  fun n i j hn => ⟨PEqualNP.Outside.L_meta_19155.upper_bound n i j hn, PEqualNP.Outside.L_meta_19155.lower_bound n i j hn⟩
