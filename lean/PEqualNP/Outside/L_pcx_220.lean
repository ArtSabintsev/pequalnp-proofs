import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.L_clb_049

namespace PEqualNP.Outside.L_pcx_220_aux

namespace GateBridge

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (FanInTwo)
open PEqualNP.MetaComplexity.NestedCover (ReadsBack)

variable {α : Type*}

private def Scheduled (n : Nat) (F : α → (Fin n → Bool) → Bool) (k : Nat) (S : Set α) : Prop :=
  ∃ gs : List Gate, gs.length = k ∧ ReadsBack n ⟨gs, 0⟩ ∧ FanInTwo ⟨gs, 0⟩ ∧
    ∀ a ∈ S, ∃ i : Nat, i < n + k ∧
      ∀ x : Fin n → Bool, ((Circuit.mk gs 0).wires (List.ofFn x)).getD i false = F a x

private theorem wireLength (C : Circuit) (w : List Bool) :
    (C.wires w).length = w.length + C.gates.length := by
  rcases C with ⟨gs, out⟩
  change (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    w).length = w.length + gs.length
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

private theorem start {n : Nat} {F : α → (Fin n → Bool) → Bool}
    (input : Fin n → α) (h : ∀ i x, F (input i) x = x i) :
    Scheduled n F 0 (Set.range input) := by
  refine ⟨[], rfl, ?_, ?_, ?_⟩
  · simp [ReadsBack]
  · simp [FanInTwo]
  · intro a ha
    obtain ⟨i, rfl⟩ := Set.mem_range.mp ha
    refine ⟨i.val, by simp, fun x => ?_⟩
    change (List.ofFn x).getD i.val false = F (input i) x
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn, h i x]

private theorem restrict {n k : Nat} {F : α → (Fin n → Bool) → Bool} {S T : Set α}
    (h : Scheduled n F k S) (hsub : T ⊆ S) : Scheduled n F k T := by
  obtain ⟨gs, hs, hr, hf, hw⟩ := h
  exact ⟨gs, hs, hr, hf, fun a ha => hw a (hsub ha)⟩

private theorem realizeDeps {n k : Nat} {F : α → (Fin n → Bool) → Bool} {S : Set α}
    {gs : List Gate}
    (hw : ∀ a ∈ S, ∃ i : Nat, i < n + k ∧
      ∀ x : Fin n → Bool, ((Circuit.mk gs 0).wires (List.ofFn x)).getD i false = F a x)
    (deps : List α) (hdeps : ∀ a ∈ deps, a ∈ S) :
    ∃ is : List Nat, is.length = deps.length ∧ (∀ i ∈ is, i < n + k) ∧
      ∀ x : Fin n → Bool,
        is.map (fun i => ((Circuit.mk gs 0).wires (List.ofFn x)).getD i false) =
          deps.map (fun a => F a x) := by
  induction deps with
  | nil => exact ⟨[], rfl, by simp, by simp⟩
  | cons a deps ih =>
    obtain ⟨i, hi, hval⟩ := hw a (hdeps a List.mem_cons_self)
    obtain ⟨is, hlen, hbound, hvals⟩ := ih (fun b hb => hdeps b (List.mem_cons_of_mem a hb))
    refine ⟨i :: is, by simp [hlen], ?_, fun x => ?_⟩
    · intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · exact hi
      · exact hbound j hj
    · simp only [List.map_cons, hval x, hvals x]

private theorem push {n k : Nat} {F : α → (Fin n → Bool) → Bool} {S : Set α}
    (h : Scheduled n F k S) (op : GateOp) (deps : List α) (out : α)
    (hop : op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hlen : deps.length ≤ 2) (hdeps : ∀ a ∈ deps, a ∈ S)
    (hval : ∀ x, F out x = op.eval (deps.map fun a => F a x)) :
    Scheduled n F (k + 1) (insert out S) := by
  obtain ⟨gs, hgs, hr, hf, hw⟩ := h
  obtain ⟨is, his, hbound, hvalues⟩ := realizeDeps hw deps hdeps
  let g : Gate := ⟨op, is⟩
  have hlength (x : Fin n → Bool) :
      ((Circuit.mk gs 0).wires (List.ofFn x)).length = n + k := by
    rw [wireLength]
    simpa using congrArg (n + ·) hgs
  have hsnoc (x : Fin n → Bool) :
      (Circuit.mk (gs ++ [g]) 0).wires (List.ofFn x) =
        (Circuit.mk gs 0).wires (List.ofFn x) ++ [F out x] := by
    simp only [Circuit.wires, List.foldl_append, List.foldl_cons, List.foldl_nil]
    change (Circuit.mk gs 0).wires (List.ofFn x) ++
      [op.eval (is.map fun i => ((Circuit.mk gs 0).wires (List.ofFn x)).getD i false)] =
        (Circuit.mk gs 0).wires (List.ofFn x) ++ [F out x]
    rw [hvalues x, hval x]
  refine ⟨gs ++ [g], by simp [hgs], ?_, ?_, ?_⟩
  · intro j hj i hi
    change j < (gs ++ [g]).length at hj
    change i ∈ ((gs ++ [g]).getD j ⟨GateOp.or, []⟩).inputs at hi
    by_cases hj' : j < gs.length
    · rw [List.getD_append _ _ _ _ hj'] at hi
      exact hr j hj' i hi
    · have heq : j = gs.length := by
        simp only [List.length_append, List.length_singleton] at hj
        omega
      subst j
      rw [List.getD_append_right _ _ _ _ le_rfl] at hi
      have hi' : i ∈ is := by simpa [g] using hi
      simpa [hgs] using hbound i hi'
  · intro g' hg'
    change g' ∈ gs ++ [g] at hg'
    rcases List.mem_append.mp hg' with hg' | hg'
    · exact hf g' hg'
    · have heq : g' = g := List.mem_singleton.mp hg'
      subst g'
      refine ⟨hop, ?_⟩
      change is.length ≤ 2
      simpa only [his] using hlen
  · intro a ha
    rcases Set.mem_insert_iff.mp ha with rfl | ha
    · refine ⟨n + k, by omega, fun x => ?_⟩
      rw [hsnoc x, List.getD_append_right _ _ _ _ (by simp [hlength x])]
      simp [hlength x]
    · obtain ⟨i, hi, hval'⟩ := hw a ha
      refine ⟨i, by omega, fun x => ?_⟩
      rw [hsnoc x, List.getD_append _ _ _ _ (by simpa [hlength x] using hi), hval' x]

end GateBridge

namespace Build220

open PEqualNP.CircuitLowerBounds

variable {n : Nat}
private abbrev Sig (n : Nat) := (Fin n → Bool) → Bool

private def Build (A B : Set (Sig n)) (b : Nat) : Prop :=
  True ∧ (∀ {m S}, GateBridge.Scheduled n id m S → A ⊆ S →
    ∃ c ≤ b, GateBridge.Scheduled n id (m + c) (S ∪ B))

private theorem Build.run {A B : Set (Sig n)} {b m S} (H : Build A B b)
    (HS : GateBridge.Scheduled n id m S) (hA : A ⊆ S) :
    ∃ c ≤ b, GateBridge.Scheduled n id (m + c) (S ∪ B) := H.2 HS hA

private theorem idle {A B : Set (Sig n)} (h : B ⊆ A) : Build A B 0 := by
  refine ⟨trivial, ?_⟩
  intro m S HS hA
  refine ⟨0, Nat.le_refl _, ?_⟩
  simpa [Set.union_eq_left.mpr (h.trans hA)] using HS

private theorem relax {A B C D : Set (Sig n)} {b d : Nat}
    (H : Build A B b) (hA : A ⊆ C) (hB : D ⊆ B) (h : b ≤ d) : Build C D d := by
  refine ⟨trivial, ?_⟩
  intro m S HS hC
  obtain ⟨c, hc, HS'⟩ := H.run HS (hA.trans hC)
  exact ⟨c, hc.trans h, GateBridge.restrict HS' (Set.union_subset_union le_rfl hB)⟩

private theorem seq {A B C : Set (Sig n)} {b c : Nat}
    (H : Build A B b) (J : Build (A ∪ B) C c) : Build A (B ∪ C) (b + c) := by
  refine ⟨trivial, ?_⟩
  intro m S HS hA
  obtain ⟨d, hd, K⟩ := H.run HS hA
  obtain ⟨e, he, K'⟩ := J.run K (Set.union_subset_union hA le_rfl)
  exact ⟨d + e, Nat.add_le_add hd he, by simpa [Nat.add_assoc, Set.union_assoc] using K'⟩

private theorem one {A : Set (Sig n)} (op : GateOp) (deps : List (Sig n))
    (hop : op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) (hlen : deps.length ≤ 2)
    (hd : ∀ g ∈ deps, g ∈ A) (f : Sig n)
    (hv : ∀ x, f x = op.eval (deps.map fun g => g x)) : Build A {f} 1 := by
  refine ⟨trivial, ?_⟩
  intro m S HS hA
  refine ⟨1, le_rfl, ?_⟩
  have h := GateBridge.push HS op deps f hop hlen (fun g hg => hA (hd g hg)) hv
  rw [Set.insert_eq] at h
  exact GateBridge.restrict h (by intro g hg; exact hg.elim Or.inr Or.inl)

private def an (f g : Sig n) : Sig n := fun x => f x && g x
private def or (f g : Sig n) : Sig n := fun x => f x || g x
private def nt (f : Sig n) : Sig n := fun x => !f x

private theorem andG {A : Set (Sig n)} {f g : Sig n} (hf : f ∈ A) (hg : g ∈ A) :
    Build A {an f g} 1 :=
  one .and [f, g] (by simp) (by simp) (by simpa using And.intro hf hg) _ (by simp [GateOp.eval, an])

private theorem orG {A : Set (Sig n)} {f g : Sig n} (hf : f ∈ A) (hg : g ∈ A) :
    Build A {or f g} 1 :=
  one .or [f, g] (by simp) (by simp) (by simpa using And.intro hf hg) _ (by simp [GateOp.eval, or])

private theorem notG {A : Set (Sig n)} {f : Sig n} (hf : f ∈ A) : Build A {nt f} 1 :=
  one .not [f] (by simp) (by simp) (by simpa using hf) _ (by simp [GateOp.eval, nt])

private theorem constG {A : Set (Sig n)} (b : Bool) : Build A {fun _ => b} 1 := by
  cases b
  · exact one .or [] (by simp) (by simp) (by simp) _ (by intro; rfl)
  · exact one .and [] (by simp) (by simp) (by simp) _ (by intro; rfl)

private theorem muxG {A : Set (Sig n)} {sw nsw t f : Sig n}
    (hsw : sw ∈ A) (hnsw : nsw ∈ A) (ht : t ∈ A) (hf : f ∈ A)
    (hneg : ∀ x, nsw x = !(sw x)) :
    Build A {fun x => if sw x then t x else f x} 3 := by
  have he : (fun x => if sw x then t x else f x) = or (an sw t) (an nsw f) := by
    funext x
    simp only [or, an, hneg x]
    cases sw x <;> cases t x <;> cases f x <;> rfl
  rw [he]
  have h1 := andG hsw ht
  have h2 := andG (A := A ∪ {an sw t}) (Or.inl hnsw) (Or.inl hf)
  have h3 := orG (A := A ∪ ({an sw t} ∪ {an nsw f}))
    (f := an sw t) (g := an nsw f) (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl))
  exact relax (seq (seq h1 h2) h3) le_rfl (Set.singleton_subset_iff.mpr (Or.inr rfl)) le_rfl

private theorem listBuild {α : Type*} {A : Set (Sig n)} (xs : List α)
    (F : α → Sig n) (c : Nat) (H : ∀ a ∈ xs, Build A {F a} c) :
    Build A {f | ∃ a ∈ xs, f = F a} (xs.length * c) := by
  induction xs with
  | nil =>
    exact relax (idle (A := A) (B := ∅) (by simp)) le_rfl (by simp) (by simp)
  | cons a xs ih =>
    have h1 := H a List.mem_cons_self
    have h2 := ih (fun b hb => H b (List.mem_cons_of_mem a hb))
    have h2' := relax h2 (C := A ∪ {F a}) Set.subset_union_left le_rfl le_rfl
    refine relax (seq h1 h2') le_rfl ?_ ?_
    · rintro f ⟨b, hb, rfl⟩
      rcases List.mem_cons.mp hb with rfl | hb
      · exact Or.inl rfl
      · exact Or.inr ⟨b, hb, rfl⟩
    · simp only [List.length_cons]
      rw [Nat.succ_mul xs.length, Nat.add_comm]

private theorem finG {k : Nat} {A : Set (Sig n)} (F : Fin k → Sig n) (c : Nat)
    (H : ∀ i, Build A {F i} c) : Build A (Set.range F) (k * c) := by
  have h := listBuild (List.finRange k) F c (fun i _ => H i)
  rw [List.length_finRange] at h
  refine relax h le_rfl ?_ le_rfl
  rintro _ ⟨i, rfl⟩
  exact ⟨i, List.mem_finRange i, rfl⟩

private theorem ltStepG {A : Set (Sig n)} {xm ym prev : Sig n}
    (hx : xm ∈ A) (hy : ym ∈ A) (hp : prev ∈ A) :
    Build A {fun v => (!(xm v) && ym v) || ((!(xm v) || ym v) && prev v)} 5 := by
  have h1 := notG hx
  have h2 := andG (A := A ∪ {nt xm}) (Or.inr rfl) (Or.inl hy)
  have h3 := orG (A := A ∪ ({nt xm} ∪ {an (nt xm) ym}))
    (Or.inr (Or.inl rfl)) (Or.inl hy)
  have h4 := andG (A := A ∪ (({nt xm} ∪ {an (nt xm) ym}) ∪ {or (nt xm) ym}))
    (Or.inr (Or.inr rfl)) (Or.inl hp)
  have h5 := orG (A := A ∪ ((({nt xm} ∪ {an (nt xm) ym}) ∪ {or (nt xm) ym}) ∪ {an (or (nt xm) ym) prev}))
    (Or.inr (Or.inl (Or.inl (Or.inr rfl)))) (Or.inr (Or.inr rfl))
  exact relax (seq (seq (seq (seq h1 h2) h3) h4) h5) le_rfl
    (Set.singleton_subset_iff.mpr (Or.inr rfl)) le_rfl

private def bitsVal (f : Nat → Bool) : Nat → Nat
  | 0 => 0
  | m + 1 => bitsVal f m + if f m then 2 ^ m else 0

private theorem bitsVal_lt (f : Nat → Bool) : ∀ m, bitsVal f m < 2 ^ m
  | 0 => by simp [bitsVal]
  | m + 1 => by
    have ih := bitsVal_lt f m
    simp only [bitsVal, Nat.pow_succ]
    cases f m <;> simp <;> omega

private theorem bitsVal_testBit (f : Nat → Bool) : ∀ m i, i < m → (bitsVal f m).testBit i = f i
  | 0, _, hi => by omega
  | m + 1, i, hi => by
    simp only [bitsVal]
    have hlt := bitsVal_lt f m
    by_cases him : i = m
    · subst him
      cases hfm : f i
      · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
        exact Nat.testBit_lt_two_pow hlt
      · simp only [↓reduceIte]
        rw [Nat.add_comm, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hlt]
        rfl
    · have him' : i < m := by omega
      cases hfm : f m
      · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
        exact bitsVal_testBit f m i him'
      · simp only [↓reduceIte]
        rw [Nat.add_comm, Nat.testBit_two_pow_add_gt him']
        exact bitsVal_testBit f m i him'

private theorem bitsVal_lt_step (f g : Nat → Bool) (m : Nat) :
    decide (bitsVal f (m + 1) < bitsVal g (m + 1)) =
      ((!(f m) && g m) || ((!(f m) || g m) && decide (bitsVal f m < bitsVal g m))) := by
  have hf := bitsVal_lt f m
  have hg := bitsVal_lt g m
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq]
  simp only [bitsVal, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq]
  cases f m <;> cases g m <;> simp <;> omega

private theorem ltWordG {A : Set (Sig n)} (f g : Nat → Sig n) (m : Nat)
    (hf : ∀ i < m, f i ∈ A) (hg : ∀ i < m, g i ∈ A) (hfalse : (fun _ => false) ∈ A) :
    Build A {fun v => decide (bitsVal (fun i => f i v) m < bitsVal (fun i => g i v) m)} (5 * m) := by
  induction m with
  | zero =>
    have he : (fun v : Fin n → Bool => decide (bitsVal (fun i => f i v) 0 < bitsVal (fun i => g i v) 0)) =
        (fun _ => false) := by
      funext v
      rfl
    rw [he]
    exact relax (idle (Set.singleton_subset_iff.mpr hfalse)) le_rfl le_rfl (by omega)
  | succ m ih =>
    have hprev := ih (fun i hi => hf i (by omega)) (fun i hi => hg i (by omega))
    let prev : Sig n := fun v => decide (bitsVal (fun i => f i v) m < bitsVal (fun i => g i v) m)
    have hstep : Build (A ∪ {prev})
        {fun v => (!(f m v) && g m v) || ((!(f m v) || g m v) && prev v)} 5 :=
      ltStepG (Or.inl (hf m (by omega))) (Or.inl (hg m (by omega))) (Or.inr rfl)
    have he : (fun v => (!(f m v) && g m v) || ((!(f m v) || g m v) && prev v)) =
        (fun v => decide (bitsVal (fun i => f i v) (m + 1) < bitsVal (fun i => g i v) (m + 1))) := by
      funext v
      exact (bitsVal_lt_step (fun i => f i v) (fun i => g i v) m).symm
    rw [he] at hstep
    refine relax (seq hprev hstep) le_rfl (Set.singleton_subset_iff.mpr (Or.inr rfl)) ?_
    omega

end Build220

namespace Bitonic

private def bitonicMerge (off : Nat) : Nat → Bool → List (Nat × Nat × Bool)
  | 0, _ => []
  | k + 1, asc =>
    let h := 2 ^ k
    let stage := (List.range h).map (fun i => (off + i, off + h + i, asc))
    stage ++ bitonicMerge off k asc ++ bitonicMerge (off + h) k asc

private def bitonicSort (off : Nat) : Nat → Bool → List (Nat × Nat × Bool)
  | 0, _ => []
  | k + 1, asc =>
    let h := 2 ^ k
    bitonicSort off k true ++ bitonicSort (off + h) k false ++ bitonicMerge off (k + 1) asc

private theorem bitonicMerge_length (off : Nat) : ∀ k asc,
    2 * (bitonicMerge off k asc).length = k * 2 ^ k
  | 0, _ => by simp [bitonicMerge]
  | k + 1, asc => by
    simp only [bitonicMerge, List.length_append, List.length_map, List.length_range]
    have h1 := bitonicMerge_length off k asc
    have h2 := bitonicMerge_length (off + 2 ^ k) k asc
    have he : (k + 1) * 2 ^ (k + 1) = 2 * 2 ^ k + 2 * (k * 2 ^ k) := by
      rw [Nat.pow_succ, Nat.succ_mul]
      rw [← Nat.mul_assoc k (2 ^ k) 2, Nat.mul_comm (k * 2 ^ k) 2, Nat.mul_comm (2 ^ k) 2, Nat.add_comm]
    omega

private theorem bitonicSort_length (off : Nat) : ∀ k asc,
    4 * (bitonicSort off k asc).length = k * (k + 1) * 2 ^ k
  | 0, _ => by simp [bitonicSort]
  | k + 1, asc => by
    simp only [bitonicSort, List.length_append]
    have h1 := bitonicSort_length off k true
    have h2 := bitonicSort_length (off + 2 ^ k) k false
    have hm := bitonicMerge_length off (k + 1) asc
    have he : (k + 1) * (k + 1 + 1) * 2 ^ (k + 1) =
        2 * (k * (k + 1) * 2 ^ k) + 2 * ((k + 1) * 2 ^ (k + 1)) := by
      rw [Nat.pow_succ]
      have e1 : k * (k + 1) * 2 ^ k = (k + 1) * k * 2 ^ k := by rw [Nat.mul_comm k (k + 1)]
      have e2 : (k + 1) * (k + 2) * (2 ^ k * 2) =
          (k + 1) * k * (2 ^ k * 2) + (k + 1) * 2 * (2 ^ k * 2) := by
        rw [Nat.mul_add (k + 1) k 2, Nat.add_mul]
      rw [e2]
      have e3 : 2 * (k * (k + 1) * 2 ^ k) = (k + 1) * k * (2 ^ k * 2) := by
        rw [e1, Nat.mul_comm 2, Nat.mul_assoc]
      have e4 : 2 * ((k + 1) * (2 ^ k * 2)) = (k + 1) * 2 * (2 ^ k * 2) := by
        rw [← Nat.mul_assoc 2 (k + 1), Nat.mul_comm 2 (k + 1)]
      omega
    omega

private theorem bitonicMerge_mem (off : Nat) : ∀ k asc c,
    c ∈ bitonicMerge off k asc → off ≤ c.1 ∧ c.1 < c.2.1 ∧ c.2.1 < off + 2 ^ k
  | 0, _, c, hc => by simp [bitonicMerge] at hc
  | k + 1, asc, c, hc => by
    simp only [bitonicMerge, List.mem_append, List.mem_map, List.mem_range] at hc
    rcases hc with (⟨i, hi, rfl⟩ | hc) | hc
    · dsimp only
      rw [Nat.pow_succ]
      omega
    · have h := bitonicMerge_mem off k asc c hc
      rw [Nat.pow_succ]
      omega
    · have h := bitonicMerge_mem (off + 2 ^ k) k asc c hc
      rw [Nat.pow_succ]
      omega

private theorem bitonicSort_mem (off : Nat) : ∀ k asc c,
    c ∈ bitonicSort off k asc → off ≤ c.1 ∧ c.1 < c.2.1 ∧ c.2.1 < off + 2 ^ k
  | 0, _, c, hc => by simp [bitonicSort] at hc
  | k + 1, asc, c, hc => by
    simp only [bitonicSort, List.mem_append] at hc
    rcases hc with (hc | hc) | hc
    · have h := bitonicSort_mem off k true c hc
      rw [Nat.pow_succ]
      omega
    · have h := bitonicSort_mem (off + 2 ^ k) k false c hc
      rw [Nat.pow_succ]
      omega
    · exact bitonicMerge_mem off (k + 1) asc c hc

private def swapBit (k1 k2 : Nat) (asc : Bool) : Bool :=
  if asc then decide (k2 < k1) else decide (k1 < k2)

private def applySwap {α : Type*} (u v : Nat) (sw : Bool) (st : Nat → α) : Nat → α :=
  fun idx =>
    if sw then
      if idx = u then st v else if idx = v then st u else st idx
    else st idx

private theorem applySwap_invol {α : Type*} (u v : Nat) (sw : Bool) (st : Nat → α) :
    applySwap u v sw (applySwap u v sw st) = st := by
  funext idx
  simp only [applySwap]
  cases sw with
  | false => rfl
  | true =>
    simp only [↓reduceIte]
    by_cases h1 : idx = u
    · subst h1
      by_cases huv : idx = v
      · subst huv; simp
      · simp [Ne.symm huv]
    · by_cases h2 : idx = v
      · subst h2; simp [h1]
      · simp [h1, h2]

private theorem applySwap_comp {α β : Type*} (u v : Nat) (sw : Bool) (f : α → β) (st : Nat → α) :
    applySwap u v sw (fun idx => f (st idx)) = fun idx => f (applySwap u v sw st idx) := by
  funext idx
  simp only [applySwap]
  cases sw <;> simp only [Bool.false_eq_true, ↓reduceIte]
  by_cases h1 : idx = u
  · simp [h1]
  · by_cases h2 : idx = v
    · subst h2; simp [h1]
    · simp [h1, h2]

private def runNet {α : Type*} (key : α → Nat) : List (Nat × Nat × Bool) → (Nat → α) → (Nat → α)
  | [], st => st
  | (u, v, asc) :: rest, st =>
    let sw := swapBit (key (st u)) (key (st v)) asc
    runNet key rest (applySwap u v sw st)

private theorem runNet_append {α : Type*} (key : α → Nat) (n1 n2 : List (Nat × Nat × Bool)) (st : Nat → α) :
    runNet key (n1 ++ n2) st = runNet key n2 (runNet key n1 st) := by
  induction n1 generalizing st with
  | nil => rfl
  | cons c rest ih =>
    rcases c with ⟨u, v, asc⟩
    simp only [List.cons_append, runNet]
    exact ih _

private def netSwaps {α : Type*} (key : α → Nat) : List (Nat × Nat × Bool) → (Nat → α) → List (Nat × Nat × Bool)
  | [], _ => []
  | (u, v, asc) :: rest, st =>
    let sw := swapBit (key (st u)) (key (st v)) asc
    (u, v, sw) :: netSwaps key rest (applySwap u v sw st)

private def replaySwaps {β : Type*} : List (Nat × Nat × Bool) → (Nat → β) → (Nat → β)
  | [], st => st
  | (u, v, sw) :: rest, st => replaySwaps rest (applySwap u v sw st)

private theorem replaySwaps_append {β : Type*} (s1 s2 : List (Nat × Nat × Bool)) (st : Nat → β) :
    replaySwaps (s1 ++ s2) st = replaySwaps s2 (replaySwaps s1 st) := by
  induction s1 generalizing st with
  | nil => rfl
  | cons c rest ih =>
    rcases c with ⟨u, v, sw⟩
    simp only [List.cons_append, replaySwaps]
    exact ih _

private theorem replaySwaps_comp {α β : Type*} (sws : List (Nat × Nat × Bool)) (f : α → β) (st : Nat → α) :
    replaySwaps sws (fun idx => f (st idx)) = fun idx => f (replaySwaps sws st idx) := by
  induction sws generalizing st with
  | nil => rfl
  | cons c rest ih =>
    rcases c with ⟨u, v, sw⟩
    simp only [replaySwaps]
    rw [applySwap_comp]
    exact ih _

private theorem replaySwaps_reverse_cancel {β : Type*} (sws : List (Nat × Nat × Bool)) (st : Nat → β) :
    replaySwaps sws.reverse (replaySwaps sws st) = st := by
  induction sws generalizing st with
  | nil => rfl
  | cons c rest ih =>
    rcases c with ⟨u, v, sw⟩
    simp only [List.reverse_cons, replaySwaps, replaySwaps_append]
    rw [ih, applySwap_invol]

private theorem runNet_eq_replay {α : Type*} (key : α → Nat) (net : List (Nat × Nat × Bool)) (st : Nat → α) :
    runNet key net st = replaySwaps (netSwaps key net st) st := by
  induction net generalizing st with
  | nil => rfl
  | cons c rest ih =>
    rcases c with ⟨u, v, asc⟩
    simp only [runNet, netSwaps, replaySwaps]
    exact ih _

private theorem runNet_unchanged {α : Type*} (key : α → Nat) (net : List (Nat × Nat × Bool))
    (st : Nat → α) (idx : Nat) (h : ∀ c ∈ net, idx ≠ c.1 ∧ idx ≠ c.2.1) :
    runNet key net st idx = st idx := by
  induction net generalizing st with
  | nil => rfl
  | cons c rest ih =>
    rcases c with ⟨u, v, asc⟩
    have hc := h (u, v, asc) List.mem_cons_self
    simp only [runNet]
    rw [ih _ (fun c' hc' => h c' (List.mem_cons_of_mem _ hc'))]
    simp only [applySwap]
    cases swapBit (key (st u)) (key (st v)) asc
    · rfl
    · simp only [↓reduceIte, hc.1, hc.2]

private theorem runNet_mono_map {α : Type*} (key : α → Nat) (f : Nat → Bool)
    (hf : ∀ x y, x ≤ y → f x = true → f y = true)
    (net : List (Nat × Nat × Bool)) (st : Nat → α) :
    (fun idx => f (key (runNet key net st idx))) =
      runNet (fun b : Bool => b.toNat) net (fun idx => f (key (st idx))) := by
  induction net generalizing st with
  | nil => rfl
  | cons c rest ih =>
    rcases c with ⟨u, v, asc⟩
    simp only [runNet]
    rw [ih]
    congr 1
    funext idx
    simp only [applySwap, swapBit]
    have hpair :
        (f (key (if (if asc then decide (key (st v) < key (st u)) else decide (key (st u) < key (st v)))
          then st v else st u)) =
         if (if asc then decide ((f (key (st v))).toNat < (f (key (st u))).toNat)
             else decide ((f (key (st u))).toNat < (f (key (st v))).toNat))
          then f (key (st v)) else f (key (st u))) ∧
        (f (key (if (if asc then decide (key (st v) < key (st u)) else decide (key (st u) < key (st v)))
          then st u else st v)) =
         if (if asc then decide ((f (key (st v))).toNat < (f (key (st u))).toNat)
             else decide ((f (key (st u))).toNat < (f (key (st v))).toNat))
          then f (key (st u)) else f (key (st v))) := by
      cases asc <;> simp only [Bool.false_eq_true, ↓reduceIte]
      · by_cases hlt : key (st u) < key (st v)
        · have hle : key (st u) ≤ key (st v) := Nat.le_of_lt hlt
          simp only [hlt, decide_true, ↓reduceIte]
          cases hfu : f (key (st u)) <;> cases hfv : f (key (st v))
          · simp
          · simp
          · exact absurd (hf _ _ hle hfu) (by rw [hfv]; decide)
          · simp
        · have hle : key (st v) ≤ key (st u) := Nat.le_of_not_lt hlt
          simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte]
          cases hfu : f (key (st u)) <;> cases hfv : f (key (st v))
          · simp
          · exact absurd (hf _ _ hle hfv) (by rw [hfu]; decide)
          · simp
          · simp
      · by_cases hlt : key (st v) < key (st u)
        · have hle : key (st v) ≤ key (st u) := Nat.le_of_lt hlt
          simp only [hlt, decide_true, ↓reduceIte]
          cases hfu : f (key (st u)) <;> cases hfv : f (key (st v))
          · simp
          · exact absurd (hf _ _ hle hfv) (by rw [hfu]; decide)
          · simp
          · simp
        · have hle : key (st u) ≤ key (st v) := Nat.le_of_not_lt hlt
          simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte]
          cases hfu : f (key (st u)) <;> cases hfv : f (key (st v))
          · simp
          · simp
          · exact absurd (hf _ _ hle hfu) (by rw [hfv]; decide)
          · simp
    by_cases h1 : idx = u
    · subst h1
      have hl := hpair.1
      by_cases hs1 : (if asc then decide (key (st v) < key (st idx)) else decide (key (st idx) < key (st v))) = true <;>
        by_cases hs2 : (if asc then decide ((f (key (st v))).toNat < (f (key (st idx))).toNat)
          else decide ((f (key (st idx))).toNat < (f (key (st v))).toNat)) = true <;>
        simp only [hs1, hs2, ↓reduceIte] at hl ⊢ <;> exact hl
    · by_cases h2 : idx = v
      · subst h2
        have hr := hpair.2
        by_cases hs1 : (if asc then decide (key (st idx) < key (st u)) else decide (key (st u) < key (st idx))) = true <;>
          by_cases hs2 : (if asc then decide ((f (key (st idx))).toNat < (f (key (st u))).toNat)
            else decide ((f (key (st u))).toNat < (f (key (st idx))).toNat)) = true <;>
          simp only [hs1, hs2, h1, ↓reduceIte] at hr ⊢ <;> exact hr
      · by_cases hs1 : (if asc then decide (key (st v) < key (st u)) else decide (key (st u) < key (st v))) = true <;>
          by_cases hs2 : (if asc then decide ((f (key (st v))).toNat < (f (key (st u))).toNat)
            else decide ((f (key (st u))).toNat < (f (key (st v))).toNat)) = true <;>
          simp only [hs1, hs2, h1, h2, Bool.false_eq_true, ↓reduceIte]

private def IsBitonic (off len : Nat) (g : Nat → Bool) : Prop :=
  ∃ s e, s ≤ e ∧ e ≤ len ∧
    ((∀ i < len, g (off + i) = true ↔ s ≤ i ∧ i < e) ∨
     (∀ i < len, g (off + i) = false ↔ s ≤ i ∧ i < e))

private def IsSortedBool (off len : Nat) (asc : Bool) (g : Nat → Bool) : Prop :=
  ∀ i j, i ≤ j → j < len →
    if asc then (g (off + i) = true → g (off + j) = true)
    else (g (off + j) = true → g (off + i) = true)

private theorem runNet_bool_const (net : List (Nat × Nat × Bool)) (off len : Nat) (v : Bool)
    (g : Nat → Bool)
    (hnet : ∀ c ∈ net, off ≤ c.1 ∧ c.1 < off + len ∧ off ≤ c.2.1 ∧ c.2.1 < off + len)
    (hg : ∀ i < len, g (off + i) = v) :
    ∀ i < len, runNet (fun b : Bool => b.toNat) net g (off + i) = v := by
  induction net generalizing g with
  | nil => exact hg
  | cons c rest ih =>
    rcases c with ⟨x, y, asc⟩
    have hc := hnet (x, y, asc) List.mem_cons_self
    dsimp only at hc
    simp only [runNet]
    apply ih _ (fun c' hc' => hnet c' (List.mem_cons_of_mem _ hc'))
    intro i hi
    simp only [applySwap]
    have hx : g x = v := by
      have e : off + (x - off) = x := by omega
      rw [← e]; exact hg (x - off) (by omega)
    have hy : g y = v := by
      have e : off + (y - off) = y := by omega
      rw [← e]; exact hg (y - off) (by omega)
    cases swapBit (g x).toNat (g y).toNat asc
    · exact hg i hi
    · simp only [↓reduceIte]
      by_cases h1 : off + i = x
      · simp [h1, hy]
      · by_cases h2 : off + i = y
        · simp only [h1, ↓reduceIte]; simp only [h2, ↓reduceIte]; exact hx
        · simp [h1, h2, hg i hi]

private theorem stage_eval (off h : Nat) (asc : Bool) (g : Nat → Bool) :
    ∀ m ≤ h, ∀ idx,
      let stage := (List.range m).map (fun i => (off + i, off + h + i, asc))
      runNet (fun b : Bool => b.toNat) stage g idx =
        if off ≤ idx ∧ idx < off + m then
          if asc then g idx && g (idx + h) else g idx || g (idx + h)
        else if off + h ≤ idx ∧ idx < off + h + m then
          if asc then g (idx - h) || g idx else g (idx - h) && g idx
        else g idx := by
  intro m
  induction m with
  | zero =>
    intro _ idx
    dsimp only
    simp only [List.range_zero, List.map_nil, runNet, Nat.add_zero]
    simp only [show ¬ (off ≤ idx ∧ idx < off) by omega,
      show ¬ (off + h ≤ idx ∧ idx < off + h) by omega, ↓reduceIte]
  | succ m ih =>
    intro hm idx
    dsimp only
    rw [List.range_succ, List.map_append, List.map_cons, List.map_nil, runNet_append]
    simp only [runNet, applySwap, swapBit]
    have h1 := ih (by omega) (off + m)
    have h2 := ih (by omega) (off + h + m)
    have h3 := ih (by omega) idx
    have h1' : runNet (fun b : Bool => b.toNat) ((List.range m).map (fun i => (off + i, off + h + i, asc))) g (off + m) = g (off + m) := by
      rw [h1]; simp only [show ¬ (off ≤ off + m ∧ off + m < off + m) by omega,
        show ¬ (off + h ≤ off + m ∧ off + m < off + h + m) by omega, ↓reduceIte]
    have h2' : runNet (fun b : Bool => b.toNat) ((List.range m).map (fun i => (off + i, off + h + i, asc))) g (off + h + m) = g (off + h + m) := by
      rw [h2]; simp only [show ¬ (off ≤ off + h + m ∧ off + h + m < off + m) by omega,
        show ¬ (off + h ≤ off + h + m ∧ off + h + m < off + h + m) by omega, ↓reduceIte]
    rw [h1', h2']
    by_cases hidx1 : idx = off + m
    · subst hidx1
      rw [h1']
      have e1 : off + m + h = off + h + m := by omega
      have hc1 : off ≤ off + m ∧ off + m < off + (m + 1) := by omega
      simp only [hc1, ↓reduceIte, e1]
      cases asc <;> cases g (off + m) <;> cases g (off + h + m) <;> rfl
    · by_cases hidx2 : idx = off + h + m
      · subst hidx2
        rw [h2']
        have e1 : off + h + m - h = off + m := by omega
        have hc1 : ¬ (off ≤ off + h + m ∧ off + h + m < off + (m + 1)) := by omega
        have hc2 : off + h ≤ off + h + m ∧ off + h + m < off + h + (m + 1) := by omega
        have hne : off + h + m ≠ off + m := by omega
        simp only [hc1, hc2, hne, ↓reduceIte, e1]
        cases asc <;> cases g (off + m) <;> cases g (off + h + m) <;> rfl
      · have hne1 : ¬ (idx = off + m) := hidx1
        have hne2 : ¬ (idx = off + h + m) := hidx2
        have heq : (if (if asc then decide ((g (off + h + m)).toNat < (g (off + m)).toNat)
            else decide ((g (off + m)).toNat < (g (off + h + m)).toNat)) then
            if idx = off + m then g (off + h + m) else if idx = off + h + m then g (off + m)
            else runNet (fun b : Bool => b.toNat) ((List.range m).map (fun i => (off + i, off + h + i, asc))) g idx
          else runNet (fun b : Bool => b.toNat) ((List.range m).map (fun i => (off + i, off + h + i, asc))) g idx) =
          runNet (fun b : Bool => b.toNat) ((List.range m).map (fun i => (off + i, off + h + i, asc))) g idx := by
          cases (if asc then decide ((g (off + h + m)).toNat < (g (off + m)).toNat)
            else decide ((g (off + m)).toNat < (g (off + h + m)).toNat)) <;> simp [hne1, hne2]
        rw [heq, h3]
        by_cases c1 : off ≤ idx ∧ idx < off + m
        · have c1' : off ≤ idx ∧ idx < off + (m + 1) := by omega
          simp only [c1, c1', and_self, ↓reduceIte]
        · by_cases c2 : off + h ≤ idx ∧ idx < off + h + m
          · have c1' : ¬ (off ≤ idx ∧ idx < off + (m + 1)) := by omega
            have c2' : off + h ≤ idx ∧ idx < off + h + (m + 1) := by omega
            simp only [c1, c2, c1', c2', ↓reduceIte]
          · have c1' : ¬ (off ≤ idx ∧ idx < off + (m + 1)) := by omega
            have c2' : ¬ (off + h ≤ idx ∧ idx < off + h + (m + 1)) := by omega
            simp only [c1, c2, c1', c2', ↓reduceIte]

private theorem bitonic_split_true (off h : Nat) (g : Nat → Bool) (hb : IsBitonic off (2 * h) g) :
    let lo : Nat → Bool := fun idx => g idx && g (idx + h)
    let hi : Nat → Bool := fun idx => g (idx - h) || g idx
    IsBitonic off h lo ∧ IsBitonic (off + h) h hi ∧
      ((∀ i < h, lo (off + i) = false) ∨ (∀ i < h, hi (off + h + i) = true)) := by
  intro lo hi
  rcases hb with ⟨s, e, hse, he2h, htr | hfa⟩
  · by_cases hlen : e - s ≤ h
    · have hlo_all : ∀ i < h, lo (off + i) = false := by
        intro i hi_lt
        dsimp only [lo]
        cases h1 : g (off + i) with
        | false => rfl
        | true =>
          have hi1 := (htr i (by omega)).mp h1
          cases h2 : g (off + i + h) with
          | false => rfl
          | true =>
            have e1 : off + i + h = off + (h + i) := by omega
            rw [e1] at h2
            have hi2 := (htr (h + i) (by omega)).mp h2
            omega
      refine ⟨⟨0, 0, Nat.le_refl 0, Nat.zero_le h, Or.inl (fun i hi_lt => by rw [hlo_all i hi_lt]; simp)⟩,
        ?_, Or.inl hlo_all⟩
      have hhi_iff : ∀ i < h, hi (off + h + i) = true ↔ (s ≤ i ∧ i < e) ∨ (s ≤ h + i ∧ h + i < e) := by
        intro i hi_lt
        dsimp only [hi]
        have e1 : off + h + i - h = off + i := by omega
        have e2 : off + h + i = off + (h + i) := by omega
        rw [e1, e2, Bool.or_eq_true, htr i (by omega), htr (h + i) (by omega)]
      by_cases heh : e ≤ h
      · exact ⟨s, e, hse, heh, Or.inl (fun i hi_lt => by rw [hhi_iff i hi_lt]; omega)⟩
      · by_cases hhs : h ≤ s
        · exact ⟨s - h, e - h, by omega, by omega, Or.inl (fun i hi_lt => by rw [hhi_iff i hi_lt]; omega)⟩
        · refine ⟨e - h, s, by omega, by omega, Or.inr (fun i hi_lt => ?_)⟩
          have h1 := hhi_iff i hi_lt
          cases hval : hi (off + h + i) with
          | false =>
            have hnt : ¬ ((s ≤ i ∧ i < e) ∨ (s ≤ h + i ∧ h + i < e)) := fun hp => by
              have := h1.mpr hp; rw [hval] at this; cases this
            constructor
            · intro _; omega
            · intro _; rfl
          | true =>
            have ht := h1.mp hval
            constructor
            · intro hc; cases hc
            · intro hr; omega
    · have hhi_all : ∀ i < h, hi (off + h + i) = true := by
        intro i hi_lt
        dsimp only [hi]
        have e1 : off + h + i - h = off + i := by omega
        have e2 : off + h + i = off + (h + i) := by omega
        rw [e1, e2, Bool.or_eq_true, htr i (by omega), htr (h + i) (by omega)]
        omega
      refine ⟨⟨s, e - h, by omega, by omega, Or.inl (fun i hi_lt => ?_)⟩,
        ⟨0, h, Nat.zero_le h, Nat.le_refl h, Or.inl (fun i hi_lt => by rw [hhi_all i hi_lt]; simp [hi_lt])⟩,
        Or.inr hhi_all⟩
      dsimp only [lo]
      have e1 : off + i + h = off + (h + i) := by omega
      rw [e1, Bool.and_eq_true, htr i (by omega), htr (h + i) (by omega)]
      omega
  · by_cases hlen : e - s ≤ h
    · have hhi_all : ∀ i < h, hi (off + h + i) = true := by
        intro i hi_lt
        dsimp only [hi]
        have e1 : off + h + i - h = off + i := by omega
        have e2 : off + h + i = off + (h + i) := by omega
        rw [e1, e2]
        cases h1 : g (off + i) with
        | true => rfl
        | false =>
          have hi1 := (hfa i (by omega)).mp h1
          cases h2 : g (off + (h + i)) with
          | true => rfl
          | false =>
            have hi2 := (hfa (h + i) (by omega)).mp h2
            omega
      refine ⟨?_, ⟨0, h, Nat.zero_le h, Nat.le_refl h, Or.inl (fun i hi_lt => by rw [hhi_all i hi_lt]; simp [hi_lt])⟩,
        Or.inr hhi_all⟩
      have hlo_iff : ∀ i < h, lo (off + i) = false ↔ (s ≤ i ∧ i < e) ∨ (s ≤ h + i ∧ h + i < e) := by
        intro i hi_lt
        dsimp only [lo]
        have e1 : off + i + h = off + (h + i) := by omega
        rw [e1, Bool.and_eq_false_iff, hfa i (by omega), hfa (h + i) (by omega)]
      by_cases heh : e ≤ h
      · exact ⟨s, e, hse, heh, Or.inr (fun i hi_lt => by rw [hlo_iff i hi_lt]; omega)⟩
      · by_cases hhs : h ≤ s
        · exact ⟨s - h, e - h, by omega, by omega, Or.inr (fun i hi_lt => by rw [hlo_iff i hi_lt]; omega)⟩
        · refine ⟨e - h, s, by omega, by omega, Or.inl (fun i hi_lt => ?_)⟩
          have h1 := hlo_iff i hi_lt
          cases hval : lo (off + i) with
          | true =>
            have hnf : ¬ ((s ≤ i ∧ i < e) ∨ (s ≤ h + i ∧ h + i < e)) := fun hp => by
              have := h1.mpr hp; rw [hval] at this; cases this
            constructor
            · intro _; omega
            · intro _; rfl
          | false =>
            have hf := h1.mp hval
            constructor
            · intro hc; cases hc
            · intro hr; omega
    · have hlo_all : ∀ i < h, lo (off + i) = false := by
        intro i hi_lt
        dsimp only [lo]
        have e1 : off + i + h = off + (h + i) := by omega
        rw [e1, Bool.and_eq_false_iff, hfa i (by omega), hfa (h + i) (by omega)]
        omega
      refine ⟨⟨0, 0, Nat.le_refl 0, Nat.zero_le h, Or.inl (fun i hi_lt => by rw [hlo_all i hi_lt]; simp)⟩,
        ⟨s, e - h, by omega, by omega, Or.inr (fun i hi_lt => ?_)⟩,
        Or.inl hlo_all⟩
      dsimp only [hi]
      have e1 : off + h + i - h = off + i := by omega
      have e2 : off + h + i = off + (h + i) := by omega
      rw [e1, e2, Bool.or_eq_false_iff, hfa i (by omega), hfa (h + i) (by omega)]
      omega

private theorem bitonicMerge_sorted (off : Nat) : ∀ k asc (g : Nat → Bool),
    IsBitonic off (2 ^ k) g →
    IsSortedBool off (2 ^ k) asc (runNet (fun b : Bool => b.toNat) (bitonicMerge off k asc) g)
  | 0, asc, g, _ => by
    intro i j hij hj
    have hi0 : i = 0 := by omega
    have hj0 : j = 0 := by omega
    subst hi0; subst hj0
    cases asc <;> exact fun h => h
  | k + 1, asc, g, hb => by
    let h := 2 ^ k
    have h2 : 2 ^ (k + 1) = 2 * h := by dsimp [h]; rw [Nat.pow_succ, Nat.mul_comm]
    rw [h2] at hb ⊢
    simp only [bitonicMerge, runNet_append]
    let stage := (List.range h).map (fun i => (off + i, off + h + i, asc))
    let g1 := runNet (fun b : Bool => b.toNat) stage g
    let g2 := runNet (fun b : Bool => b.toNat) (bitonicMerge off k asc) g1
    let g3 := runNet (fun b : Bool => b.toNat) (bitonicMerge (off + h) k asc) g2
    change IsSortedBool off (2 * h) asc g3
    have hstage := stage_eval off h asc g h (Nat.le_refl h)
    have hg1_L : ∀ i < h, g1 (off + i) = if asc then g (off + i) && g (off + i + h) else g (off + i) || g (off + i + h) := by
      intro i hi_lt
      have hs := hstage (off + i)
      dsimp only at hs
      have hc1 : off ≤ off + i ∧ off + i < off + h := by omega
      simp only [hc1, and_self, ↓reduceIte] at hs
      exact hs
    have hg1_R : ∀ i < h, g1 (off + h + i) = if asc then g (off + h + i - h) || g (off + h + i) else g (off + h + i - h) && g (off + h + i) := by
      intro i hi_lt
      have hs := hstage (off + h + i)
      dsimp only at hs
      have hc1 : ¬ (off ≤ off + h + i ∧ off + h + i < off + h) := by omega
      have hc2 : off + h ≤ off + h + i ∧ off + h + i < off + h + h := by omega
      simp only [hc1, hc2, and_self, ↓reduceIte] at hs
      exact hs
    have hsp := bitonic_split_true off h g hb
    have hleft_bit : IsBitonic off h g1 := by
      cases asc with
      | true =>
        rcases hsp.1 with ⟨s, e, h1, h2', h3⟩
        refine ⟨s, e, h1, h2', ?_⟩
        rcases h3 with h3 | h3
        · left
          intro i hi_lt
          rw [hg1_L i hi_lt]
          exact h3 i hi_lt
        · right
          intro i hi_lt
          rw [hg1_L i hi_lt]
          exact h3 i hi_lt
      | false =>
        rcases hsp.2.1 with ⟨s, e, h1, h2', h3⟩
        refine ⟨s, e, h1, h2', ?_⟩
        rcases h3 with h3 | h3
        · left
          intro i hi_lt
          have e1 : off + h + i - h = off + i := by omega
          have e2 : off + h + i = off + i + h := by omega
          have h3' := h3 i hi_lt
          dsimp only at h3'
          rw [e1, e2] at h3'
          rw [hg1_L i hi_lt]
          exact h3'
        · right
          intro i hi_lt
          have e1 : off + h + i - h = off + i := by omega
          have e2 : off + h + i = off + i + h := by omega
          have h3' := h3 i hi_lt
          dsimp only at h3'
          rw [e1, e2] at h3'
          rw [hg1_L i hi_lt]
          exact h3'
    have hright_bit : IsBitonic (off + h) h g2 := by
      have hg2_eq : ∀ i < h, g2 (off + h + i) = g1 (off + h + i) := by
        intro i hi_lt
        apply runNet_unchanged
        intro c hc
        have hm := bitonicMerge_mem off k asc c hc
        dsimp only [h] at hi_lt ⊢
        omega
      cases asc with
      | true =>
        rcases hsp.2.1 with ⟨s, e, h1, h2', h3⟩
        refine ⟨s, e, h1, h2', ?_⟩
        rcases h3 with h3 | h3
        · left
          intro i hi_lt
          rw [hg2_eq i hi_lt, hg1_R i hi_lt]
          exact h3 i hi_lt
        · right
          intro i hi_lt
          rw [hg2_eq i hi_lt, hg1_R i hi_lt]
          exact h3 i hi_lt
      | false =>
        rcases hsp.1 with ⟨s, e, h1, h2', h3⟩
        refine ⟨s, e, h1, h2', ?_⟩
        rcases h3 with h3 | h3
        · left
          intro i hi_lt
          have e1 : off + h + i - h = off + i := by omega
          have e2 : off + h + i = off + i + h := by omega
          rw [hg2_eq i hi_lt, hg1_R i hi_lt]
          simp only [Bool.false_eq_true, ↓reduceIte]
          rw [e1, e2]
          exact h3 i hi_lt
        · right
          intro i hi_lt
          have e1 : off + h + i - h = off + i := by omega
          have e2 : off + h + i = off + i + h := by omega
          rw [hg2_eq i hi_lt, hg1_R i hi_lt]
          simp only [Bool.false_eq_true, ↓reduceIte]
          rw [e1, e2]
          exact h3 i hi_lt
    have hsL : IsSortedBool off h asc g2 := bitonicMerge_sorted off k asc g1 hleft_bit
    have hsR : IsSortedBool (off + h) h asc g3 := bitonicMerge_sorted (off + h) k asc g2 hright_bit
    have hg3_left : ∀ i < h, g3 (off + i) = g2 (off + i) := by
      intro i hi_lt
      apply runNet_unchanged
      intro c hc
      have hm := bitonicMerge_mem (off + h) k asc c hc
      dsimp only [h] at hi_lt ⊢
      omega
    have hnetL : ∀ c ∈ bitonicMerge off k asc, off ≤ c.1 ∧ c.1 < off + h ∧ off ≤ c.2.1 ∧ c.2.1 < off + h := by
      intro c hc; have hm := bitonicMerge_mem off k asc c hc; dsimp [h]; omega
    have hnetR : ∀ c ∈ bitonicMerge (off + h) k asc,
        off + h ≤ c.1 ∧ c.1 < off + h + h ∧ off + h ≤ c.2.1 ∧ c.2.1 < off + h + h := by
      intro c hc; have hm := bitonicMerge_mem (off + h) k asc c hc; dsimp [h]; omega
    intro i j hij hj
    by_cases hjh : j < h
    · rw [hg3_left i (by omega), hg3_left j hjh]
      exact hsL i j hij hjh
    · by_cases hih : h ≤ i
      · have ei : off + i = off + h + (i - h) := by omega
        have ej : off + j = off + h + (j - h) := by omega
        rw [ei, ej]
        exact hsR (i - h) (j - h) (by omega) (by omega)
      · have hi_lt : i < h := by omega
        have hj_lt : j - h < h := by omega
        have ej : off + j = off + h + (j - h) := by omega
        rw [hg3_left i hi_lt, ej]
        cases asc with
        | true =>
          simp only [↓reduceIte]
          rcases hsp.2.2 with hlo | hhi
          · have hg1L : ∀ x < h, g1 (off + x) = false := by
              intro x hx
              rw [hg1_L x hx]
              exact hlo x hx
            have hg2i : g2 (off + i) = false :=
              runNet_bool_const (bitonicMerge off k true) off h false g1 hnetL hg1L i hi_lt
            intro ht; rw [hg2i] at ht; cases ht
          · have hg2R : ∀ x < h, g2 (off + h + x) = true := by
              intro x hx
              have heq : g2 (off + h + x) = g1 (off + h + x) := by
                apply runNet_unchanged; intro c hc; have hm := bitonicMerge_mem off k true c hc; dsimp [h] at hx ⊢; omega
              rw [heq, hg1_R x hx]
              exact hhi x hx
            intro _
            exact runNet_bool_const (bitonicMerge (off + h) k true) (off + h) h true g2 hnetR hg2R (j - h) hj_lt
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          rcases hsp.2.2 with hlo | hhi
          · have hg2R : ∀ x < h, g2 (off + h + x) = false := by
              intro x hx
              have heq : g2 (off + h + x) = g1 (off + h + x) := by
                apply runNet_unchanged; intro c hc; have hm := bitonicMerge_mem off k false c hc; dsimp [h] at hx ⊢; omega
              rw [heq, hg1_R x hx]
              simp only [Bool.false_eq_true, ↓reduceIte]
              have e1 : off + h + x - h = off + x := by omega
              have e2 : off + h + x = off + x + h := by omega
              rw [e1, e2]
              exact hlo x hx
            have hg3j : g3 (off + h + (j - h)) = false :=
              runNet_bool_const (bitonicMerge (off + h) k false) (off + h) h false g2 hnetR hg2R (j - h) hj_lt
            intro ht; rw [hg3j] at ht; cases ht
          · have hg1L : ∀ x < h, g1 (off + x) = true := by
              intro x hx
              rw [hg1_L x hx]
              simp only [Bool.false_eq_true, ↓reduceIte]
              have e1 : off + h + x - h = off + x := by omega
              have e2 : off + h + x = off + x + h := by omega
              have hhi' := hhi x hx
              dsimp only at hhi'
              rw [e1, e2] at hhi'
              exact hhi'
            intro _
            exact runNet_bool_const (bitonicMerge off k false) off h true g1 hnetL hg1L i hi_lt

private theorem sorted_asc_desc_bitonic (off h : Nat) (g : Nat → Bool)
    (hL : IsSortedBool off h true g) (hR : IsSortedBool (off + h) h false g) :
    IsBitonic off (2 * h) g := by
  have hexL : ∃ s ≤ h, ∀ i < h, g (off + i) = true ↔ s ≤ i := by
    have hgenL : ∀ n, IsSortedBool off n true g → ∃ s ≤ n, ∀ i < n, g (off + i) = true ↔ s ≤ i := by
      intro n
      induction n with
      | zero => intro _; exact ⟨0, Nat.le_refl 0, fun i hi => by omega⟩
      | succ m ih =>
        intro hLm
        rcases ih (fun i j hij hj => hLm i j hij (by omega)) with ⟨s, hsm, hs⟩
        cases hgm : g (off + m) with
        | false =>
          refine ⟨m + 1, Nat.le_refl _, fun i hi => ?_⟩
          constructor
          · intro ht
            by_cases him : i = m
            · subst him; rw [hgm] at ht; cases ht
            · have hgt := hLm i m (by omega) (by omega)
              simp only [↓reduceIte] at hgt
              have := hgt ht; rw [hgm] at this; cases this
          · intro hc; omega
        | true =>
          refine ⟨s, by omega, fun i hi => ?_⟩
          by_cases him : i = m
          · subst i; rw [hgm]; simp [show s ≤ m from hsm]
          · exact hs i (by omega)
    exact hgenL h hL
  have hexR : ∃ e ≤ h, ∀ i < h, g (off + h + i) = true ↔ i < e := by
    have hgen : ∀ n (g' : Nat → Bool), IsSortedBool 0 n false g' →
        ∃ e ≤ n, ∀ i < n, g' i = true ↔ i < e := by
      intro n g'
      induction n with
      | zero => intro _; exact ⟨0, Nat.le_refl 0, fun i hi => by omega⟩
      | succ m ih =>
        intro hg'
        rcases ih (fun i j hij hj => hg' i j hij (by omega)) with ⟨e, hem, he⟩
        cases hgm : g' m with
        | false =>
          refine ⟨e, by omega, fun i hi => ?_⟩
          by_cases him : i = m
          · subst i; rw [hgm]; simp [show ¬ m < e by omega]
          · exact he i (by omega)
        | true =>
          refine ⟨m + 1, Nat.le_refl _, fun i hi => ?_⟩
          constructor
          · intro _; omega
          · intro _
            have := hg' i m (by omega) (by omega)
            simp only [Nat.zero_add, Bool.false_eq_true, ↓reduceIte] at this
            exact this hgm
    have hR' : IsSortedBool 0 h false (fun i => g (off + h + i)) := by
      intro i j hij hj
      simpa only [Nat.zero_add] using hR i j hij hj
    exact hgen h (fun i => g (off + h + i)) hR'
  rcases hexL with ⟨s, hsh, hs⟩
  rcases hexR with ⟨e, heh, he⟩
  refine ⟨s, h + e, by omega, by omega, Or.inl (fun i hi => ?_)⟩
  by_cases hih : i < h
  · rw [hs i hih]
    omega
  · have e1 : off + i = off + h + (i - h) := by omega
    rw [e1, he (i - h) (by omega)]
    omega

private theorem bitonicSort_sorted_bool (off : Nat) : ∀ k asc (g : Nat → Bool),
    IsSortedBool off (2 ^ k) asc (runNet (fun b : Bool => b.toNat) (bitonicSort off k asc) g)
  | 0, asc, g => by
    intro i j hij hj
    have hi0 : i = 0 := by omega
    have hj0 : j = 0 := by omega
    subst hi0; subst hj0
    cases asc <;> exact fun h => h
  | k + 1, asc, g => by
    let h := 2 ^ k
    simp only [bitonicSort, runNet_append]
    let g1 := runNet (fun b : Bool => b.toNat) (bitonicSort off k true) g
    let g2 := runNet (fun b : Bool => b.toNat) (bitonicSort (off + h) k false) g1
    have hsL : IsSortedBool off h true g1 := bitonicSort_sorted_bool off k true g
    have hsR : IsSortedBool (off + h) h false g2 := bitonicSort_sorted_bool (off + h) k false g1
    have hg2L : IsSortedBool off h true g2 := by
      intro i j hij hj
      have e1 : g2 (off + i) = g1 (off + i) := by
        apply runNet_unchanged; intro c hc; have hm := bitonicSort_mem (off + h) k false c hc; dsimp [h] at hij hj ⊢; omega
      have e2 : g2 (off + j) = g1 (off + j) := by
        apply runNet_unchanged; intro c hc; have hm := bitonicSort_mem (off + h) k false c hc; dsimp [h] at hj ⊢; omega
      rw [e1, e2]
      exact hsL i j hij hj
    have hbit : IsBitonic off (2 ^ (k + 1)) g2 := by
      rw [Nat.pow_succ, Nat.mul_comm]
      exact sorted_asc_desc_bitonic off h g2 hg2L hsR
    exact bitonicMerge_sorted off (k + 1) asc g2 hbit

private theorem bitonicSort_sorted {α : Type*} (key : α → Nat) (p : Nat) (st : Nat → α) :
    ∀ i j, i ≤ j → j < 2 ^ p →
      key (runNet key (bitonicSort 0 p true) st i) ≤ key (runNet key (bitonicSort 0 p true) st j) := by
  intro i j hij hj
  let T := key (runNet key (bitonicSort 0 p true) st i)
  let f : Nat → Bool := fun x => decide (T ≤ x)
  have hf : ∀ x y, x ≤ y → f x = true → f y = true := by
    intro x y hxy hx
    simp only [f, decide_eq_true_eq] at hx ⊢
    omega
  have hs := bitonicSort_sorted_bool 0 p true (fun idx => f (key (st idx))) i j hij hj
  simp only [Nat.zero_add, ↓reduceIte] at hs
  rw [← runNet_mono_map key f hf] at hs
  have hiT : f (key (runNet key (bitonicSort 0 p true) st i)) = true := by
    simp [f, T]
  have hjT := hs hiT
  simp only [f, decide_eq_true_eq] at hjT
  exact hjT

end Bitonic
namespace Gadgets

open Build220 Bitonic
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

private theorem bitsVal_eq_iff (f g : Nat → Bool) : ∀ m,
    bitsVal f m = bitsVal g m ↔ ∀ i < m, f i = g i := by
  intro m
  constructor
  · intro h i hi
    rw [← bitsVal_testBit f m i hi, ← bitsVal_testBit g m i hi, h]
  · intro h
    induction m with
    | zero => rfl
    | succ m ih =>
      simp only [bitsVal, ih (fun i hi => h i (by omega)), h m (Nat.lt_succ_self m)]

private theorem bitsVal_testBit_self (a : Nat) : ∀ m, a < 2 ^ m →
    bitsVal (fun i => a.testBit i) m = a := by
  intro m hm
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < m
  · exact bitsVal_testBit (fun j => a.testBit j) m i hi
  · have h1 : (bitsVal (fun j => a.testBit j) m).testBit i = false :=
      Nat.testBit_lt_two_pow ((bitsVal_lt _ m).trans_le (Nat.pow_le_pow_right (by omega) (by omega)))
    have h2 : a.testBit i = false :=
      Nat.testBit_lt_two_pow (hm.trans_le (Nat.pow_le_pow_right (by omega) (by omega)))
    rw [h1, h2]

private theorem flatten_ofFn_length {α : Type*} : ∀ {p c : Nat} (g : Fin p → Fin c → α),
    ((List.ofFn (fun i : Fin p => List.ofFn (g i))).flatten).length = p * c
  | 0, _, _ => by simp
  | p + 1, c, g => by
    simp only [List.ofFn_succ, List.flatten_cons, List.length_append, List.length_ofFn,
      flatten_ofFn_length (fun i : Fin p => g i.succ)]
    ring

private theorem flatten_ofFn_getElem {α : Type*} : ∀ {p c : Nat} (g : Fin p → Fin c → α)
    (t : Nat) (ht : t < ((List.ofFn (fun i : Fin p => List.ofFn (g i))).flatten).length),
    have hc : 0 < c := by
      rw [flatten_ofFn_length] at ht
      by_contra h0
      have hc0 : c = 0 := by omega
      subst hc0; simp at ht
    ((List.ofFn (fun i : Fin p => List.ofFn (g i))).flatten)[t] =
      g ⟨t / c, (Nat.div_lt_iff_lt_mul hc).mpr (by rwa [flatten_ofFn_length] at ht)⟩
        ⟨t % c, Nat.mod_lt t hc⟩
  | 0, _, _, t, ht => by simp at ht
  | p + 1, c, g, t, ht => by
    have hc : 0 < c := by
      rw [flatten_ofFn_length] at ht
      by_contra h0
      have hc0 : c = 0 := by omega
      subst hc0; simp at ht
    simp only [List.ofFn_succ, List.flatten_cons]
    by_cases htc : t < c
    · rw [List.getElem_append_left (by simp [htc]), List.getElem_ofFn]
      have hdiv : t / c = 0 := Nat.div_eq_of_lt htc
      have hmod : t % c = t := Nat.mod_eq_of_lt htc
      congr 1
      · ext; exact hdiv.symm
      · ext; exact hmod.symm
    · rw [List.getElem_append_right (by simp; omega)]
      simp only [List.length_ofFn]
      rw [flatten_ofFn_getElem (fun i : Fin p => g i.succ) (t - c) (by
        rw [flatten_ofFn_length] at ht ⊢; rw [Nat.succ_mul] at ht; omega)]
      have hdiv : t / c = (t - c) / c + 1 := by
        have h1 : t = (t - c) + c := by omega
        conv_lhs => rw [h1]
        rw [Nat.add_div_right _ hc]
      have hmod : t % c = (t - c) % c := by
        have h1 : t = (t - c) + c := by omega
        conv_lhs => rw [h1]
        rw [Nat.add_mod_right]
      congr 1
      · ext; simp [hdiv]
      · ext; exact hmod.symm

private theorem wires_take_succ (gs : List Gate) (x : List Bool) (r : Nat) (hr : r < gs.length) :
    (Circuit.mk (gs.take (r + 1)) 0).wires x =
      (Circuit.mk (gs.take r) 0).wires x ++
        [(gs[r]).op.eval ((gs[r]).inputs.map (fun i => ((Circuit.mk (gs.take r) 0).wires x).getD i false))] := by
  simp only [Circuit.wires, List.take_succ_eq_append_getElem hr, List.foldl_append, List.foldl_cons,
    List.foldl_nil]

private theorem embedCircuit {I m_in : Nat} {A : Set (Sig I)}
    (C_sub : Circuit) (hfan : FanInTwo C_sub) (hrb : ReadsBack m_in C_sub)
    (inSig : Fin m_in → Sig I) (hin : ∀ k, inSig k ∈ A) :
    Build A {f | ∃ j < m_in + C_sub.size,
      f = fun x => (C_sub.wires (List.ofFn (fun k => inSig k x))).getD j false} C_sub.size := by
  have hpref : ∀ r ≤ C_sub.gates.length,
      Build A {f | ∃ j < m_in + r,
        f = fun x => ((Circuit.mk (C_sub.gates.take r) 0).wires
          (List.ofFn (fun k => inSig k x))).getD j false} r := by
    intro r
    induction r with
    | zero =>
      intro _
      refine relax (idle ?_) le_rfl le_rfl (by omega)
      rintro f ⟨j, hj, rfl⟩
      have hj' : j < m_in := by omega
      have he : (fun x => ((Circuit.mk (C_sub.gates.take 0) 0).wires
            (List.ofFn (fun k => inSig k x))).getD j false) = inSig ⟨j, hj'⟩ := by
        funext x
        simp only [List.take_zero, Circuit.wires, List.foldl_nil]
        rw [List.getD_eq_getElem _ _ (by simp [hj']), List.getElem_ofFn]
      rw [he]
      exact hin ⟨j, hj'⟩
    | succ r ih =>
      intro hr
      have Hprev := ih (by omega)
      let g := C_sub.gates[r]'(by omega)
      have hg_mem : g ∈ C_sub.gates := List.getElem_mem (by omega)
      have hg_fan := hfan g hg_mem
      have hg_rb : ∀ i ∈ g.inputs, i < m_in + r := by
        intro i hi
        have hrb_r := hrb r (by omega) i
        have hge : gateAt C_sub r = g := by
          dsimp only [gateAt, g]
          exact List.getD_eq_getElem _ _ (by omega)
        rw [hge] at hrb_r
        exact hrb_r hi
      let wPrev : Nat → Sig I := fun j x =>
        ((Circuit.mk (C_sub.gates.take r) 0).wires (List.ofFn (fun k => inSig k x))).getD j false
      let wNew : Sig I := fun x =>
        ((Circuit.mk (C_sub.gates.take (r + 1)) 0).wires
          (List.ofFn (fun k => inSig k x))).getD (m_in + r) false
      have hlen_prev : ∀ x, ((Circuit.mk (C_sub.gates.take r) 0).wires
          (List.ofFn (fun k => inSig k x))).length = m_in + r := by
        intro x
        rw [GateBridge.wireLength, List.length_ofFn, List.length_take, Nat.min_eq_left (by omega)]
      have Hstep : Build (A ∪ {f | ∃ j < m_in + r, f = wPrev j}) {wNew} 1 := by
        refine one g.op (g.inputs.map wPrev) hg_fan.1 (by simp [hg_fan.2]) ?_ wNew ?_
        · intro s hs
          obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hs
          exact Or.inr ⟨i, hg_rb i hi, rfl⟩
        · intro x
          dsimp only [wNew]
          rw [wires_take_succ C_sub.gates _ r (by omega),
            List.getD_append_right _ _ _ _ (by simp [hlen_prev x]), hlen_prev x, Nat.sub_self]
          simp only [List.getD_cons_zero, List.map_map, Function.comp_def, wPrev, g]
      refine relax (seq Hprev Hstep) le_rfl ?_ (by omega)
      rintro f ⟨j, hj, rfl⟩
      by_cases hjm : j < m_in + r
      · left
        refine ⟨j, hjm, ?_⟩
        funext x
        rw [wires_take_succ C_sub.gates _ r (by omega),
          List.getD_append _ _ _ _ (by rw [hlen_prev x]; exact hjm)]
      · right
        have hjeq : j = m_in + r := by omega
        subst hjeq
        rfl
  have hfull := hpref C_sub.gates.length le_rfl
  have htake : C_sub.gates.take C_sub.gates.length = C_sub.gates := List.take_length
  refine relax hfull le_rfl ?_ le_rfl
  rintro f ⟨j, hj, rfl⟩
  refine ⟨j, hj, ?_⟩
  funext x
  rw [htake]
  rfl

private theorem lookupRowG {n w q : Nat} {A : Set (Sig (n * 2 ^ (w + 1)))}
    (rowIdx : Fin n) (patSig : Fin q → Fin (w + 1) → Sig (n * 2 ^ (w + 1)))
    (hpat : ∀ j bit, patSig j bit ∈ A)
    (hIn : ∀ a : Fin (n * 2 ^ (w + 1)), (fun x => x a) ∈ A) :
    Build A
      {f | ∃ j : Fin q, f = fun x =>
        x ⟨rowIdx.val * 2 ^ (w + 1) +
          bitsVal (fun bit => if h : bit < w + 1 then patSig j ⟨bit, h⟩ x else false) (w + 1),
          by
            have hlt := bitsVal_lt
              (fun bit => if h : bit < w + 1 then patSig j ⟨bit, h⟩ x else false) (w + 1)
            have h1 : (rowIdx.val + 1) * 2 ^ (w + 1) ≤ n * 2 ^ (w + 1) :=
              Nat.mul_le_mul_right _ rowIdx.isLt
            rw [Nat.add_mul, Nat.one_mul] at h1
            omega⟩}
      (128 * (2 ^ (w + 1) + q) * (w + 1 + 1 + Nat.log2 (q + 1) + 3) ^ 3) := by
  obtain ⟨C_sub, outBit, hfan, hrb, _, hsize, heval⟩ := PEqualNP.Outside.L_clb_049 (w + 1) 1 q
  let words := 2 ^ (w + 1)
  let m_in := words * 1 + q * (w + 1)
  let inSig : Fin m_in → Sig (n * 2 ^ (w + 1)) := fun k =>
    if hk : k.val < words then
      fun x => x ⟨rowIdx.val * words + k.val, by
        have h1 : (rowIdx.val + 1) * words ≤ n * words := Nat.mul_le_mul_right _ rowIdx.isLt
        rw [Nat.add_mul, Nat.one_mul] at h1
        dsimp only [words] at h1 hk ⊢; omega⟩
    else
      let rem := k.val - words
      let j : Fin q := ⟨rem / (w + 1), (Nat.div_lt_iff_lt_mul (by omega)).mpr (by
        have := k.isLt; dsimp only [m_in, rem] at *; omega)⟩
      let bit : Fin (w + 1) := ⟨rem % (w + 1), Nat.mod_lt _ (by omega)⟩
      patSig j bit
  have hin : ∀ k, inSig k ∈ A := by
    intro k
    dsimp only [inSig]
    split_ifs with hk
    · exact hIn _
    · exact hpat _ _
  have Hemb := embedCircuit C_sub hfan hrb inSig hin
  refine relax Hemb le_rfl ?_ hsize
  rintro f ⟨j, rfl⟩
  refine ⟨(outBit j 0).val, (outBit j 0).isLt, ?_⟩
  funext x
  let tab : Fin words → Fin 1 → Bool := fun p _ =>
    x ⟨rowIdx.val * words + p.val, by
      have h1 : (rowIdx.val + 1) * words ≤ n * words := Nat.mul_le_mul_right _ rowIdx.isLt
      rw [Nat.add_mul, Nat.one_mul] at h1
      dsimp only [words] at h1 ⊢; have := p.isLt; omega⟩
  let addr : Fin q → Fin words := fun j' =>
    ⟨bitsVal (fun bit => if h : bit < w + 1 then patSig j' ⟨bit, h⟩ x else false) (w + 1),
      bitsVal_lt _ _⟩
  have hlist : List.ofFn (fun k : Fin m_in => inSig k x) =
      (List.ofFn (fun p : Fin words => List.ofFn (tab p))).flatten ++
      (List.ofFn (fun j' : Fin q =>
        List.ofFn (fun bit : Fin (w + 1) => (addr j').val.testBit bit.val))).flatten := by
    apply List.ext_getElem
    · simp only [List.length_ofFn, List.length_append, flatten_ofFn_length, m_in]
    · intro t ht1 ht2
      rw [List.getElem_ofFn]
      simp only [List.length_ofFn] at ht1
      by_cases htw : t < words
      · rw [List.getElem_append_left (by rw [flatten_ofFn_length]; omega),
          flatten_ofFn_getElem]
        dsimp only [inSig, tab]
        simp only [htw, ↓reduceDIte, Nat.div_one]
      · have hlen1 : (List.ofFn (fun p : Fin words => List.ofFn (tab p))).flatten.length = words := by
          rw [flatten_ofFn_length, Nat.mul_one]
        rw [List.getElem_append_right (by omega)]
        have hidx_eq : t - (List.ofFn (fun p : Fin words => List.ofFn (tab p))).flatten.length =
            t - words := by rw [hlen1]
        have ht2' : t - words < (List.ofFn (fun j' : Fin q =>
            List.ofFn (fun bit : Fin (w + 1) => (addr j').val.testBit bit.val))).flatten.length := by
          rw [flatten_ofFn_length]; dsimp only [m_in] at ht1; omega
        have hge : ((List.ofFn (fun j' : Fin q =>
            List.ofFn (fun bit : Fin (w + 1) => (addr j').val.testBit bit.val))).flatten)[
              t - (List.ofFn (fun p : Fin words => List.ofFn (tab p))).flatten.length]'(by
                rw [hidx_eq]; exact ht2') =
          ((List.ofFn (fun j' : Fin q =>
            List.ofFn (fun bit : Fin (w + 1) => (addr j').val.testBit bit.val))).flatten)[t - words]'ht2' := by
          congr 1
        rw [hge, flatten_ofFn_getElem]
        dsimp only [inSig, addr]
        simp only [htw, ↓reduceDIte]
        rw [bitsVal_testBit _ (w + 1) _ (Nat.mod_lt _ (by omega))]
        have hmlt : (t - words) % (w + 1) < w + 1 := Nat.mod_lt _ (by omega)
        simp only [hmlt, ↓reduceDIte]
  rw [hlist]
  exact (heval tab addr j 0).symm

private structure Rec2 (kb vb : Nat) where
  keyBit : Nat → Bool
  valBit : Fin vb → Bool

private def recKey2 {kb vb : Nat} (r : Rec2 kb vb) : Nat :=
  bitsVal r.keyBit kb

private theorem netCircuit2 {I kb vb : Nat} {A : Set (Sig I)} (N : Nat)
    (net : List (Nat × Nat × Bool))
    (hnet : ∀ c ∈ net, c.1 < N ∧ c.2.1 < N)
    (st0 : (Fin I → Bool) → Nat → Rec2 kb vb)
    (hK : ∀ idx < N, ∀ j < kb, (fun v => (st0 v idx).keyBit j) ∈ A)
    (hV : ∀ idx < N, ∀ j : Fin vb, (fun v => (st0 v idx).valBit j) ∈ A)
    (hfalse : (fun _ => false) ∈ A) :
    Build A
      ({f | ∃ idx < N, ∃ j < kb, f = fun v => (runNet recKey2 net (st0 v) idx).keyBit j} ∪
       {f | ∃ idx < N, ∃ j : Fin vb, f = fun v => (runNet recKey2 net (st0 v) idx).valBit j} ∪
       {f | ∃ t < net.length,
         f = (fun v => ((netSwaps recKey2 net (st0 v)).getD t (0, 0, false)).2.2) ∨
         f = (fun v => !(((netSwaps recKey2 net (st0 v)).getD t (0, 0, false)).2.2))})
      (net.length * (11 * kb + 6 * vb + 1)) := by
  induction net generalizing st0 A with
  | nil =>
    refine relax (idle ?_) le_rfl le_rfl (by simp)
    rintro f ((⟨idx, hidx, j, hj, rfl⟩ | ⟨idx, hidx, j, rfl⟩) | ⟨t, ht, _⟩)
    · exact hK idx hidx j hj
    · exact hV idx hidx j
    · simp at ht
  | cons c rest ih =>
    rcases c with ⟨u, v, asc⟩
    have hc := hnet (u, v, asc) List.mem_cons_self
    let swSig : Sig I := fun x => swapBit (recKey2 (st0 x u)) (recKey2 (st0 x v)) asc
    have Hsw : Build A {swSig} (5 * kb) := by
      cases asc with
      | true =>
        exact ltWordG (fun j x => (st0 x v).keyBit j) (fun j x => (st0 x u).keyBit j) kb
          (fun j hj => hK v hc.2 j hj) (fun j hj => hK u hc.1 j hj) hfalse
      | false =>
        exact ltWordG (fun j x => (st0 x u).keyBit j) (fun j x => (st0 x v).keyBit j) kb
          (fun j hj => hK u hc.1 j hj) (fun j hj => hK v hc.2 j hj) hfalse
    let nswSig : Sig I := nt swSig
    have Hnsw : Build (A ∪ {swSig}) {nswSig} 1 := notG (Or.inr rfl)
    let st1 : (Fin I → Bool) → Nat → Rec2 kb vb := fun x => applySwap u v (swSig x) (st0 x)
    let A1 := A ∪ ({swSig} ∪ {nswSig})
    have hsw1 : swSig ∈ A1 := Or.inr (Or.inl rfl)
    have hnsw1 : nswSig ∈ A1 := Or.inr (Or.inr rfl)
    let K1 : Fin kb → Sig I := fun j x => (st1 x u).keyBit j.val
    let K2 : Fin kb → Sig I := fun j x => (st1 x v).keyBit j.val
    let V1 : Fin vb → Sig I := fun j x => (st1 x u).valBit j
    let V2 : Fin vb → Sig I := fun j x => (st1 x v).valBit j
    have HK1 : Build A1 (Set.range K1) (kb * 3) := finG K1 3 fun j => by
      have he : K1 j = fun x => if swSig x then (st0 x v).keyBit j.val else (st0 x u).keyBit j.val := by
        funext x; simp only [K1, st1, applySwap]; cases swSig x <;> simp
      rw [he]
      exact muxG hsw1 hnsw1 (Or.inl (hK v hc.2 j.val j.isLt)) (Or.inl (hK u hc.1 j.val j.isLt)) (fun _ => rfl)
    have HK2 : Build (A1 ∪ Set.range K1) (Set.range K2) (kb * 3) := finG K2 3 fun j => by
      have he : K2 j = fun x => if swSig x then (st0 x u).keyBit j.val else (st0 x v).keyBit j.val := by
        funext x; simp only [K2, st1, applySwap]
        by_cases huv : v = u
        · subst huv; cases swSig x <;> simp
        · cases swSig x <;> simp [huv]
      rw [he]
      exact muxG (Or.inl hsw1) (Or.inl hnsw1) (Or.inl (Or.inl (hK u hc.1 j.val j.isLt)))
        (Or.inl (Or.inl (hK v hc.2 j.val j.isLt))) (fun _ => rfl)
    have HV1 : Build (A1 ∪ (Set.range K1 ∪ Set.range K2)) (Set.range V1) (vb * 3) := finG V1 3 fun j => by
      have he : V1 j = fun x => if swSig x then (st0 x v).valBit j else (st0 x u).valBit j := by
        funext x; simp only [V1, st1, applySwap]; cases swSig x <;> simp
      rw [he]
      exact muxG (Or.inl hsw1) (Or.inl hnsw1) (Or.inl (Or.inl (hV v hc.2 j)))
        (Or.inl (Or.inl (hV u hc.1 j))) (fun _ => rfl)
    have HV2 : Build (A1 ∪ ((Set.range K1 ∪ Set.range K2) ∪ Set.range V1)) (Set.range V2) (vb * 3) := finG V2 3 fun j => by
      have he : V2 j = fun x => if swSig x then (st0 x u).valBit j else (st0 x v).valBit j := by
        funext x; simp only [V2, st1, applySwap]
        by_cases huv : v = u
        · subst huv; cases swSig x <;> simp
        · cases swSig x <;> simp [huv]
      rw [he]
      exact muxG (Or.inl hsw1) (Or.inl hnsw1) (Or.inl (Or.inl (hV u hc.1 j)))
        (Or.inl (Or.inl (hV v hc.2 j))) (fun _ => rfl)
    let B1 := ({swSig} ∪ {nswSig}) ∪ (((Set.range K1 ∪ Set.range K2) ∪ Set.range V1) ∪ Set.range V2)
    have Hstep : Build A B1 (11 * kb + 6 * vb + 1) := by
      have H0 := seq Hsw Hnsw
      have H1 := seq (seq (seq HK1 HK2) HV1) HV2
      exact relax (seq H0 H1) le_rfl le_rfl (by omega)
    have hK1 : ∀ idx < N, ∀ j < kb, (fun x => (st1 x idx).keyBit j) ∈ A ∪ B1 := by
      intro idx hidx j hj
      by_cases hu : idx = u
      · subst hu; exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl ⟨⟨j, hj⟩, rfl⟩))))
      · by_cases hv : idx = v
        · subst hv; exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inr ⟨⟨j, hj⟩, rfl⟩))))
        · have he : (fun x => (st1 x idx).keyBit j) = (fun x => (st0 x idx).keyBit j) := by
            funext x; simp only [st1, applySwap]; cases swSig x <;> simp [hu, hv]
          rw [he]; exact Or.inl (hK idx hidx j hj)
    have hV1 : ∀ idx < N, ∀ j : Fin vb, (fun x => (st1 x idx).valBit j) ∈ A ∪ B1 := by
      intro idx hidx j
      by_cases hu : idx = u
      · subst hu; exact Or.inr (Or.inr (Or.inl (Or.inr ⟨j, rfl⟩)))
      · by_cases hv : idx = v
        · subst hv; exact Or.inr (Or.inr (Or.inr ⟨j, rfl⟩))
        · have he : (fun x => (st1 x idx).valBit j) = (fun x => (st0 x idx).valBit j) := by
            funext x; simp only [st1, applySwap]; cases swSig x <;> simp [hu, hv]
          rw [he]; exact Or.inl (hV idx hidx j)
    have Hrest := ih (fun c' hc' => hnet c' (List.mem_cons_of_mem _ hc')) st1 hK1 hV1 (Or.inl hfalse)
    refine relax (seq Hstep Hrest) le_rfl ?_ ?_
    · rintro f ((⟨idx, hidx, j, hj, rfl⟩ | ⟨idx, hidx, j, rfl⟩) | ⟨t, ht, hft⟩)
      · exact Or.inr (Or.inl (Or.inl ⟨idx, hidx, j, hj, rfl⟩))
      · exact Or.inr (Or.inl (Or.inr ⟨idx, hidx, j, rfl⟩))
      · cases t with
        | zero =>
          rcases hft with rfl | rfl
          · exact Or.inl (Or.inl (Or.inl rfl))
          · exact Or.inl (Or.inl (Or.inr rfl))
        | succ t =>
          simp only [List.length_cons] at ht
          exact Or.inr (Or.inr ⟨t, by omega, hft⟩)
    · simp only [List.length_cons]
      rw [Nat.succ_mul rest.length, Nat.add_comm]

private theorem netSwaps_length {α : Type*} (key : α → Nat) (net : List (Nat × Nat × Bool)) (st : Nat → α) :
    (netSwaps key net st).length = net.length := by
  induction net generalizing st with
  | nil => rfl
  | cons c rest ih =>
    rcases c with ⟨u, v, asc⟩
    simp [netSwaps, ih]

private theorem netSwaps_getD_uv {α : Type*} (key : α → Nat) (net : List (Nat × Nat × Bool)) (st : Nat → α) :
    ∀ t < net.length,
      ((netSwaps key net st).getD t (0, 0, false)).1 = (net.getD t (0, 0, false)).1 ∧
      ((netSwaps key net st).getD t (0, 0, false)).2.1 = (net.getD t (0, 0, false)).2.1 := by
  induction net generalizing st with
  | nil => intro t ht; simp at ht
  | cons c rest ih =>
    rcases c with ⟨u, v, asc⟩
    intro t ht
    cases t with
    | zero => simp [netSwaps]
    | succ t =>
      simp only [List.length_cons] at ht
      simpa [netSwaps] using ih _ t (by omega)

private theorem getD_reverse_eq {α : Type*} (l : List α) (d0 : α) (t : Nat) (ht : t < l.length) :
    l.reverse.getD t d0 = l.getD (l.length - 1 - t) d0 := by
  rw [List.getD_eq_getElem _ _ (by simp [ht]), List.getElem_reverse,
    List.getD_eq_getElem _ _ (by omega)]

private theorem replayCircuit2 {I b : Nat} {A : Set (Sig I)} (N : Nat)
    (sws : (Fin I → Bool) → List (Nat × Nat × Bool))
    (L : Nat) (hL : ∀ v, (sws v).length = L)
    (hidx_fixed : ∀ t < L, ∃ u v, u < N ∧ v < N ∧
      ∀ x, ((sws x).getD t (0, 0, false)).1 = u ∧ ((sws x).getD t (0, 0, false)).2.1 = v)
    (hsw_mem : ∀ t < L,
      (fun x => ((sws x).getD t (0, 0, false)).2.2) ∈ A ∧
      (fun x => !(((sws x).getD t (0, 0, false)).2.2)) ∈ A)
    (ans0 : (Fin I → Bool) → Nat → Fin b → Bool)
    (hA0 : ∀ idx < N, ∀ j : Fin b, (fun x => ans0 x idx j) ∈ A) :
    Build A {f | ∃ idx < N, ∃ j : Fin b, f = fun x => replaySwaps (sws x) (ans0 x) idx j} (L * (6 * b)) := by
  induction L generalizing sws ans0 A with
  | zero =>
    refine relax (idle ?_) le_rfl le_rfl (by simp)
    rintro f ⟨idx, hidx, j, rfl⟩
    have he : (fun x => replaySwaps (sws x) (ans0 x) idx j) = (fun x => ans0 x idx j) := by
      funext x
      have hnil : sws x = [] := List.eq_nil_of_length_eq_zero (hL x)
      rw [hnil]; rfl
    rw [he]; exact hA0 idx hidx j
  | succ L ih =>
    rcases hidx_fixed 0 (Nat.zero_lt_succ L) with ⟨u, v, hu, hv, huv⟩
    let swSig : Sig I := fun x => ((sws x).getD 0 (0, 0, false)).2.2
    let nswSig : Sig I := fun x => !(((sws x).getD 0 (0, 0, false)).2.2)
    have hsw0 := hsw_mem 0 (Nat.zero_lt_succ L)
    let ans1 : (Fin I → Bool) → Nat → Fin b → Bool := fun x => applySwap u v (swSig x) (ans0 x)
    let V1 : Fin b → Sig I := fun j x => ans1 x u j
    let V2 : Fin b → Sig I := fun j x => ans1 x v j
    have HV1 : Build A (Set.range V1) (b * 3) := finG V1 3 fun j => by
      have he : V1 j = fun x => if swSig x then ans0 x v j else ans0 x u j := by
        funext x; simp only [V1, ans1, applySwap]; cases swSig x <;> simp
      rw [he]
      exact muxG hsw0.1 hsw0.2 (hA0 v hv j) (hA0 u hu j) (fun _ => rfl)
    have HV2 : Build (A ∪ Set.range V1) (Set.range V2) (b * 3) := finG V2 3 fun j => by
      have he : V2 j = fun x => if swSig x then ans0 x u j else ans0 x v j := by
        funext x; simp only [V2, ans1, applySwap]
        by_cases hvu : v = u
        · subst hvu; cases swSig x <;> simp
        · cases swSig x <;> simp [hvu]
      rw [he]
      exact muxG (Or.inl hsw0.1) (Or.inl hsw0.2) (Or.inl (hA0 u hu j)) (Or.inl (hA0 v hv j)) (fun _ => rfl)
    have Hstep := seq HV1 HV2
    let sws' : (Fin I → Bool) → List (Nat × Nat × Bool) := fun x => (sws x).tail
    have hL' : ∀ x, (sws' x).length = L := by intro x; simp [sws', List.length_tail, hL x]
    have hget_tail : ∀ t < L, ∀ x, (sws' x).getD t (0, 0, false) = (sws x).getD (t + 1) (0, 0, false) := by
      intro t ht x
      cases hs : sws x with
      | nil => have := hL x; rw [hs] at this; simp at this
      | cons c cs => simp [sws', hs]
    have hidx' : ∀ t < L, ∃ u' v', u' < N ∧ v' < N ∧
        ∀ x, ((sws' x).getD t (0, 0, false)).1 = u' ∧ ((sws' x).getD t (0, 0, false)).2.1 = v' := by
      intro t ht
      rcases hidx_fixed (t + 1) (by omega) with ⟨u', v', hu', hv', hEq⟩
      exact ⟨u', v', hu', hv', fun x => by rw [hget_tail t ht x]; exact hEq x⟩
    have hsw' : ∀ t < L,
        (fun x => ((sws' x).getD t (0, 0, false)).2.2) ∈ A ∪ (Set.range V1 ∪ Set.range V2) ∧
        (fun x => !(((sws' x).getD t (0, 0, false)).2.2)) ∈ A ∪ (Set.range V1 ∪ Set.range V2) := by
      intro t ht
      have h1 := hsw_mem (t + 1) (by omega)
      have e1 : (fun x => ((sws' x).getD t (0, 0, false)).2.2) = (fun x => ((sws x).getD (t + 1) (0, 0, false)).2.2) := by
        funext x; rw [hget_tail t ht x]
      have e2 : (fun x => !(((sws' x).getD t (0, 0, false)).2.2)) = (fun x => !(((sws x).getD (t + 1) (0, 0, false)).2.2)) := by
        funext x; rw [hget_tail t ht x]
      rw [e1, e2]
      exact ⟨Or.inl h1.1, Or.inl h1.2⟩
    have hA1 : ∀ idx < N, ∀ j : Fin b, (fun x => ans1 x idx j) ∈ A ∪ (Set.range V1 ∪ Set.range V2) := by
      intro idx hidx j
      by_cases h1 : idx = u
      · subst h1; exact Or.inr (Or.inl ⟨j, rfl⟩)
      · by_cases h2 : idx = v
        · subst h2; exact Or.inr (Or.inr ⟨j, rfl⟩)
        · have he : (fun x => ans1 x idx j) = (fun x => ans0 x idx j) := by
            funext x; simp only [ans1, applySwap]; cases swSig x <;> simp [h1, h2]
          rw [he]; exact Or.inl (hA0 idx hidx j)
    have Hrest := ih sws' hL' hidx' hsw' ans1 hA1
    refine relax (seq Hstep Hrest) le_rfl ?_ ?_
    · rintro f ⟨idx, hidx, j, rfl⟩
      right
      refine ⟨idx, hidx, j, ?_⟩
      funext x
      cases hs : sws x with
      | nil => have := hL x; rw [hs] at this; simp at this
      | cons c cs =>
        have h0 := huv x; rw [hs] at h0; simp only [List.getD_cons_zero] at h0
        rcases c with ⟨cu, cv, csw⟩; dsimp only at h0; rcases h0 with ⟨rfl, rfl⟩
        have he_sw : swSig x = csw := by simp [swSig, hs]
        simp only [replaySwaps, sws', hs, List.tail_cons, ans1, he_sw]
    · rw [Nat.succ_mul L]; omega

private theorem replayReverseCircuit {I kb vb b : Nat} {A : Set (Sig I)} (N : Nat)
    (net : List (Nat × Nat × Bool))
    (hnet : ∀ c ∈ net, c.1 < N ∧ c.2.1 < N)
    (st0 : (Fin I → Bool) → Nat → Rec2 kb vb)
    (hsw_mem : ∀ t < net.length,
      (fun x => ((netSwaps recKey2 net (st0 x)).getD t (0, 0, false)).2.2) ∈ A ∧
      (fun x => !(((netSwaps recKey2 net (st0 x)).getD t (0, 0, false)).2.2)) ∈ A)
    (ans0 : (Fin I → Bool) → Nat → Fin b → Bool)
    (hA0 : ∀ idx < N, ∀ j : Fin b, (fun x => ans0 x idx j) ∈ A) :
    Build A {f | ∃ idx < N, ∃ j : Fin b,
      f = fun x => replaySwaps (netSwaps recKey2 net (st0 x)).reverse (ans0 x) idx j}
      (net.length * (6 * b)) := by
  refine replayCircuit2 N (fun x => (netSwaps recKey2 net (st0 x)).reverse) net.length
    (fun x => by simp [netSwaps_length]) ?_ ?_ ans0 hA0
  · intro t ht
    let idx := net.length - 1 - t
    have hidx : idx < net.length := by omega
    let c := net.getD idx (0, 0, false)
    have hc_mem : c ∈ net := by
      dsimp only [c]; rw [List.getD_eq_getElem _ _ hidx]; exact List.getElem_mem hidx
    have hcb := hnet c hc_mem
    refine ⟨c.1, c.2.1, hcb.1, hcb.2, fun x => ?_⟩
    rw [getD_reverse_eq _ _ t (by rw [netSwaps_length]; exact ht), netSwaps_length]
    exact netSwaps_getD_uv recKey2 net (st0 x) idx hidx
  · intro t ht
    let idx := net.length - 1 - t
    have hidx : idx < net.length := by omega
    have h1 := hsw_mem idx hidx
    have he1 : (fun x => ((netSwaps recKey2 net (st0 x)).reverse.getD t (0, 0, false)).2.2) =
        (fun x => ((netSwaps recKey2 net (st0 x)).getD idx (0, 0, false)).2.2) := by
      funext x
      rw [getD_reverse_eq _ _ t (by rw [netSwaps_length]; exact ht), netSwaps_length]
    have he2 : (fun x => !(((netSwaps recKey2 net (st0 x)).reverse.getD t (0, 0, false)).2.2)) =
        (fun x => !(((netSwaps recKey2 net (st0 x)).getD idx (0, 0, false)).2.2)) := by
      funext x
      rw [getD_reverse_eq _ _ t (by rw [netSwaps_length]; exact ht), netSwaps_length]
    rw [he1, he2]
    exact h1

private def dupScan {b : Nat} (isRep : Nat → Bool) (repVal : Nat → Fin b → Bool) :
    Nat → (Fin b → Bool) × (Nat → Fin b → Bool)
  | 0 => (fun _ => false, fun _ _ => false)
  | t + 1 =>
    let prev := dupScan isRep repVal t
    let cur' := fun j => if isRep t then repVal t j else prev.1 j
    (cur', fun idx => if idx = t then cur' else prev.2 idx)

private theorem dupScanCircuit {I b : Nat} {A : Set (Sig I)} (N : Nat)
    (isRep : (Fin I → Bool) → Nat → Bool)
    (repVal : (Fin I → Bool) → Nat → Fin b → Bool)
    (hRep : ∀ idx < N, (fun x => isRep x idx) ∈ A)
    (hVal : ∀ idx < N, ∀ j : Fin b, (fun x => repVal x idx j) ∈ A)
    (hfalse : (fun _ => false) ∈ A) :
    ∀ m ≤ N,
      Build A
        ({f | ∃ j : Fin b, f = fun x => (dupScan (isRep x) (repVal x) m).1 j} ∪
         {f | ∃ idx < m, ∃ j : Fin b, f = fun x => (dupScan (isRep x) (repVal x) m).2 idx j})
        (m * (3 * b + 1)) := by
  intro m
  induction m with
  | zero =>
    intro _
    refine relax (idle ?_) le_rfl le_rfl (by simp)
    rintro f (⟨j, rfl⟩ | ⟨idx, hidx, _⟩)
    · exact hfalse
    · omega
  | succ m ih =>
    intro hm
    have Hprev := ih (by omega)
    let Bprev :=
      {f | ∃ j : Fin b, f = fun x => (dupScan (isRep x) (repVal x) m).1 j} ∪
      {f | ∃ idx < m, ∃ j : Fin b, f = fun x => (dupScan (isRep x) (repVal x) m).2 idx j}
    let A1 := A ∪ Bprev
    let rSig : Sig I := fun x => isRep x m
    have Hnr : Build A1 {nt rSig} 1 := notG (Or.inl (hRep m (by omega)))
    let curF : Fin b → Sig I := fun j x => (dupScan (isRep x) (repVal x) (m + 1)).1 j
    have Hcur : Build (A1 ∪ {nt rSig}) (Set.range curF) (b * 3) := finG curF 3 fun j => by
      have he : curF j = fun x => if rSig x then repVal x m j else (dupScan (isRep x) (repVal x) m).1 j := rfl
      rw [he]
      exact muxG (Or.inl (Or.inl (hRep m (by omega)))) (Or.inr rfl)
        (Or.inl (Or.inl (hVal m (by omega) j)))
        (Or.inl (Or.inr (Or.inl ⟨j, rfl⟩)))
        (fun _ => rfl)
    refine relax (seq Hprev (seq Hnr Hcur)) le_rfl ?_ ?_
    · rintro f (⟨j, rfl⟩ | ⟨idx, hidx, j, rfl⟩)
      · exact Or.inr (Or.inr ⟨j, rfl⟩)
      · by_cases hjm : idx = m
        · subst hjm
          exact Or.inr (Or.inr ⟨j, by funext x; simp [curF, dupScan]⟩)
        · exact Or.inl (Or.inr ⟨idx, by omega, j, by funext x; simp [dupScan, hjm]⟩)
    · rw [Nat.succ_mul m]; omega

private def anyNat {I : Nat} (F : Nat → Sig I) : Nat → Sig I
  | 0 => fun _ => false
  | m + 1 => fun x => anyNat F m x || F m x

private theorem anyNatG {I : Nat} {A : Set (Sig I)} (F : Nat → Sig I) (hfalse : (fun _ => false) ∈ A) :
    ∀ m, (∀ j < m, F j ∈ A) → Build A {anyNat F m} m := by
  intro m
  induction m with
  | zero =>
    intro _
    exact relax (idle (Set.singleton_subset_iff.mpr hfalse)) le_rfl le_rfl (by omega)
  | succ m ih =>
    intro hF
    have H1 := ih (fun j hj => hF j (by omega))
    have H2 : Build (A ∪ {anyNat F m}) {or (anyNat F m) (F m)} 1 :=
      orG (Or.inr rfl) (Or.inl (hF m (Nat.lt_succ_self m)))
    exact relax (seq H1 H2) le_rfl (Set.singleton_subset_iff.mpr (Or.inr rfl)) (by omega)

private theorem anyNat_eq_true {I : Nat} (F : Nat → Sig I) (x : Fin I → Bool) :
    ∀ m, anyNat F m x = true ↔ ∃ j < m, F j x = true
  | 0 => by simp [anyNat]
  | m + 1 => by
    simp only [anyNat, Bool.or_eq_true, anyNat_eq_true F x m]
    constructor
    · rintro (⟨j, hj, h⟩ | h)
      · exact ⟨j, by omega, h⟩
      · exact ⟨m, Nat.lt_succ_self m, h⟩
    · rintro ⟨j, hj, h⟩
      by_cases hjm : j = m
      · subst hjm; exact Or.inr h
      · exact Or.inl ⟨j, by omega, h⟩

private def allNat {I : Nat} (F : Nat → Sig I) : Nat → Sig I
  | 0 => fun _ => true
  | m + 1 => fun x => allNat F m x && F m x

private theorem allNatG {I : Nat} {A : Set (Sig I)} (F : Nat → Sig I) (htrue : (fun _ => true) ∈ A) :
    ∀ m, (∀ j < m, F j ∈ A) → Build A {allNat F m} m := by
  intro m
  induction m with
  | zero =>
    intro _
    exact relax (idle (Set.singleton_subset_iff.mpr htrue)) le_rfl le_rfl (by omega)
  | succ m ih =>
    intro hF
    have H1 := ih (fun j hj => hF j (by omega))
    have H2 : Build (A ∪ {allNat F m}) {an (allNat F m) (F m)} 1 :=
      andG (Or.inr rfl) (Or.inl (hF m (Nat.lt_succ_self m)))
    exact relax (seq H1 H2) le_rfl (Set.singleton_subset_iff.mpr (Or.inr rfl)) (by omega)

private theorem allNat_eq_true {I : Nat} (F : Nat → Sig I) (x : Fin I → Bool) :
    ∀ m, allNat F m x = true ↔ ∀ j < m, F j x = true
  | 0 => by simp [allNat]
  | m + 1 => by
    simp only [allNat, Bool.and_eq_true, allNat_eq_true F x m]
    constructor
    · rintro ⟨h1, h2⟩ j hj
      by_cases hjm : j = m
      · subst hjm; exact h2
      · exact h1 j (by omega)
    · intro h
      exact ⟨fun j hj => h j (by omega), h m (Nat.lt_succ_self m)⟩

end Gadgets
namespace PcxAlgo

open Build220 Bitonic Gadgets
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

private def posFn (n : Nat) (hn : 0 < n) (v : Nat) : Fin n :=
  ⟨v % n, Nat.mod_lt _ hn⟩

private def tabEval {n w : Nat} (x : Fin (n * 2 ^ (w + 1)) → Bool)
    (rowIdx : Fin n) (pat : Fin (w + 1) → Bool) : Bool :=
  x ⟨rowIdx.val * 2 ^ (w + 1) +
    bitsVal (fun bit => if h : bit < w + 1 then pat ⟨bit, h⟩ else false) (w + 1),
    by
      have hlt := bitsVal_lt (fun bit => if h : bit < w + 1 then pat ⟨bit, h⟩ else false) (w + 1)
      have h1 : (rowIdx.val + 1) * 2 ^ (w + 1) ≤ n * 2 ^ (w + 1) :=
        Nat.mul_le_mul_right _ rowIdx.isLt
      rw [Nat.add_mul, Nat.one_mul] at h1
      omega⟩

private def extPat {w : Nat} (z : Fin w → Bool) (b : Bool) (k : Fin (w + 1)) : Bool :=
  if hk : k.val < w then z ⟨k.val, hk⟩ else b

private def nextZ {w : Nat} (z : Fin w → Bool) (b : Bool) (r : Fin w) : Bool :=
  if hr : r.val + 1 < w then z ⟨r.val + 1, hr⟩ else b

private def wrapPat {w : Nat} (a z : Fin w → Bool) (offset : Fin w) (k : Fin (w + 1)) : Bool :=
  if hk : offset.val + k.val < w then z ⟨offset.val + k.val, hk⟩
  else a ⟨offset.val + k.val - w, by have := offset.isLt; have := k.isLt; omega⟩

private abbrev LayerState (w K : Nat) := Fin K → Bool × (Fin w → Bool) × (Fin w → Bool)

private def sortPow (K : Nat) : Nat :=
  Nat.log2 (2 * K - 1) + 1

private theorem sortPow_bounds {w K : Nat} (hKlo : 2 ^ w ≤ K) (hKhi : K ≤ 4 ^ w) :
    2 * K ≤ 2 ^ sortPow K ∧ 2 ^ sortPow K < 4 * K ∧ sortPow K ≤ 2 * w + 1 := by
  have hKpos : 1 ≤ K := (Nat.two_pow_pos w).trans_le hKlo
  have hne : 2 * K - 1 ≠ 0 := by omega
  have hlt := Nat.lt_log2_self (n := 2 * K - 1)
  have hle := Nat.log2_self_le hne
  have h1 : 2 * K ≤ 2 ^ sortPow K := by dsimp [sortPow]; omega
  have h2 : 2 ^ sortPow K < 4 * K := by
    dsimp [sortPow]
    rw [Nat.pow_succ, Nat.mul_comm]
    omega
  have h3 : sortPow K ≤ 2 * w + 1 := by
    dsimp [sortPow]
    have h4w : 4 ^ w = 2 ^ (2 * w) := by
      rw [show (4 : Nat) = 2 ^ 2 by rfl, ← Nat.pow_mul]
    have hlt2 : 2 * K - 1 < 2 ^ (2 * w + 1) := by
      rw [Nat.pow_succ, Nat.mul_comm, ← h4w]; omega
    by_contra hgt
    have hge : 2 * w + 1 ≤ Nat.log2 (2 * K - 1) := by omega
    have hp := Nat.pow_le_pow_right Nat.zero_lt_two hge
    omega
  exact ⟨h1, h2, h3⟩

private def sortNet (K : Nat) : List (Nat × Nat × Bool) :=
  bitonicSort 0 (sortPow K) true

private theorem sortNet_bounds {w K : Nat} (hKlo : 2 ^ w ≤ K) (hKhi : K ≤ 4 ^ w) :
    (∀ c ∈ sortNet K, c.1 < 2 ^ sortPow K ∧ c.2.1 < 2 ^ sortPow K) ∧
    (sortNet K).length ≤ (2 * w + 1) * (2 * w + 2) * K := by
  rcases sortPow_bounds hKlo hKhi with ⟨_, hNlt, hple⟩
  constructor
  · intro c hc
    have hm := bitonicSort_mem 0 (sortPow K) true c hc
    omega
  · have hl := bitonicSort_length 0 (sortPow K) true
    have h1 : sortPow K * (sortPow K + 1) ≤ (2 * w + 1) * (2 * w + 2) :=
      Nat.mul_le_mul hple (by omega)
    have h2 : sortPow K * (sortPow K + 1) * 2 ^ sortPow K ≤
        (2 * w + 1) * (2 * w + 2) * (4 * K) :=
      Nat.mul_le_mul h1 (Nat.le_of_lt hNlt)
    have h3 : (2 * w + 1) * (2 * w + 2) * (4 * K) =
        4 * ((2 * w + 1) * (2 * w + 2) * K) := by ring
    dsimp [sortNet]
    omega

private def childLookup {n w K : Nat} (hn : 0 < n) (h : Nat) (st : LayerState w K)
    (x : Fin (n * 2 ^ (w + 1)) → Bool) (idx : Fin (2 * K)) : Bool :=
  let parent : Fin K := ⟨idx.val / 2, (Nat.div_lt_iff_lt_mul (by omega)).mpr (by
    have := idx.isLt; omega)⟩
  let b : Bool := decide (idx.val % 2 = 1)
  tabEval x (posFn n hn h) (extPat (st parent).2.2 b)

private def childRec1 {n w K : Nat} (hn : 0 < n) (h : Nat) (st : LayerState w K)
    (x : Fin (n * 2 ^ (w + 1)) → Bool) (idx : Nat) : Rec2 (2 * w + 1) 0 :=
  if hidx : idx < 2 * K then
    let parent : Fin K := ⟨idx / 2, (Nat.div_lt_iff_lt_mul (by omega)).mpr (by omega)⟩
    let b : Bool := decide (idx % 2 = 1)
    let valid := (st parent).1 && childLookup hn h st x ⟨idx, hidx⟩
    let a := (st parent).2.1
    let z' := nextZ (st parent).2.2 b
    ⟨fun j => if hj : j < w then a ⟨j, hj⟩
              else if hj2 : j < 2 * w then z' ⟨j - w, by omega⟩
              else !valid,
     fun j => j.elim0⟩
  else
    ⟨fun j => if j < 2 * w then false else true, fun j => j.elim0⟩

private def sorted1 {n w K : Nat} (hn : 0 < n) (h : Nat) (st : LayerState w K)
    (x : Fin (n * 2 ^ (w + 1)) → Bool) : Nat → Rec2 (2 * w + 1) 0 :=
  runNet recKey2 (sortNet K) (childRec1 hn h st x)

private def swaps1 {n w K : Nat} (hn : 0 < n) (h : Nat) (st : LayerState w K)
    (x : Fin (n * 2 ^ (w + 1)) → Bool) : List (Nat × Nat × Bool) :=
  netSwaps recKey2 (sortNet K) (childRec1 hn h st x)

private def isRepFn {n w K : Nat} (hn : 0 < n) (h : Nat) (st : LayerState w K)
    (x : Fin (n * 2 ^ (w + 1)) → Bool) (idx : Nat) : Bool :=
  let s := sorted1 hn h st x
  let v := !((s idx).keyBit (2 * w))
  if idx = 0 then v
  else v && decide (recKey2 (s (idx - 1)) < recKey2 (s idx))

private def childRec2 {n w K : Nat} (hn : 0 < n) (h : Nat) (st : LayerState w K)
    (x : Fin (n * 2 ^ (w + 1)) → Bool) (idx : Nat) : Rec2 1 (2 * w + 1) :=
  let s := sorted1 hn h st x idx
  let rep := isRepFn hn h st x idx
  ⟨fun _ => !rep,
   fun j => if j.val < 2 * w then s.keyBit j.val else rep⟩

private def sorted2 {n w K : Nat} (hn : 0 < n) (h : Nat) (st : LayerState w K)
    (x : Fin (n * 2 ^ (w + 1)) → Bool) : Nat → Rec2 1 (2 * w + 1) :=
  runNet recKey2 (sortNet K) (childRec2 hn h st x)

private def swaps2 {n w K : Nat} (hn : 0 < n) (h : Nat) (st : LayerState w K)
    (x : Fin (n * 2 ^ (w + 1)) → Bool) : List (Nat × Nat × Bool) :=
  netSwaps recKey2 (sortNet K) (childRec2 hn h st x)

private def fwdStep {n w K : Nat} (hn : 0 < n) (h : Nat) (st : LayerState w K)
    (x : Fin (n * 2 ^ (w + 1)) → Bool) : LayerState w K :=
  fun i =>
    let r := sorted2 hn h st x i.val
    (r.valBit ⟨2 * w, by omega⟩,
     fun j : Fin w => r.valBit ⟨j.val, by omega⟩,
     fun j : Fin w => r.valBit ⟨w + j.val, by omega⟩)

private def fwdInit (w K : Nat) : LayerState w K :=
  fun i =>
    if i.val < 2 ^ w then
      (true, fun r => i.val.testBit r.val, fun r => i.val.testBit r.val)
    else
      (false, fun _ => false, fun _ => false)

private def fwdLayer {n w K : Nat} (hn : 0 < n) :
    Nat → (Fin (n * 2 ^ (w + 1)) → Bool) → LayerState w K
  | 0, _ => fwdInit w K
  | h + 1, x => fwdStep hn h (fwdLayer hn h x) x

private def wrapLookup {n w K : Nat} (hn : 0 < n)
    (x : Fin (n * 2 ^ (w + 1)) → Bool) (offset : Fin w) (i : Fin K) : Bool :=
  let st := fwdLayer hn (n - w) x i
  tabEval x (posFn n hn (n - w + offset.val)) (wrapPat st.2.1 st.2.2 offset)

private def survivesFn {n w K : Nat} (hn : 0 < n)
    (x : Fin (n * 2 ^ (w + 1)) → Bool) (i : Fin K) : Bool :=
  (fwdLayer hn (n - w) x i).1 &&
    allNat (fun off x' => if h : off < w then wrapLookup hn x' ⟨off, h⟩ i else true) w x

private def evalOutFn {n w K : Nat} (hn : 0 < n)
    (x : Fin (n * 2 ^ (w + 1)) → Bool) : Bool :=
  !(anyNat (fun idx x' => if h : idx < K then survivesFn hn x' ⟨idx, h⟩ else false) K x)

private def termScan {n w K : Nat} (hn : 0 < n) (i : Fin K) :
    Nat → (Fin (n * 2 ^ (w + 1)) → Bool) → Bool × (Fin (2 * w) → Bool)
  | 0, _ => (false, fun _ => false)
  | m + 1, x =>
    let prev := termScan hn i m x
    let okm := if hm : m < w then wrapLookup hn x ⟨m, hm⟩ i else true
    let pick := !prev.1 && !okm
    (prev.1 || !okm,
     fun j =>
       if pick then
         if j.val < w then decide (j.val ≤ m)
         else decide (m ≤ j.val - w)
       else prev.2 j)

private def termMask {n w K : Nat} (hn : 0 < n) (x : Fin (n * 2 ^ (w + 1)) → Bool)
    (i : Fin K) : Fin (2 * w) → Bool :=
  (termScan hn i w x).2

private def childClauseMask {n w K : Nat} (hn : 0 < n) (h : Nat)
    (clNext : Fin K → Fin (2 * w) → Bool) (x : Fin (n * 2 ^ (w + 1)) → Bool) :
    Nat → Fin (2 * w) → Bool :=
  let st : LayerState w K := fwdLayer hn h x
  let N := 2 ^ sortPow K
  let ans2 : Nat → Fin (2 * w) → Bool := fun idx =>
    if hidx : idx < K then clNext ⟨idx, hidx⟩ else fun _ => false
  let unp2 := replaySwaps (swaps2 hn h st x).reverse ans2
  let sc := (dupScan (isRepFn hn h st x) unp2 N).2
  replaySwaps (swaps1 hn h st x).reverse sc

private def childMaskAt {n w K : Nat} (hn : 0 < n) (h : Nat)
    (clNext : Fin K → Fin (2 * w) → Bool) (x : Fin (n * 2 ^ (w + 1)) → Bool)
    (i : Fin K) (b : Bool) : (Fin (2 * w) → Bool) × Bool :=
  let st : LayerState w K := fwdLayer hn h x
  let cIdx : Fin (2 * K) := ⟨2 * i.val + b.toNat, by cases b <;> (dsimp; omega)⟩
  let ok := childLookup hn h st x cIdx
  let cm := childClauseMask hn h clNext x cIdx.val
  let mask : Fin (2 * w) → Bool := fun j =>
    if j.val < w then
      if ok then cm j else false
    else
      if ok then
        if j.val = w then false else cm ⟨j.val - 1, by omega⟩
      else true
  let piv : Bool :=
    if ok then
      if hw : 0 < w then cm ⟨2 * w - 1, by omega⟩ else false
    else true
  (mask, piv)

private def parentStep {n w K : Nat} (hn : 0 < n) (h : Nat)
    (clNext : Fin K → Fin (2 * w) → Bool) (x : Fin (n * 2 ^ (w + 1)) → Bool)
    (i : Fin K) : (Fin (2 * w) → Bool) × Bool :=
  let d0 := childMaskAt hn h clNext x i false
  let d1 := childMaskAt hn h clNext x i true
  let doRes := d0.2 && d1.2
  let mask : Fin (2 * w) → Bool := fun j =>
    if !d0.2 then d0.1 j
    else if !d1.2 then d1.1 j
    else (d0.1 j || d1.1 j)
  (mask, doRes)

private def bwdMaskAux {n w K : Nat} (hn : 0 < n) :
    Nat → (Fin (n * 2 ^ (w + 1)) → Bool) → Fin K → Fin (2 * w) → Bool
  | 0, x => termMask hn x
  | r + 1, x =>
    let h := n - w - (r + 1)
    let clNext := bwdMaskAux hn r x
    fun i => (parentStep hn h clNext x i).1

private def bwdMask {n w K : Nat} (hn : 0 < n) (h : Nat)
    (x : Fin (n * 2 ^ (w + 1)) → Bool) : Fin K → Fin (2 * w) → Bool :=
  bwdMaskAux hn (n - w - h) x

private def seedMaskAux {n w K : Nat} (hn : 0 < n) (hKlo : 2 ^ w ≤ K) :
    (r : Nat) → r ≤ w → (Fin (n * 2 ^ (w + 1)) → Bool) →
      Fin (2 ^ (w - r)) → Fin (w - r) → Bool
  | 0, _, x, idx, j =>
    let cl0 := bwdMask hn 0 x ⟨idx.val, idx.isLt.trans_le (by simpa using hKlo)⟩
    cl0 ⟨j.val, by omega⟩ || cl0 ⟨w + j.val, by omega⟩
  | r + 1, hr, x, idx, j =>
    let d_lev := w - (r + 1)
    have hstep : w - r = d_lev + 1 := by omega
    let idxL : Fin (2 ^ (w - r)) := ⟨idx.val, by
      have h1 : idx.val < 2 ^ d_lev := idx.isLt
      have h2 : 2 ^ d_lev < 2 ^ (w - r) := Nat.pow_lt_pow_right (by omega) (by omega)
      omega⟩
    let idxR : Fin (2 ^ (w - r)) := ⟨idx.val + 2 ^ d_lev, by
      have h1 : idx.val < 2 ^ d_lev := idx.isLt
      have h2 : 2 ^ (w - r) = 2 ^ d_lev + 2 ^ d_lev := by
        rw [hstep, Nat.pow_succ]; omega
      omega⟩
    let mL := seedMaskAux hn hKlo r (by omega) x idxL
    let mR := seedMaskAux hn hKlo r (by omega) x idxR
    let pivL := mL ⟨d_lev, by omega⟩
    let pivR := mR ⟨d_lev, by omega⟩
    if !pivL then mL ⟨j.val, by omega⟩
    else if !pivR then mR ⟨j.val, by omega⟩
    else (mL ⟨j.val, by omega⟩ || mR ⟨j.val, by omega⟩)

private def seedDoRes {n w K : Nat} (hn : 0 < n) (hKlo : 2 ^ w ≤ K)
    (d_lev : Nat) (hd : d_lev < w) (x : Fin (n * 2 ^ (w + 1)) → Bool)
    (idx : Fin (2 ^ d_lev)) : Bool :=
  let r := w - (d_lev + 1)
  have hr : r ≤ w := by omega
  have hwr : w - r = d_lev + 1 := by omega
  let idxL : Fin (2 ^ (w - r)) := ⟨idx.val, by
    have h1 : idx.val < 2 ^ d_lev := idx.isLt
    have h2 : 2 ^ d_lev < 2 ^ (w - r) := Nat.pow_lt_pow_right (by omega) (by omega)
    omega⟩
  let idxR : Fin (2 ^ (w - r)) := ⟨idx.val + 2 ^ d_lev, by
    have h1 : idx.val < 2 ^ d_lev := idx.isLt
    have h2 : 2 ^ (w - r) = 2 ^ d_lev + 2 ^ d_lev := by rw [hwr, Nat.pow_succ]; omega
    omega⟩
  seedMaskAux hn hKlo r hr x idxL ⟨d_lev, by omega⟩ &&
    seedMaskAux hn hKlo r hr x idxR ⟨d_lev, by omega⟩

private def seedMaskAt {n w K : Nat} (hn : 0 < n) (hKlo : 2 ^ w ≤ K)
    (d_lev : Nat) (hd : d_lev ≤ w) (x : Fin (n * 2 ^ (w + 1)) → Bool)
    (idx : Fin (2 ^ d_lev)) (j : Fin d_lev) : Bool :=
  let r := w - d_lev
  have hr : r ≤ w := by omega
  have hwr : w - r = d_lev := by omega
  seedMaskAux hn hKlo r hr x ⟨idx.val, hwr.symm ▸ idx.isLt⟩ ⟨j.val, hwr.symm ▸ j.isLt⟩

private def clauseMemBit {n w : Nat} (h : Nat) (a z : Fin w → Bool)
    (mask : Fin (2 * w) → Bool) (lit : PEqualNP.ProofComplexity.Literal (Fin n)) : Bool :=
  let v := lit.1
  let sg := lit.2
  let tA := if hv : v.val < w then mask ⟨v.val, by omega⟩ && (!(a ⟨v.val, hv⟩) == sg) else false
  let tZ := if hv : h ≤ v.val ∧ v.val < h + w then
      mask ⟨w + (v.val - h), by omega⟩ && (!(z ⟨v.val - h, by omega⟩) == sg)
    else false
  tA || tZ

private def axiomMemBit {n w : Nat} (h : Nat) (z : Fin w → Bool) (b : Bool)
    (lit : PEqualNP.ProofComplexity.Literal (Fin n)) : Bool :=
  let v := lit.1
  let sg := lit.2
  if hv : h ≤ v.val ∧ v.val < h + w then !(z ⟨v.val - h, by omega⟩) == sg
  else if v.val = h + w then !b == sg
  else false

private def slotEnable {n w K : Nat} (hn : 0 < n) (hKlo : 2 ^ w ≤ K)
    (s : Fin ((3 * (n - w) + 2) * K)) (x : Fin (n * 2 ^ (w + 1)) → Bool) : Bool :=
  if s.val < K then
    if hs : s.val + 1 < 2 ^ w then
      let d_lev := Nat.log2 (s.val + 1)
      have hd : d_lev < w := by
        by_contra hge
        have hp := Nat.pow_le_pow_right Nat.zero_lt_two (show w ≤ d_lev by omega)
        have hl := Nat.log2_self_le (show s.val + 1 ≠ 0 by omega)
        dsimp only [d_lev] at hp hl; omega
      let idx : Fin (2 ^ d_lev) := ⟨s.val + 1 - 2 ^ d_lev, by
        have hlt := Nat.lt_log2_self (n := s.val + 1)
        have hle := Nat.log2_self_le (show s.val + 1 ≠ 0 by omega)
        rw [Nat.pow_succ] at hlt
        dsimp only [d_lev] at hlt hle ⊢; omega⟩
      seedDoRes hn hKlo d_lev hd x idx
    else false
  else if hs2 : s.val < K + (n - w) * (3 * K) then
    let rem := s.val - K
    have hKpos : 0 < K := (Nat.two_pow_pos w).trans_le hKlo
    let h := rem / (3 * K)
    let inH := rem % (3 * K)
    let kind := inH / K
    let i : Fin K := ⟨inH % K, Nat.mod_lt _ hKpos⟩
    let st : LayerState w K := fwdLayer hn h x
    if kind = 0 then
      (st i).1 && (parentStep hn h (bwdMask hn (h + 1) x) x i).2
    else if kind = 1 then
      (st i).1 && !(childLookup hn h st x ⟨2 * i.val, by have := i.isLt; omega⟩)
    else
      (st i).1 && !(childLookup hn h st x ⟨2 * i.val + 1, by have := i.isLt; omega⟩)
  else
    let i : Fin K := ⟨s.val - (K + (n - w) * (3 * K)), by
      have := s.isLt
      have hS : (3 * (n - w) + 2) * K = K + (n - w) * (3 * K) + K := by ring
      omega⟩
    (fwdLayer hn (n - w) x i).1

private def slotMember {n w K : Nat} (hn : 0 < n) (hKlo : 2 ^ w ≤ K)
    (s : Fin ((3 * (n - w) + 2) * K))
    (lit : PEqualNP.ProofComplexity.Literal (Fin n))
    (x : Fin (n * 2 ^ (w + 1)) → Bool) : Bool :=
  if s.val < K then
    if hs : s.val + 1 < 2 ^ w then
      let d_lev := Nat.log2 (s.val + 1)
      have hd : d_lev < w := by
        by_contra hge
        have hp := Nat.pow_le_pow_right Nat.zero_lt_two (show w ≤ d_lev by omega)
        have hl := Nat.log2_self_le (show s.val + 1 ≠ 0 by omega)
        dsimp only [d_lev] at hp hl; omega
      let idx : Fin (2 ^ d_lev) := ⟨s.val + 1 - 2 ^ d_lev, by
        have hlt := Nat.lt_log2_self (n := s.val + 1)
        have hle := Nat.log2_self_le (show s.val + 1 ≠ 0 by omega)
        rw [Nat.pow_succ] at hlt
        dsimp only [d_lev] at hlt hle ⊢; omega⟩
      if hv : lit.1.val < d_lev then
        if !(idx.val.testBit lit.1.val) == lit.2 then
          seedMaskAt hn hKlo d_lev (by omega) x idx ⟨lit.1.val, hv⟩
        else false
      else false
    else false
  else if hs2 : s.val < K + (n - w) * (3 * K) then
    let rem := s.val - K
    have hKpos : 0 < K := (Nat.two_pow_pos w).trans_le hKlo
    let h := rem / (3 * K)
    let inH := rem % (3 * K)
    let kind := inH / K
    let i : Fin K := ⟨inH % K, Nat.mod_lt _ hKpos⟩
    let st : LayerState w K := fwdLayer hn h x
    if kind = 0 then
      clauseMemBit h (st i).2.1 (st i).2.2 (bwdMask hn h x i) lit
    else if kind = 1 then
      axiomMemBit h (st i).2.2 false lit
    else
      axiomMemBit h (st i).2.2 true lit
  else
    let i : Fin K := ⟨s.val - (K + (n - w) * (3 * K)), by
      have := s.isLt
      have hS : (3 * (n - w) + 2) * K = K + (n - w) * (3 * K) + K := by ring
      omega⟩
    let st : LayerState w K := fwdLayer hn (n - w) x
    clauseMemBit (n - w) (st i).2.1 (st i).2.2 (termMask hn x i) lit

end PcxAlgo
namespace PcxBuild

open Build220 Bitonic Gadgets PcxAlgo
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

private theorem buildSelf {I c : Nat} {A B : Set (Sig I)} (h : Build A B c) :
    Build A (A ∪ B) c := by
  refine ⟨trivial, ?_⟩
  intro m S HS hA
  obtain ⟨c', hc', HS'⟩ := h.run HS hA
  refine ⟨c', hc', GateBridge.restrict HS' ?_⟩
  rintro f (hf | (hf | hf))
  · exact Or.inl hf
  · exact Or.inl (hA hf)
  · exact Or.inr hf

private theorem stepU {I c1 c2 : Nat} {A A1 B : Set (Sig I)}
    (h1 : Build A A1 c1) (h2 : Build A1 B c2) : Build A (A1 ∪ B) (c1 + c2) :=
  seq h1 (relax h2 Set.subset_union_right le_rfl le_rfl)

private theorem lookup_cost_bound {n w K q : Nat} (hn : 0 < n) (hwn : w ≤ n)
    (hKlo : 2 ^ w ≤ K) (hKhi : K ≤ 4 ^ w) (hq : q ≤ 2 * K) :
    128 * (2 ^ (w + 1) + q) * (w + 1 + 1 + Nat.log2 (q + 1) + 3) ^ 3 ≤
      64000 * (n + 1) ^ 3 * K := by
  have hKpos : 1 ≤ K := (Nat.two_pow_pos w).trans_le hKlo
  have h2w1 : 2 ^ (w + 1) ≤ 2 * K := by rw [Nat.pow_succ, Nat.mul_comm]; omega
  have hsum : 2 ^ (w + 1) + q ≤ 4 * K := by omega
  have h4w : 4 ^ w = 2 ^ (2 * w) := by rw [show (4 : Nat) = 2 ^ 2 by rfl, ← Nat.pow_mul]
  rw [h4w] at hKhi
  have hlog : Nat.log2 (q + 1) ≤ 2 * w + 1 := by
    by_cases hq0 : q + 1 = 0
    · omega
    · by_contra hgt
      have hge : 2 * w + 2 ≤ Nat.log2 (q + 1) := by omega
      have hp := Nat.pow_le_pow_right Nat.zero_lt_two hge
      have hle := Nat.log2_self_le hq0
      have h22 : 2 ^ (2 * w + 2) = 4 * 2 ^ (2 * w) := by
        rw [Nat.pow_succ, Nat.pow_succ]; ring
      omega
  have hbase : w + 1 + 1 + Nat.log2 (q + 1) + 3 ≤ 5 * (n + 1) := by omega
  have hcub : (w + 1 + 1 + Nat.log2 (q + 1) + 3) ^ 3 ≤ (5 * (n + 1)) ^ 3 :=
    Nat.pow_le_pow_left hbase 3
  have hmul : (2 ^ (w + 1) + q) * (w + 1 + 1 + Nat.log2 (q + 1) + 3) ^ 3 ≤
      (4 * K) * (5 * (n + 1)) ^ 3 := Nat.mul_le_mul hsum hcub
  calc 128 * (2 ^ (w + 1) + q) * (w + 1 + 1 + Nat.log2 (q + 1) + 3) ^ 3
      = 128 * ((2 ^ (w + 1) + q) * (w + 1 + 1 + Nat.log2 (q + 1) + 3) ^ 3) := by ring
    _ ≤ 128 * ((4 * K) * (5 * (n + 1)) ^ 3) := Nat.mul_le_mul_left 128 hmul
    _ = 64000 * (n + 1) ^ 3 * K := by ring

private def StateSet {n w K : Nat} (st : (Fin (n * 2 ^ (w + 1)) → Bool) → LayerState w K) :
    Set (Sig (n * 2 ^ (w + 1))) :=
  {f | ∃ i : Fin K, f = (fun x => (st x i).1) ∨
    (∃ r : Fin w, f = (fun x => (st x i).2.1 r)) ∨
    (∃ r : Fin w, f = (fun x => (st x i).2.2 r))}

private def FwdStepOut {n w K : Nat} (hn : 0 < n) (h : Nat)
    (st : (Fin (n * 2 ^ (w + 1)) → Bool) → LayerState w K) :
    Set (Sig (n * 2 ^ (w + 1))) :=
  StateSet (fun x => fwdStep hn h (st x) x) ∪
  {f | ∃ idx : Fin (2 * K), f = fun x => childLookup hn h (st x) x idx} ∪
  {f | ∃ idx < 2 ^ sortPow K, f = fun x => isRepFn hn h (st x) x idx} ∪
  {f | ∃ t < (sortNet K).length,
    f = (fun x => ((swaps1 hn h (st x) x).getD t (0, 0, false)).2.2) ∨
    f = (fun x => !(((swaps1 hn h (st x) x).getD t (0, 0, false)).2.2))} ∪
  {f | ∃ t < (sortNet K).length,
    f = (fun x => ((swaps2 hn h (st x) x).getD t (0, 0, false)).2.2) ∨
    f = (fun x => !(((swaps2 hn h (st x) x).getD t (0, 0, false)).2.2))}

private theorem build_fwdStep {n w K : Nat} (hn : 0 < n) (hwn : w ≤ n)
    (hKlo : 2 ^ w ≤ K) (hKhi : K ≤ 4 ^ w) {A : Set (Sig (n * 2 ^ (w + 1)))}
    (hIn : ∀ a : Fin (n * 2 ^ (w + 1)), (fun x => x a) ∈ A)
    (hF : (fun _ => false) ∈ A) (hT : (fun _ => true) ∈ A)
    (h : Nat) (st : (Fin (n * 2 ^ (w + 1)) → Bool) → LayerState w K)
    (hSt : StateSet st ⊆ A) :
    Build A (FwdStepOut hn h st) (65000 * (n + 1) ^ 3 * K) := by
  let I := n * 2 ^ (w + 1)
  let N := 2 ^ sortPow K
  rcases sortPow_bounds hKlo hKhi with ⟨hNlo, hNhi, _⟩
  rcases sortNet_bounds hKlo hKhi with ⟨hnet_mem, hnet_len⟩
  let patSig : Fin (2 * K) → Fin (w + 1) → Sig I := fun idx bit x =>
    let parent : Fin K := ⟨idx.val / 2, (Nat.div_lt_iff_lt_mul (by omega)).mpr (by have := idx.isLt; omega)⟩
    extPat (st x parent).2.2 (decide (idx.val % 2 = 1)) bit
  have hpat : ∀ idx bit, patSig idx bit ∈ A := by
    intro idx bit
    dsimp only [patSig, extPat]
    split_ifs with hbit
    · exact hSt ⟨_, Or.inr (Or.inr ⟨⟨bit.val, hbit⟩, rfl⟩)⟩
    · cases decide (idx.val % 2 = 1)
      · exact hF
      · exact hT
  have Hlook : Build A {f | ∃ idx : Fin (2 * K), f = fun x => childLookup hn h (st x) x idx}
      (64000 * (n + 1) ^ 3 * K) := by
    refine relax (lookupRowG (posFn n hn h) patSig hpat hIn) le_rfl ?_
      (lookup_cost_bound hn hwn hKlo hKhi le_rfl)
    rintro f ⟨idx, rfl⟩
    exact ⟨idx, rfl⟩
  let A1 := A ∪ {f | ∃ idx : Fin (2 * K), f = fun x => childLookup hn h (st x) x idx}
  let nvSig : Fin (2 * K) → Sig I := fun idx x =>
    !((st x ⟨idx.val / 2, (Nat.div_lt_iff_lt_mul (by omega)).mpr (by have := idx.isLt; omega)⟩).1 &&
      childLookup hn h (st x) x idx)
  have Hnv : Build A1 (Set.range nvSig) (2 * K * 2) := finG nvSig 2 fun idx => by
    let parent : Fin K := ⟨idx.val / 2, (Nat.div_lt_iff_lt_mul (by omega)).mpr (by have := idx.isLt; omega)⟩
    have h1 : Build A1 {an (fun x => (st x parent).1) (fun x => childLookup hn h (st x) x idx)} 1 :=
      andG (Or.inl (hSt ⟨parent, Or.inl rfl⟩)) (Or.inr ⟨idx, rfl⟩)
    have h2 : Build (A1 ∪ {an (fun x => (st x parent).1) (fun x => childLookup hn h (st x) x idx)})
        {nvSig idx} 1 := notG (Or.inr rfl)
    exact relax (seq h1 h2) le_rfl (Set.singleton_subset_iff.mpr (Or.inr rfl)) (by omega)
  let A2 := A1 ∪ Set.range nvSig
  have hK1 : ∀ idx < N, ∀ j < 2 * w + 1, (fun x => (childRec1 hn h (st x) x idx).keyBit j) ∈ A2 := by
    intro idx _ j hj
    dsimp only [childRec1]
    by_cases hidx : idx < 2 * K
    · simp only [hidx, ↓reduceDIte]
      by_cases hj1 : j < w
      · simp only [hj1, ↓reduceDIte]
        exact Or.inl (Or.inl (hSt ⟨_, Or.inr (Or.inl ⟨⟨j, hj1⟩, rfl⟩)⟩))
      · by_cases hj2 : j < 2 * w
        · simp only [hj1, hj2, ↓reduceDIte, nextZ]
          by_cases hr : j - w + 1 < w
          · simp only [hr, ↓reduceDIte]
            exact Or.inl (Or.inl (hSt ⟨_, Or.inr (Or.inr ⟨⟨j - w + 1, hr⟩, rfl⟩)⟩))
          · simp only [hr, ↓reduceDIte]
            cases decide (idx % 2 = 1)
            · exact Or.inl (Or.inl hF)
            · exact Or.inl (Or.inl hT)
        · simp only [hj1, hj2, ↓reduceDIte]
          exact Or.inr ⟨⟨idx, hidx⟩, rfl⟩
    · simp only [hidx, ↓reduceDIte]
      by_cases hj2 : j < 2 * w
      · simp only [hj2, ↓reduceIte]; exact Or.inl (Or.inl hF)
      · simp only [hj2, ↓reduceIte]; exact Or.inl (Or.inl hT)
  have Hsort1 := netCircuit2 (A := A2) (kb := 2 * w + 1) (vb := 0) N (sortNet K) hnet_mem
    (fun x => childRec1 hn h (st x) x) hK1 (fun _ _ j => j.elim0) (Or.inl (Or.inl hF))
  let Bsort1 :=
    ({f | ∃ idx < N, ∃ j < 2 * w + 1, f = fun x => (sorted1 hn h (st x) x idx).keyBit j} ∪
     {f | ∃ idx < N, ∃ j : Fin 0, f = fun x => (sorted1 hn h (st x) x idx).valBit j} ∪
     {f | ∃ t < (sortNet K).length,
       f = (fun x => ((swaps1 hn h (st x) x).getD t (0, 0, false)).2.2) ∨
       f = (fun x => !(((swaps1 hn h (st x) x).getD t (0, 0, false)).2.2))})
  let A3 := A2 ∪ Bsort1
  let repSig : Fin N → Sig I := fun idx x => isRepFn hn h (st x) x idx.val
  let nrepSig : Fin N → Sig I := fun idx x => !(isRepFn hn h (st x) x idx.val)
  have Hrep : Build A3 (Set.range repSig ∪ Set.range nrepSig) (N * (10 * w + 8)) := by
    have h1 : Build A3 (Set.range repSig) (N * (10 * w + 7)) := finG repSig (10 * w + 7) fun idx => by
      dsimp only [repSig, isRepFn]
      by_cases h0 : idx.val = 0
      · simp only [h0, ↓reduceIte]
        have hv : (fun x => (sorted1 hn h (st x) x 0).keyBit (2 * w)) ∈ A3 :=
          Or.inr (Or.inl (Or.inl ⟨0, by omega, 2 * w, by omega, rfl⟩))
        exact relax (notG hv) le_rfl le_rfl (by omega)
      · simp only [h0, ↓reduceIte]
        have hv : (fun x => (sorted1 hn h (st x) x idx.val).keyBit (2 * w)) ∈ A3 :=
          Or.inr (Or.inl (Or.inl ⟨idx.val, idx.isLt, 2 * w, by omega, rfl⟩))
        let ltSig : Sig I := fun x => decide (recKey2 (sorted1 hn h (st x) x (idx.val - 1)) <
          recKey2 (sorted1 hn h (st x) x idx.val))
        have hlt : Build A3 {ltSig} (5 * (2 * w + 1)) :=
          ltWordG (fun j x => (sorted1 hn h (st x) x (idx.val - 1)).keyBit j)
            (fun j x => (sorted1 hn h (st x) x idx.val).keyBit j) (2 * w + 1)
            (fun j hj => Or.inr (Or.inl (Or.inl ⟨idx.val - 1, by omega, j, hj, rfl⟩)))
            (fun j hj => Or.inr (Or.inl (Or.inl ⟨idx.val, idx.isLt, j, hj, rfl⟩)))
            (Or.inl (Or.inl (Or.inl hF)))
        let nvS : Sig I := nt (fun x => (sorted1 hn h (st x) x idx.val).keyBit (2 * w))
        have hnv : Build (A3 ∪ {ltSig}) {nvS} 1 := notG (Or.inl hv)
        have hand : Build (A3 ∪ ({ltSig} ∪ {nvS})) {an nvS ltSig} 1 :=
          andG (Or.inr (Or.inr rfl)) (Or.inr (Or.inl rfl))
        exact relax (seq (seq hlt hnv) hand) le_rfl (Set.singleton_subset_iff.mpr (Or.inr rfl)) (by omega)
    have h2 : Build (A3 ∪ Set.range repSig) (Set.range nrepSig) (N * 1) :=
      finG nrepSig 1 fun idx => notG (Or.inr ⟨idx, rfl⟩)
    exact relax (seq h1 h2) le_rfl le_rfl (by rw [← Nat.mul_add])
  let A4 := A3 ∪ (Set.range repSig ∪ Set.range nrepSig)
  have hK2 : ∀ idx < N, ∀ j < 1, (fun x => (childRec2 hn h (st x) x idx).keyBit j) ∈ A4 := by
    intro idx hidx _ _
    exact Or.inr (Or.inr ⟨⟨idx, hidx⟩, rfl⟩)
  have hV2 : ∀ idx < N, ∀ j : Fin (2 * w + 1), (fun x => (childRec2 hn h (st x) x idx).valBit j) ∈ A4 := by
    intro idx hidx j
    dsimp only [childRec2]
    split_ifs with hj
    · exact Or.inl (Or.inr (Or.inl (Or.inl ⟨idx, hidx, j.val, by omega, rfl⟩)))
    · exact Or.inr (Or.inl ⟨⟨idx, hidx⟩, rfl⟩)
  have Hsort2 := netCircuit2 (A := A4) (kb := 1) (vb := 2 * w + 1) N (sortNet K) hnet_mem
    (fun x => childRec2 hn h (st x) x) hK2 hV2 (Or.inl (Or.inl (Or.inl (Or.inl hF))))
  have Htot := stepU (stepU (stepU (stepU (buildSelf Hlook) Hnv) Hsort1) Hrep) Hsort2
  refine relax Htot le_rfl ?_ ?_
  · rintro f ((((hStOut | ⟨idx, rfl⟩) | ⟨idx, hidx, rfl⟩) | ⟨t, ht, hsw1⟩) | ⟨t, ht, hsw2⟩)
    · rcases hStOut with ⟨i, rfl | ⟨r, rfl⟩ | ⟨r, rfl⟩⟩
      · exact Or.inr (Or.inl (Or.inr ⟨i.val, by omega, ⟨2 * w, by omega⟩, rfl⟩))
      · exact Or.inr (Or.inl (Or.inr ⟨i.val, by omega, ⟨r.val, by omega⟩, rfl⟩))
      · exact Or.inr (Or.inl (Or.inr ⟨i.val, by omega, ⟨w + r.val, by omega⟩, rfl⟩))
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨idx, rfl⟩))))
    · exact Or.inl (Or.inr (Or.inl ⟨⟨idx, hidx⟩, rfl⟩))
    · exact Or.inl (Or.inl (Or.inr (Or.inr ⟨t, ht, hsw1⟩)))
    · exact Or.inr (Or.inr ⟨t, ht, hsw2⟩)
  · have hstep1 : (sortNet K).length * (11 * (2 * w + 1) + 6 * 0 + 1) +
        (sortNet K).length * (11 * 1 + 6 * (2 * w + 1) + 1) =
        (sortNet K).length * (34 * w + 30) := by ring
    have hnet_cub : (sortNet K).length * (34 * w + 30) ≤
        ((2 * w + 1) * (2 * w + 2) * K) * (34 * w + 30) :=
      Nat.mul_le_mul_right _ hnet_len
    have hpoly : (2 * w + 1) * (2 * w + 2) * (34 * w + 30) ≤ 256 * (n + 1) ^ 3 := by
      have h1 : 2 * w + 1 ≤ 2 * (n + 1) := by omega
      have h2 : 2 * w + 2 ≤ 2 * (n + 1) := by omega
      have h3 : 34 * w + 30 ≤ 34 * (n + 1) := by omega
      calc (2 * w + 1) * (2 * w + 2) * (34 * w + 30)
          ≤ (2 * (n + 1)) * (2 * (n + 1)) * (34 * (n + 1)) :=
            Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3
        _ = 136 * (n + 1) ^ 3 := by ring
        _ ≤ 256 * (n + 1) ^ 3 := Nat.mul_le_mul_right _ (by omega)
    have hnet_final : (sortNet K).length * (34 * w + 30) ≤ 256 * (n + 1) ^ 3 * K := by
      calc (sortNet K).length * (34 * w + 30)
          ≤ ((2 * w + 1) * (2 * w + 2) * K) * (34 * w + 30) := hnet_cub
        _ = ((2 * w + 1) * (2 * w + 2) * (34 * w + 30)) * K := by ring
        _ ≤ (256 * (n + 1) ^ 3) * K := Nat.mul_le_mul_right K hpoly
    have hrep_le : N * (10 * w + 8) ≤ 40 * (n + 1) ^ 3 * K := by
      have h1 : 10 * w + 8 ≤ 10 * (n + 1) := by omega
      have h2 : 1 ≤ (n + 1) ^ 2 := Nat.one_le_pow 2 (n + 1) (by omega)
      have h3 : n + 1 ≤ (n + 1) * (n + 1) ^ 2 := Nat.le_mul_of_pos_right _ (by omega)
      calc N * (10 * w + 8) ≤ (4 * K) * (10 * (n + 1)) := Nat.mul_le_mul (Nat.le_of_lt hNhi) h1
        _ = 40 * (n + 1) * K := by ring
        _ ≤ 40 * ((n + 1) * (n + 1) ^ 2) * K := Nat.mul_le_mul_right K (Nat.mul_le_mul_left 40 h3)
        _ = 40 * (n + 1) ^ 3 * K := by ring
    have hnv_le : 2 * K * 2 ≤ 4 * (n + 1) ^ 3 * K := by
      have h1 : 1 ≤ (n + 1) ^ 3 := Nat.one_le_pow 3 (n + 1) (by omega)
      calc 2 * K * 2 = 4 * 1 * K := by ring
        _ ≤ 4 * (n + 1) ^ 3 * K := Nat.mul_le_mul_right K (Nat.mul_le_mul_left 4 h1)
    have hsum_le : 64000 * (n + 1) ^ 3 * K + 2 * K * 2 +
        (sortNet K).length * (11 * (2 * w + 1) + 6 * 0 + 1) + N * (10 * w + 8) +
        (sortNet K).length * (11 * 1 + 6 * (2 * w + 1) + 1) ≤
        (64000 + 4 + 256 + 40) * ((n + 1) ^ 3 * K) := by
      have ha : 64000 * (n + 1) ^ 3 * K = 64000 * ((n + 1) ^ 3 * K) := by ring
      have hb : 4 * (n + 1) ^ 3 * K = 4 * ((n + 1) ^ 3 * K) := by ring
      have hc : 256 * (n + 1) ^ 3 * K = 256 * ((n + 1) ^ 3 * K) := by ring
      have hd : 40 * (n + 1) ^ 3 * K = 40 * ((n + 1) ^ 3 * K) := by ring
      omega
    calc 64000 * (n + 1) ^ 3 * K + 2 * K * 2 +
          (sortNet K).length * (11 * (2 * w + 1) + 6 * 0 + 1) + N * (10 * w + 8) +
          (sortNet K).length * (11 * 1 + 6 * (2 * w + 1) + 1)
        ≤ 64300 * ((n + 1) ^ 3 * K) := hsum_le
      _ ≤ 65000 * ((n + 1) ^ 3 * K) := Nat.mul_le_mul_right _ (by omega)
      _ = 65000 * (n + 1) ^ 3 * K := by ring

private def FwdAllSet {n w K : Nat} (hn : 0 < n) (m : Nat) : Set (Sig (n * 2 ^ (w + 1))) :=
  {f | ∃ h ≤ m, f ∈ StateSet (fwdLayer (K := K) hn h)} ∪
  {f | ∃ h < m, f ∈ FwdStepOut (K := K) hn h (fwdLayer (K := K) hn h)}

private theorem build_fwdAll {n w K : Nat} (hn : 0 < n) (hwn : w ≤ n)
    (hKlo : 2 ^ w ≤ K) (hKhi : K ≤ 4 ^ w) {A : Set (Sig (n * 2 ^ (w + 1)))}
    (hIn : ∀ a : Fin (n * 2 ^ (w + 1)), (fun x => x a) ∈ A)
    (hF : (fun _ => false) ∈ A) (hT : (fun _ => true) ∈ A) :
    ∀ m, Build A (FwdAllSet (K := K) hn m) (m * (65000 * (n + 1) ^ 3 * K)) := by
  intro m
  induction m with
  | zero =>
    refine relax (idle ?_) le_rfl le_rfl (by simp)
    rintro f (⟨h, hh, hst⟩ | ⟨h, hh, _⟩)
    · have h0 : h = 0 := by omega
      subst h0
      rcases hst with ⟨i, rfl | ⟨r, rfl⟩ | ⟨r, rfl⟩⟩
      · dsimp only [fwdLayer, fwdInit]
        by_cases hi : i.val < 2 ^ w
        · simp only [hi, ↓reduceIte]; exact hT
        · simp only [hi, ↓reduceIte]; exact hF
      · dsimp only [fwdLayer, fwdInit]
        by_cases hi : i.val < 2 ^ w
        · cases htb : i.val.testBit r.val
          · have he : (fun _ : Fin (n * 2 ^ (w + 1)) → Bool =>
                (if i.val < 2 ^ w then (true, fun (r : Fin w) => i.val.testBit r.val, fun (r : Fin w) => i.val.testBit r.val)
                 else (false, fun _ => false, fun _ => false)).2.1 r) = fun _ => false := by
              funext _; simp [hi, htb]
            rw [he]; exact hF
          · have he : (fun _ : Fin (n * 2 ^ (w + 1)) → Bool =>
                (if i.val < 2 ^ w then (true, fun (r : Fin w) => i.val.testBit r.val, fun (r : Fin w) => i.val.testBit r.val)
                 else (false, fun _ => false, fun _ => false)).2.1 r) = fun _ => true := by
              funext _; simp [hi, htb]
            rw [he]; exact hT
        · simp only [hi, ↓reduceIte]; exact hF
      · dsimp only [fwdLayer, fwdInit]
        by_cases hi : i.val < 2 ^ w
        · cases htb : i.val.testBit r.val
          · have he : (fun _ : Fin (n * 2 ^ (w + 1)) → Bool =>
                (if i.val < 2 ^ w then (true, fun (r : Fin w) => i.val.testBit r.val, fun (r : Fin w) => i.val.testBit r.val)
                 else (false, fun _ => false, fun _ => false)).2.2 r) = fun _ => false := by
              funext _; simp [hi, htb]
            rw [he]; exact hF
          · have he : (fun _ : Fin (n * 2 ^ (w + 1)) → Bool =>
                (if i.val < 2 ^ w then (true, fun (r : Fin w) => i.val.testBit r.val, fun (r : Fin w) => i.val.testBit r.val)
                 else (false, fun _ => false, fun _ => false)).2.2 r) = fun _ => true := by
              funext _; simp [hi, htb]
            rw [he]; exact hT
        · simp only [hi, ↓reduceIte]; exact hF
    · omega
  | succ m ih =>
    have Hstep := build_fwdStep hn hwn hKlo hKhi (A := A ∪ FwdAllSet (K := K) hn m)
      (fun a => Or.inl (hIn a)) (Or.inl hF) (Or.inl hT) m (fwdLayer hn m)
      (fun f hf => Or.inr (Or.inl ⟨m, le_rfl, hf⟩))
    refine relax (seq ih Hstep) le_rfl ?_ ?_
    · rintro f (⟨h, hh, hst⟩ | ⟨h, hh, hso⟩)
      · by_cases hhm : h ≤ m
        · exact Or.inl (Or.inl ⟨h, hhm, hst⟩)
        · have heq : h = m + 1 := by omega
          subst heq
          exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl hst))))
      · by_cases hhm : h < m
        · exact Or.inl (Or.inr ⟨h, hhm, hso⟩)
        · have heq : h = m := by omega
          subst heq
          exact Or.inr hso
    · rw [Nat.succ_mul m]

private def WrapOutSet {n w K : Nat} (hn : 0 < n) : Set (Sig (n * 2 ^ (w + 1))) :=
  {evalOutFn (K := K) hn} ∪
  {f | ∃ i : Fin K, ∃ j : Fin (2 * w), f = fun x => termMask hn x i j}

private theorem build_wrap {n w K : Nat} (hn : 0 < n) (hwn : w ≤ n)
    (hKlo : 2 ^ w ≤ K) (hKhi : K ≤ 4 ^ w) {A : Set (Sig (n * 2 ^ (w + 1)))}
    (hIn : ∀ a : Fin (n * 2 ^ (w + 1)), (fun x => x a) ∈ A)
    (hF : (fun _ => false) ∈ A) (hT : (fun _ => true) ∈ A)
    (hSt : StateSet (fwdLayer (K := K) hn (n - w)) ⊆ A) :
    Build A (WrapOutSet (K := K) hn) (w * (64000 * (n + 1) ^ 3 * K) + 20 * (n + 1) ^ 2 * K) := by
  let I := n * 2 ^ (w + 1)
  have HlookAll : ∀ m ≤ w,
      Build A {f | ∃ (off : Fin w), off.val < m ∧ ∃ i : Fin K, f = fun x => wrapLookup hn x off i}
        (m * (64000 * (n + 1) ^ 3 * K)) := by
    intro m
    induction m with
    | zero =>
      intro _
      refine relax (idle ?_) le_rfl le_rfl (by simp)
      rintro f ⟨off, hoff, _⟩; omega
    | succ m ih =>
      intro hm
      have Hprev := ih (by omega)
      let Bprev := {f | ∃ (off : Fin w), off.val < m ∧ ∃ i : Fin K, f = fun x => wrapLookup hn x off i}
      let off : Fin w := ⟨m, hm⟩
      let patSig : Fin K → Fin (w + 1) → Sig I := fun i bit x =>
        wrapPat (fwdLayer hn (n - w) x i).2.1 (fwdLayer hn (n - w) x i).2.2 off bit
      have hpat : ∀ i bit, patSig i bit ∈ A ∪ Bprev := by
        intro i bit
        dsimp only [patSig, wrapPat]
        split_ifs with hk
        · exact Or.inl (hSt ⟨i, Or.inr (Or.inr ⟨⟨off.val + bit.val, hk⟩, rfl⟩)⟩)
        · exact Or.inl (hSt ⟨i, Or.inr (Or.inl ⟨⟨off.val + bit.val - w, by
            have := off.isLt; have := bit.isLt; omega⟩, rfl⟩)⟩)
      have Hstep : Build (A ∪ Bprev) {f | ∃ i : Fin K, f = fun x => wrapLookup hn x off i}
          (64000 * (n + 1) ^ 3 * K) :=
        relax (lookupRowG (posFn n hn (n - w + off.val)) patSig hpat (fun a => Or.inl (hIn a)))
          le_rfl (by rintro f ⟨i, rfl⟩; exact ⟨i, rfl⟩)
          (lookup_cost_bound hn hwn hKlo hKhi (by omega))
      refine relax (seq Hprev Hstep) le_rfl ?_ (by rw [Nat.succ_mul m])
      rintro f ⟨off', hoff', i, rfl⟩
      by_cases hlt : off'.val < m
      · exact Or.inl ⟨off', hlt, i, rfl⟩
      · have heq : off' = off := Fin.ext (by dsimp only [off]; omega)
        subst heq
        exact Or.inr ⟨i, rfl⟩
  have Hlook := HlookAll w le_rfl
  let A1 := A ∪ {f | ∃ (off : Fin w), off.val < w ∧ ∃ i : Fin K, f = fun x => wrapLookup hn x off i}
  have hWL : ∀ (off : Fin w) (i : Fin K), (fun x => wrapLookup hn x off i) ∈ A1 :=
    fun off i => Or.inr ⟨off, off.isLt, i, rfl⟩
  have Hsurv : Build A1 (Set.range (fun i : Fin K => fun x => survivesFn hn x i)) (K * (w + 1)) :=
    finG (fun i x => survivesFn hn x i) (w + 1) fun i => by
      let allSig : Sig I := allNat (fun off x => if h : off < w then wrapLookup hn x ⟨off, h⟩ i else true) w
      have Hall : Build A1 {allSig} w :=
        allNatG (fun off x => if h : off < w then wrapLookup hn x ⟨off, h⟩ i else true) (Or.inl hT) w fun j hj => by
          have he : (fun x => if h : j < w then wrapLookup hn x ⟨j, h⟩ i else true) =
              fun x => wrapLookup hn x ⟨j, hj⟩ i := by funext x; simp only [hj, ↓reduceDIte]
          rw [he]; exact hWL ⟨j, hj⟩ i
      have Hand : Build (A1 ∪ {allSig}) {fun x => survivesFn hn x i} 1 :=
        andG (Or.inl (Or.inl (hSt ⟨i, Or.inl rfl⟩))) (Or.inr rfl)
      exact relax (seq Hall Hand) le_rfl (Set.singleton_subset_iff.mpr (Or.inr rfl)) (by omega)
  let A2 := A1 ∪ Set.range (fun i : Fin K => fun x => survivesFn hn x i)
  have Heval : Build A2 {evalOutFn (K := K) hn} (K + 1) := by
    let anySig : Sig I := anyNat (fun idx x => if h : idx < K then survivesFn hn x ⟨idx, h⟩ else false) K
    have Hany : Build A2 {anySig} K :=
      anyNatG (fun idx x => if h : idx < K then survivesFn hn x ⟨idx, h⟩ else false) (Or.inl (Or.inl hF)) K fun idx hidx => by
        have he : (fun (x : Fin I → Bool) => if h : idx < K then survivesFn hn x ⟨idx, h⟩ else false) =
            fun (x : Fin I → Bool) => survivesFn hn x ⟨idx, hidx⟩ := by funext x; simp only [hidx, ↓reduceDIte]
        rw [he]; exact Or.inr ⟨⟨idx, hidx⟩, rfl⟩
    have Hnot : Build (A2 ∪ {anySig}) {evalOutFn (K := K) hn} 1 := notG (Or.inr rfl)
    exact relax (seq Hany Hnot) le_rfl (Set.singleton_subset_iff.mpr (Or.inr rfl)) (by omega)
  let A3 := A2 ∪ {evalOutFn (K := K) hn}
  have HtermOne : ∀ i : Fin K, ∀ m ≤ w,
      Build A3 ({fun x => (termScan hn i m x).1} ∪
        {f | ∃ j : Fin (2 * w), f = fun x => (termScan hn i m x).2 j}) (m * (6 * w + 5)) := by
    intro i m
    induction m with
    | zero =>
      intro _
      refine relax (idle ?_) le_rfl le_rfl (by simp)
      rintro f (rfl | ⟨j, rfl⟩) <;> exact Or.inl (Or.inl (Or.inl hF))
    | succ m ih =>
      intro hm
      have Hprev := ih (by omega)
      let Bprev := {fun x => (termScan hn i m x).1} ∪
        {f | ∃ j : Fin (2 * w), f = fun x => (termScan hn i m x).2 j}
      let A' := A3 ∪ Bprev
      let okSig : Sig I := fun x => wrapLookup hn x ⟨m, hm⟩ i
      have hok : okSig ∈ A' := Or.inl (Or.inl (Or.inl (hWL ⟨m, hm⟩ i)))
      have hp1 : (fun x => (termScan hn i m x).1) ∈ A' := Or.inr (Or.inl rfl)
      let np1 : Sig I := nt (fun x => (termScan hn i m x).1)
      let nok : Sig I := nt okSig
      let pickSig : Sig I := an np1 nok
      let npick : Sig I := nt pickSig
      let orSig : Sig I := or (fun x => (termScan hn i m x).1) nok
      have H1 : Build A' {np1} 1 := notG hp1
      have H2 : Build (A' ∪ {np1}) {nok} 1 := notG (Or.inl hok)
      have H3 : Build (A' ∪ ({np1} ∪ {nok})) {pickSig} 1 := andG (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl))
      have H4 : Build (A' ∪ (({np1} ∪ {nok}) ∪ {pickSig})) {npick} 1 := notG (Or.inr (Or.inr rfl))
      have H5 : Build (A' ∪ ((({np1} ∪ {nok}) ∪ {pickSig}) ∪ {npick})) {orSig} 1 :=
        orG (Or.inl hp1) (Or.inr (Or.inl (Or.inl (Or.inr rfl))))
      let C5 : Set (Sig I) := ((({np1} ∪ {nok}) ∪ {pickSig}) ∪ {npick}) ∪ {orSig}
      let nextMask : Fin (2 * w) → Sig I := fun j x => (termScan hn i (m + 1) x).2 j
      have H6 : Build (A' ∪ C5) (Set.range nextMask) (2 * w * 3) := finG nextMask 3 fun j => by
        let constB : Bool := if j.val < w then decide (j.val ≤ m) else decide (m ≤ j.val - w)
        have he : nextMask j = fun x => if pickSig x then constB else (termScan hn i m x).2 j := by
          funext x
          have hmlt : m < w := by omega
          simp only [nextMask, termScan, hmlt, ↓reduceDIte, pickSig, np1, nok, an, nt, okSig, constB]
        rw [he]
        have hcb : (fun _ : Fin I → Bool => constB) ∈ A' ∪ C5 := by
          cases constB
          · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hF))))
          · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hT))))
        exact muxG (Or.inr (Or.inl (Or.inl (Or.inr rfl)))) (Or.inr (Or.inl (Or.inr rfl)))
          hcb (Or.inl (Or.inr (Or.inr ⟨j, rfl⟩))) (fun _ => rfl)
      have Hstep := seq (seq (seq (seq (seq H1 H2) H3) H4) H5) H6
      refine relax (seq Hprev Hstep) le_rfl ?_ (by rw [Nat.succ_mul m]; omega)
      rintro f (rfl | ⟨j, rfl⟩)
      · exact Or.inr (Or.inl (Or.inr (by
          funext x
          have hmlt : m < w := by omega
          simp [termScan, hmlt, orSig, nok, Build220.or, nt, okSig])))
      · exact Or.inr (Or.inr ⟨j, rfl⟩)
  have Hterm : Build A3 {f | ∃ i : Fin K, ∃ j : Fin (2 * w), f = fun x => termMask hn x i j}
      (K * (w * (6 * w + 5))) := by
    have hall : Build A3
        {f | ∃ i ∈ List.finRange K, f ∈ ({fun x => (termScan hn i w x).1} ∪
          {g | ∃ j : Fin (2 * w), g = fun x => (termScan hn i w x).2 j})}
        ((List.finRange K).length * (w * (6 * w + 5))) := by
      clear Hlook Hsurv Heval
      induction (List.finRange K) with
      | nil => exact relax (idle (Set.empty_subset _)) le_rfl (by intro f hf; simp at hf) (by simp)
      | cons i is ih =>
        have h1 := HtermOne i w le_rfl
        have h2 := relax ih (C := A3 ∪ ({fun x => (termScan hn i w x).1} ∪
          {g | ∃ j : Fin (2 * w), g = fun x => (termScan hn i w x).2 j})) Set.subset_union_left le_rfl le_rfl
        refine relax (seq h1 h2) le_rfl ?_ (by simp [Nat.succ_mul, Nat.add_comm])
        rintro f ⟨i', hi', hf⟩
        rcases List.mem_cons.mp hi' with rfl | hi'
        · exact Or.inl hf
        · exact Or.inr ⟨i', hi', hf⟩
    rw [List.length_finRange] at hall
    refine relax hall le_rfl ?_ le_rfl
    rintro f ⟨i, j, rfl⟩
    exact ⟨i, List.mem_finRange i, Or.inr ⟨j, rfl⟩⟩
  refine relax (stepU (stepU (stepU (buildSelf Hlook) Hsurv) Heval) Hterm) le_rfl ?_ ?_
  · rintro f (rfl | ⟨i, j, rfl⟩)
    · exact Or.inl (Or.inr rfl)
    · exact Or.inr ⟨i, j, rfl⟩
  · have hKpos : 1 ≤ K := (Nat.two_pow_pos w).trans_le hKlo
    have h1 : K * (w + 1) + (K + 1) + K * (w * (6 * w + 5)) ≤ 20 * (n + 1) ^ 2 * K := by
      have hw1 : w ≤ n := hwn
      have hsq : w * (6 * w + 5) ≤ 11 * (n + 1) ^ 2 := by nlinarith
      have hl : (w + 1) ≤ (n + 1) ^ 2 := by nlinarith
      nlinarith
    omega

private theorem build_bwdStep {n w K : Nat} (hn : 0 < n) (hwn : w ≤ n)
    (hKlo : 2 ^ w ≤ K) (hKhi : K ≤ 4 ^ w) {A : Set (Sig (n * 2 ^ (w + 1)))}
    (hF : (fun _ => false) ∈ A) (hT : (fun _ => true) ∈ A)
    (h : Nat) (hFwd : FwdStepOut (K := K) hn h (fwdLayer hn h) ⊆ A)
    (clNext : (Fin (n * 2 ^ (w + 1)) → Bool) → Fin K → Fin (2 * w) → Bool)
    (hCl : ∀ i j, (fun x => clNext x i j) ∈ A) :
    Build A
      ({f | ∃ i : Fin K, ∃ j : Fin (2 * w), f = fun x => (parentStep hn h (clNext x) x i).1 j} ∪
       {f | ∃ i : Fin K, f = fun x => (parentStep hn h (clNext x) x i).2})
      (200 * (n + 1) ^ 3 * K) := by
  let I := n * 2 ^ (w + 1)
  let N := 2 ^ sortPow K
  rcases sortPow_bounds hKlo hKhi with ⟨hNlo, hNhi, _⟩
  rcases sortNet_bounds hKlo hKhi with ⟨hnet_mem, hnet_len⟩
  let ans2 : (Fin I → Bool) → Nat → Fin (2 * w) → Bool := fun x idx =>
    if hidx : idx < K then clNext x ⟨idx, hidx⟩ else fun _ => false
  have hA2 : ∀ idx < N, ∀ j : Fin (2 * w), (fun x => ans2 x idx j) ∈ A := by
    intro idx _ j
    dsimp only [ans2]
    split_ifs with hidx
    · exact hCl ⟨idx, hidx⟩ j
    · exact hF
  have Hrep2 := replayReverseCircuit (A := A) N (sortNet K) hnet_mem
    (fun x => childRec2 hn h (fwdLayer hn h x) x)
    (fun t ht => ⟨hFwd (Or.inr ⟨t, ht, Or.inl rfl⟩), hFwd (Or.inr ⟨t, ht, Or.inr rfl⟩)⟩)
    ans2 hA2
  let unp2 : (Fin I → Bool) → Nat → Fin (2 * w) → Bool := fun x =>
    replaySwaps (swaps2 hn h (fwdLayer (K := K) hn h x) x).reverse (ans2 x)
  let A1 := A ∪ {f | ∃ idx < N, ∃ j : Fin (2 * w), f = fun x => unp2 x idx j}
  have Hscan := dupScanCircuit (A := A1) N (fun x => isRepFn hn h (fwdLayer (K := K) hn h x) x) unp2
    (fun idx hidx => Or.inl (hFwd (Or.inl (Or.inl (Or.inr ⟨idx, hidx, rfl⟩)))))
    (fun idx hidx j => Or.inr ⟨idx, hidx, j, rfl⟩) (Or.inl hF) N le_rfl
  let sc : (Fin I → Bool) → Nat → Fin (2 * w) → Bool := fun x =>
    (dupScan (isRepFn hn h (fwdLayer (K := K) hn h x) x) (unp2 x) N).2
  let A2 := A1 ∪ ({f | ∃ j : Fin (2 * w), f = fun x => (dupScan (isRepFn hn h (fwdLayer (K := K) hn h x) x) (unp2 x) N).1 j} ∪
    {f | ∃ idx < N, ∃ j : Fin (2 * w), f = fun x => sc x idx j})
  have Hrep1 := replayReverseCircuit (A := A2) N (sortNet K) hnet_mem
    (fun x => childRec1 hn h (fwdLayer (K := K) hn h x) x)
    (fun t ht => ⟨Or.inl (Or.inl (hFwd (Or.inl (Or.inr ⟨t, ht, Or.inl rfl⟩)))),
      Or.inl (Or.inl (hFwd (Or.inl (Or.inr ⟨t, ht, Or.inr rfl⟩))))⟩)
    sc (fun idx hidx j => Or.inr (Or.inr ⟨idx, hidx, j, rfl⟩))
  let A3 := A2 ∪ {f | ∃ idx < N, ∃ j : Fin (2 * w),
    f = fun x => childClauseMask hn h (clNext x) x idx j}
  have hCM : ∀ idx < 2 * K, ∀ j : Fin (2 * w),
      (fun x => childClauseMask hn h (clNext x) x idx j) ∈ A3 :=
    fun idx hidx j => Or.inr ⟨idx, by omega, j, rfl⟩
  have hCL : ∀ idx : Fin (2 * K),
      (fun x => childLookup hn h (fwdLayer hn h x) x idx) ∈ A3 :=
    fun idx => Or.inl (Or.inl (Or.inl (hFwd (Or.inl (Or.inl (Or.inl (Or.inr ⟨idx, rfl⟩)))))))
  have hF3 : (fun _ : Fin I → Bool => false) ∈ A3 := Or.inl (Or.inl (Or.inl hF))
  have hT3 : (fun _ : Fin I → Bool => true) ∈ A3 := Or.inl (Or.inl (Or.inl hT))
  have HparOne : ∀ i : Fin K,
      Build A3 ({f | ∃ j : Fin (2 * w), f = fun x => (parentStep hn h (clNext x) x i).1 j} ∪
        {fun x => (parentStep hn h (clNext x) x i).2}) (30 * w + 16) := by
    intro i
    let c0 : Fin (2 * K) := ⟨2 * i.val, by have := i.isLt; omega⟩
    let c1 : Fin (2 * K) := ⟨2 * i.val + 1, by have := i.isLt; omega⟩
    let ok0 : Sig I := fun x => childLookup hn h (fwdLayer hn h x) x c0
    let ok1 : Sig I := fun x => childLookup hn h (fwdLayer hn h x) x c1
    have Hnok0 : Build A3 {nt ok0} 1 := notG (hCL c0)
    have Hnok1 : Build (A3 ∪ {nt ok0}) {nt ok1} 1 := notG (Or.inl (hCL c1))
    let A' := A3 ∪ ({nt ok0} ∪ {nt ok1})
    let d0M : Fin (2 * w) → Sig I := fun j x => (childMaskAt hn h (clNext x) x i false).1 j
    let d1M : Fin (2 * w) → Sig I := fun j x => (childMaskAt hn h (clNext x) x i true).1 j
    let d0P : Sig I := fun x => (childMaskAt hn h (clNext x) x i false).2
    let d1P : Sig I := fun x => (childMaskAt hn h (clNext x) x i true).2
    have Hd0M : Build A' (Set.range d0M) (2 * w * 3) := finG d0M 3 fun j => by
      dsimp only [d0M, childMaskAt]
      by_cases hj : j.val < w
      · simp only [hj, ↓reduceIte]
        exact muxG (Or.inl (hCL c0)) (Or.inr (Or.inl rfl)) (Or.inl (hCM c0.val c0.isLt j))
          (Or.inl hF3) (fun _ => rfl)
      · simp only [hj, ↓reduceIte]
        by_cases hjw : j.val = w
        · simp only [hjw, ↓reduceIte]
          exact muxG (Or.inl (hCL c0)) (Or.inr (Or.inl rfl)) (Or.inl hF3) (Or.inl hT3) (fun _ => rfl)
        · simp only [hjw, ↓reduceIte]
          exact muxG (Or.inl (hCL c0)) (Or.inr (Or.inl rfl))
            (Or.inl (hCM c0.val c0.isLt ⟨j.val - 1, by omega⟩)) (Or.inl hT3) (fun _ => rfl)
    have Hd1M : Build (A' ∪ Set.range d0M) (Set.range d1M) (2 * w * 3) := finG d1M 3 fun j => by
      dsimp only [d1M, childMaskAt]
      by_cases hj : j.val < w
      · simp only [hj, ↓reduceIte]
        exact muxG (Or.inl (Or.inl (hCL c1))) (Or.inl (Or.inr (Or.inr rfl)))
          (Or.inl (Or.inl (hCM c1.val c1.isLt j))) (Or.inl (Or.inl hF3)) (fun _ => rfl)
      · simp only [hj, ↓reduceIte]
        by_cases hjw : j.val = w
        · simp only [hjw, ↓reduceIte]
          exact muxG (Or.inl (Or.inl (hCL c1))) (Or.inl (Or.inr (Or.inr rfl)))
            (Or.inl (Or.inl hF3)) (Or.inl (Or.inl hT3)) (fun _ => rfl)
        · simp only [hjw, ↓reduceIte]
          exact muxG (Or.inl (Or.inl (hCL c1))) (Or.inl (Or.inr (Or.inr rfl)))
            (Or.inl (Or.inl (hCM c1.val c1.isLt ⟨j.val - 1, by omega⟩)))
            (Or.inl (Or.inl hT3)) (fun _ => rfl)
    have Hd0P : Build (A' ∪ (Set.range d0M ∪ Set.range d1M)) {d0P} 3 := by
      dsimp only [d0P, childMaskAt]
      by_cases hw : 0 < w
      · simp only [hw, ↓reduceDIte]
        exact muxG (Or.inl (Or.inl (hCL c0))) (Or.inl (Or.inr (Or.inl rfl)))
          (Or.inl (Or.inl (hCM c0.val c0.isLt ⟨2 * w - 1, by omega⟩)))
          (Or.inl (Or.inl hT3)) (fun _ => rfl)
      · simp only [hw, ↓reduceDIte]
        exact muxG (Or.inl (Or.inl (hCL c0))) (Or.inl (Or.inr (Or.inl rfl)))
          (Or.inl (Or.inl hF3)) (Or.inl (Or.inl hT3)) (fun _ => rfl)
    have Hd1P : Build (A' ∪ ((Set.range d0M ∪ Set.range d1M) ∪ {d0P})) {d1P} 3 := by
      dsimp only [d1P, childMaskAt]
      by_cases hw : 0 < w
      · simp only [hw, ↓reduceDIte]
        exact muxG (Or.inl (Or.inl (hCL c1))) (Or.inl (Or.inr (Or.inr rfl)))
          (Or.inl (Or.inl (hCM c1.val c1.isLt ⟨2 * w - 1, by omega⟩)))
          (Or.inl (Or.inl hT3)) (fun _ => rfl)
      · simp only [hw, ↓reduceDIte]
        exact muxG (Or.inl (Or.inl (hCL c1))) (Or.inl (Or.inr (Or.inr rfl)))
          (Or.inl (Or.inl hF3)) (Or.inl (Or.inl hT3)) (fun _ => rfl)
    let C4 := (Set.range d0M ∪ Set.range d1M) ∪ ({d0P} ∪ {d1P})
    have Hc4 : Build A' C4 (12 * w + 6) :=
      relax (seq (seq (seq Hd0M Hd1M) Hd0P) Hd1P) le_rfl (by
        rintro f ((hf | hf) | (hf | hf))
        · exact Or.inl (Or.inl (Or.inl hf))
        · exact Or.inl (Or.inl (Or.inr hf))
        · exact Or.inl (Or.inr hf)
        · exact Or.inr hf) (by omega)
    let A'' := A' ∪ C4
    have Hnp0 : Build A'' {nt d0P} 1 := notG (Or.inr (Or.inr (Or.inl rfl)))
    have Hnp1 : Build (A'' ∪ {nt d0P}) {nt d1P} 1 := notG (Or.inl (Or.inr (Or.inr (Or.inr rfl))))
    have Hres : Build (A'' ∪ ({nt d0P} ∪ {nt d1P})) {an d0P d1P} 1 :=
      andG (Or.inl (Or.inr (Or.inr (Or.inl rfl)))) (Or.inl (Or.inr (Or.inr (Or.inr rfl))))
    let A''' := A'' ∪ (({nt d0P} ∪ {nt d1P}) ∪ {an d0P d1P})
    let outM : Fin (2 * w) → Sig I := fun j x => (parentStep hn h (clNext x) x i).1 j
    have HoutM : Build A''' (Set.range outM) (2 * w * 7) := finG outM 7 fun j => by
      have hor : Build A''' {or (d0M j) (d1M j)} 1 :=
        orG (Or.inl (Or.inr (Or.inl (Or.inl ⟨j, rfl⟩)))) (Or.inl (Or.inr (Or.inl (Or.inr ⟨j, rfl⟩))))
      have hm1 : Build (A''' ∪ {or (d0M j) (d1M j)})
          {fun x => if !d1P x then d1M j x else or (d0M j) (d1M j) x} 3 :=
        muxG (Or.inl (Or.inr (Or.inl (Or.inr rfl)))) (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr rfl)))))
          (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr ⟨j, rfl⟩))))) (Or.inr rfl)
          (fun x => (Bool.not_not (d1P x)).symm)
      have hm2 : Build (A''' ∪ ({or (d0M j) (d1M j)} ∪
            {fun x => if !d1P x then d1M j x else or (d0M j) (d1M j) x}))
          {outM j} 3 :=
        muxG (Or.inl (Or.inr (Or.inl (Or.inl rfl)))) (Or.inl (Or.inl (Or.inr (Or.inr (Or.inl rfl)))))
          (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl ⟨j, rfl⟩))))) (Or.inr (Or.inr rfl))
          (fun x => (Bool.not_not (d0P x)).symm)
      exact relax (seq (seq hor hm1) hm2) le_rfl (Set.singleton_subset_iff.mpr (Or.inr rfl)) (by omega)
    refine relax (seq (seq Hnok0 Hnok1) (seq Hc4 (seq (seq (seq Hnp0 Hnp1) Hres) HoutM)))
      le_rfl ?_ (by omega)
    rintro f (⟨j, rfl⟩ | rfl)
    · exact Or.inr (Or.inr (Or.inr ⟨j, rfl⟩))
    · exact Or.inr (Or.inr (Or.inl (Or.inr rfl)))
  have HparAll : Build A3
      ({f | ∃ i : Fin K, ∃ j : Fin (2 * w), f = fun x => (parentStep hn h (clNext x) x i).1 j} ∪
       {f | ∃ i : Fin K, f = fun x => (parentStep hn h (clNext x) x i).2})
      (K * (30 * w + 16)) := by
    have hall : Build A3
        {f | ∃ i ∈ List.finRange K, f ∈
          ({g | ∃ j : Fin (2 * w), g = fun x => (parentStep hn h (clNext x) x i).1 j} ∪
           {fun x => (parentStep hn h (clNext x) x i).2})}
        ((List.finRange K).length * (30 * w + 16)) := by
      clear Hrep2 Hscan Hrep1
      induction (List.finRange K) with
      | nil => exact relax (idle (Set.empty_subset _)) le_rfl (by intro f hf; simp at hf) (by simp)
      | cons i is ih =>
        have h1 := HparOne i
        have h2 := relax ih (C := A3 ∪ ({g | ∃ j : Fin (2 * w), g = fun x => (parentStep hn h (clNext x) x i).1 j} ∪
          {fun x => (parentStep hn h (clNext x) x i).2})) Set.subset_union_left le_rfl le_rfl
        refine relax (seq h1 h2) le_rfl ?_ (by simp [Nat.succ_mul, Nat.add_comm])
        rintro f ⟨i', hi', hf⟩
        rcases List.mem_cons.mp hi' with rfl | hi'
        · exact Or.inl hf
        · exact Or.inr ⟨i', hi', hf⟩
    rw [List.length_finRange] at hall
    refine relax hall le_rfl ?_ le_rfl
    rintro f (⟨i, j, rfl⟩ | ⟨i, rfl⟩)
    · exact ⟨i, List.mem_finRange i, Or.inl ⟨j, rfl⟩⟩
    · exact ⟨i, List.mem_finRange i, Or.inr rfl⟩
  refine relax (stepU (stepU (stepU (buildSelf Hrep2) Hscan) Hrep1) HparAll) le_rfl
    (fun f hf => Or.inr hf) ?_
  have hnet_tot : (sortNet K).length * (6 * (2 * w)) + (sortNet K).length * (6 * (2 * w)) ≤
      96 * (n + 1) ^ 3 * K := by
    have h1 : 2 * w + 1 ≤ 2 * (n + 1) := by omega
    have h2 : 2 * w + 2 ≤ 2 * (n + 1) := by omega
    have h3 : 24 * w ≤ 24 * (n + 1) := by omega
    have hpoly : (2 * w + 1) * (2 * w + 2) * (24 * w) ≤ 96 * (n + 1) ^ 3 := by
      calc (2 * w + 1) * (2 * w + 2) * (24 * w)
          ≤ (2 * (n + 1)) * (2 * (n + 1)) * (24 * (n + 1)) :=
            Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3
        _ = 96 * (n + 1) ^ 3 := by ring
    calc (sortNet K).length * (6 * (2 * w)) + (sortNet K).length * (6 * (2 * w))
        = (sortNet K).length * (24 * w) := by ring
      _ ≤ ((2 * w + 1) * (2 * w + 2) * K) * (24 * w) := Nat.mul_le_mul_right _ hnet_len
      _ = ((2 * w + 1) * (2 * w + 2) * (24 * w)) * K := by ring
      _ ≤ 96 * (n + 1) ^ 3 * K := Nat.mul_le_mul_right K hpoly
  have hsc_le : N * (3 * (2 * w) + 1) ≤ 28 * (n + 1) ^ 3 * K := by
    have h1 : 3 * (2 * w) + 1 ≤ 7 * (n + 1) := by omega
    have h2 : 1 ≤ (n + 1) ^ 2 := Nat.one_le_pow 2 (n + 1) (by omega)
    have h3 : n + 1 ≤ (n + 1) * (n + 1) ^ 2 := Nat.le_mul_of_pos_right _ (by omega)
    calc N * (3 * (2 * w) + 1) ≤ (4 * K) * (7 * (n + 1)) := Nat.mul_le_mul (Nat.le_of_lt hNhi) h1
      _ = 28 * (n + 1) * K := by ring
      _ ≤ 28 * ((n + 1) * (n + 1) ^ 2) * K := Nat.mul_le_mul_right K (Nat.mul_le_mul_left 28 h3)
      _ = 28 * (n + 1) ^ 3 * K := by ring
  have hpar_le : K * (30 * w + 16) ≤ 30 * (n + 1) ^ 3 * K := by
    have h1 : 30 * w + 16 ≤ 30 * (n + 1) := by omega
    have h2 : 1 ≤ (n + 1) ^ 2 := Nat.one_le_pow 2 (n + 1) (by omega)
    have h3 : n + 1 ≤ (n + 1) * (n + 1) ^ 2 := Nat.le_mul_of_pos_right _ (by omega)
    calc K * (30 * w + 16) ≤ K * (30 * (n + 1)) := Nat.mul_le_mul_left K h1
      _ = 30 * (n + 1) * K := by ring
      _ ≤ 30 * ((n + 1) * (n + 1) ^ 2) * K := Nat.mul_le_mul_right K (Nat.mul_le_mul_left 30 h3)
      _ = 30 * (n + 1) ^ 3 * K := by ring
  have hsum_le : (sortNet K).length * (6 * (2 * w)) + N * (3 * (2 * w) + 1) +
      (sortNet K).length * (6 * (2 * w)) + K * (30 * w + 16) ≤
      (96 + 28 + 30) * ((n + 1) ^ 3 * K) := by
    have ha : 96 * (n + 1) ^ 3 * K = 96 * ((n + 1) ^ 3 * K) := by ring
    have hb : 28 * (n + 1) ^ 3 * K = 28 * ((n + 1) ^ 3 * K) := by ring
    have hc : 30 * (n + 1) ^ 3 * K = 30 * ((n + 1) ^ 3 * K) := by ring
    omega
  calc (sortNet K).length * (6 * (2 * w)) + N * (3 * (2 * w) + 1) +
        (sortNet K).length * (6 * (2 * w)) + K * (30 * w + 16)
      ≤ 154 * ((n + 1) ^ 3 * K) := hsum_le
    _ ≤ 200 * ((n + 1) ^ 3 * K) := Nat.mul_le_mul_right _ (by omega)
    _ = 200 * (n + 1) ^ 3 * K := by ring

private def BwdAllSet {n w K : Nat} (hn : 0 < n) (m : Nat) : Set (Sig (n * 2 ^ (w + 1))) :=
  {f | ∃ r ≤ m, ∃ i : Fin K, ∃ j : Fin (2 * w), f = fun x => bwdMaskAux hn r x i j} ∪
  {f | ∃ r < m, ∃ i : Fin K,
    f = fun x => (parentStep hn (n - w - (r + 1)) (bwdMaskAux hn r x) x i).2}

private theorem build_bwdAll {n w K : Nat} (hn : 0 < n) (hwn : w ≤ n)
    (hKlo : 2 ^ w ≤ K) (hKhi : K ≤ 4 ^ w) {A : Set (Sig (n * 2 ^ (w + 1)))}
    (hF : (fun _ => false) ∈ A) (hT : (fun _ => true) ∈ A)
    (hFwd : FwdAllSet (K := K) hn (n - w) ⊆ A)
    (hWrap : WrapOutSet (K := K) hn ⊆ A) :
    ∀ m ≤ n - w, Build A (BwdAllSet (K := K) hn m) (m * (200 * (n + 1) ^ 3 * K)) := by
  intro m
  induction m with
  | zero =>
    intro _
    refine relax (idle ?_) le_rfl le_rfl (by simp)
    rintro f (⟨r, hr, i, j, rfl⟩ | ⟨r, hr, _⟩)
    · have hr0 : r = 0 := by omega
      subst hr0
      exact hWrap (Or.inr ⟨i, j, rfl⟩)
    · omega
  | succ m ih =>
    intro hm
    have Hprev := ih (by omega)
    let h := n - w - (m + 1)
    have hh_lt : h < n - w := by dsimp [h]; omega
    have Hstep := build_bwdStep hn hwn hKlo hKhi (A := A ∪ BwdAllSet (K := K) hn m)
      (Or.inl hF) (Or.inl hT) h
      (fun f hf => Or.inl (hFwd (Or.inr ⟨h, hh_lt, hf⟩)))
      (bwdMaskAux hn m) (fun i j => Or.inr (Or.inl ⟨m, le_rfl, i, j, rfl⟩))
    refine relax (seq Hprev Hstep) le_rfl ?_ (by rw [Nat.succ_mul m])
    rintro f (⟨r, hr, i, j, rfl⟩ | ⟨r, hr, i, rfl⟩)
    · by_cases hrm : r ≤ m
      · exact Or.inl (Or.inl ⟨r, hrm, i, j, rfl⟩)
      · have heq : r = m + 1 := by omega
        subst heq
        exact Or.inr (Or.inl ⟨i, j, rfl⟩)
    · by_cases hrm : r < m
      · exact Or.inl (Or.inr ⟨r, hrm, i, rfl⟩)
      · have heq : r = m := by omega
        subst heq
        exact Or.inr (Or.inr ⟨i, rfl⟩)

private def SeedAllSet {n w K : Nat} (hn : 0 < n) (hKlo : 2 ^ w ≤ K) (m : Nat) (hm : m ≤ w) :
    Set (Sig (n * 2 ^ (w + 1))) :=
  {f | ∃ (r : Nat) (hr : r ≤ m), ∃ (idx : Fin (2 ^ (w - r))) (j : Fin (w - r)),
    f = fun x => seedMaskAux hn hKlo r (hr.trans hm) x idx j} ∪
  {f | ∃ (d_lev : Nat) (hd : d_lev < w), w - (d_lev + 1) < m ∧ ∃ idx : Fin (2 ^ d_lev),
    f = fun x => seedDoRes hn hKlo d_lev hd x idx}

private theorem build_seedAll {n w K : Nat} (hn : 0 < n) (hKlo : 2 ^ w ≤ K)
    {A : Set (Sig (n * 2 ^ (w + 1)))}
    (hBwd0 : ∀ (i : Fin K) (j : Fin (2 * w)), (fun x => bwdMask hn 0 x i j) ∈ A) :
    ∀ m (hm : m ≤ w),
      Build A (SeedAllSet (K := K) hn hKlo m hm) ((2 ^ w + 2 ^ w - 2 ^ (w - m)) * (7 * w + 3)) := by
  intro m
  induction m with
  | zero =>
    intro hm
    let pairList := List.finRange (2 ^ w)
    have Hbase : Build A
        {f | ∃ (idx : Fin (2 ^ w)) (j : Fin w),
          f = fun x => seedMaskAux hn hKlo 0 (Nat.zero_le w) x
            ⟨idx.val, by simp⟩ ⟨j.val, by simp⟩}
        (2 ^ w * w) := by
      have Hidx : ∀ idx : Fin (2 ^ w),
          Build A (Set.range (fun j : Fin w => fun x =>
            seedMaskAux hn hKlo 0 (Nat.zero_le w) x
              ⟨idx.val, by simp⟩ ⟨j.val, by simp⟩)) (w * 1) := by
        intro idx
        refine finG _ 1 fun j => ?_
        exact orG (hBwd0 ⟨idx.val, idx.isLt.trans_le hKlo⟩ ⟨j.val, by omega⟩)
          (hBwd0 ⟨idx.val, idx.isLt.trans_le hKlo⟩ ⟨w + j.val, by omega⟩)
      have hall : Build A
          {f | ∃ idx ∈ List.finRange (2 ^ w), f ∈ Set.range (fun j : Fin w => fun x =>
            seedMaskAux hn hKlo 0 (Nat.zero_le w) x
              ⟨idx.val, by simp⟩ ⟨j.val, by simp⟩)}
          ((List.finRange (2 ^ w)).length * (w * 1)) := by
        induction (List.finRange (2 ^ w)) with
        | nil => exact relax (idle (Set.empty_subset _)) le_rfl (by intro f hf; simp at hf) (by simp)
        | cons idx is ih =>
          have h1 := Hidx idx
          have h2 := relax ih (C := A ∪ Set.range (fun j : Fin w => fun x =>
            seedMaskAux hn hKlo 0 (Nat.zero_le w) x
              ⟨idx.val, by simp⟩ ⟨j.val, by simp⟩)) Set.subset_union_left le_rfl le_rfl
          refine relax (seq h1 h2) le_rfl ?_ (by simp only [List.length_cons]; rw [Nat.add_mul, Nat.one_mul, Nat.add_comm])
          rintro f ⟨i', hi', hf⟩
          rcases List.mem_cons.mp hi' with rfl | hi'
          · exact Or.inl hf
          · exact Or.inr ⟨i', hi', hf⟩
      rw [List.length_finRange, Nat.mul_one] at hall
      refine relax hall le_rfl ?_ le_rfl
      rintro f ⟨idx, j, rfl⟩
      exact ⟨idx, List.mem_finRange idx, j, rfl⟩
    refine relax Hbase le_rfl ?_ ?_
    · rintro f (⟨r, hr, idx, j, rfl⟩ | ⟨d_lev, hd, hlt, _⟩)
      · have hr0 : r = 0 := by omega
        subst hr0
        exact ⟨⟨idx.val, by simp⟩, ⟨j.val, by simp⟩, rfl⟩
      · omega
    · simp only [Nat.sub_zero, Nat.add_sub_cancel]
      exact Nat.mul_le_mul_left _ (by omega)
  | succ m ih =>
    intro hm
    have Hprev := ih (by omega)
    let d_lev := w - (m + 1)
    have hd : d_lev < w := by dsimp [d_lev]; omega
    let A1 := A ∪ SeedAllSet (K := K) hn hKlo m (by omega)
    have Hnode : ∀ idx : Fin (2 ^ d_lev),
        Build A1
          ({f | ∃ j : Fin d_lev, f = fun x => seedMaskAux hn hKlo (m + 1) hm x idx j} ∪
           {fun x => seedDoRes hn hKlo d_lev hd x idx})
          (7 * d_lev + 3) := by
      intro idx
      have hwr : w - m = d_lev + 1 := by dsimp [d_lev]; omega
      let idxL : Fin (2 ^ (w - m)) := ⟨idx.val, by
        have h1 : idx.val < 2 ^ d_lev := idx.isLt
        have h2 : 2 ^ d_lev < 2 ^ (w - m) := Nat.pow_lt_pow_right (by omega) (by omega)
        omega⟩
      let idxR : Fin (2 ^ (w - m)) := ⟨idx.val + 2 ^ d_lev, by
        have h1 : idx.val < 2 ^ d_lev := idx.isLt
        have h2 : 2 ^ (w - m) = 2 ^ d_lev + 2 ^ d_lev := by rw [hwr, Nat.pow_succ]; omega
        omega⟩
      let pL : Sig (n * 2 ^ (w + 1)) := fun x => seedMaskAux hn hKlo m (by omega) x idxL ⟨d_lev, by omega⟩
      let pR : Sig (n * 2 ^ (w + 1)) := fun x => seedMaskAux hn hKlo m (by omega) x idxR ⟨d_lev, by omega⟩
      have hpL : pL ∈ A1 := Or.inr (Or.inl ⟨m, le_rfl, idxL, ⟨d_lev, by omega⟩, rfl⟩)
      have hpR : pR ∈ A1 := Or.inr (Or.inl ⟨m, le_rfl, idxR, ⟨d_lev, by omega⟩, rfl⟩)
      have HnpL : Build A1 {nt pL} 1 := notG hpL
      have HnpR : Build (A1 ∪ {nt pL}) {nt pR} 1 := notG (Or.inl hpR)
      have Hres : Build (A1 ∪ ({nt pL} ∪ {nt pR})) {an pL pR} 1 :=
        andG (Or.inl hpL) (Or.inl hpR)
      let A2 := A1 ∪ (({nt pL} ∪ {nt pR}) ∪ {an pL pR})
      let outM : Fin d_lev → Sig (n * 2 ^ (w + 1)) := fun j x => seedMaskAux hn hKlo (m + 1) hm x idx j
      have Hout : Build A2 (Set.range outM) (d_lev * 7) := finG outM 7 fun j => by
        let mLj : Sig (n * 2 ^ (w + 1)) := fun x => seedMaskAux hn hKlo m (by omega) x idxL ⟨j.val, by omega⟩
        let mRj : Sig (n * 2 ^ (w + 1)) := fun x => seedMaskAux hn hKlo m (by omega) x idxR ⟨j.val, by omega⟩
        have hmL : mLj ∈ A2 := Or.inl (Or.inr (Or.inl ⟨m, le_rfl, idxL, ⟨j.val, by omega⟩, rfl⟩))
        have hmR : mRj ∈ A2 := Or.inl (Or.inr (Or.inl ⟨m, le_rfl, idxR, ⟨j.val, by omega⟩, rfl⟩))
        have hor : Build A2 {or mLj mRj} 1 := orG hmL hmR
        have hm1 : Build (A2 ∪ {or mLj mRj}) {fun x => if !pR x then mRj x else or mLj mRj x} 3 :=
          muxG (Or.inl (Or.inr (Or.inl (Or.inr rfl)))) (Or.inl (Or.inl hpR))
            (Or.inl hmR) (Or.inr rfl) (fun x => (Bool.not_not (pR x)).symm)
        have hm2 : Build (A2 ∪ ({or mLj mRj} ∪ {fun x => if !pR x then mRj x else or mLj mRj x})) {outM j} 3 :=
          muxG (Or.inl (Or.inr (Or.inl (Or.inl rfl)))) (Or.inl (Or.inl hpL))
            (Or.inl hmL) (Or.inr (Or.inr rfl)) (fun x => (Bool.not_not (pL x)).symm)
        exact relax (seq (seq hor hm1) hm2) le_rfl (Set.singleton_subset_iff.mpr (Or.inr rfl)) (by omega)
      refine relax (seq (seq (seq HnpL HnpR) Hres) Hout) le_rfl ?_ (by omega)
      rintro f (⟨j, rfl⟩ | rfl)
      · exact Or.inr ⟨j, rfl⟩
      · exact Or.inl (Or.inr (by
          funext x
          dsimp only [seedDoRes, an, pL, pR]
          have hrm : w - (d_lev + 1) = m := by dsimp [d_lev]; omega
          have heqAux : ∀ (a : Nat) (ha : a ≤ w) (hea : a = m)
              (i1 : Fin (2 ^ (w - a))) (j1 : Fin (w - a)),
              seedMaskAux hn hKlo a ha x i1 j1 =
              seedMaskAux hn hKlo m (by omega) x ⟨i1.val, by rw [← hea]; exact i1.isLt⟩
                ⟨j1.val, by rw [← hea]; exact j1.isLt⟩ := by
            intro a ha hea i1 j1; subst hea; rfl
          rw [heqAux (w - (d_lev + 1)) _ hrm, heqAux (w - (d_lev + 1)) _ hrm]))
    have Hlevel : Build A1
        ({f | ∃ (idx : Fin (2 ^ d_lev)) (j : Fin d_lev),
          f = fun x => seedMaskAux hn hKlo (m + 1) hm x idx j} ∪
         {f | ∃ idx : Fin (2 ^ d_lev), f = fun x => seedDoRes hn hKlo d_lev hd x idx})
        (2 ^ d_lev * (7 * d_lev + 3)) := by
      have hall : Build A1
          {f | ∃ idx ∈ List.finRange (2 ^ d_lev), f ∈
            ({g | ∃ j : Fin d_lev, g = fun x => seedMaskAux hn hKlo (m + 1) hm x idx j} ∪
             {fun x => seedDoRes hn hKlo d_lev hd x idx})}
          ((List.finRange (2 ^ d_lev)).length * (7 * d_lev + 3)) := by
        clear Hprev
        induction (List.finRange (2 ^ d_lev)) with
        | nil => exact relax (idle (Set.empty_subset _)) le_rfl (by intro f hf; simp at hf) (by simp)
        | cons idx is ih' =>
          have h1 := Hnode idx
          have h2 := relax ih' (C := A1 ∪ ({g | ∃ j : Fin d_lev, g = fun x => seedMaskAux hn hKlo (m + 1) hm x idx j} ∪
            {fun x => seedDoRes hn hKlo d_lev hd x idx})) Set.subset_union_left le_rfl le_rfl
          refine relax (seq h1 h2) le_rfl ?_ (by simp only [List.length_cons]; rw [Nat.add_mul, Nat.one_mul, Nat.add_comm])
          rintro f ⟨i', hi', hf⟩
          rcases List.mem_cons.mp hi' with rfl | hi'
          · exact Or.inl hf
          · exact Or.inr ⟨i', hi', hf⟩
      rw [List.length_finRange] at hall
      refine relax hall le_rfl ?_ le_rfl
      rintro f (⟨idx, j, rfl⟩ | ⟨idx, rfl⟩)
      · exact ⟨idx, List.mem_finRange idx, Or.inl ⟨j, rfl⟩⟩
      · exact ⟨idx, List.mem_finRange idx, Or.inr rfl⟩
    refine relax (seq Hprev Hlevel) le_rfl ?_ ?_
    · rintro f (⟨r, hr, idx, j, rfl⟩ | ⟨dl, hdl, hlt, idx, rfl⟩)
      · by_cases hrm : r ≤ m
        · exact Or.inl (Or.inl ⟨r, hrm, idx, j, rfl⟩)
        · have heq : r = m + 1 := by omega
          subst heq
          exact Or.inr (Or.inl ⟨idx, j, rfl⟩)
      · by_cases hltm : w - (dl + 1) < m
        · exact Or.inl (Or.inr ⟨dl, hdl, hltm, idx, rfl⟩)
        · have heq : dl = d_lev := by dsimp [d_lev]; omega
          subst heq
          exact Or.inr (Or.inr ⟨idx, rfl⟩)
    · have hpow : 2 ^ (w - m) = 2 ^ d_lev + 2 ^ d_lev := by
        rw [show w - m = d_lev + 1 by dsimp [d_lev]; omega, Nat.pow_succ]; omega
      have hle_pow : 2 ^ (w - m) ≤ 2 ^ w := Nat.pow_le_pow_right Nat.zero_lt_two (by omega)
      have hle1 : 2 ^ d_lev * (7 * d_lev + 3) ≤ 2 ^ d_lev * (7 * w + 3) :=
        Nat.mul_le_mul_left _ (by omega)
      have hstep : (2 ^ w + 2 ^ w - 2 ^ (w - m)) + 2 ^ d_lev = 2 ^ w + 2 ^ w - 2 ^ (w - (m + 1)) := by
        rw [hpow] at hle_pow ⊢
        change (2 ^ w + 2 ^ w - (2 ^ d_lev + 2 ^ d_lev)) + 2 ^ d_lev = 2 ^ w + 2 ^ w - 2 ^ d_lev
        generalize 2 ^ w = A at hle_pow ⊢
        generalize 2 ^ d_lev = B at hle_pow ⊢
        omega
      rw [← hstep, Nat.add_mul]
      exact Nat.add_le_add_left hle1 _

private theorem build_all_outputs {n w K : Nat} (hn : 0 < n) (hwn : w ≤ n)
    (hKlo : 2 ^ w ≤ K) (hKhi : K ≤ 4 ^ w) :
    let I := n * 2 ^ (w + 1)
    let S := (3 * (n - w) + 2) * K
    ∃ c ≤ 262144 * (n + 1) ^ 4 * K,
      GateBridge.Scheduled I id c
        ({evalOutFn (K := K) hn} ∪
         {f | ∃ s : Fin S, f = slotEnable hn hKlo s} ∪
         {f | ∃ (s : Fin S) (lit : PEqualNP.ProofComplexity.Literal (Fin n)),
           f = slotMember hn hKlo s lit}) := by
  intro I S
  have hStart : GateBridge.Scheduled I id 0 (Set.range (fun a : Fin I => fun x : Fin I → Bool => x a)) :=
    GateBridge.start (F := id) (fun a => fun x => x a) (fun _ _ => rfl)
  let A0 := Set.range (fun a : Fin I => fun x : Fin I → Bool => x a)
  have Hconst : Build A0 ({fun _ => false} ∪ {fun _ => true}) 2 :=
    seq (constG false) (constG true)
  obtain ⟨c0, hc0, HS0⟩ := Hconst.run hStart le_rfl
  let B0 := A0 ∪ ({fun _ => false} ∪ {fun _ => true})
  have hIn : ∀ a : Fin I, (fun x => x a) ∈ B0 := fun a => Or.inl ⟨a, rfl⟩
  have hF : (fun _ : Fin I → Bool => false) ∈ B0 := Or.inr (Or.inl rfl)
  have hT : (fun _ : Fin I → Bool => true) ∈ B0 := Or.inr (Or.inr rfl)
  have Hfwd := build_fwdAll (K := K) hn hwn hKlo hKhi hIn hF hT (n - w)
  have Hwrap := build_wrap (K := K) hn hwn hKlo hKhi (A := B0 ∪ FwdAllSet (K := K) hn (n - w))
    (fun a => Or.inl (hIn a)) (Or.inl hF) (Or.inl hT)
    (fun f hf => Or.inr (Or.inl ⟨n - w, le_rfl, hf⟩))
  have Hbwd := build_bwdAll (K := K) hn hwn hKlo hKhi
    (A := (B0 ∪ FwdAllSet (K := K) hn (n - w)) ∪ WrapOutSet (K := K) hn)
    (Or.inl (Or.inl hF)) (Or.inl (Or.inl hT))
    (fun f hf => Or.inl (Or.inr hf)) (fun f hf => Or.inr hf) (n - w) le_rfl
  let B3 := ((B0 ∪ FwdAllSet (K := K) hn (n - w)) ∪ WrapOutSet (K := K) hn) ∪
    BwdAllSet (K := K) hn (n - w)
  have Hseed := build_seedAll (K := K) hn hKlo (A := B3)
    (fun i j => Or.inr (Or.inl ⟨n - w, le_rfl, i, j, rfl⟩)) w le_rfl
  let B4 := B3 ∪ SeedAllSet (K := K) hn hKlo w le_rfl
  have hF4 : (fun _ : Fin I → Bool => false) ∈ B4 := Or.inl (Or.inl (Or.inl (Or.inl hF)))
  have hT4 : (fun _ : Fin I → Bool => true) ∈ B4 := Or.inl (Or.inl (Or.inl (Or.inl hT)))
  have hSt4 : ∀ h ≤ n - w, StateSet (fwdLayer (K := K) hn h) ⊆ B4 :=
    fun h hh f hf => Or.inl (Or.inl (Or.inl (Or.inr (Or.inl ⟨h, hh, hf⟩))))
  have hCL4 : ∀ h < n - w, ∀ idx : Fin (2 * K),
      (fun x => childLookup hn h (fwdLayer hn h x) x idx) ∈ B4 :=
    fun h hh idx => Or.inl (Or.inl (Or.inl (Or.inr (Or.inr ⟨h, hh, Or.inl (Or.inl (Or.inl (Or.inr ⟨idx, rfl⟩)))⟩))))
  have hBwd4 : ∀ h ≤ n - w, ∀ (i : Fin K) (j : Fin (2 * w)),
      (fun x => bwdMask hn h x i j) ∈ B4 :=
    fun h hh i j => Or.inl (Or.inr (Or.inl ⟨n - w - h, by omega, i, j, rfl⟩))
  have hParRes4 : ∀ h < n - w, ∀ i : Fin K,
      (fun x => (parentStep hn h (bwdMask hn (h + 1) x) x i).2) ∈ B4 := by
    intro h hh i
    have hr : n - w - (h + 1) < n - w := by omega
    have hmem : (fun x => (parentStep hn (n - w - (n - w - (h + 1) + 1))
        (bwdMaskAux hn (n - w - (h + 1)) x) x i).2) ∈ B4 :=
      Or.inl (Or.inr (Or.inr ⟨n - w - (h + 1), hr, i, rfl⟩))
    have heq : n - w - (n - w - (h + 1) + 1) = h := by omega
    simpa only [heq, bwdMask] using hmem
  have Henable : Build B4 (Set.range (fun s : Fin S => slotEnable hn hKlo s)) (S * 2) :=
    finG (fun s => slotEnable hn hKlo s) 2 fun s => by
      change Build B4 {fun x => slotEnable hn hKlo s x} 2
      dsimp only [slotEnable]
      split_ifs with hs1 hsSeed hs2 hk0 hk1
      · refine relax (idle ?_) le_rfl le_rfl (by omega)
        rintro _ rfl
        have hd : Nat.log2 (s.val + 1) < w := by
          by_contra hge
          have hp := Nat.pow_le_pow_right Nat.zero_lt_two (show w ≤ Nat.log2 (s.val + 1) by omega)
          have hl := Nat.log2_self_le (show s.val + 1 ≠ 0 by omega)
          omega
        exact Or.inr (Or.inr ⟨Nat.log2 (s.val + 1), hd, by omega, _, rfl⟩)
      · exact relax (idle (Set.singleton_subset_iff.mpr hF4)) le_rfl le_rfl (by omega)
      · have hKpos : 0 < K := (Nat.two_pow_pos w).trans_le hKlo
        have hh : (s.val - K) / (3 * K) < n - w :=
          (Nat.div_lt_iff_lt_mul (by omega)).mpr (by omega)
        let hcur := (s.val - K) / (3 * K)
        let icur : Fin K := ⟨(s.val - K) % (3 * K) % K, Nat.mod_lt _ hKpos⟩
        have h1 := andG (hSt4 hcur (by omega) ⟨icur, Or.inl rfl⟩) (hParRes4 hcur hh icur)
        exact relax h1 le_rfl le_rfl (by omega)
      · have hKpos : 0 < K := (Nat.two_pow_pos w).trans_le hKlo
        have hh : (s.val - K) / (3 * K) < n - w :=
          (Nat.div_lt_iff_lt_mul (by omega)).mpr (by omega)
        let hcur := (s.val - K) / (3 * K)
        let icur : Fin K := ⟨(s.val - K) % (3 * K) % K, Nat.mod_lt _ hKpos⟩
        let c0 : Fin (2 * K) := ⟨2 * icur.val, by have := icur.isLt; omega⟩
        have h1 : Build B4 {nt (fun x => childLookup hn hcur (fwdLayer hn hcur x) x c0)} 1 := notG (hCL4 hcur hh c0)
        have h2 := andG (A := B4 ∪ {nt (fun x => childLookup hn hcur (fwdLayer hn hcur x) x c0)})
          (Or.inl (hSt4 hcur (by omega) ⟨icur, Or.inl rfl⟩)) (Or.inr rfl)
        exact relax (seq h1 h2) le_rfl (Set.singleton_subset_iff.mpr (Or.inr rfl)) (by omega)
      · have hKpos : 0 < K := (Nat.two_pow_pos w).trans_le hKlo
        have hh : (s.val - K) / (3 * K) < n - w :=
          (Nat.div_lt_iff_lt_mul (by omega)).mpr (by omega)
        let hcur := (s.val - K) / (3 * K)
        let icur : Fin K := ⟨(s.val - K) % (3 * K) % K, Nat.mod_lt _ hKpos⟩
        let c1 : Fin (2 * K) := ⟨2 * icur.val + 1, by have := icur.isLt; omega⟩
        have h1 : Build B4 {nt (fun x => childLookup hn hcur (fwdLayer hn hcur x) x c1)} 1 := notG (hCL4 hcur hh c1)
        have h2 := andG (A := B4 ∪ {nt (fun x => childLookup hn hcur (fwdLayer hn hcur x) x c1)})
          (Or.inl (hSt4 hcur (by omega) ⟨icur, Or.inl rfl⟩)) (Or.inr rfl)
        exact relax (seq h1 h2) le_rfl (Set.singleton_subset_iff.mpr (Or.inr rfl)) (by omega)
      · exact relax (idle (Set.singleton_subset_iff.mpr (hSt4 (n - w) le_rfl ⟨_, Or.inl rfl⟩)))
          le_rfl le_rfl (by omega)
  let B5 := B4 ∪ Set.range (fun s : Fin S => slotEnable hn hKlo s)
  have hClauseMemG : ∀ (h : Nat) (hh : h ≤ n - w) (i : Fin K)
      (lit : PEqualNP.ProofComplexity.Literal (Fin n)),
      Build B5 (Set.singleton (fun x => clauseMemBit h (fwdLayer hn h x i).2.1 (fwdLayer hn h x i).2.2
        (bwdMask hn h x i) lit)) 5 := by
    intro h hh i lit
    have hF5 : (fun _ : Fin I → Bool => false) ∈ B5 := Or.inl hF4
    let aSig : Sig I := fun x => if hv : lit.1.val < w then
      bwdMask hn h x i ⟨lit.1.val, by omega⟩ &&
        (!((fwdLayer hn h x i).2.1 ⟨lit.1.val, hv⟩) == lit.2) else false
    let zSig : Sig I := fun x => if hv : h ≤ lit.1.val ∧ lit.1.val < h + w then
      bwdMask hn h x i ⟨w + (lit.1.val - h), by omega⟩ &&
        (!((fwdLayer hn h x i).2.2 ⟨lit.1.val - h, by omega⟩) == lit.2) else false
    have hA_term : Build B5 {aSig} 2 := by
      dsimp only [aSig]
      split_ifs with hv
      · cases hsg : lit.2
        · have he : (fun (x : Fin I → Bool) => bwdMask hn h x i ⟨lit.1.val, by omega⟩ &&
              (!((fwdLayer hn h x i).2.1 ⟨lit.1.val, hv⟩) == false)) =
              an (fun x => bwdMask hn h x i ⟨lit.1.val, by omega⟩)
                 (fun x => (fwdLayer hn h x i).2.1 ⟨lit.1.val, hv⟩) := by
            funext x; simp [an]
          rw [he]
          exact relax (andG (Or.inl (hBwd4 h hh i _))
            (Or.inl (hSt4 h hh ⟨i, Or.inr (Or.inl ⟨⟨lit.1.val, hv⟩, rfl⟩)⟩))) le_rfl le_rfl (by omega)
        · have he : (fun (x : Fin I → Bool) => bwdMask hn h x i ⟨lit.1.val, by omega⟩ &&
              (!((fwdLayer hn h x i).2.1 ⟨lit.1.val, hv⟩) == true)) =
              an (fun x => bwdMask hn h x i ⟨lit.1.val, by omega⟩)
                 (nt (fun x => (fwdLayer hn h x i).2.1 ⟨lit.1.val, hv⟩)) := by
            funext x; simp [an, nt]
          rw [he]
          have h1 : Build B5 {nt (fun x => (fwdLayer hn h x i).2.1 ⟨lit.1.val, hv⟩)} 1 :=
            notG (Or.inl (hSt4 h hh ⟨i, Or.inr (Or.inl ⟨⟨lit.1.val, hv⟩, rfl⟩)⟩))
          have h2 := andG (A := B5 ∪ {nt (fun x => (fwdLayer hn h x i).2.1 ⟨lit.1.val, hv⟩)})
            (Or.inl (Or.inl (hBwd4 h hh i ⟨lit.1.val, by omega⟩))) (Or.inr rfl)
          exact relax (seq h1 h2) le_rfl (Set.singleton_subset_iff.mpr (Or.inr rfl)) (by omega)
      · exact relax (idle (Set.singleton_subset_iff.mpr hF5)) le_rfl le_rfl (by omega)
    have hZ_term : Build (B5 ∪ {aSig}) {zSig} 2 := by
      dsimp only [zSig]
      split_ifs with hv
      · cases hsg : lit.2
        · have he : (fun (x : Fin I → Bool) => bwdMask (w := w) hn h x i ⟨w + (lit.1.val - h), by omega⟩ &&
              (!((fwdLayer hn h x i).2.2 ⟨lit.1.val - h, by omega⟩) == false)) =
              an (fun x => bwdMask (w := w) hn h x i ⟨w + (lit.1.val - h), by omega⟩)
                 (fun x => (fwdLayer hn h x i).2.2 ⟨lit.1.val - h, by omega⟩) := by
            funext x; simp [an]
          rw [he]
          exact relax (andG (Or.inl (Or.inl (hBwd4 h hh i ⟨w + (lit.1.val - h), by omega⟩)))
            (Or.inl (Or.inl (hSt4 h hh ⟨i, Or.inr (Or.inr ⟨⟨lit.1.val - h, by omega⟩, rfl⟩)⟩))))
            le_rfl le_rfl (by omega)
        · have he : (fun (x : Fin I → Bool) => bwdMask (w := w) hn h x i ⟨w + (lit.1.val - h), by omega⟩ &&
              (!((fwdLayer hn h x i).2.2 ⟨lit.1.val - h, by omega⟩) == true)) =
              an (fun x => bwdMask (w := w) hn h x i ⟨w + (lit.1.val - h), by omega⟩)
                 (nt (fun x => (fwdLayer hn h x i).2.2 ⟨lit.1.val - h, by omega⟩)) := by
            funext x; simp [an, nt]
          rw [he]
          have h1 : Build (B5 ∪ {aSig}) {nt (fun x => (fwdLayer hn h x i).2.2 ⟨lit.1.val - h, by omega⟩)} 1 :=
            notG (Or.inl (Or.inl (hSt4 h hh ⟨i, Or.inr (Or.inr ⟨⟨lit.1.val - h, by omega⟩, rfl⟩)⟩)))
          have h2 := andG (A := (B5 ∪ {aSig}) ∪ {nt (fun x => (fwdLayer hn h x i).2.2 ⟨lit.1.val - h, by omega⟩)})
            (Or.inl (Or.inl (Or.inl (hBwd4 h hh i ⟨w + (lit.1.val - h), by omega⟩)))) (Or.inr rfl)
          exact relax (seq h1 h2) le_rfl (Set.singleton_subset_iff.mpr (Or.inr rfl)) (by omega)
      · exact relax (idle (Set.singleton_subset_iff.mpr (Or.inl hF5))) le_rfl le_rfl (by omega)
    have hOr : Build (B5 ∪ ({aSig} ∪ {zSig}))
        (Set.singleton (fun x => clauseMemBit h (fwdLayer hn h x i).2.1 (fwdLayer hn h x i).2.2
          (bwdMask hn h x i) lit)) 1 :=
      orG (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl))
    exact relax (seq (seq hA_term hZ_term) hOr) le_rfl (Set.singleton_subset_iff.mpr (Or.inr rfl)) (by omega)
  have hMemOne : ∀ (s : Fin S) (lit : PEqualNP.ProofComplexity.Literal (Fin n)),
      Build B5 {slotMember hn hKlo s lit} 5 := by
    intro s lit
    change Build B5 {fun x => slotMember hn hKlo s lit x} 5
    dsimp only [slotMember]
    split_ifs with hs1 hsSeed hv hbit hs2 hk0 hk1
    · refine relax (idle ?_) le_rfl le_rfl (by omega)
      rintro _ rfl
      have hd : Nat.log2 (s.val + 1) < w := by
        by_contra hge
        have hp := Nat.pow_le_pow_right Nat.zero_lt_two (show w ≤ Nat.log2 (s.val + 1) by omega)
        have hl := Nat.log2_self_le (show s.val + 1 ≠ 0 by omega)
        omega
      exact Or.inl (Or.inr (Or.inl ⟨w - Nat.log2 (s.val + 1), by omega, _, _, rfl⟩))
    · exact relax (idle (Set.singleton_subset_iff.mpr (Or.inl hF4))) le_rfl le_rfl (by omega)
    · exact relax (idle (Set.singleton_subset_iff.mpr (Or.inl hF4))) le_rfl le_rfl (by omega)
    · exact relax (idle (Set.singleton_subset_iff.mpr (Or.inl hF4))) le_rfl le_rfl (by omega)
    · have hKpos : 0 < K := (Nat.two_pow_pos w).trans_le hKlo
      have hh : (s.val - K) / (3 * K) < n - w := (Nat.div_lt_iff_lt_mul (by omega)).mpr (by omega)
      exact hClauseMemG _ (by omega) _ lit
    · have hKpos : 0 < K := (Nat.two_pow_pos w).trans_le hKlo
      have hh : (s.val - K) / (3 * K) < n - w := (Nat.div_lt_iff_lt_mul (by omega)).mpr (by omega)
      dsimp only [axiomMemBit]
      split_ifs with hv1 hv2
      · cases lit.2
        · have he : (fun (x : Fin I → Bool) => !((fwdLayer (w := w) (K := K) hn ((s.val - K) / (3 * K)) x ⟨(s.val - K) % (3 * K) % K,
              Nat.mod_lt _ hKpos⟩).2.2 ⟨lit.1.val - (s.val - K) / (3 * K), by omega⟩) == false) =
              fun (x : Fin I → Bool) => (fwdLayer (w := w) (K := K) hn ((s.val - K) / (3 * K)) x ⟨(s.val - K) % (3 * K) % K,
                Nat.mod_lt _ hKpos⟩).2.2 ⟨lit.1.val - (s.val - K) / (3 * K), by omega⟩ := by
            funext x; simp
          rw [he]
          exact relax (idle (Set.singleton_subset_iff.mpr (Or.inl (hSt4 ((s.val - K) / (3 * K)) (by omega) ⟨_, Or.inr (Or.inr ⟨_, rfl⟩)⟩))))
            le_rfl le_rfl (by omega)
        · have he : (fun (x : Fin I → Bool) => !((fwdLayer (w := w) (K := K) hn ((s.val - K) / (3 * K)) x ⟨(s.val - K) % (3 * K) % K,
              Nat.mod_lt _ hKpos⟩).2.2 ⟨lit.1.val - (s.val - K) / (3 * K), by omega⟩) == true) =
              nt (fun (x : Fin I → Bool) => (fwdLayer (w := w) (K := K) hn ((s.val - K) / (3 * K)) x ⟨(s.val - K) % (3 * K) % K,
                Nat.mod_lt _ hKpos⟩).2.2 ⟨lit.1.val - (s.val - K) / (3 * K), by omega⟩) := by
            funext x; simp [nt]
          rw [he]
          exact relax (notG (Or.inl (hSt4 ((s.val - K) / (3 * K)) (by omega) ⟨_, Or.inr (Or.inr ⟨_, rfl⟩)⟩))) le_rfl le_rfl (by omega)
      · cases lit.2
        · exact relax (idle (Set.singleton_subset_iff.mpr (Or.inl hF4))) le_rfl le_rfl (by omega)
        · exact relax (idle (Set.singleton_subset_iff.mpr (Or.inl hT4))) le_rfl le_rfl (by omega)
      · exact relax (idle (Set.singleton_subset_iff.mpr (Or.inl hF4))) le_rfl le_rfl (by omega)
    · have hKpos : 0 < K := (Nat.two_pow_pos w).trans_le hKlo
      have hh : (s.val - K) / (3 * K) < n - w := (Nat.div_lt_iff_lt_mul (by omega)).mpr (by omega)
      dsimp only [axiomMemBit]
      split_ifs with hv1 hv2
      · cases lit.2
        · have he : (fun (x : Fin I → Bool) => !((fwdLayer (w := w) (K := K) hn ((s.val - K) / (3 * K)) x ⟨(s.val - K) % (3 * K) % K,
              Nat.mod_lt _ hKpos⟩).2.2 ⟨lit.1.val - (s.val - K) / (3 * K), by omega⟩) == false) =
              fun (x : Fin I → Bool) => (fwdLayer (w := w) (K := K) hn ((s.val - K) / (3 * K)) x ⟨(s.val - K) % (3 * K) % K,
                Nat.mod_lt _ hKpos⟩).2.2 ⟨lit.1.val - (s.val - K) / (3 * K), by omega⟩ := by
            funext x; simp
          rw [he]
          exact relax (idle (Set.singleton_subset_iff.mpr (Or.inl (hSt4 ((s.val - K) / (3 * K)) (by omega) ⟨_, Or.inr (Or.inr ⟨_, rfl⟩)⟩))))
            le_rfl le_rfl (by omega)
        · have he : (fun (x : Fin I → Bool) => !((fwdLayer (w := w) (K := K) hn ((s.val - K) / (3 * K)) x ⟨(s.val - K) % (3 * K) % K,
              Nat.mod_lt _ hKpos⟩).2.2 ⟨lit.1.val - (s.val - K) / (3 * K), by omega⟩) == true) =
              nt (fun (x : Fin I → Bool) => (fwdLayer (w := w) (K := K) hn ((s.val - K) / (3 * K)) x ⟨(s.val - K) % (3 * K) % K,
                Nat.mod_lt _ hKpos⟩).2.2 ⟨lit.1.val - (s.val - K) / (3 * K), by omega⟩) := by
            funext x; simp [nt]
          rw [he]
          exact relax (notG (Or.inl (hSt4 ((s.val - K) / (3 * K)) (by omega) ⟨_, Or.inr (Or.inr ⟨_, rfl⟩)⟩))) le_rfl le_rfl (by omega)
      · cases lit.2
        · exact relax (idle (Set.singleton_subset_iff.mpr (Or.inl hT4))) le_rfl le_rfl (by omega)
        · exact relax (idle (Set.singleton_subset_iff.mpr (Or.inl hF4))) le_rfl le_rfl (by omega)
      · exact relax (idle (Set.singleton_subset_iff.mpr (Or.inl hF4))) le_rfl le_rfl (by omega)
    · have hterm_eq : termMask (w := w) (K := K) hn = bwdMask (w := w) (K := K) hn (n - w) := by
        funext x i j; simp [bwdMask, bwdMaskAux]
      rw [hterm_eq]
      exact hClauseMemG (n - w) le_rfl _ lit
  let allPairs : List (Fin S × PEqualNP.ProofComplexity.Literal (Fin n)) :=
    (List.finRange S).flatMap (fun s =>
      (List.finRange n).flatMap (fun v => [(s, (v, false)), (s, (v, true))]))
  have hallPairs_len : allPairs.length = S * (2 * n) := by
    have h1 : ∀ s : Fin S, ((List.finRange n).flatMap (fun v => [(s, (v, false)), (s, (v, true))])).length = 2 * n := by
      intro s
      have : ∀ l : List (Fin n), (l.flatMap (fun v => [(s, (v, false)), (s, (v, true))])).length = 2 * l.length := by
        intro l; induction l with
        | nil => simp
        | cons a ls ih => simp [ih]; omega
      rw [this, List.length_finRange]
    have h2 : ∀ l : List (Fin S),
        (l.flatMap (fun s => (List.finRange n).flatMap (fun v => [(s, (v, false)), (s, (v, true))]))).length =
          l.length * (2 * n) := by
      intro l; induction l with
      | nil => simp
      | cons a ls ih => simp [h1 a, ih]; ring
    dsimp only [allPairs]
    rw [h2, List.length_finRange]
  have Hmem : Build B5 {f | ∃ (s : Fin S) (lit : PEqualNP.ProofComplexity.Literal (Fin n)),
      f = slotMember hn hKlo s lit} (S * (2 * n) * 5) := by
    have Hlist := listBuild allPairs (fun p => slotMember hn hKlo p.1 p.2) 5
      (fun p _ => hMemOne p.1 p.2)
    rw [hallPairs_len] at Hlist
    refine relax Hlist le_rfl ?_ le_rfl
    rintro f ⟨s, ⟨v, sg⟩, rfl⟩
    refine ⟨(s, (v, sg)), ?_, rfl⟩
    dsimp only [allPairs]
    rw [List.mem_flatMap]
    refine ⟨s, List.mem_finRange s, ?_⟩
    rw [List.mem_flatMap]
    refine ⟨v, List.mem_finRange v, ?_⟩
    cases sg <;> simp
  have Hgrand := stepU (stepU (stepU (stepU (stepU (buildSelf Hfwd) Hwrap) Hbwd) Hseed) Henable) Hmem
  obtain ⟨c1, hc1, HS1⟩ := Hgrand.run HS0 le_rfl
  rw [Nat.zero_add] at HS1
  refine ⟨c0 + c1, ?_, GateBridge.restrict HS1 ?_⟩
  · have hKpos : 1 ≤ K := (Nat.two_pow_pos w).trans_le hKlo
    have h1p2 : 1 ≤ (n + 1) ^ 2 := Nat.one_le_pow 2 (n + 1) (by omega)
    have h1p3 : 1 ≤ (n + 1) ^ 3 := Nat.one_le_pow 3 (n + 1) (by omega)
    have h1p4 : 1 ≤ (n + 1) ^ 4 := Nat.one_le_pow 4 (n + 1) (by omega)
    have hnw : (n - w) * (65000 * (n + 1) ^ 3 * K) + w * (64000 * (n + 1) ^ 3 * K) ≤
        65000 * (n + 1) ^ 4 * K := by
      have h0 : 64000 * (n + 1) ^ 3 * K ≤ 65000 * (n + 1) ^ 3 * K := by
        rw [Nat.mul_assoc, Nat.mul_assoc]; exact Nat.mul_le_mul_right _ (by omega)
      have h1 : w * (64000 * (n + 1) ^ 3 * K) ≤ w * (65000 * (n + 1) ^ 3 * K) :=
        Nat.mul_le_mul_left w h0
      have h2 : (n - w) + w = n := Nat.sub_add_cancel hwn
      have h3 : (n - w) * (65000 * (n + 1) ^ 3 * K) + w * (65000 * (n + 1) ^ 3 * K) =
          n * (65000 * (n + 1) ^ 3 * K) := by rw [← Nat.add_mul, h2]
      have h4 : n * (65000 * (n + 1) ^ 3 * K) ≤ (n + 1) * (65000 * (n + 1) ^ 3 * K) :=
        Nat.mul_le_mul_right _ (by omega)
      have h5 : (n + 1) * (65000 * (n + 1) ^ 3 * K) = 65000 * (n + 1) ^ 4 * K := by ring
      omega
    have hbwd_le : (n - w) * (200 * (n + 1) ^ 3 * K) ≤ 200 * (n + 1) ^ 4 * K := by
      have h1 := Nat.mul_le_mul_right (200 * (n + 1) ^ 3 * K) (show n - w ≤ n + 1 by omega)
      have h2 : (n + 1) * (200 * (n + 1) ^ 3 * K) = 200 * (n + 1) ^ 4 * K := by ring
      omega
    have hseed_le : (2 ^ w + 2 ^ w - 2 ^ (w - w)) * (7 * w + 3) ≤ 14 * (n + 1) ^ 4 * K := by
      have h1 : 2 ^ w + 2 ^ w - 2 ^ (w - w) ≤ 2 * K := by rw [Nat.sub_self, Nat.pow_zero]; omega
      have h2 : 7 * w + 3 ≤ 7 * (n + 1) := by omega
      have h3 : n + 1 ≤ (n + 1) * (n + 1) ^ 3 := Nat.le_mul_of_pos_right _ (by omega)
      calc (2 ^ w + 2 ^ w - 2 ^ (w - w)) * (7 * w + 3)
          ≤ (2 * K) * (7 * (n + 1)) := Nat.mul_le_mul h1 h2
        _ = 14 * (n + 1) * K := by ring
        _ ≤ 14 * ((n + 1) * (n + 1) ^ 3) * K := Nat.mul_le_mul_right K (Nat.mul_le_mul_left 14 h3)
        _ = 14 * (n + 1) ^ 4 * K := by ring
    have hS_le : S ≤ 3 * (n + 1) * K := by
      dsimp only [S]
      exact Nat.mul_le_mul_right K (by omega)
    have hen_le : S * 2 ≤ 6 * (n + 1) ^ 4 * K := by
      have h3 : n + 1 ≤ (n + 1) * (n + 1) ^ 3 := Nat.le_mul_of_pos_right _ (by omega)
      calc S * 2 ≤ (3 * (n + 1) * K) * 2 := Nat.mul_le_mul_right 2 hS_le
        _ = 6 * (n + 1) * K := by ring
        _ ≤ 6 * ((n + 1) * (n + 1) ^ 3) * K := Nat.mul_le_mul_right K (Nat.mul_le_mul_left 6 h3)
        _ = 6 * (n + 1) ^ 4 * K := by ring
    have hmem_le : S * (2 * n) * 5 ≤ 30 * (n + 1) ^ 4 * K := by
      have h1 : S * (2 * n) ≤ (3 * (n + 1) * K) * (2 * (n + 1)) :=
        Nat.mul_le_mul hS_le (by omega)
      have h3 : (n + 1) ^ 2 ≤ (n + 1) ^ 2 * (n + 1) ^ 2 := Nat.le_mul_of_pos_right _ (by omega)
      calc S * (2 * n) * 5 ≤ (3 * (n + 1) * K) * (2 * (n + 1)) * 5 := Nat.mul_le_mul_right 5 h1
        _ = 30 * (n + 1) ^ 2 * K := by ring
        _ ≤ 30 * ((n + 1) ^ 2 * (n + 1) ^ 2) * K := Nat.mul_le_mul_right K (Nat.mul_le_mul_left 30 h3)
        _ = 30 * (n + 1) ^ 4 * K := by ring
    have h20 : 20 * (n + 1) ^ 2 * K ≤ 20 * (n + 1) ^ 4 * K := by
      have h3 : (n + 1) ^ 2 ≤ (n + 1) ^ 2 * (n + 1) ^ 2 := Nat.le_mul_of_pos_right _ (by omega)
      calc 20 * (n + 1) ^ 2 * K ≤ 20 * ((n + 1) ^ 2 * (n + 1) ^ 2) * K :=
            Nat.mul_le_mul_right K (Nat.mul_le_mul_left 20 h3)
        _ = 20 * (n + 1) ^ 4 * K := by ring
    have h2_le : 2 ≤ 2 * (n + 1) ^ 4 * K := by
      have h3 : 1 ≤ (n + 1) ^ 4 * K := Nat.mul_le_mul h1p4 hKpos
      calc 2 = 2 * 1 := by ring
        _ ≤ 2 * ((n + 1) ^ 4 * K) := Nat.mul_le_mul_left 2 h3
        _ = 2 * (n + 1) ^ 4 * K := by ring
    have htot_le : c0 + c1 ≤ (2 + 65000 + 20 + 200 + 14 + 6 + 30) * ((n + 1) ^ 4 * K) := by
      have ha : 2 * (n + 1) ^ 4 * K = 2 * ((n + 1) ^ 4 * K) := by ring
      have hb : 65000 * (n + 1) ^ 4 * K = 65000 * ((n + 1) ^ 4 * K) := by ring
      have hc : 20 * (n + 1) ^ 4 * K = 20 * ((n + 1) ^ 4 * K) := by ring
      have hd : 200 * (n + 1) ^ 4 * K = 200 * ((n + 1) ^ 4 * K) := by ring
      have he : 14 * (n + 1) ^ 4 * K = 14 * ((n + 1) ^ 4 * K) := by ring
      have hf : 6 * (n + 1) ^ 4 * K = 6 * ((n + 1) ^ 4 * K) := by ring
      have hg : 30 * (n + 1) ^ 4 * K = 30 * ((n + 1) ^ 4 * K) := by ring
      omega
    calc c0 + c1 ≤ 65272 * ((n + 1) ^ 4 * K) := htot_le
      _ ≤ 262144 * ((n + 1) ^ 4 * K) := Nat.mul_le_mul_right _ (by omega)
      _ = 262144 * (n + 1) ^ 4 * K := by ring
  · rintro f ((rfl | ⟨s, rfl⟩) | ⟨s, lit, rfl⟩)
    · exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl rfl))))))
    · exact Or.inr (Or.inl (Or.inr ⟨s, rfl⟩))
    · exact Or.inr (Or.inr ⟨s, lit, rfl⟩)

end PcxBuild
namespace PcxSem

open Build220 Bitonic Gadgets PcxAlgo PcxBuild
open PEqualNP.ProofComplexity PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

private theorem not_beq_eq_true (a b : Bool) : (!a == b) = true ↔ (!a) = b := by
  cases a <;> cases b <;> decide

private def tableInputVec {n w : Nat} (hn : 0 < n)
    (table : Fin n → (Fin (w + 1) → Bool) → Bool) : Fin (n * 2 ^ (w + 1)) → Bool :=
  fun a => table (posFn n hn (a.val / 2 ^ (w + 1))) (fun bit => a.val.testBit bit.val)

private def reachedOf {n : Nat} (hn : 0 < n) (w : Nat)
    (table : Fin n → (Fin (w + 1) → Bool) → Bool) (h : Nat) :
    Finset ((Fin w → Bool) × (Fin w → Bool)) :=
  ((Finset.univ : Finset (Fin n → Bool)).filter (fun word =>
    ∀ t : Fin h, table (posFn n hn t.val) (fun j => word (posFn n hn (t.val + j.val))) = true)).image
    (fun word => ((fun a : Fin w => word (posFn n hn a.val)),
                  (fun z : Fin w => word (posFn n hn (h + z.val)))))

private def formulaOf {n : Nat} (hn : 0 < n) (w : Nat)
    (table : Fin n → (Fin (w + 1) → Bool) → Bool) : Set (Clause (Fin n)) :=
  {D | ∃ (i : Fin n) (p : Fin (w + 1) → Bool), table i p = false ∧
    D = Finset.univ.image (fun k : Fin (w + 1) => (posFn n hn (i.val + k.val), !(p k)))}

private theorem tabEval_tableInputVec {n w : Nat} (hn : 0 < n)
    (table : Fin n → (Fin (w + 1) → Bool) → Bool) (row : Fin n) (pat : Fin (w + 1) → Bool) :
    tabEval (tableInputVec hn table) row pat = table row pat := by
  dsimp only [tabEval, tableInputVec]
  let p := bitsVal (fun bit => if h : bit < w + 1 then pat ⟨bit, h⟩ else false) (w + 1)
  have hp : p < 2 ^ (w + 1) := bitsVal_lt _ (w + 1)
  have hpos : posFn n hn ((row.val * 2 ^ (w + 1) + p) / 2 ^ (w + 1)) = row := by
    have hdiv : (row.val * 2 ^ (w + 1) + p) / 2 ^ (w + 1) = row.val := by
      rw [Nat.mul_comm, Nat.mul_add_div (Nat.two_pow_pos (w + 1)), Nat.div_eq_of_lt hp, Nat.add_zero]
    apply Fin.ext
    dsimp only [posFn]
    rw [hdiv, Nat.mod_eq_of_lt row.isLt]
  have hpat : (fun bit : Fin (w + 1) => (row.val * 2 ^ (w + 1) + p).testBit bit.val) = pat := by
    funext bit
    have hpow : 2 ^ (w + 1) = 2 ^ bit.val * 2 ^ (w + 1 - bit.val) := by
      rw [← Nat.pow_add, Nat.add_sub_of_le (by omega)]
    have hdiv : (row.val * 2 ^ (w + 1) + p) / 2 ^ bit.val =
        row.val * 2 ^ (w + 1 - bit.val) + p / 2 ^ bit.val := by
      rw [hpow, show row.val * (2 ^ bit.val * 2 ^ (w + 1 - bit.val)) =
        2 ^ bit.val * (row.val * 2 ^ (w + 1 - bit.val)) by ring]
      rw [Nat.mul_add_div (Nat.two_pow_pos bit.val)]
    have hmod2 : (row.val * 2 ^ (w + 1 - bit.val) + p / 2 ^ bit.val) % 2 = (p / 2 ^ bit.val) % 2 := by
      have hge : 1 ≤ w + 1 - bit.val := by omega
      have h2 : 2 ^ (w + 1 - bit.val) = 2 * 2 ^ (w - bit.val) := by
        rw [show w + 1 - bit.val = (w - bit.val) + 1 by omega, Nat.pow_succ, Nat.mul_comm]
      rw [h2, show row.val * (2 * 2 ^ (w - bit.val)) = 2 * (row.val * 2 ^ (w - bit.val)) by ring]
      rw [Nat.mul_add_mod]
    have htb : (row.val * 2 ^ (w + 1) + p).testBit bit.val = p.testBit bit.val := by
      rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq, hdiv, hmod2]
    rw [htb, bitsVal_testBit _ (w + 1) bit.val bit.isLt]
    simp [bit.isLt]
  rw [hpos, hpat]

private theorem posFn_of_lt {n : Nat} (hn : 0 < n) {v : Nat} (hv : v < n) :
    posFn n hn v = ⟨v, hv⟩ := by
  apply Fin.ext
  dsimp only [posFn]
  exact Nat.mod_eq_of_lt hv

private theorem reachedOf_zero {n w : Nat} (hn : 0 < n) (hwn : w ≤ n)
    (table : Fin n → (Fin (w + 1) → Bool) → Bool) (pr : (Fin w → Bool) × (Fin w → Bool)) :
    pr ∈ reachedOf hn w table 0 ↔ pr.1 = pr.2 := by
  simp only [reachedOf, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨word, _, hpr⟩
    rw [← hpr]
    dsimp only
    funext r
    simp
  · intro heq
    rcases pr with ⟨a, z⟩
    dsimp only at heq
    subst heq
    refine ⟨fun v => if hv : v.val < w then a ⟨v.val, hv⟩ else false, fun t => t.elim0, ?_⟩
    apply Prod.ext <;> (funext r; simp [posFn_of_lt hn (by omega : r.val < n), r.isLt])

private theorem reachedOf_succ {n w : Nat} (hn : 0 < n)
    (table : Fin n → (Fin (w + 1) → Bool) → Bool) {h : Nat} (hh : h < n - w)
    (a z' : Fin w → Bool) :
    (a, z') ∈ reachedOf hn w table (h + 1) ↔
      ∃ z b, (a, z) ∈ reachedOf hn w table h ∧
        table (posFn n hn h) (extPat z b) = true ∧ z' = nextZ z b := by
  simp only [reachedOf, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨word, hpass, hpr⟩
    have ha : (fun r : Fin w => word (posFn n hn r.val)) = a := congrArg Prod.fst hpr
    have hz' : (fun r : Fin w => word (posFn n hn (h + 1 + r.val))) = z' := congrArg Prod.snd hpr
    refine ⟨fun r => word (posFn n hn (h + r.val)), word (posFn n hn (h + w)),
      ⟨word, fun t => hpass ⟨t.val, by omega⟩, Prod.ext ha rfl⟩, ?_, ?_⟩
    · have hp := hpass ⟨h, Nat.lt_succ_self h⟩
      convert hp using 2
      funext k
      dsimp only [extPat]
      split_ifs with hk
      · rfl
      · have hkw : k.val = w := by have := k.isLt; omega
        rw [hkw]
    · rw [← hz']
      funext r
      dsimp only [nextZ]
      split_ifs with hr
      · congr 1; congr 1; omega
      · congr 1; congr 1; have := r.isLt; omega
  · rintro ⟨z, b, ⟨word, hpass, hpr⟩, htab, rfl⟩
    have ha : (fun r : Fin w => word (posFn n hn r.val)) = a := congrArg Prod.fst hpr
    have hz : (fun r : Fin w => word (posFn n hn (h + r.val))) = z := congrArg Prod.snd hpr
    let piv : Fin n := posFn n hn (h + w)
    have hpiv : piv.val = h + w := by dsimp [piv, posFn]; exact Nat.mod_eq_of_lt (by omega)
    let word' : Fin n → Bool := Function.update word piv b
    have hupd_ne : ∀ v < h + w, word' (posFn n hn v) = word (posFn n hn v) := by
      intro v hv
      have hne : posFn n hn v ≠ piv := by
        intro heq
        have hv1 : (posFn n hn v).val = v := by dsimp [posFn]; exact Nat.mod_eq_of_lt (by omega)
        have := congrArg Fin.val heq
        omega
      exact Function.update_of_ne hne b word
    refine ⟨word', ?_, ?_⟩
    · intro t
      by_cases ht : t.val < h
      · have hpat : (fun j : Fin (w + 1) => word' (posFn n hn (t.val + j.val))) =
            fun j : Fin (w + 1) => word (posFn n hn (t.val + j.val)) := by
          funext j; exact hupd_ne (t.val + j.val) (by have := j.isLt; omega)
        rw [hpat]
        exact hpass ⟨t.val, ht⟩
      · have hth : t.val = h := by have := t.isLt; omega
        rw [hth]
        have hpat : (fun j : Fin (w + 1) => word' (posFn n hn (h + j.val))) = extPat z b := by
          funext j
          dsimp only [extPat]
          split_ifs with hj
          · rw [hupd_ne (h + j.val) (by omega), ← hz]
          · have hjw : j.val = w := by have := j.isLt; omega
            rw [hjw]
            exact Function.update_self piv b word
        rw [hpat]
        exact htab
    · apply Prod.ext
      · funext r
        dsimp only
        rw [hupd_ne r.val (by have := r.isLt; omega), ← ha]
      · funext r
        dsimp only [nextZ]
        split_ifs with hr
        · rw [hupd_ne (h + 1 + r.val) (by omega), ← hz]
          congr 1; congr 1; dsimp; omega
        · have hrw : h + 1 + r.val = h + w := by have := r.isLt; omega
          rw [hrw]
          exact Function.update_self piv b word

private theorem reachedOf_overlap {n w : Nat} (hn : 0 < n) (_hwn : w ≤ n)
    (table : Fin n → (Fin (w + 1) → Bool) → Bool) {h : Nat} {a z : Fin w → Bool}
    (hmem : (a, z) ∈ reachedOf hn w table h) {v : Nat} (hv1 : v < w) (hv2 : h ≤ v) (hv3 : v < h + w) :
    a ⟨v, hv1⟩ = z ⟨v - h, by omega⟩ := by
  simp only [reachedOf, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
  rcases hmem with ⟨word, _, hpr⟩
  have ha : word (posFn n hn v) = a ⟨v, hv1⟩ := congrFun (congrArg Prod.fst hpr) ⟨v, hv1⟩
  have hz : word (posFn n hn (h + (v - h))) = z ⟨v - h, by omega⟩ := congrFun (congrArg Prod.snd hpr) ⟨v - h, by omega⟩
  rw [← ha, ← hz]
  congr 1; congr 1; omega

private theorem satisfies_iff_table {n w : Nat} (hn : 0 < n)
    (table : Fin n → (Fin (w + 1) → Bool) → Bool) (word : Fin n → Bool) :
    Satisfies word (formulaOf hn w table) ↔
      ∀ i : Fin n, table i (fun k => word (posFn n hn (i.val + k.val))) = true := by
  constructor
  · intro hsat i
    by_contra hne
    have hfalse : table i (fun k => word (posFn n hn (i.val + k.val))) = false :=
      Bool.eq_false_iff.mpr hne
    let D : Clause (Fin n) := Finset.univ.image
      (fun k : Fin (w + 1) => (posFn n hn (i.val + k.val), !(word (posFn n hn (i.val + k.val)))))
    have hDF : D ∈ formulaOf hn w table := ⟨i, fun k => word (posFn n hn (i.val + k.val)), hfalse, rfl⟩
    rcases hsat D hDF with ⟨l, hl, hval⟩
    simp only [D, Finset.mem_image, Finset.mem_univ, true_and] at hl
    rcases hl with ⟨k, rfl⟩
    simp at hval
  · intro htab D hDF
    rcases hDF with ⟨i, p, hfalse, rfl⟩
    have htrue := htab i
    have hne : (fun k : Fin (w + 1) => word (posFn n hn (i.val + k.val))) ≠ p := by
      intro heq; rw [heq] at htrue; rw [hfalse] at htrue; cases htrue
    have hex : ∃ k : Fin (w + 1), word (posFn n hn (i.val + k.val)) ≠ p k := by
      by_contra hall
      push Not at hall
      exact hne (funext hall)
    rcases hex with ⟨k, hk⟩
    refine ⟨(posFn n hn (i.val + k.val), !(p k)),
      Finset.mem_image.mpr ⟨k, Finset.mem_univ k, rfl⟩, ?_⟩
    cases h1 : word (posFn n hn (i.val + k.val)) <;> cases h2 : p k <;> simp_all

private theorem applySwap_comp {α β : Type*} (u v : Nat) (sw : Bool) (g : α → β) (st : Nat → α) :
    applySwap u v sw (g ∘ st) = g ∘ applySwap u v sw st := by
  funext i
  dsimp only [applySwap, Function.comp]
  cases sw
  · rfl
  · simp only [↓reduceIte]; split_ifs <;> rfl

private theorem replaySwaps_comp {α β : Type*} (sws : List (Nat × Nat × Bool))
    (g : α → β) (st : Nat → α) :
    replaySwaps sws (g ∘ st) = g ∘ replaySwaps sws st := by
  induction sws generalizing st with
  | nil => rfl
  | cons c cs ih =>
    rcases c with ⟨u, v, sw⟩
    simp only [replaySwaps, applySwap_comp]
    exact ih (applySwap u v sw st)

private theorem replaySwaps_eq_comp_id {α : Type*} (sws : List (Nat × Nat × Bool)) (st : Nat → α) :
    replaySwaps sws st = st ∘ replaySwaps sws id := by
  simpa using replaySwaps_comp sws st id

private theorem replaySwaps_id_inv (sws : List (Nat × Nat × Bool)) (i : Nat) :
    replaySwaps sws id (replaySwaps sws.reverse id i) = i := by
  have h := congrFun (replaySwaps_reverse_cancel sws id) i
  rw [replaySwaps_eq_comp_id sws.reverse (replaySwaps sws id)] at h
  exact h

private theorem replaySwaps_id_inv_left (sws : List (Nat × Nat × Bool)) (i : Nat) :
    replaySwaps sws.reverse id (replaySwaps sws id i) = i := by
  have h := replaySwaps_id_inv sws.reverse i
  simpa using h

private theorem replaySwaps_id_lt {N : Nat} (sws : List (Nat × Nat × Bool))
    (hb : ∀ c ∈ sws, c.1 < N ∧ c.2.1 < N) :
    ∀ i < N, replaySwaps sws id i < N := by
  induction sws with
  | nil => intro i hi; exact hi
  | cons c cs ih =>
    rcases c with ⟨u, v, sw⟩
    have hc := hb (u, v, sw) List.mem_cons_self
    have hcs : ∀ x ∈ cs, x.1 < N ∧ x.2.1 < N := fun x hx => hb x (List.mem_cons_of_mem _ hx)
    intro i hi
    simp only [replaySwaps]
    rw [replaySwaps_eq_comp_id cs (applySwap u v sw id)]
    change applySwap u v sw id (replaySwaps cs id i) < N
    have hj := ih hcs i hi
    dsimp only [applySwap]
    cases sw
    · exact hj
    · simp only [↓reduceIte]
      split_ifs
      · exact hc.2
      · exact hc.1
      · exact hj

private theorem netSwaps_mem_bounds {α : Type*} {N : Nat} (key : α → Nat)
    (net : List (Nat × Nat × Bool)) (hb : ∀ c ∈ net, c.1 < N ∧ c.2.1 < N) (st : Nat → α) :
    ∀ c ∈ netSwaps key net st, c.1 < N ∧ c.2.1 < N := by
  induction net generalizing st with
  | nil => intro c hc; simp [netSwaps] at hc
  | cons p ps ih =>
    rcases p with ⟨u, v, asc⟩
    have hp := hb (u, v, asc) List.mem_cons_self
    have hps : ∀ x ∈ ps, x.1 < N ∧ x.2.1 < N := fun x hx => hb x (List.mem_cons_of_mem _ hx)
    intro c hc
    simp only [netSwaps, List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact hp
    · exact ih hps _ c hc

private theorem dupScan_snd_of_lt {b : Nat} (isRep : Nat → Bool) (repVal : Nat → Fin b → Bool) :
    ∀ m idx, idx < m → (dupScan isRep repVal m).2 idx = (dupScan isRep repVal (idx + 1)).1 := by
  intro m
  induction m with
  | zero => intro idx h; omega
  | succ m ih =>
    intro idx hidx
    dsimp only [dupScan]
    by_cases heq : idx = m
    · subst heq; simp
    · simp only [heq, ↓reduceIte]
      exact ih idx (by omega)

private theorem dupScan_fst_eq_rep {b : Nat} (isRep : Nat → Bool) (repVal : Nat → Fin b → Bool)
    (r : Nat) (hr : isRep r = true) :
    ∀ idx, r ≤ idx → (∀ t, r < t → t ≤ idx → isRep t = false) →
      (dupScan isRep repVal (idx + 1)).1 = repVal r := by
  intro idx
  induction idx with
  | zero =>
    intro hle _
    have hr0 : r = 0 := by omega
    subst hr0
    funext j
    simp [dupScan, hr]
  | succ idx ih =>
    intro hle hno
    by_cases heq : r = idx + 1
    · subst heq
      funext j
      simp [dupScan, hr]
    · have hlt : r < idx + 1 := by omega
      have hfalse : isRep (idx + 1) = false := hno (idx + 1) hlt le_rfl
      have hprev := ih (by omega) (fun t ht1 ht2 => hno t ht1 (by omega))
      funext j
      change (if isRep (idx + 1) then repVal (idx + 1) j else (dupScan isRep repVal (idx + 1)).1 j) = repVal r j
      rw [hfalse, hprev]; rfl

private theorem recKey2_childRec1_valid {n w K : Nat} (hn : 0 < n) (h : Nat) (st : LayerState w K)
    (x : Fin (n * 2 ^ (w + 1)) → Bool) (idx : Nat) :
    (childRec1 hn h st x idx).keyBit (2 * w) = false ↔
      ∃ hidx : idx < 2 * K,
        (st ⟨idx / 2, (Nat.div_lt_iff_lt_mul (by omega)).mpr (by omega)⟩).1 = true ∧
        childLookup hn h st x ⟨idx, hidx⟩ = true := by
  dsimp only [childRec1]
  by_cases hidx : idx < 2 * K
  · conv_lhs => simp only [hidx, ↓reduceDIte, show ¬(2 * w < w) by omega,
      show ¬(2 * w < 2 * w) by omega, Bool.not_eq_false', Bool.and_eq_true]
    exact ⟨fun hv => ⟨hidx, hv⟩, fun ⟨_, hv⟩ => hv⟩
  · conv_lhs => simp only [hidx, ↓reduceDIte, show ¬(2 * w < 2 * w) by omega, ↓reduceIte]
    constructor
    · intro h0; cases h0
    · rintro ⟨hlt, _⟩; exact absurd hlt hidx

private theorem recKey2_lt_iff_bits {kb vb : Nat} (r1 r2 : Rec2 kb vb) :
    recKey2 r1 = recKey2 r2 ↔ ∀ j < kb, r1.keyBit j = r2.keyBit j :=
  bitsVal_eq_iff r1.keyBit r2.keyBit kb

private theorem recKey2_childRec2 {n w K : Nat} (hn : 0 < n) (h : Nat) (st : LayerState w K)
    (x : Fin (n * 2 ^ (w + 1)) → Bool) (idx : Nat) :
    recKey2 (childRec2 hn h st x idx) = if isRepFn hn h st x idx then 0 else 1 := by
  dsimp only [recKey2, childRec2, bitsVal]
  cases isRepFn hn h st x idx <;> rfl

private structure LayerInv {n w K : Nat} (hn : 0 < n)
    (table : Fin n → (Fin (w + 1) → Bool) → Bool) (h : Nat) : Prop where
  sound : ∀ i : Fin K, (fwdLayer (K := K) hn h (tableInputVec hn table) i).1 = true →
    ((fwdLayer (K := K) hn h (tableInputVec hn table) i).2.1,
     (fwdLayer (K := K) hn h (tableInputVec hn table) i).2.2) ∈ reachedOf hn w table h
  complete : ∀ pr ∈ reachedOf hn w table h,
    ∃ i : Fin K, (fwdLayer (K := K) hn h (tableInputVec hn table) i).1 = true ∧
      ((fwdLayer (K := K) hn h (tableInputVec hn table) i).2.1,
       (fwdLayer (K := K) hn h (tableInputVec hn table) i).2.2) = pr
  unique : ∀ i j : Fin K,
    (fwdLayer (K := K) hn h (tableInputVec hn table) i).1 = true →
    (fwdLayer (K := K) hn h (tableInputVec hn table) j).1 = true →
    ((fwdLayer (K := K) hn h (tableInputVec hn table) i).2.1,
     (fwdLayer (K := K) hn h (tableInputVec hn table) i).2.2) =
    ((fwdLayer (K := K) hn h (tableInputVec hn table) j).2.1,
     (fwdLayer (K := K) hn h (tableInputVec hn table) j).2.2) → i = j

private theorem fwdLayer_inv_zero {n w K : Nat} (hn : 0 < n) (hwn : w ≤ n) (hKlo : 2 ^ w ≤ K)
    (table : Fin n → (Fin (w + 1) → Bool) → Bool) :
    LayerInv (K := K) hn table 0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    dsimp only [fwdLayer, fwdInit] at hi ⊢
    by_cases hlt : i.val < 2 ^ w
    · simp only [hlt, ↓reduceIte]
      exact (reachedOf_zero hn hwn table _).mpr rfl
    · simp only [hlt, ↓reduceIte] at hi; cases hi
  · intro pr hpr
    rw [reachedOf_zero hn hwn table] at hpr
    rcases pr with ⟨a, z⟩
    dsimp only at hpr
    subst hpr
    let v := bitsVal (fun r => if hr : r < w then a ⟨r, hr⟩ else false) w
    have hv : v < 2 ^ w := bitsVal_lt _ w
    refine ⟨⟨v, hv.trans_le hKlo⟩, ?_, ?_⟩
    · simp [fwdLayer, fwdInit, hv]
    · simp only [fwdLayer, fwdInit, hv, ↓reduceIte]
      apply Prod.ext <;> (funext r; dsimp only [v]; rw [bitsVal_testBit _ w r.val r.isLt]; simp [r.isLt])
  · intro i j hi hj heq
    dsimp only [fwdLayer, fwdInit] at hi hj heq
    by_cases h1 : i.val < 2 ^ w <;> by_cases h2 : j.val < 2 ^ w
    · simp only [h1, h2, ↓reduceIte] at heq
      have hfst := congrArg Prod.fst heq
      apply Fin.ext
      rw [← bitsVal_testBit_self i.val w h1, ← bitsVal_testBit_self j.val w h2]
      exact (bitsVal_eq_iff _ _ w).mpr fun r hr => congrFun hfst ⟨r, hr⟩
    · simp only [h2, ↓reduceIte] at hj; cases hj
    · simp only [h1, ↓reduceIte] at hi; cases hi
    · simp only [h1, ↓reduceIte] at hi; cases hi

private theorem fwdStep_inv_and_route {n w K : Nat} (hn : 0 < n) (hKlo : 2 ^ w ≤ K) (hKhi : K ≤ 4 ^ w)
    (table : Fin n → (Fin (w + 1) → Bool) → Bool) {h : Nat} (hh : h < n - w)
    (hInv : LayerInv (K := K) hn table h)
    (hCard : (reachedOf hn w table (h + 1)).card ≤ K) :
    LayerInv (K := K) hn table (h + 1) ∧
    ∀ (clNext : Fin K → Fin (2 * w) → Bool) (i : Fin K) (b : Bool),
      (fwdLayer (K := K) hn h (tableInputVec hn table) i).1 = true →
      childLookup hn h (fwdLayer (K := K) hn h (tableInputVec hn table)) (tableInputVec hn table)
        ⟨2 * i.val + b.toNat, by have := i.isLt; cases b <;> (dsimp; omega)⟩ = true →
      ∃ j : Fin K,
        (fwdLayer (K := K) hn (h + 1) (tableInputVec hn table) j).1 = true ∧
        (fwdLayer (K := K) hn (h + 1) (tableInputVec hn table) j).2.1 =
          (fwdLayer (K := K) hn h (tableInputVec hn table) i).2.1 ∧
        (fwdLayer (K := K) hn (h + 1) (tableInputVec hn table) j).2.2 =
          nextZ (fwdLayer (K := K) hn h (tableInputVec hn table) i).2.2 b ∧
        childClauseMask hn h clNext (tableInputVec hn table) (2 * i.val + b.toNat) = clNext j := by
  let x := tableInputVec hn table
  let st : LayerState w K := fwdLayer (K := K) hn h x
  let N := 2 ^ sortPow K
  rcases sortPow_bounds hKlo hKhi with ⟨hNlo, hNhi, _⟩
  rcases sortNet_bounds hKlo hKhi with ⟨hnet_mem, _⟩
  let sw1 := swaps1 hn h st x
  let sw2 := swaps2 hn h st x
  let σ1 := replaySwaps sw1 id
  let σ1i := replaySwaps sw1.reverse id
  let σ2 := replaySwaps sw2 id
  let σ2i := replaySwaps sw2.reverse id
  have hsw1_b := netSwaps_mem_bounds recKey2 (sortNet K) hnet_mem (childRec1 hn h st x)
  have hsw2_b := netSwaps_mem_bounds recKey2 (sortNet K) hnet_mem (childRec2 hn h st x)
  have hσ1_lt : ∀ t < N, σ1 t < N := replaySwaps_id_lt sw1 hsw1_b
  have hσ1i_lt : ∀ t < N, σ1i t < N := replaySwaps_id_lt sw1.reverse
    (fun c hc => hsw1_b c (List.mem_reverse.mp hc))
  have hσ2_lt : ∀ t < N, σ2 t < N := replaySwaps_id_lt sw2 hsw2_b
  have hσ2i_lt : ∀ t < N, σ2i t < N := replaySwaps_id_lt sw2.reverse
    (fun c hc => hsw2_b c (List.mem_reverse.mp hc))
  have hs1_eq : ∀ t, sorted1 hn h st x t = childRec1 hn h st x (σ1 t) := fun t => by
    dsimp only [sorted1, σ1, sw1, swaps1]
    rw [runNet_eq_replay, replaySwaps_eq_comp_id]; rfl
  have hs2_eq : ∀ t, sorted2 hn h st x t = childRec2 hn h st x (σ2 t) := fun t => by
    dsimp only [sorted2, σ2, sw2, swaps2]
    rw [runNet_eq_replay, replaySwaps_eq_comp_id]; rfl
  have hs1_mono : ∀ t1 t2, t1 ≤ t2 → t2 < N →
      recKey2 (sorted1 hn h st x t1) ≤ recKey2 (sorted1 hn h st x t2) :=
    bitonicSort_sorted recKey2 (sortPow K) (childRec1 hn h st x)
  have hs2_mono : ∀ t1 t2, t1 ≤ t2 → t2 < N →
      recKey2 (sorted2 hn h st x t1) ≤ recKey2 (sorted2 hn h st x t2) :=
    bitonicSort_sorted recKey2 (sortPow K) (childRec2 hn h st x)
  let pairOf : Rec2 (2 * w + 1) 0 → (Fin w → Bool) × (Fin w → Bool) := fun r =>
    (fun j => r.keyBit j.val, fun j => r.keyBit (w + j.val))
  have hchild_pair : ∀ idx (hidx : idx < 2 * K),
      pairOf (childRec1 hn h st x idx) =
        ((st ⟨idx / 2, (Nat.div_lt_iff_lt_mul (by omega)).mpr (by omega)⟩).2.1,
         nextZ (st ⟨idx / 2, (Nat.div_lt_iff_lt_mul (by omega)).mpr (by omega)⟩).2.2 (decide (idx % 2 = 1))) := by
    intro idx hidx
    apply Prod.ext
    · funext j; simp [pairOf, childRec1, hidx, j.isLt]
    · funext j
      have hj1 : ¬(w + j.val < w) := by omega
      have hj2 : w + j.val < 2 * w := by have := j.isLt; omega
      have hsub : w + j.val - w = j.val := by omega
      simp [pairOf, childRec1, hidx, hj1, hj2, hsub]
  have hvalid_mem : ∀ r, r.keyBit (2 * w) = false →
      (∃ idx < N, r = childRec1 hn h st x idx) → pairOf r ∈ reachedOf hn w table (h + 1) := by
    rintro r hrv ⟨idx, _, rfl⟩
    rcases (recKey2_childRec1_valid hn h st x idx).mp hrv with ⟨hidx, hstV, hclV⟩
    rw [hchild_pair idx hidx]
    let par : Fin K := ⟨idx / 2, (Nat.div_lt_iff_lt_mul (by omega)).mpr (by omega)⟩
    have hpar_mem := hInv.sound par hstV
    have htab : table (posFn n hn h) (extPat (st par).2.2 (decide (idx % 2 = 1))) = true := by
      dsimp only [childLookup] at hclV
      rw [tabEval_tableInputVec] at hclV
      exact hclV
    exact (reachedOf_succ hn table hh _ _).mpr ⟨(st par).2.2, decide (idx % 2 = 1), hpar_mem, htab, rfl⟩
  have hrep_sound : ∀ t < N, isRepFn hn h st x t = true →
      (sorted1 hn h st x t).keyBit (2 * w) = false ∧
      pairOf (sorted1 hn h st x t) ∈ reachedOf hn w table (h + 1) := by
    intro t ht hrep
    have hv : (sorted1 hn h st x t).keyBit (2 * w) = false := by
      dsimp only [isRepFn] at hrep
      by_cases ht0 : t = 0
      · subst ht0; simp at hrep; exact hrep
      · simp [ht0] at hrep; exact hrep.1
    exact ⟨hv, hvalid_mem _ hv ⟨σ1 t, hσ1_lt t ht, hs1_eq t⟩⟩
  have hrep_inj : ∀ t1 < N, ∀ t2 < N, isRepFn hn h st x t1 = true → isRepFn hn h st x t2 = true →
      pairOf (sorted1 hn h st x t1) = pairOf (sorted1 hn h st x t2) → t1 = t2 := by
    intro t1 ht1 t2 ht2 hr1 hr2 hpeq
    have hv1 := (hrep_sound t1 ht1 hr1).1
    have hv2 := (hrep_sound t2 ht2 hr2).1
    have hkeq : recKey2 (sorted1 hn h st x t1) = recKey2 (sorted1 hn h st x t2) := by
      rw [recKey2_lt_iff_bits]
      intro j hj
      by_cases h1 : j < w
      · exact congrFun (congrArg Prod.fst hpeq) ⟨j, h1⟩
      · by_cases h2 : j < 2 * w
        · have := congrFun (congrArg Prod.snd hpeq) ⟨j - w, by omega⟩
          simpa [pairOf, Nat.add_sub_cancel' (show w ≤ j by omega)] using this
        · have hjw : j = 2 * w := by omega
          rw [hjw, hv1, hv2]
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have ht2pos : t2 ≠ 0 := by omega
      dsimp only [isRepFn] at hr2
      simp only [ht2pos, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at hr2
      have hle := hs1_mono t1 (t2 - 1) (by omega) (by omega)
      omega
    · have ht1pos : t1 ≠ 0 := by omega
      dsimp only [isRepFn] at hr1
      simp only [ht1pos, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at hr1
      have hle := hs1_mono t2 (t1 - 1) (by omega) (by omega)
      omega
  let reps : Finset Nat := (Finset.range N).filter (fun t => isRepFn hn h st x t = true)
  have hreps_card : reps.card ≤ K := by
    have hle1 : reps.card ≤ (reachedOf hn w table (h + 1)).card := by
      refine Finset.card_le_card_of_injOn (fun t => pairOf (sorted1 hn h st x t)) ?_ ?_
      · intro t ht
        simp only [reps, Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at ht
        exact (hrep_sound t ht.1 ht.2).2
      · intro t1 ht1 t2 ht2 heq
        simp only [reps, Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at ht1 ht2
        exact hrep_inj t1 ht1.1 t2 ht2.1 ht1.2 ht2.2 heq
    exact hle1.trans hCard
  have hpack_lt : ∀ t < N, isRepFn hn h st x t = true → σ2i t < K := by
    intro t ht hrep
    by_contra hge
    let j := σ2i t
    have hjN : j < N := hσ2i_lt t ht
    have hK_le : K ≤ j := by omega
    have hj_key : recKey2 (sorted2 hn h st x j) = 0 := by
      rw [hs2_eq j, recKey2_childRec2]
      have : σ2 j = t := replaySwaps_id_inv sw2 t
      rw [this, hrep]; rfl
    have hall_rep : ∀ u < j + 1, σ2 u ∈ reps := by
      intro u hu
      have hle := hs2_mono u j (by omega) hjN
      rw [hj_key] at hle
      have hu0 : recKey2 (sorted2 hn h st x u) = 0 := by omega
      rw [hs2_eq u, recKey2_childRec2] at hu0
      have hru : isRepFn hn h st x (σ2 u) = true := by
        cases h : isRepFn hn h st x (σ2 u) <;> simp [h] at hu0 ⊢
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (hσ2_lt u (by omega)), hru⟩
    have hcard_ge : j + 1 ≤ reps.card := by
      calc j + 1 = (Finset.range (j + 1)).card := (Finset.card_range _).symm
        _ ≤ reps.card := by
          refine Finset.card_le_card_of_injOn σ2 ?_ ?_
          · intro u hu; exact hall_rep u (Finset.mem_range.mp hu)
          · intro u1 _ u2 _ heq
            have h1 : σ2i (σ2 u1) = u1 := replaySwaps_id_inv_left sw2 u1
            have h2 : σ2i (σ2 u2) = u2 := replaySwaps_id_inv_left sw2 u2
            rw [heq] at h1; omega
    omega
  have hnext_at : ∀ j : Fin K,
      (fwdLayer (K := K) hn (h + 1) x j).1 = isRepFn hn h st x (σ2 j.val) ∧
      ((fwdLayer (K := K) hn (h + 1) x j).2.1, (fwdLayer (K := K) hn (h + 1) x j).2.2) =
        pairOf (sorted1 hn h st x (σ2 j.val)) := by
    intro j
    dsimp only [fwdLayer, fwdStep]
    rw [hs2_eq j.val]
    dsimp only [childRec2, pairOf]
    refine ⟨?_, Prod.ext ?_ ?_⟩
    · simp
    · funext r; simp [show r.val < 2 * w by have := r.isLt; omega]
    · funext r; simp [show w + r.val < 2 * w by have := r.isLt; omega]
  have hfind_rep : ∀ t < N, (sorted1 hn h st x t).keyBit (2 * w) = false →
      ∃ r ≤ t, isRepFn hn h st x r = true ∧
        recKey2 (sorted1 hn h st x r) = recKey2 (sorted1 hn h st x t) ∧
        (∀ u, r < u → u ≤ t → isRepFn hn h st x u = false) := by
    intro t ht hv
    let P : Nat → Prop := fun r => r ≤ t ∧ recKey2 (sorted1 hn h st x r) = recKey2 (sorted1 hn h st x t)
    have hex : ∃ r, P r := ⟨t, le_rfl, rfl⟩
    let r := Nat.find hex
    have hrP : P r := Nat.find_spec hex
    have hr_min : ∀ u < r, ¬P u := fun u hu => Nat.find_min hex hu
    have hr_key : recKey2 (sorted1 hn h st x r) = recKey2 (sorted1 hn h st x t) := hrP.2
    have hrv : (sorted1 hn h st x r).keyBit (2 * w) = false := by
      have hbits := (recKey2_lt_iff_bits _ _).mp hr_key (2 * w) (by omega)
      rw [hbits, hv]
    have hrep_r : isRepFn hn h st x r = true := by
      dsimp only [isRepFn]
      by_cases hr0 : r = 0
      · simp only [hr0, ↓reduceIte, Bool.not_eq_true']
        simpa [hr0] using hrv
      · simp only [hr0, ↓reduceIte, hrv, Bool.not_false, Bool.true_and, decide_eq_true_eq]
        have hle := hs1_mono (r - 1) r (by omega) (by omega)
        have hne : recKey2 (sorted1 hn h st x (r - 1)) ≠ recKey2 (sorted1 hn h st x r) := by
          intro heq
          exact hr_min (r - 1) (by omega) ⟨by omega, heq.trans hr_key⟩
        omega
    refine ⟨r, hrP.1, hrep_r, hr_key, ?_⟩
    intro u hu1 hu2
    have hu_eq : recKey2 (sorted1 hn h st x u) = recKey2 (sorted1 hn h st x t) := by
      have h1 := hs1_mono r u (by omega) (by omega)
      have h2 := hs1_mono u t hu2 ht
      omega
    have hu1_eq : recKey2 (sorted1 hn h st x (u - 1)) = recKey2 (sorted1 hn h st x t) := by
      have h1 := hs1_mono r (u - 1) (by omega) (by omega)
      have h2 := hs1_mono (u - 1) t (by omega) ht
      omega
    dsimp only [isRepFn]
    simp [show u ≠ 0 by omega, hu_eq, hu1_eq]
  constructor
  · refine ⟨?_, ?_, ?_⟩
    · intro j hj
      rcases hnext_at j with ⟨hv, hp⟩
      rw [hv] at hj
      rw [hp]
      exact (hrep_sound (σ2 j.val) (hσ2_lt j.val (by omega)) hj).2
    · intro pr hpr
      rcases pr with ⟨a, z'⟩
      rcases (reachedOf_succ hn table hh a z').mp hpr with ⟨z, b, hpar_mem, htab, rfl⟩
      rcases hInv.complete (a, z) hpar_mem with ⟨i, hiV, hiPair⟩
      have hia : (st i).2.1 = a := congrArg Prod.fst hiPair
      have hiz : (st i).2.2 = z := congrArg Prod.snd hiPair
      let cIdx : Nat := 2 * i.val + b.toNat
      have hcIdx : cIdx < 2 * K := by dsimp [cIdx]; have := i.isLt; cases b <;> (dsimp; omega)
      have hcDiv : cIdx / 2 = i.val := by dsimp [cIdx]; cases b <;> (dsimp; omega)
      have hcMod : decide (cIdx % 2 = 1) = b := by
        dsimp [cIdx]; cases b
        · exact decide_eq_false (by dsimp; omega)
        · exact decide_eq_true (by dsimp; omega)
      have hcLookup : childLookup hn h st x ⟨cIdx, hcIdx⟩ = true := by
        dsimp only [childLookup]
        rw [tabEval_tableInputVec]
        have hparEq : (⟨cIdx / 2, (Nat.div_lt_iff_lt_mul (by omega)).mpr (by have := hcIdx; omega)⟩ : Fin K) = i :=
          Fin.ext hcDiv
        rw [hparEq, hiz, hcMod]
        exact htab
      let t := σ1i cIdx
      have htN : t < N := hσ1i_lt cIdx (by omega)
      have hs1t : sorted1 hn h st x t = childRec1 hn h st x cIdx := by
        rw [hs1_eq t, show σ1 t = cIdx from replaySwaps_id_inv sw1 cIdx]
      have htv : (sorted1 hn h st x t).keyBit (2 * w) = false := by
        rw [hs1t]
        exact (recKey2_childRec1_valid hn h st x cIdx).mpr ⟨hcIdx, by
          have hparEq : (⟨cIdx / 2, (Nat.div_lt_iff_lt_mul (by omega)).mpr (by have := hcIdx; omega)⟩ : Fin K) = i :=
            Fin.ext hcDiv
          rw [hparEq]; exact hiV, hcLookup⟩
      rcases hfind_rep t htN htv with ⟨r, hrle, hrep_r, hkeq, _⟩
      have hjK : σ2i r < K := hpack_lt r (by omega) hrep_r
      let j : Fin K := ⟨σ2i r, hjK⟩
      have hσ2j : σ2 j.val = r := replaySwaps_id_inv sw2 r
      refine ⟨j, ?_, ?_⟩
      · rw [(hnext_at j).1, hσ2j]; exact hrep_r
      · rw [(hnext_at j).2, hσ2j]
        have hp_eq : pairOf (sorted1 hn h st x r) = pairOf (sorted1 hn h st x t) := by
          have hb := (recKey2_lt_iff_bits _ _).mp hkeq
          apply Prod.ext
          · funext m; exact hb m.val (by omega)
          · funext m; exact hb (w + m.val) (by omega)
        rw [hp_eq, hs1t, hchild_pair cIdx hcIdx]
        have hparEq : (⟨cIdx / 2, (Nat.div_lt_iff_lt_mul (by omega)).mpr (by have := hcIdx; omega)⟩ : Fin K) = i :=
          Fin.ext hcDiv
        rw [hparEq, hia, hiz, hcMod]
    · intro j1 j2 hj1 hj2 hpeq
      rcases hnext_at j1 with ⟨hv1, hp1⟩
      rcases hnext_at j2 with ⟨hv2, hp2⟩
      rw [hv1] at hj1; rw [hv2] at hj2; rw [hp1, hp2] at hpeq
      have hσeq := hrep_inj (σ2 j1.val) (hσ2_lt j1.val (by omega))
        (σ2 j2.val) (hσ2_lt j2.val (by omega)) hj1 hj2 hpeq
      have h1 : σ2i (σ2 j1.val) = j1.val := replaySwaps_id_inv_left sw2 j1.val
      have h2 : σ2i (σ2 j2.val) = j2.val := replaySwaps_id_inv_left sw2 j2.val
      rw [hσeq] at h1
      exact Fin.ext (by omega)
  · intro clNext i b hiV hcLookup
    let cIdx : Fin (2 * K) := ⟨2 * i.val + b.toNat, by have := i.isLt; cases b <;> (dsimp; omega)⟩
    have hcDiv : cIdx.val / 2 = i.val := by dsimp [cIdx]; cases b <;> (dsimp; omega)
    have hcMod : decide (cIdx.val % 2 = 1) = b := by
      dsimp [cIdx]; cases b
      · exact decide_eq_false (by dsimp; omega)
      · exact decide_eq_true (by dsimp; omega)
    let t := σ1i cIdx.val
    have htN : t < N := hσ1i_lt cIdx.val (by omega)
    have hs1t : sorted1 hn h st x t = childRec1 hn h st x cIdx.val := by
      rw [hs1_eq t, show σ1 t = cIdx.val from replaySwaps_id_inv sw1 cIdx.val]
    have htv : (sorted1 hn h st x t).keyBit (2 * w) = false := by
      rw [hs1t]
      exact (recKey2_childRec1_valid hn h st x cIdx.val).mpr ⟨cIdx.isLt, by
        have hparEq : (⟨cIdx.val / 2, (Nat.div_lt_iff_lt_mul (by omega)).mpr (by have := cIdx.isLt; omega)⟩ : Fin K) = i :=
          Fin.ext hcDiv
        rw [hparEq]; exact hiV, hcLookup⟩
    rcases hfind_rep t htN htv with ⟨r, hrle, hrep_r, hkeq, hno⟩
    have hjK : σ2i r < K := hpack_lt r (by omega) hrep_r
    let j : Fin K := ⟨σ2i r, hjK⟩
    have hσ2j : σ2 j.val = r := replaySwaps_id_inv sw2 r
    have hp_eq : pairOf (sorted1 hn h st x r) = pairOf (sorted1 hn h st x t) := by
      have hb := (recKey2_lt_iff_bits _ _).mp hkeq
      apply Prod.ext
      · funext m; exact hb m.val (by omega)
      · funext m; exact hb (w + m.val) (by omega)
    have hpar_child : pairOf (sorted1 hn h st x r) = ((st i).2.1, nextZ (st i).2.2 b) := by
      rw [hp_eq, hs1t, hchild_pair cIdx.val cIdx.isLt]
      have hparEq : (⟨cIdx.val / 2, (Nat.div_lt_iff_lt_mul (by omega)).mpr (by have := cIdx.isLt; omega)⟩ : Fin K) = i :=
        Fin.ext hcDiv
      rw [hparEq, hcMod]
    have hpj : ((fwdLayer (K := K) hn (h + 1) x j).2.1, (fwdLayer (K := K) hn (h + 1) x j).2.2) =
        ((st i).2.1, nextZ (st i).2.2 b) := (hnext_at j).2.trans (by rw [hσ2j]; exact hpar_child)
    refine ⟨j, ?_, (Prod.mk.inj hpj).1, (Prod.mk.inj hpj).2, ?_⟩
    · rw [(hnext_at j).1, hσ2j]; exact hrep_r
    · dsimp only [childClauseMask]
      rw [replaySwaps_eq_comp_id (swaps1 hn h st x).reverse]
      change (dupScan (isRepFn hn h st x)
        (replaySwaps (swaps2 hn h st x).reverse (fun idx => if hidx : idx < K then clNext ⟨idx, hidx⟩ else fun _ => false)) N).2 t = clNext j
      rw [dupScan_snd_of_lt _ _ N t htN, dupScan_fst_eq_rep _ _ r hrep_r t hrle hno]
      rw [replaySwaps_eq_comp_id (swaps2 hn h st x).reverse]
      change (if hidx : σ2i r < K then clNext ⟨σ2i r, hidx⟩ else fun _ => false) = clNext j
      simp [hjK, j]

private theorem fwdLayer_inv {n w K : Nat} (hn : 0 < n) (hwn : w ≤ n)
    (hKlo : 2 ^ w ≤ K) (hKhi : K ≤ 4 ^ w)
    (table : Fin n → (Fin (w + 1) → Bool) → Bool)
    (hReached : ∀ h ≤ n - w, (reachedOf hn w table h).card ≤ K) :
    ∀ h ≤ n - w, LayerInv (K := K) hn table h := by
  intro h
  induction h with
  | zero => intro _; exact fwdLayer_inv_zero hn hwn hKlo table
  | succ h ih =>
    intro hh
    exact (fwdStep_inv_and_route hn hKlo hKhi table (by omega) (ih (by omega)) (hReached (h + 1) hh)).1

private theorem evalOut_iff_unsat {n w K : Nat} (hn : 0 < n) (hwn : w ≤ n)
    (hKlo : 2 ^ w ≤ K) (hKhi : K ≤ 4 ^ w)
    (table : Fin n → (Fin (w + 1) → Bool) → Bool)
    (hReached : ∀ h ≤ n - w, (reachedOf hn w table h).card ≤ K) :
    evalOutFn (K := K) hn (tableInputVec hn table) = true ↔ ¬ Satisfiable (formulaOf hn w table) := by
  let x := tableInputVec hn table
  have hInv := fwdLayer_inv hn hwn hKlo hKhi table hReached (n - w) le_rfl
  have hex_surv : (∃ i : Fin K, survivesFn hn x i = true) ↔ Satisfiable (formulaOf hn w table) := by
    constructor
    · rintro ⟨i, hsi⟩
      dsimp only [survivesFn] at hsi
      rw [Bool.and_eq_true, allNat_eq_true] at hsi
      rcases hsi with ⟨hiV, hall⟩
      have hmem := hInv.sound i hiV
      simp only [reachedOf, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
      rcases hmem with ⟨word, hpass, hpr⟩
      have ha : (fun r : Fin w => word (posFn n hn r.val)) = (fwdLayer hn (n - w) x i).2.1 :=
        congrArg Prod.fst hpr
      have hz : (fun r : Fin w => word (posFn n hn (n - w + r.val))) = (fwdLayer hn (n - w) x i).2.2 :=
        congrArg Prod.snd hpr
      refine ⟨word, (satisfies_iff_table hn table word).mpr fun row => ?_⟩
      by_cases hr : row.val < n - w
      · have hp := hpass ⟨row.val, hr⟩
        simpa [posFn_of_lt hn row.isLt] using hp
      · let off : Nat := row.val - (n - w)
        have hoff : off < w := by have := row.isLt; omega
        have hok := hall off hoff
        simp only [hoff, ↓reduceDIte, wrapLookup] at hok
        rw [tabEval_tableInputVec] at hok
        have hrow_eq : posFn n hn (n - w + off) = row := by
          rw [show n - w + off = row.val by omega, posFn_of_lt hn row.isLt]
        have hpat_eq : wrapPat (fwdLayer hn (n - w) x i).2.1 (fwdLayer hn (n - w) x i).2.2 ⟨off, hoff⟩ =
            fun k => word (posFn n hn (row.val + k.val)) := by
          funext k
          dsimp only [wrapPat]
          split_ifs with hk
          · rw [← hz]; dsimp only; congr 1; congr 1; dsimp [off]; omega
          · rw [← ha]; dsimp only
            congr 1
            apply Fin.ext
            dsimp only [posFn, off]
            have hsum : row.val + k.val = n + (row.val - (n - w) + k.val - w) := by omega
            rw [hsum, Nat.add_mod_left]
        rw [hrow_eq, hpat_eq] at hok
        exact hok
    · rintro ⟨word, hsat⟩
      have htab := (satisfies_iff_table hn table word).mp hsat
      have hmem : ((fun r : Fin w => word (posFn n hn r.val)),
                   (fun r : Fin w => word (posFn n hn (n - w + r.val)))) ∈ reachedOf hn w table (n - w) := by
        simp only [reachedOf, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨word, fun t => ?_, rfl⟩
        have ht := htab (posFn n hn t.val)
        have htv : (posFn n hn t.val).val = t.val := by
          dsimp [posFn]; exact Nat.mod_eq_of_lt (by have := t.isLt; omega)
        simpa [htv] using ht
      rcases hInv.complete _ hmem with ⟨i, hiV, hpr⟩
      have ha : (fwdLayer hn (n - w) x i).2.1 = fun r : Fin w => word (posFn n hn r.val) :=
        congrArg Prod.fst hpr
      have hz : (fwdLayer hn (n - w) x i).2.2 = fun r : Fin w => word (posFn n hn (n - w + r.val)) :=
        congrArg Prod.snd hpr
      refine ⟨i, ?_⟩
      dsimp only [survivesFn]
      rw [Bool.and_eq_true, allNat_eq_true]
      refine ⟨hiV, fun off hoff => ?_⟩
      simp only [hoff, ↓reduceDIte, wrapLookup]
      rw [tabEval_tableInputVec]
      let row : Fin n := ⟨n - w + off, by omega⟩
      have hrow_eq : posFn n hn (n - w + off) = row := posFn_of_lt hn (by omega)
      have hpat_eq : wrapPat (fwdLayer hn (n - w) x i).2.1 (fwdLayer hn (n - w) x i).2.2 ⟨off, hoff⟩ =
          fun k => word (posFn n hn (row.val + k.val)) := by
        funext k
        dsimp only [wrapPat]
        split_ifs with hk
        · rw [hz]; dsimp only; congr 1; congr 1; dsimp [row]; omega
        · rw [ha]; dsimp only
          congr 1
          apply Fin.ext
          dsimp only [posFn, row]
          have hsum : n - w + off + k.val = n + (off + k.val - w) := by omega
          rw [hsum, Nat.add_mod_left]
      rw [hrow_eq, hpat_eq]
      exact htab row
  have hAny : anyNat (fun idx x' => if h : idx < K then survivesFn hn x' ⟨idx, h⟩ else false) K x = true ↔
      ∃ i : Fin K, survivesFn hn x i = true := by
    rw [anyNat_eq_true]
    constructor
    · rintro ⟨idx, hidx, h⟩; simp only [hidx, ↓reduceDIte] at h; exact ⟨⟨idx, hidx⟩, h⟩
    · rintro ⟨i, hi⟩; exact ⟨i.val, i.isLt, by simp [i.isLt, hi]⟩
  change !(anyNat (fun idx x' => if h : idx < K then survivesFn hn x' ⟨idx, h⟩ else false) K x) = true ↔
    ¬ Satisfiable (formulaOf hn w table)
  rw [Bool.not_eq_true', Bool.eq_false_iff]
  exact (not_congr hAny).trans (not_congr hex_surv)

private def clauseOf {n w : Nat} (h : Nat) (a z : Fin w → Bool) (mask : Fin (2 * w) → Bool) :
    Clause (Fin n) :=
  Finset.univ.filter (fun lit : Literal (Fin n) => clauseMemBit h a z mask lit = true)

private def axiomOf {n w : Nat} (h : Nat) (z : Fin w → Bool) (b : Bool) : Clause (Fin n) :=
  Finset.univ.filter (fun lit : Literal (Fin n) => axiomMemBit h z b lit = true)

private def seedClause {n : Nat} (d_lev : Nat) (idx : Fin (2 ^ d_lev)) (mask : Fin d_lev → Bool) :
    Clause (Fin n) :=
  Finset.univ.filter (fun lit : Literal (Fin n) =>
    (if hv : lit.1.val < d_lev then
      if !(idx.val.testBit lit.1.val) == lit.2 then mask ⟨lit.1.val, hv⟩ else false
    else false) = true)

private theorem clauseOf_or {n w : Nat} (h : Nat) (a z : Fin w → Bool)
    (m0 m1 : Fin (2 * w) → Bool) :
    clauseOf (n := n) h a z (fun j => m0 j || m1 j) = clauseOf h a z m0 ∪ clauseOf h a z m1 := by
  ext lit
  simp only [clauseOf, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, clauseMemBit]
  by_cases h1 : lit.1.val < w <;> by_cases h2 : h ≤ lit.1.val ∧ lit.1.val < h + w <;>
    simp [h1, h2] <;> tauto

private theorem clauseOf_card_le {n w : Nat} (hn : 0 < n) (_hwn : w ≤ n)
    {h : Nat} (_hh : h ≤ n - w) (a z : Fin w → Bool) (mask : Fin (2 * w) → Bool) :
    (clauseOf (n := n) h a z mask).card ≤ 2 * w := by
  let SA : Finset (Literal (Fin n)) := Finset.univ.image (fun r : Fin w => (posFn n hn r.val, !(a r)))
  let SZ : Finset (Literal (Fin n)) := Finset.univ.image (fun r : Fin w => (posFn n hn (h + r.val), !(z r)))
  have hsub : clauseOf (n := n) h a z mask ⊆ SA ∪ SZ := by
    intro lit hlit
    simp only [clauseOf, Finset.mem_filter, Finset.mem_univ, true_and, clauseMemBit,
      Bool.or_eq_true] at hlit
    rcases hlit with hA | hZ
    · split_ifs at hA with hv
      · rw [Bool.and_eq_true] at hA
        apply Finset.mem_union_left
        refine Finset.mem_image.mpr ⟨⟨lit.1.val, hv⟩, Finset.mem_univ _, ?_⟩
        exact Prod.ext (posFn_of_lt hn lit.1.isLt) ((not_beq_eq_true _ _).mp hA.2)
    · split_ifs at hZ with hv
      · rw [Bool.and_eq_true] at hZ
        apply Finset.mem_union_right
        refine Finset.mem_image.mpr ⟨⟨lit.1.val - h, by omega⟩, Finset.mem_univ _, ?_⟩
        exact Prod.ext (by rw [show h + (lit.1.val - h) = lit.1.val by omega]; exact posFn_of_lt hn lit.1.isLt)
          ((not_beq_eq_true _ _).mp hZ.2)
  calc (clauseOf (n := n) h a z mask).card ≤ (SA ∪ SZ).card := Finset.card_le_card hsub
    _ ≤ SA.card + SZ.card := Finset.card_union_le SA SZ
    _ ≤ w + w := Nat.add_le_add
        ((Finset.card_image_le).trans (by simp)) ((Finset.card_image_le).trans (by simp))
    _ = 2 * w := by omega

private theorem axiomOf_eq_image {n w : Nat} (hn : 0 < n) {h : Nat} (hh : h < n - w)
    (z : Fin w → Bool) (b : Bool) :
    axiomOf (n := n) h z b =
      Finset.univ.image (fun k : Fin (w + 1) =>
        (posFn n hn ((posFn n hn h).val + k.val), !(extPat z b k))) := by
  have hh_val : (posFn n hn h).val = h := by dsimp [posFn]; exact Nat.mod_eq_of_lt (by omega)
  ext ⟨v, sg⟩
  simp only [axiomOf, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, hh_val]
  dsimp only [axiomMemBit]
  constructor
  · intro hm
    by_cases hv1 : h ≤ v.val ∧ v.val < h + w
    · simp only [hv1, and_self, ↓reduceDIte] at hm
      have hsg : (!(z ⟨v.val - h, by omega⟩)) = sg := (not_beq_eq_true _ _).mp hm
      refine ⟨⟨v.val - h, by omega⟩, ?_⟩
      apply Prod.ext
      · dsimp only; rw [show h + (v.val - h) = v.val by omega]; exact posFn_of_lt hn v.isLt
      · dsimp only [extPat]; simp only [show v.val - h < w by omega, ↓reduceDIte]; exact hsg
    · simp only [hv1, ↓reduceDIte] at hm
      by_cases hv2 : v.val = h + w
      · simp only [hv2, ↓reduceIte] at hm
        have hsg : (!b) = sg := (not_beq_eq_true _ _).mp hm
        refine ⟨⟨w, Nat.lt_succ_self w⟩, ?_⟩
        apply Prod.ext
        · dsimp only; rw [← hv2]; exact posFn_of_lt hn v.isLt
        · dsimp only [extPat]; simp only [Nat.lt_irrefl, ↓reduceDIte]; exact hsg
      · simp only [hv2, ↓reduceIte] at hm; cases hm
  · rintro ⟨k, hkeq⟩
    have hv_eq : posFn n hn (h + k.val) = v := congrArg Prod.fst hkeq
    have hsg_eq : (!(extPat z b k)) = sg := congrArg Prod.snd hkeq
    have hv_val : v.val = h + k.val := by
      rw [← hv_eq]; dsimp [posFn]; exact Nat.mod_eq_of_lt (by have := k.isLt; omega)
    by_cases hk : k.val < w
    · have hv1 : h ≤ v.val ∧ v.val < h + w := by omega
      simp only [hv1, and_self, ↓reduceDIte]
      apply (not_beq_eq_true _ _).mpr
      rw [← hsg_eq]
      dsimp only [extPat]
      simp only [hk, ↓reduceDIte]
      congr 2; exact Fin.ext (by dsimp only; omega)
    · have hkw : k.val = w := by have := k.isLt; omega
      have hv1 : ¬(h ≤ v.val ∧ v.val < h + w) := by omega
      have hv2 : v.val = h + w := by omega
      simp only [hv1, ↓reduceDIte]
      simp only [hv2, ↓reduceIte]
      apply (not_beq_eq_true _ _).mpr
      rw [← hsg_eq]
      dsimp only [extPat]
      simp only [hkw, Nat.lt_irrefl, ↓reduceDIte]

private theorem axiomOf_card_le {n w : Nat} (hn : 0 < n) {h : Nat} (hh : h < n - w)
    (z : Fin w → Bool) (b : Bool) :
    (axiomOf (n := n) h z b).card ≤ w + 1 := by
  rw [axiomOf_eq_image hn hh z b]
  exact (Finset.card_image_le).trans (by simp)

private theorem axiomOf_mem_formula {n w : Nat} (hn : 0 < n)
    (table : Fin n → (Fin (w + 1) → Bool) → Bool) {h : Nat} (hh : h < n - w)
    (z : Fin w → Bool) (b : Bool) (hfalse : table (posFn n hn h) (extPat z b) = false) :
    axiomOf (n := n) h z b ∈ formulaOf hn w table :=
  ⟨posFn n hn h, extPat z b, hfalse, axiomOf_eq_image hn hh z b⟩

private theorem seedClause_card_le {n : Nat} (d_lev : Nat) (idx : Fin (2 ^ d_lev))
    (mask : Fin d_lev → Bool) :
    (seedClause (n := n) d_lev idx mask).card ≤ d_lev := by
  have hle : (seedClause (n := n) d_lev idx mask).card ≤ (Finset.range d_lev).card := by
    refine Finset.card_le_card_of_injOn (fun lit : Literal (Fin n) => lit.1.val) ?_ ?_
    · intro lit hlit
      simp only [seedClause, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hlit
      by_cases hv : lit.1.val < d_lev
      · exact Finset.mem_coe.mpr (Finset.mem_range.mpr hv)
      · simp only [hv, ↓reduceDIte] at hlit; cases hlit
    · intro l1 hl1 l2 hl2 heq
      dsimp only at heq
      simp only [seedClause, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hl1 hl2
      apply Prod.ext
      · exact Fin.ext heq
      · by_cases hv1 : l1.1.val < d_lev
        · have hv2 : l2.1.val < d_lev := by rw [← heq]; exact hv1
          simp only [hv1, ↓reduceDIte] at hl1
          simp only [hv2, ↓reduceDIte] at hl2
          by_cases hs1 : (!(idx.val.testBit l1.1.val) == l1.2) = true
          · by_cases hs2 : (!(idx.val.testBit l2.1.val) == l2.2) = true
            · have e1 : (!(idx.val.testBit l1.1.val)) = l1.2 := (not_beq_eq_true _ _).mp hs1
              have e2 : (!(idx.val.testBit l2.1.val)) = l2.2 := (not_beq_eq_true _ _).mp hs2
              rw [← e1, ← e2, heq]
            · simp [hs2] at hl2
          · simp [hs1] at hl1
        · simp only [hv1, ↓reduceDIte] at hl1; cases hl1
  simpa using hle

private theorem termScan_spec {n w K : Nat} (hn : 0 < n) (x : Fin (n * 2 ^ (w + 1)) → Bool)
    (i : Fin K) :
    ∀ m (hm : m ≤ w),
      ((termScan hn i m x).1 = false → ∀ k (hk : k < m), wrapLookup hn x ⟨k, by omega⟩ i = true) ∧
      ((termScan hn i m x).1 = true →
        ∃ m0 : Nat, ∃ hm0 : m0 < m, wrapLookup hn x ⟨m0, by omega⟩ i = false ∧
          ∀ j : Fin (2 * w), (termScan hn i m x).2 j =
            if j.val < w then decide (j.val ≤ m0) else decide (m0 ≤ j.val - w)) := by
  intro m
  induction m with
  | zero =>
    intro _
    exact ⟨fun _ k hk => by omega, fun h => by simp [termScan] at h⟩
  | succ m ih =>
    intro hm
    rcases ih (by omega) with ⟨hF, hT⟩
    constructor
    · intro hfalse k hk
      dsimp only [termScan] at hfalse
      simp only [show m < w by omega, ↓reduceDIte, Bool.or_eq_false_iff, Bool.not_eq_false'] at hfalse
      by_cases hkm : k < m
      · exact hF hfalse.1 k hkm
      · have hkeq : k = m := by omega
        subst hkeq; exact hfalse.2
    · intro htrue
      dsimp only [termScan] at htrue
      simp only [show m < w by omega, ↓reduceDIte, Bool.or_eq_true, Bool.not_eq_true'] at htrue
      by_cases hprev : (termScan hn i m x).1 = true
      · rcases hT hprev with ⟨m0, hm0, hwl, hmask⟩
        refine ⟨m0, by omega, hwl, fun j => ?_⟩
        simp only [termScan, show m < w by omega, ↓reduceDIte, hprev, Bool.not_true, Bool.false_and,
          Bool.false_eq_true, ↓reduceIte]
        exact hmask j
      · have hpf : (termScan hn i m x).1 = false := Bool.eq_false_iff.mpr hprev
        have hwl : wrapLookup hn x ⟨m, hm⟩ i = false := by
          rcases htrue with h1 | h2
          · exact absurd h1 hprev
          · exact h2
        refine ⟨m, Nat.lt_succ_self m, hwl, fun j => ?_⟩
        simp only [termScan, show m < w by omega, ↓reduceDIte, hpf, hwl, Bool.not_false, Bool.and_self,
          ↓reduceIte]

private theorem termClause_mem_formula {n w : Nat} (hn : 0 < n) (hwn : w ≤ n)
    (table : Fin n → (Fin (w + 1) → Bool) → Bool)
    {a z : Fin w → Bool} (_hmem : (a, z) ∈ reachedOf hn w table (n - w))
    (m0 : Fin w) (hfalse : table (posFn n hn (n - w + m0.val)) (wrapPat a z m0) = false) :
    clauseOf (n := n) (n - w) a z
      (fun j => if j.val < w then decide (j.val ≤ m0.val) else decide (m0.val ≤ j.val - w)) ∈
      formulaOf hn w table := by
  let row : Fin n := posFn n hn (n - w + m0.val)
  have hrow : row.val = n - w + m0.val := by
    dsimp [row, posFn]; exact Nat.mod_eq_of_lt (by have := m0.isLt; omega)
  refine ⟨row, wrapPat a z m0, hfalse, ?_⟩
  ext ⟨v, sg⟩
  simp only [clauseOf, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, hrow]
  dsimp only [clauseMemBit]
  rw [Bool.or_eq_true]
  constructor
  · rintro (hA | hZ)
    · by_cases hv : v.val < w
      · simp only [hv, ↓reduceDIte, ↓reduceIte, Bool.and_eq_true] at hA
        have hvle : v.val ≤ m0.val := of_decide_eq_true hA.1
        have hsg : (!(a ⟨v.val, hv⟩)) = sg := (not_beq_eq_true _ _).mp hA.2
        let k : Fin (w + 1) := ⟨w - m0.val + v.val, by omega⟩
        refine ⟨k, ?_⟩
        apply Prod.ext
        · dsimp only
          apply Fin.ext
          dsimp only [posFn, k]
          have hsum : n - w + m0.val + (w - m0.val + v.val) = n + v.val := by have := m0.isLt; omega
          rw [hsum, Nat.add_mod_left, Nat.mod_eq_of_lt v.isLt]
        · dsimp only [wrapPat, k]
          have hge : ¬(m0.val + (w - m0.val + v.val) < w) := by omega
          simp only [hge, ↓reduceDIte]
          have hfin : (⟨m0.val + (w - m0.val + v.val) - w, by have := m0.isLt; omega⟩ : Fin w) = ⟨v.val, hv⟩ :=
            Fin.ext (by dsimp only; have := m0.isLt; omega)
          rw [hfin]; exact hsg
      · simp only [hv, ↓reduceDIte] at hA; cases hA
    · by_cases hv : n - w ≤ v.val ∧ v.val < n - w + w
      · have hnotlt : ¬(w + (v.val - (n - w)) < w) := by omega
        simp only [hv, and_self, ↓reduceDIte, hnotlt, ↓reduceIte, Bool.and_eq_true] at hZ
        have hm0le : m0.val ≤ v.val - (n - w) := by
          have h1 := of_decide_eq_true hZ.1
          omega
        have hsg : (!(z ⟨v.val - (n - w), by omega⟩)) = sg := (not_beq_eq_true _ _).mp hZ.2
        let k : Fin (w + 1) := ⟨v.val - (n - w) - m0.val, by omega⟩
        refine ⟨k, ?_⟩
        apply Prod.ext
        · dsimp only
          apply Fin.ext
          dsimp only [posFn, k]
          have hsum : n - w + m0.val + (v.val - (n - w) - m0.val) = v.val := by omega
          rw [hsum, Nat.mod_eq_of_lt v.isLt]
        · dsimp only [wrapPat, k]
          have hlt : m0.val + (v.val - (n - w) - m0.val) < w := by omega
          simp only [hlt, ↓reduceDIte]
          have hfin : (⟨m0.val + (v.val - (n - w) - m0.val), hlt⟩ : Fin w) = ⟨v.val - (n - w), by omega⟩ :=
            Fin.ext (by dsimp only; omega)
          rw [hfin]; exact hsg
      · simp only [hv, ↓reduceDIte] at hZ; cases hZ
  · rintro ⟨k, hkeq⟩
    have hv_eq : posFn n hn (n - w + m0.val + k.val) = v := congrArg Prod.fst hkeq
    have hsg_eq : (!(wrapPat a z m0 k)) = sg := congrArg Prod.snd hkeq
    dsimp only [wrapPat] at hsg_eq
    by_cases hk : m0.val + k.val < w
    · simp only [hk, ↓reduceDIte] at hsg_eq
      have hv_val : v.val = n - w + m0.val + k.val := by
        rw [← hv_eq]; dsimp [posFn]; exact Nat.mod_eq_of_lt (by omega)
      right
      have hvZ : n - w ≤ v.val ∧ v.val < n - w + w := by omega
      simp only [hvZ, and_self, ↓reduceDIte, show ¬(w + (v.val - (n - w)) < w) by omega, ↓reduceIte,
        Bool.and_eq_true]
      refine ⟨decide_eq_true (by omega), (not_beq_eq_true _ _).mpr ?_⟩
      rw [← hsg_eq]
      congr 2; exact Fin.ext (by dsimp only; omega)
    · simp only [hk, ↓reduceDIte] at hsg_eq
      have hv_val : v.val = m0.val + k.val - w := by
        rw [← hv_eq]
        dsimp [posFn]
        have hsum : n - w + m0.val + k.val = n + (m0.val + k.val - w) := by omega
        rw [hsum, Nat.add_mod_left, Nat.mod_eq_of_lt (by have := m0.isLt; have := k.isLt; omega)]
      left
      have hvA : v.val < w := by have := m0.isLt; have := k.isLt; omega
      simp only [hvA, ↓reduceDIte, ↓reduceIte, Bool.and_eq_true]
      refine ⟨decide_eq_true (by have := k.isLt; omega), (not_beq_eq_true _ _).mpr ?_⟩
      rw [← hsg_eq]
      congr 2; exact Fin.ext (by dsimp only; omega)

private theorem childMaskAt_spec {n w K : Nat} (hn : 0 < n)
    (table : Fin n → (Fin (w + 1) → Bool) → Bool) {h : Nat} (hh : h < n - w)
    (clNext : Fin K → Fin (2 * w) → Bool) (i : Fin K) (b : Bool) :
    let x := tableInputVec hn table
    let st := fwdLayer (K := K) hn h x
    let cIdx : Fin (2 * K) := ⟨2 * i.val + b.toNat, by have := i.isLt; cases b <;> (dsimp; omega)⟩
    let ok := childLookup hn h st x cIdx
    let cm := childClauseMask hn h clNext x cIdx.val
    let D : Clause (Fin n) := if ok then clauseOf (h + 1) (st i).2.1 (nextZ (st i).2.2 b) cm
      else axiomOf h (st i).2.2 b
    let res := childMaskAt hn h clNext x i b
    let piv : Fin n := ⟨h + w, by omega⟩
    (res.2 = false → clauseOf h (st i).2.1 (st i).2.2 res.1 = D) ∧
    (res.2 = true → (piv, !b) ∈ D ∧ D.erase (piv, !b) = clauseOf h (st i).2.1 (st i).2.2 res.1) := by
  intro x st cIdx ok cm D res piv
  have hmem_other : ∀ lit : Literal (Fin n), lit.1 ≠ piv →
      (lit ∈ clauseOf h (st i).2.1 (st i).2.2 res.1 ↔ lit ∈ D) := by
    intro ⟨v, sg⟩ hne
    have hvne : v.val ≠ h + w := fun heq => hne (Fin.ext heq)
    dsimp only [D, res, childMaskAt]
    cases hok : childLookup hn h st x cIdx
    · have hok' : ok = false := hok
      simp only [hok', Bool.false_eq_true, ↓reduceIte]
      simp only [clauseOf, axiomOf, Finset.mem_filter, Finset.mem_univ, true_and]
      dsimp only [clauseMemBit, axiomMemBit]
      by_cases h1 : v.val < w <;> by_cases h2 : h ≤ v.val ∧ v.val < h + w <;>
        simp [h1, h2, hvne, show ¬(w + (v.val - h) < w) by omega]
    · have hok' : ok = true := hok
      simp only [hok', ↓reduceIte]
      simp only [clauseOf, Finset.mem_filter, Finset.mem_univ, true_and]
      dsimp only [clauseMemBit]
      refine Iff.of_eq (congrArg (· = true) ?_)
      apply congrArg₂ (· || ·)
      · by_cases hv : v.val < w
        · simp only [hv, ↓reduceDIte, ↓reduceIte]; rfl
        · simp only [hv, ↓reduceDIte]
      · by_cases hv : h ≤ v.val ∧ v.val < h + w
        · by_cases hvh : v.val = h
          · simp only [hv, and_self, ↓reduceDIte]
            simp only [hvh, show ¬(h + 1 ≤ h ∧ h < h + 1 + w) by omega, ↓reduceDIte,
              Nat.sub_self, Nat.add_zero, Nat.lt_irrefl, ↓reduceIte, Bool.false_and]
          · have hv' : h + 1 ≤ v.val ∧ v.val < h + 1 + w := by omega
            simp only [hv, hv', and_self, ↓reduceDIte, show ¬(w + (v.val - h) < w) by omega,
              show w + (v.val - h) ≠ w by omega, ↓reduceIte, nextZ, show v.val - (h + 1) + 1 < w by omega]
            apply congrArg₂ (· && ·)
            · dsimp only [cm, cIdx]
              have hfin1 : (⟨w + (v.val - h) - 1, by omega⟩ : Fin (2 * w)) =
                  ⟨w + (v.val - (h + 1)), by omega⟩ := Fin.ext (by dsimp only; omega)
              rw [hfin1]
            · have hfin2 : (⟨v.val - h, by omega⟩ : Fin w) =
                  ⟨v.val - (h + 1) + 1, by omega⟩ := Fin.ext (by dsimp only; omega)
              rw [hfin2]
        · have hv' : ¬(h + 1 ≤ v.val ∧ v.val < h + 1 + w) := by omega
          simp only [hv, hv', ↓reduceDIte]
  have hnot_piv_res : ∀ sg : Bool, (piv, sg) ∉ clauseOf h (st i).2.1 (st i).2.2 res.1 := by
    intro sg
    simp only [clauseOf, Finset.mem_filter, Finset.mem_univ, true_and]
    dsimp only [clauseMemBit, piv]
    simp [show ¬(h + w < w) by omega]
  have hpiv_D : ∀ sg : Bool, ((piv, sg) ∈ D ↔ res.2 = true ∧ sg = !b) := by
    intro sg
    dsimp only [D, res, childMaskAt]
    cases hok : childLookup hn h st x cIdx
    · have hok' : ok = false := hok
      simp only [hok', Bool.false_eq_true, ↓reduceIte]
      simp only [axiomOf, Finset.mem_filter, Finset.mem_univ, true_and]
      dsimp only [axiomMemBit, piv]
      simp only [show ¬(h ≤ h + w ∧ h + w < h + w) by omega, ↓reduceDIte, ↓reduceIte]
      rw [not_beq_eq_true]
      exact ⟨Eq.symm, Eq.symm⟩
    · have hok' : ok = true := hok
      simp only [hok', ↓reduceIte]
      simp only [clauseOf, Finset.mem_filter, Finset.mem_univ, true_and]
      dsimp only [clauseMemBit, piv]
      simp only [show ¬(h + w < w) by omega, ↓reduceDIte, Bool.false_or]
      by_cases hw : 0 < w
      · have hrange : h + 1 ≤ h + w ∧ h + w < h + 1 + w := by omega
        simp only [hw, hrange, and_self, ↓reduceDIte, Bool.and_eq_true, nextZ,
          show ¬(h + w - (h + 1) + 1 < w) by omega]
        rw [not_beq_eq_true]
        have hidx : (⟨w + (h + w - (h + 1)), by omega⟩ : Fin (2 * w)) = ⟨2 * w - 1, by omega⟩ :=
          Fin.ext (by dsimp; omega)
        rw [hidx]
        exact ⟨fun ⟨h1, h2⟩ => ⟨h1, h2.symm⟩, fun ⟨h1, h2⟩ => ⟨h1, h2.symm⟩⟩
      · have hrange : ¬(h + 1 ≤ h + w ∧ h + w < h + 1 + w) := by omega
        simp only [hw, hrange, ↓reduceDIte, Bool.false_eq_true, false_and]
  constructor
  · intro hpivF
    ext ⟨v, sg⟩
    by_cases hv : v = piv
    · subst hv
      simp [hnot_piv_res sg, hpiv_D sg, hpivF]
    · exact hmem_other (v, sg) hv
  · intro hpivT
    refine ⟨(hpiv_D (!b)).mpr ⟨hpivT, rfl⟩, ?_⟩
    ext ⟨v, sg⟩
    rw [Finset.mem_erase]
    by_cases hv : v = piv
    · subst hv
      simp only [hnot_piv_res sg, iff_false, not_and]
      intro hne hmem
      rcases (hpiv_D sg).mp hmem with ⟨_, rfl⟩
      exact hne rfl
    · have hne : (v, sg) ≠ (piv, !b) := fun heq => hv (congrArg Prod.fst heq)
      simp only [hne, ne_eq, not_false_eq_true, true_and]
      exact (hmem_other (v, sg) hv).symm

private theorem parentStep_spec {n w K : Nat} (hn : 0 < n)
    (table : Fin n → (Fin (w + 1) → Bool) → Bool) {h : Nat} (hh : h < n - w)
    (clNext : Fin K → Fin (2 * w) → Bool) (i : Fin K) :
    let x := tableInputVec hn table
    let st := fwdLayer (K := K) hn h x
    let c0 : Fin (2 * K) := ⟨2 * i.val, by have := i.isLt; omega⟩
    let c1 : Fin (2 * K) := ⟨2 * i.val + 1, by have := i.isLt; omega⟩
    let D0 : Clause (Fin n) := if childLookup hn h st x c0 then
      clauseOf (h + 1) (st i).2.1 (nextZ (st i).2.2 false) (childClauseMask hn h clNext x c0.val)
      else axiomOf h (st i).2.2 false
    let D1 : Clause (Fin n) := if childLookup hn h st x c1 then
      clauseOf (h + 1) (st i).2.1 (nextZ (st i).2.2 true) (childClauseMask hn h clNext x c1.val)
      else axiomOf h (st i).2.2 true
    let ps := parentStep hn h clNext x i
    (ps.2 = true → IsResolvent D0 D1 (clauseOf h (st i).2.1 (st i).2.2 ps.1)) ∧
    (ps.2 = false → clauseOf h (st i).2.1 (st i).2.2 ps.1 = D0 ∨
      clauseOf h (st i).2.1 (st i).2.2 ps.1 = D1) := by
  intro x st c0 c1 D0 D1 ps
  have h0 := childMaskAt_spec hn table hh clNext i false
  have h1 := childMaskAt_spec hn table hh clNext i true
  dsimp only [Bool.toNat, Nat.add_zero] at h0 h1
  constructor
  · intro hres
    dsimp only [ps, parentStep] at hres ⊢
    rw [Bool.and_eq_true] at hres
    rcases hres with ⟨hp0, hp1⟩
    rcases h0.2 hp0 with ⟨hmem0, her0⟩
    rcases h1.2 hp1 with ⟨hmem1, her1⟩
    refine ⟨⟨h + w, by omega⟩, hmem0, hmem1, ?_⟩
    simp only [hp0, hp1, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [clauseOf_or]
    exact congrArg₂ (· ∪ ·) her0.symm her1.symm
  · intro hno
    dsimp only [ps, parentStep] at hno ⊢
    cases hp0 : (childMaskAt hn h clNext x i false).2
    · simp only [Bool.not_false, ↓reduceIte]
      exact Or.inl (h0.1 hp0)
    · cases hp1 : (childMaskAt hn h clNext x i true).2
      · simp only [Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte]
        exact Or.inr (h1.1 hp1)
      · simp [hp0, hp1] at hno

private theorem seedClause_base {n w K : Nat} (hn : 0 < n) (hKlo : 2 ^ w ≤ K)
    (x : Fin (n * 2 ^ (w + 1)) → Bool) (idx : Fin (2 ^ w)) :
    let i : Fin K := ⟨idx.val, idx.isLt.trans_le hKlo⟩
    seedClause (n := n) w idx (seedMaskAt hn hKlo w le_rfl x idx) =
      clauseOf 0 (fwdLayer (K := K) hn 0 x i).2.1 (fwdLayer (K := K) hn 0 x i).2.2 (bwdMask hn 0 x i) := by
  intro i
  have hzero : ∀ (r : Nat) (hr : r ≤ w) (h0 : r = 0) (i1 : Fin (2 ^ (w - r))) (j1 : Fin (w - r)),
      seedMaskAux hn hKlo r hr x i1 j1 =
        (bwdMask (K := K) hn 0 x ⟨i1.val, Nat.lt_of_lt_of_le i1.isLt ((Nat.pow_le_pow_right (by omega) (by omega)).trans hKlo)⟩ ⟨j1.val, by omega⟩ ||
         bwdMask (K := K) hn 0 x ⟨i1.val, Nat.lt_of_lt_of_le i1.isLt ((Nat.pow_le_pow_right (by omega) (by omega)).trans hKlo)⟩ ⟨w + j1.val, by omega⟩) := by
    intro r hr h0 i1 j1; subst h0; rfl
  ext ⟨v, sg⟩
  simp only [seedClause, clauseOf, Finset.mem_filter, Finset.mem_univ, true_and]
  dsimp only [clauseMemBit, fwdLayer, fwdInit, i, seedMaskAt]
  simp only [idx.isLt, ↓reduceIte]
  by_cases hv : v.val < w
  · simp only [hv, ↓reduceDIte, Nat.zero_le, Nat.zero_add, Nat.sub_zero, true_and]
    rw [hzero (w - w) (by omega) (Nat.sub_self w)]
    cases hb : (!(idx.val.testBit v.val) == sg) <;> simp
  · simp [hv]

private theorem seedStep_spec {n w K : Nat} (hn : 0 < n) (hwn : w ≤ n) (hKlo : 2 ^ w ≤ K)
    (x : Fin (n * 2 ^ (w + 1)) → Bool) {d_lev : Nat} (hd : d_lev < w) (idx : Fin (2 ^ d_lev)) :
    let idxL : Fin (2 ^ (d_lev + 1)) := ⟨idx.val, idx.isLt.trans (Nat.pow_lt_pow_right (by omega) (by omega))⟩
    let idxR : Fin (2 ^ (d_lev + 1)) := ⟨idx.val + 2 ^ d_lev, by
      have h1 := idx.isLt; rw [Nat.pow_succ]; omega⟩
    let CL : Clause (Fin n) := seedClause (d_lev + 1) idxL (seedMaskAt hn hKlo (d_lev + 1) (by omega) x idxL)
    let CR : Clause (Fin n) := seedClause (d_lev + 1) idxR (seedMaskAt hn hKlo (d_lev + 1) (by omega) x idxR)
    let COut : Clause (Fin n) := seedClause d_lev idx (seedMaskAt hn hKlo d_lev (by omega) x idx)
    (seedDoRes hn hKlo d_lev hd x idx = true → IsResolvent CL CR COut) ∧
    (seedDoRes hn hKlo d_lev hd x idx = false → COut = CL ∨ COut = CR) := by
  intro idxL idxR CL CR COut
  let r := w - (d_lev + 1)
  have hr : r ≤ w := by omega
  have hwr : w - r = d_lev + 1 := by omega
  have hwr1 : w - (r + 1) = d_lev := by omega
  let mL : Fin (d_lev + 1) → Bool := seedMaskAt hn hKlo (d_lev + 1) (by omega) x idxL
  let mR : Fin (d_lev + 1) → Bool := seedMaskAt hn hKlo (d_lev + 1) (by omega) x idxR
  let pivL : Bool := mL ⟨d_lev, Nat.lt_succ_self d_lev⟩
  let pivR : Bool := mR ⟨d_lev, Nat.lt_succ_self d_lev⟩
  have hmOut_eq : ∀ j : Fin d_lev,
      seedMaskAt hn hKlo d_lev (by omega) x idx j =
      (if !pivL then mL ⟨j.val, by omega⟩
       else if !pivR then mR ⟨j.val, by omega⟩
       else (mL ⟨j.val, by omega⟩ || mR ⟨j.val, by omega⟩)) := by
    intro j
    have hsub : w - d_lev = r + 1 := by omega
    have hcast : ∀ (a : Nat) (ha : a ≤ w) (he : a = r + 1)
        (i1 : Fin (2 ^ (w - a))) (j1 : Fin (w - a)),
        seedMaskAux hn hKlo a ha x i1 j1 =
        seedMaskAux hn hKlo (r + 1) (by omega) x ⟨i1.val, by rw [← he]; exact i1.isLt⟩
          ⟨j1.val, by rw [← he]; exact j1.isLt⟩ := by
      intro a ha he i1 j1; subst he; rfl
    dsimp only [seedMaskAt]
    rw [hcast (w - d_lev) (by omega) hsub]
    dsimp only [seedMaskAux]
    have hL_aux : ∀ (k : Fin (d_lev + 1)),
        seedMaskAux hn hKlo r hr x ⟨idx.val, by have := idxL.isLt; rw [hwr]; exact this⟩ ⟨k.val, by rw [hwr]; exact k.isLt⟩ =
        mL k := fun _ => rfl
    have hR_aux : ∀ (k : Fin (d_lev + 1)),
        seedMaskAux hn hKlo r hr x ⟨idx.val + 2 ^ (w - (r + 1)), by
          have := idxR.isLt; rw [hwr, hwr1]; exact this⟩ ⟨k.val, by rw [hwr]; exact k.isLt⟩ =
        mR k := by
      intro k
      dsimp only [mR, seedMaskAt, idxR]
      congr 1; apply Fin.ext; dsimp only; rw [hwr1]
    have h1 : seedMaskAux hn hKlo r (by omega) x ⟨idx.val, by have := idxL.isLt; rw [hwr]; exact this⟩
        ⟨w - (r + 1), by omega⟩ = pivL := by
      have : (⟨w - (r + 1), by omega⟩ : Fin (w - r)) = ⟨d_lev, by rw [hwr]; omega⟩ := Fin.ext hwr1
      rw [this]; exact hL_aux ⟨d_lev, Nat.lt_succ_self d_lev⟩
    have h2 : seedMaskAux hn hKlo r (by omega) x ⟨idx.val + 2 ^ (w - (r + 1)), by
        have := idxR.isLt; rw [hwr, hwr1]; exact this⟩ ⟨w - (r + 1), by omega⟩ = pivR := by
      have : (⟨w - (r + 1), by omega⟩ : Fin (w - r)) = ⟨d_lev, by rw [hwr]; omega⟩ := Fin.ext hwr1
      rw [this]; exact hR_aux ⟨d_lev, Nat.lt_succ_self d_lev⟩
    have h3 : seedMaskAux hn hKlo r (by omega) x ⟨idx.val, by have := idxL.isLt; rw [hwr]; exact this⟩
        ⟨j.val, by omega⟩ = mL ⟨j.val, by omega⟩ := hL_aux ⟨j.val, by omega⟩
    have h4 : seedMaskAux hn hKlo r (by omega) x ⟨idx.val + 2 ^ (w - (r + 1)), by
        have := idxR.isLt; rw [hwr, hwr1]; exact this⟩ ⟨j.val, by omega⟩ = mR ⟨j.val, by omega⟩ :=
      hR_aux ⟨j.val, by omega⟩
    rw [h1, h2, h3, h4]
  have hdoRes_eq : seedDoRes hn hKlo d_lev hd x idx = (pivL && pivR) := rfl
  have htbL_piv : idxL.val.testBit d_lev = false := Nat.testBit_lt_two_pow idx.isLt
  have htbR_piv : idxR.val.testBit d_lev = true := by
    dsimp only [idxR]
    rw [Nat.testBit_eq_decide_div_mod_eq, Nat.add_div_right _ (Nat.two_pow_pos d_lev),
      Nat.div_eq_of_lt idx.isLt]
    simp
  have htbR_lt : ∀ k < d_lev, idxR.val.testBit k = idx.val.testBit k := by
    intro k hk
    dsimp only [idxR]
    have hpow : 2 ^ d_lev = 2 ^ k * 2 ^ (d_lev - k) := by
      rw [← Nat.pow_add, Nat.add_sub_of_le (by omega)]
    have hsum : idx.val + 2 ^ d_lev = idx.val + 2 ^ k * 2 ^ (d_lev - k) := congrArg (idx.val + ·) hpow
    rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq, hsum]
    have hdiv : (idx.val + 2 ^ k * 2 ^ (d_lev - k)) / 2 ^ k = idx.val / 2 ^ k + 2 ^ (d_lev - k) := by
      rw [Nat.add_comm, Nat.mul_add_div (Nat.two_pow_pos k), Nat.add_comm]
    rw [hdiv]
    have h2 : 2 ^ (d_lev - k) = 2 * 2 ^ (d_lev - k - 1) := by
      conv_lhs => rw [show d_lev - k = (d_lev - k - 1) + 1 by omega]
      rw [Nat.pow_succ, Nat.mul_comm]
    rw [h2, Nat.add_mul_mod_self_left]
  let piv : Fin n := ⟨d_lev, by omega⟩
  have hmemCL_piv : ∀ sg, (piv, sg) ∈ CL ↔ pivL = true ∧ sg = true := by
    intro sg
    simp only [CL, seedClause, Finset.mem_filter, Finset.mem_univ, true_and, piv,
      Nat.lt_succ_self, ↓reduceDIte, htbL_piv]
    cases sg <;> simp [pivL, mL]
  have hmemCR_piv : ∀ sg, (piv, sg) ∈ CR ↔ pivR = true ∧ sg = false := by
    intro sg
    simp only [CR, seedClause, Finset.mem_filter, Finset.mem_univ, true_and, piv,
      Nat.lt_succ_self, ↓reduceDIte, htbR_piv]
    cases sg <;> simp [pivR, mR]
  have hmem_lt : ∀ (v : Fin n) (sg : Bool) (hv : v.val < d_lev),
      ((v, sg) ∈ CL ↔ (!(idx.val.testBit v.val)) = sg ∧ mL ⟨v.val, by omega⟩ = true) ∧
      ((v, sg) ∈ CR ↔ (!(idx.val.testBit v.val)) = sg ∧ mR ⟨v.val, by omega⟩ = true) ∧
      ((v, sg) ∈ COut ↔ (!(idx.val.testBit v.val)) = sg ∧ seedMaskAt hn hKlo d_lev (by omega) x idx ⟨v.val, hv⟩ = true) := by
    intro v sg hv
    refine ⟨?_, ?_, ?_⟩
    · simp only [CL, seedClause, Finset.mem_filter, Finset.mem_univ, true_and,
        show v.val < d_lev + 1 by omega, ↓reduceDIte]
      dsimp only [idxL]
      cases h : (!(idx.val.testBit v.val) == sg)
      · simp only [Bool.false_eq_true, ↓reduceIte, false_iff, not_and]
        intro heq; rw [(not_beq_eq_true _ _).mpr heq] at h; cases h
      · simp only [↓reduceIte, (not_beq_eq_true _ _).mp h, true_and]; rfl
    · simp only [CR, seedClause, Finset.mem_filter, Finset.mem_univ, true_and,
        show v.val < d_lev + 1 by omega, ↓reduceDIte, htbR_lt v.val hv]
      cases h : (!(idx.val.testBit v.val) == sg)
      · simp only [Bool.false_eq_true, ↓reduceIte, false_iff, not_and]
        intro heq; rw [(not_beq_eq_true _ _).mpr heq] at h; cases h
      · simp only [↓reduceIte, (not_beq_eq_true _ _).mp h, true_and]; rfl
    · simp only [COut, seedClause, Finset.mem_filter, Finset.mem_univ, true_and, hv, ↓reduceDIte]
      cases h : (!(idx.val.testBit v.val) == sg)
      · simp only [Bool.false_eq_true, ↓reduceIte, false_iff, not_and]
        intro heq; rw [(not_beq_eq_true _ _).mpr heq] at h; cases h
      · simp only [↓reduceIte, (not_beq_eq_true _ _).mp h, true_and]
  have hmem_gt : ∀ (v : Fin n) (sg : Bool), d_lev < v.val →
      (v, sg) ∉ CL ∧ (v, sg) ∉ CR ∧ (v, sg) ∉ COut := by
    intro v sg hv
    have h1 : ¬(v.val < d_lev + 1) := by omega
    have h2 : ¬(v.val < d_lev) := by omega
    refine ⟨?_, ?_, ?_⟩
    · simp only [CL, seedClause, Finset.mem_filter, Finset.mem_univ, true_and, h1, ↓reduceDIte]; simp
    · simp only [CR, seedClause, Finset.mem_filter, Finset.mem_univ, true_and, h1, ↓reduceDIte]; simp
    · simp only [COut, seedClause, Finset.mem_filter, Finset.mem_univ, true_and, h2, ↓reduceDIte]; simp
  have hCOut_piv : ∀ sg, (piv, sg) ∉ COut := by
    intro sg; simp [COut, seedClause, piv]
  constructor
  · intro hres
    rw [hdoRes_eq, Bool.and_eq_true] at hres
    rcases hres with ⟨hL, hR⟩
    refine ⟨piv, (hmemCL_piv true).mpr ⟨hL, rfl⟩, (hmemCR_piv false).mpr ⟨hR, rfl⟩, ?_⟩
    ext ⟨v, sg⟩
    rw [Finset.mem_union, Finset.mem_erase, Finset.mem_erase]
    by_cases hlt : v.val < d_lev
    · have hne1 : (v, sg) ≠ (piv, true) := fun h => by have := congrArg (fun p => p.1.val) h; dsimp [piv] at this; omega
      have hne2 : (v, sg) ≠ (piv, false) := fun h => by have := congrArg (fun p => p.1.val) h; dsimp [piv] at this; omega
      simp only [hne1, hne2, ne_eq, not_false_eq_true, true_and]
      rcases hmem_lt v sg hlt with ⟨h1, h2, h3⟩
      rw [h1, h2, h3, hmOut_eq ⟨v.val, hlt⟩]
      simp only [hL, hR, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Bool.or_eq_true]
      exact and_or_left
    · by_cases heq : v.val = d_lev
      · have hvp : v = piv := Fin.ext heq
        subst hvp
        simp only [hCOut_piv sg, false_iff, not_or, not_and]
        exact ⟨fun hne hm => hne (by rw [((hmemCL_piv sg).mp hm).2]),
               fun hne hm => hne (by rw [((hmemCR_piv sg).mp hm).2])⟩
      · have hgt : d_lev < v.val := by omega
        rcases hmem_gt v sg hgt with ⟨h1, h2, h3⟩
        simp only [h1, h2, h3, and_false, or_self]
  · intro hno
    rw [hdoRes_eq] at hno
    cases hL : pivL
    · left
      ext ⟨v, sg⟩
      by_cases hlt : v.val < d_lev
      · rcases hmem_lt v sg hlt with ⟨h1, _, h3⟩
        rw [h1, h3, hmOut_eq ⟨v.val, hlt⟩]
        simp only [hL, Bool.not_false, ↓reduceIte]
      · by_cases heq : v.val = d_lev
        · have hvp : v = piv := Fin.ext heq; subst hvp
          simp only [hCOut_piv sg, hmemCL_piv sg, hL, Bool.false_eq_true, false_and]
        · rcases hmem_gt v sg (by omega) with ⟨h1, _, h3⟩
          simp only [h1, h3]
    · cases hR : pivR
      · right
        ext ⟨v, sg⟩
        by_cases hlt : v.val < d_lev
        · rcases hmem_lt v sg hlt with ⟨_, h2, h3⟩
          rw [h2, h3, hmOut_eq ⟨v.val, hlt⟩]
          simp only [hL, hR, Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte]
        · by_cases heq : v.val = d_lev
          · have hvp : v = piv := Fin.ext heq; subst hvp
            simp only [hCOut_piv sg, hmemCR_piv sg, hR, Bool.false_eq_true, false_and]
          · rcases hmem_gt v sg (by omega) with ⟨_, h2, h3⟩
            simp only [h2, h3]
      · rw [hL, hR] at hno; cases hno

private def slotClause {n w K : Nat} (hn : 0 < n) (hKlo : 2 ^ w ≤ K)
    (x : Fin (n * 2 ^ (w + 1)) → Bool) (s : Fin ((3 * (n - w) + 2) * K)) : Clause (Fin n) :=
  Finset.univ.filter (fun lit => slotMember hn hKlo s lit x = true)

private def linesFrom {n w K : Nat} (hn : 0 < n) (hKlo : 2 ^ w ≤ K)
    (x : Fin (n * 2 ^ (w + 1)) → Bool) (t : Nat) : List (Clause (Fin n)) :=
  (((List.finRange ((3 * (n - w) + 2) * K)).drop t).filter (fun s => slotEnable hn hKlo s x)).map
    (slotClause hn hKlo x)

private theorem mem_linesFrom_iff {n w K : Nat} (hn : 0 < n) (hKlo : 2 ^ w ≤ K)
    (x : Fin (n * 2 ^ (w + 1)) → Bool) (t : Nat) (C : Clause (Fin n)) :
    C ∈ linesFrom hn hKlo x t ↔
      ∃ s : Fin ((3 * (n - w) + 2) * K), t ≤ s.val ∧ slotEnable hn hKlo s x = true ∧
        slotClause hn hKlo x s = C := by
  dsimp only [linesFrom]
  rw [List.mem_map]
  constructor
  · rintro ⟨s, hs, rfl⟩
    rw [List.mem_filter] at hs
    rcases hs with ⟨hdrop, hen⟩
    have ht : t ≤ s.val := by
      rcases List.mem_iff_getElem.mp hdrop with ⟨k, hk, hget⟩
      rw [List.getElem_drop, List.getElem_finRange] at hget
      have := congrArg Fin.val hget
      dsimp at this; omega
    exact ⟨s, ht, hen, rfl⟩
  · rintro ⟨s, ht, hen, rfl⟩
    refine ⟨s, List.mem_filter.mpr ⟨?_, hen⟩, rfl⟩
    rw [List.mem_iff_getElem]
    refine ⟨s.val - t, by simp; omega, ?_⟩
    rw [List.getElem_drop, List.getElem_finRange]
    exact Fin.ext (by simp; omega)

private theorem linesFrom_mono {n w K : Nat} (hn : 0 < n) (hKlo : 2 ^ w ≤ K)
    (x : Fin (n * 2 ^ (w + 1)) → Bool) {t1 t2 : Nat} (hle : t1 ≤ t2) {C : Clause (Fin n)}
    (hmem : C ∈ linesFrom hn hKlo x t2) : C ∈ linesFrom hn hKlo x t1 := by
  rw [mem_linesFrom_iff] at hmem ⊢
  rcases hmem with ⟨s, hs, hen, rfl⟩
  exact ⟨s, hle.trans hs, hen, rfl⟩

private theorem linesFrom_succ_eq {n w K : Nat} (hn : 0 < n) (hKlo : 2 ^ w ≤ K)
    (x : Fin (n * 2 ^ (w + 1)) → Bool) {t : Nat} (ht : t < (3 * (n - w) + 2) * K) :
    linesFrom hn hKlo x t =
      if slotEnable hn hKlo ⟨t, ht⟩ x then
        slotClause hn hKlo x ⟨t, ht⟩ :: linesFrom hn hKlo x (t + 1)
      else
        linesFrom hn hKlo x (t + 1) := by
  dsimp only [linesFrom]
  have hdrop : (List.finRange ((3 * (n - w) + 2) * K)).drop t =
      ⟨t, ht⟩ :: (List.finRange ((3 * (n - w) + 2) * K)).drop (t + 1) := by
    rw [List.drop_eq_getElem_cons (by simp [ht])]
    simp
  rw [hdrop, List.filter_cons]
  cases h : slotEnable hn hKlo ⟨t, ht⟩ x <;> simp

private theorem linesFrom_end {n w K : Nat} (hn : 0 < n) (hKlo : 2 ^ w ≤ K)
    (x : Fin (n * 2 ^ (w + 1)) → Bool) :
    linesFrom hn hKlo x ((3 * (n - w) + 2) * K) = [] := by
  dsimp only [linesFrom]
  rw [List.drop_eq_nil_of_le (by simp)]
  rfl

private theorem slot_term_eq {n w K : Nat} (hn : 0 < n) (hKlo : 2 ^ w ≤ K)
    (x : Fin (n * 2 ^ (w + 1)) → Bool) (i : Fin K) :
    let S := (3 * (n - w) + 2) * K
    let s : Fin S := ⟨K + (n - w) * (3 * K) + i.val, by
      have hi := i.isLt
      have hS : (3 * (n - w) + 2) * K = K + (n - w) * (3 * K) + K := by ring
      dsimp only [S]; omega⟩
    slotEnable hn hKlo s x = (fwdLayer hn (n - w) x i).1 ∧
    slotClause hn hKlo x s =
      clauseOf (n - w) (fwdLayer hn (n - w) x i).2.1 (fwdLayer hn (n - w) x i).2.2 (termMask hn x i) := by
  intro S s
  have h1 : ¬(s.val < K) := by dsimp [s]; omega
  have h2 : ¬(s.val < K + (n - w) * (3 * K)) := by dsimp [s]; omega
  have hi_eq : (⟨s.val - (K + (n - w) * (3 * K)), by
      have hs := s.isLt
      have hS : S = K + (n - w) * (3 * K) + K := by dsimp only [S]; ring
      omega⟩ : Fin K) = i :=
    Fin.ext (by dsimp [s]; omega)
  constructor
  · dsimp only [slotEnable]
    simp only [h1, h2, ↓reduceIte, ↓reduceDIte, hi_eq]
  · ext lit
    simp only [slotClause, clauseOf, Finset.mem_filter, Finset.mem_univ, true_and, slotMember,
      h1, h2, ↓reduceIte, ↓reduceDIte, hi_eq]

private theorem slot_layer_eq {n w K : Nat} (_hn : 0 < n) (hKlo : 2 ^ w ≤ K)
    (_x : Fin (n * 2 ^ (w + 1)) → Bool) {h : Nat} (hh : h < n - w) (kind : Nat) (hk : kind < 3) (i : Fin K) :
    let S := (3 * (n - w) + 2) * K
    let s : Fin S := ⟨K + h * (3 * K) + kind * K + i.val, by
      have := i.isLt
      have h1 : (h + 1) * (3 * K) ≤ (n - w) * (3 * K) := Nat.mul_le_mul_right _ (by omega)
      have h2 : (3 * (n - w) + 2) * K = K + (n - w) * (3 * K) + K := by ring
      dsimp [S]
      have h3 : kind * K + i.val < 3 * K := by
        have : kind * K ≤ 2 * K := Nat.mul_le_mul_right K (by omega)
        omega
      rw [Nat.add_mul, Nat.one_mul] at h1
      omega⟩
    (s.val - K) / (3 * K) = h ∧
    (s.val - K) % (3 * K) / K = kind ∧
    (s.val - K) % (3 * K) % K = i.val := by
  intro S s
  have hKpos : 0 < K := (Nat.two_pow_pos w).trans_le hKlo
  have hrem : s.val - K = h * (3 * K) + (kind * K + i.val) := by dsimp [s]; omega
  have hlt : kind * K + i.val < 3 * K := by
    have : kind * K ≤ 2 * K := Nat.mul_le_mul_right K (by omega)
    have := i.isLt; omega
  have hdiv : (s.val - K) / (3 * K) = h := by
    rw [hrem, Nat.mul_comm h (3 * K), Nat.mul_add_div (by omega), Nat.div_eq_of_lt hlt, Nat.add_zero]
  have hmod : (s.val - K) % (3 * K) = kind * K + i.val := by
    rw [hrem, Nat.mul_comm h (3 * K), Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]
  refine ⟨hdiv, ?_, ?_⟩
  · rw [hmod, Nat.mul_comm kind K, Nat.mul_add_div hKpos, Nat.div_eq_of_lt i.isLt, Nat.add_zero]
  · rw [hmod, Nat.mul_comm kind K, Nat.mul_add_mod, Nat.mod_eq_of_lt i.isLt]

private theorem linesFrom_bwd_mem {n w K : Nat} (hn : 0 < n) (hwn : w ≤ n)
    (hKlo : 2 ^ w ≤ K) (hKhi : K ≤ 4 ^ w)
    (table : Fin n → (Fin (w + 1) → Bool) → Bool)
    (hReached : ∀ h ≤ n - w, (reachedOf hn w table h).card ≤ K) :
    let x := tableInputVec hn table
    ∀ r ≤ n - w, ∀ i : Fin K,
      (fwdLayer (K := K) hn (n - w - r) x i).1 = true →
      clauseOf (n - w - r) (fwdLayer (K := K) hn (n - w - r) x i).2.1 (fwdLayer (K := K) hn (n - w - r) x i).2.2
        (bwdMask hn (n - w - r) x i) ∈ linesFrom hn hKlo x (K + (n - w - r) * (3 * K)) := by
  intro x r
  induction r with
  | zero =>
    intro _ i hiV
    simp only [Nat.sub_zero] at hiV ⊢
    have hbwd : bwdMask hn (n - w) x i = termMask hn x i := by funext j; simp [bwdMask, bwdMaskAux]
    rw [hbwd]
    rcases slot_term_eq hn hKlo x i with ⟨hen, hcl⟩
    rw [mem_linesFrom_iff]
    refine ⟨⟨K + (n - w) * (3 * K) + i.val, by
        have := i.isLt
        have hS : (3 * (n - w) + 2) * K = K + (n - w) * (3 * K) + K := by ring
        omega⟩,
      by dsimp only; omega, by rw [hen]; exact hiV, hcl⟩
  | succ r ih =>
    intro hr i hiV
    let h := n - w - (r + 1)
    change (fwdLayer (K := K) hn h x i).1 = true at hiV
    change clauseOf h (fwdLayer (K := K) hn h x i).2.1 (fwdLayer (K := K) hn h x i).2.2
      (bwdMask hn h x i) ∈ linesFrom hn hKlo x (K + h * (3 * K))
    have hh : h < n - w := by dsimp [h]; omega
    have hh1 : n - w - r = h + 1 := by dsimp [h]; omega
    have hInv := fwdLayer_inv hn hwn hKlo hKhi table hReached h (by omega)
    have hRoute := (fwdStep_inv_and_route hn hKlo hKhi table hh hInv (hReached (h + 1) (by omega))).2
    have hIH : ∀ j : Fin K, (fwdLayer (K := K) hn (h + 1) x j).1 = true →
        clauseOf (h + 1) (fwdLayer (K := K) hn (h + 1) x j).2.1 (fwdLayer (K := K) hn (h + 1) x j).2.2
          (bwdMask hn (h + 1) x j) ∈ linesFrom hn hKlo x (K + (h + 1) * (3 * K)) := by
      intro j hjV
      have := ih (by omega) j (by rwa [hh1])
      rwa [hh1] at this
    let st : LayerState w K := fwdLayer hn h x
    let childD : Bool → Clause (Fin n) := fun b =>
      let cIdx : Fin (2 * K) := ⟨2 * i.val + b.toNat, by cases b <;> (dsimp; omega)⟩
      if childLookup hn h st x cIdx then
        clauseOf (h + 1) (st i).2.1 (nextZ (st i).2.2 b)
          (childClauseMask (K := K) hn h (bwdMask (K := K) hn (h + 1) x) x cIdx.val)
      else axiomOf h (st i).2.2 b
    have hChildMem : ∀ b : Bool, childD b ∈ linesFrom hn hKlo x (K + h * (3 * K) + K) := by
      intro b
      dsimp only [childD]
      let cIdx : Fin (2 * K) := ⟨2 * i.val + b.toNat, by cases b <;> (dsimp; omega)⟩
      cases hok : childLookup hn h st x cIdx
      · simp only [Bool.false_eq_true, ↓reduceIte]
        let kind : Nat := if b then 2 else 1
        have hkind : kind < 3 := by cases b <;> simp [kind]
        rcases slot_layer_eq hn hKlo x hh kind hkind i with ⟨hdiv, hkd, hmd⟩
        let s : Fin ((3 * (n - w) + 2) * K) := ⟨K + h * (3 * K) + kind * K + i.val, by
          have hKpos : 0 < K := (Nat.two_pow_pos w).trans_le hKlo
          have := i.isLt
          have h1 : (h + 1) * (3 * K) ≤ (n - w) * (3 * K) := Nat.mul_le_mul_right _ (by omega)
          have h2 : (3 * (n - w) + 2) * K = K + (n - w) * (3 * K) + K := by ring
          have h3 : kind * K + i.val < 3 * K := by
            have : kind * K ≤ 2 * K := Nat.mul_le_mul_right K (by omega); omega
          rw [Nat.add_mul, Nat.one_mul] at h1; omega⟩
        have hs_div : (s.val - K) / (3 * K) = h := hdiv
        have hs_kd : (s.val - K) % (3 * K) / K = kind := hkd
        have hs_md : (s.val - K) % (3 * K) % K = i.val := hmd
        have hs1 : ¬(s.val < K) := by dsimp [s]; omega
        have hs2 : s.val < K + (n - w) * (3 * K) := by
          have hKpos : 0 < K := (Nat.two_pow_pos w).trans_le hKlo
          have := i.isLt
          have h1 : (h + 1) * (3 * K) ≤ (n - w) * (3 * K) := Nat.mul_le_mul_right _ (by omega)
          have h3 : kind * K + i.val < 3 * K := by
            have : kind * K ≤ 2 * K := Nat.mul_le_mul_right K (by omega); omega
          rw [Nat.add_mul, Nat.one_mul] at h1; dsimp [s]; omega
        have hi_eq : (⟨(s.val - K) % (3 * K) % K, Nat.mod_lt _ ((Nat.two_pow_pos w).trans_le hKlo)⟩ : Fin K) = i :=
          Fin.ext hmd
        rw [mem_linesFrom_iff]
        refine ⟨s, ?_, ?_, ?_⟩
        · cases b
          · dsimp only [s, kind]; simp only [Bool.false_eq_true, ↓reduceIte]; omega
          · dsimp only [s, kind]; simp only [↓reduceIte]; omega
        · dsimp only [slotEnable]
          simp only [hs1, hs2, ↓reduceIte, ↓reduceDIte, hs_div, hs_kd, hi_eq]
          cases b
          · simp only [kind, Bool.false_eq_true, ↓reduceIte, show (1 : Nat) ≠ 0 by omega]
            exact (Bool.and_eq_true _ _).mpr ⟨hiV, by rw [Bool.not_eq_true']; simp only [hs_md]; exact hok⟩
          · simp only [kind, ↓reduceIte, show (2 : Nat) ≠ 0 by omega, show (2 : Nat) ≠ 1 by omega]
            exact (Bool.and_eq_true _ _).mpr ⟨hiV, by rw [Bool.not_eq_true']; simp only [hs_md]; exact hok⟩
        · ext lit
          simp only [slotClause, axiomOf, Finset.mem_filter, Finset.mem_univ, true_and]
          dsimp only [slotMember]
          simp only [hs1, hs2, ↓reduceIte, ↓reduceDIte, hs_div, hs_kd, hi_eq]
          cases b <;> (simp [kind]; rfl)
      · simp only [↓reduceIte]
        rcases hRoute (bwdMask hn (h + 1) x) i b hiV hok with ⟨j, hjV, hja, hjz, hcm⟩
        rw [hcm, ← hja, ← hjz]
        exact linesFrom_mono hn hKlo x (by rw [Nat.add_mul, Nat.one_mul]; omega) (hIH j hjV)
    have hbwd_eq : bwdMask hn h x i = (parentStep hn h (bwdMask hn (h + 1) x) x i).1 := by
      have hr_eq : n - w - h = r + 1 := by dsimp [h]; omega
      have hr1_eq : n - w - (h + 1) = r := by dsimp [h]; omega
      funext j
      simp only [bwdMask, hr_eq, hr1_eq, bwdMaskAux]
      rfl
    rw [hbwd_eq]
    cases hdo : (parentStep hn h (bwdMask hn (h + 1) x) x i).2
    · rcases (parentStep_spec hn table hh (bwdMask hn (h + 1) x) i).2 hdo with heq | heq
      · rw [heq]; exact linesFrom_mono hn hKlo x (by omega) (hChildMem false)
      · rw [heq]; exact linesFrom_mono hn hKlo x (by omega) (hChildMem true)
    · rcases slot_layer_eq hn hKlo x hh 0 (by omega) i with ⟨hdiv, hkd, hmd⟩
      let s : Fin ((3 * (n - w) + 2) * K) := ⟨K + h * (3 * K) + 0 * K + i.val, by
        have hKpos : 0 < K := (Nat.two_pow_pos w).trans_le hKlo
        have := i.isLt
        have h1 : (h + 1) * (3 * K) ≤ (n - w) * (3 * K) := Nat.mul_le_mul_right _ (by omega)
        have h2 : (3 * (n - w) + 2) * K = K + (n - w) * (3 * K) + K := by ring
        rw [Nat.add_mul, Nat.one_mul] at h1; omega⟩
      have hs_div : (s.val - K) / (3 * K) = h := hdiv
      have hs_kd : (s.val - K) % (3 * K) / K = 0 := hkd
      have hs1 : ¬(s.val < K) := by dsimp [s]; omega
      have hs2 : s.val < K + (n - w) * (3 * K) := by
        have hKpos : 0 < K := (Nat.two_pow_pos w).trans_le hKlo
        have := i.isLt
        have h1 : (h + 1) * (3 * K) ≤ (n - w) * (3 * K) := Nat.mul_le_mul_right _ (by omega)
        rw [Nat.add_mul, Nat.one_mul] at h1; dsimp [s]; omega
      have hi_eq : (⟨(s.val - K) % (3 * K) % K, Nat.mod_lt _ ((Nat.two_pow_pos w).trans_le hKlo)⟩ : Fin K) = i :=
        Fin.ext hmd
      rw [mem_linesFrom_iff]
      refine ⟨s, by dsimp [s]; omega, ?_, ?_⟩
      · dsimp only [slotEnable]
        simp only [hs1, hs2, ↓reduceIte, ↓reduceDIte, hs_div, hs_kd, hi_eq]
        exact (Bool.and_eq_true _ _).mpr ⟨hiV, hdo⟩
      · ext lit
        simp only [slotClause, clauseOf, Finset.mem_filter, Finset.mem_univ, true_and]
        dsimp only [slotMember]
        simp only [hs1, hs2, ↓reduceIte, ↓reduceDIte, hs_div, hs_kd, hi_eq, hbwd_eq]

private theorem linesFrom_seed_mem {n w K : Nat} (hn : 0 < n) (hwn : w ≤ n)
    (hKlo : 2 ^ w ≤ K) (hKhi : K ≤ 4 ^ w)
    (table : Fin n → (Fin (w + 1) → Bool) → Bool)
    (hReached : ∀ h ≤ n - w, (reachedOf hn w table h).card ≤ K) :
    let x := tableInputVec hn table
    ∀ r (hr : r ≤ w), ∀ idx : Fin (2 ^ (w - r)),
      seedClause (n := n) (w - r) idx (seedMaskAt hn hKlo (w - r) (by omega) x idx) ∈
        linesFrom hn hKlo x (2 ^ (w - r) - 1) := by
  intro x r
  induction r with
  | zero =>
    intro _ idx
    simp only [Nat.sub_zero]
    rw [seedClause_base hn hKlo x idx]
    have h0 := linesFrom_bwd_mem hn hwn hKlo hKhi table hReached (n - w) le_rfl
      ⟨idx.val, idx.isLt.trans_le hKlo⟩ (by simp [fwdLayer, fwdInit])
    simp only [Nat.sub_self, Nat.zero_mul, Nat.add_zero] at h0
    exact linesFrom_mono hn hKlo x (by omega) h0
  | succ r ih =>
    intro hr idx
    let d_lev := w - (r + 1)
    have hd : d_lev < w := by dsimp [d_lev]; omega
    have hwr : w - r = d_lev + 1 := by dsimp [d_lev]; omega
    have hidxLt : idx.val < 2 ^ d_lev := idx.isLt
    let idxL : Fin (2 ^ (d_lev + 1)) := ⟨idx.val, hidxLt.trans (Nat.pow_lt_pow_right (by omega) (by omega))⟩
    let idxR : Fin (2 ^ (d_lev + 1)) := ⟨idx.val + 2 ^ d_lev, by rw [Nat.pow_succ]; omega⟩
    have hcastMem : ∀ (a b : Nat) (hab : a = b) (ha : a ≤ w) (i1 : Fin (2 ^ a)),
        seedClause (n := n) a i1 (seedMaskAt hn hKlo a ha x i1) ∈ linesFrom hn hKlo x (2 ^ a - 1) →
        seedClause (n := n) b ⟨i1.val, hab ▸ i1.isLt⟩
          (seedMaskAt hn hKlo b (hab ▸ ha) x ⟨i1.val, hab ▸ i1.isLt⟩) ∈ linesFrom hn hKlo x (2 ^ b - 1) := by
      intro a b hab ha i1 hm; subst hab; exact hm
    have hL : seedClause (n := n) (d_lev + 1) idxL (seedMaskAt hn hKlo (d_lev + 1) (by omega) x idxL) ∈
        linesFrom hn hKlo x (2 ^ (d_lev + 1) - 1) :=
      hcastMem (w - r) (d_lev + 1) hwr (by omega) ⟨idxL.val, hwr.symm ▸ idxL.isLt⟩
        (ih (by omega) ⟨idxL.val, hwr.symm ▸ idxL.isLt⟩)
    have hR : seedClause (n := n) (d_lev + 1) idxR (seedMaskAt hn hKlo (d_lev + 1) (by omega) x idxR) ∈
        linesFrom hn hKlo x (2 ^ (d_lev + 1) - 1) :=
      hcastMem (w - r) (d_lev + 1) hwr (by omega) ⟨idxR.val, hwr.symm ▸ idxR.isLt⟩
        (ih (by omega) ⟨idxR.val, hwr.symm ▸ idxR.isLt⟩)
    have hmon : 2 ^ d_lev - 1 ≤ 2 ^ (d_lev + 1) - 1 := by
      have : 2 ^ d_lev ≤ 2 ^ (d_lev + 1) := Nat.pow_le_pow_right (by omega) (by omega); omega
    change seedClause (n := n) d_lev idx (seedMaskAt hn hKlo d_lev (by omega) x idx) ∈
      linesFrom hn hKlo x (2 ^ d_lev - 1)
    cases hdo : seedDoRes hn hKlo d_lev hd x idx
    · rcases (seedStep_spec hn hwn hKlo x hd idx).2 hdo with heq | heq
      · rw [heq]; exact linesFrom_mono hn hKlo x hmon hL
      · rw [heq]; exact linesFrom_mono hn hKlo x hmon hR
    · have hpow_le : 2 ^ (d_lev + 1) ≤ 2 ^ w := Nat.pow_le_pow_right (by omega) (by omega)
      let sv : Nat := 2 ^ d_lev - 1 + idx.val
      have hsv_lt2w : sv + 1 < 2 ^ w := by
        dsimp [sv]; have := Nat.two_pow_pos d_lev; rw [Nat.pow_succ] at hpow_le; omega
      have hsv_ltK : sv < K := by omega
      have hlog : Nat.log2 (sv + 1) = d_lev := by
        have hlo : 2 ^ d_lev ≤ sv + 1 := by dsimp [sv]; have := Nat.two_pow_pos d_lev; omega
        have hhi : sv + 1 < 2 ^ (d_lev + 1) := by dsimp [sv]; have := Nat.two_pow_pos d_lev; rw [Nat.pow_succ]; omega
        have h1 : d_lev ≤ Nat.log2 (sv + 1) := by
          by_contra hlt
          have h2 := Nat.lt_log2_self (n := sv + 1)
          have h3 := Nat.pow_le_pow_right Nat.zero_lt_two (show Nat.log2 (sv + 1) + 1 ≤ d_lev by omega)
          omega
        have h2 : Nat.log2 (sv + 1) ≤ d_lev := by
          by_contra hgt
          have h3 := Nat.log2_self_le (show sv + 1 ≠ 0 by omega)
          have h4 := Nat.pow_le_pow_right Nat.zero_lt_two (show d_lev + 1 ≤ Nat.log2 (sv + 1) by omega)
          omega
        omega
      let s : Fin ((3 * (n - w) + 2) * K) := ⟨sv, by
        have : K ≤ (3 * (n - w) + 2) * K := Nat.le_mul_of_pos_left K (by omega); omega⟩
      have hidx_eq : sv + 1 - 2 ^ d_lev = idx.val := by dsimp [sv]; have := Nat.two_pow_pos d_lev; omega
      rw [mem_linesFrom_iff]
      refine ⟨s, by dsimp [s, sv]; omega, ?_, ?_⟩
      · dsimp only [slotEnable, s]
        simp only [hsv_ltK, hsv_lt2w, ↓reduceIte, ↓reduceDIte]
        have heq_do : ∀ (dl : Nat) (hdl : dl < w) (hdl_eq : dl = d_lev) (i1 : Fin (2 ^ dl)),
            i1.val = idx.val → seedDoRes hn hKlo dl hdl x i1 = seedDoRes hn hKlo d_lev hd x idx := by
          intro dl hdl hdl_eq i1 hi1; subst hdl_eq; have : i1 = idx := Fin.ext hi1; subst this; rfl
        rw [heq_do (Nat.log2 (sv + 1)) (by rw [hlog]; exact hd) hlog ⟨sv + 1 - 2 ^ Nat.log2 (sv + 1), _⟩
          (by dsimp only; rw [hlog, hidx_eq])]
        exact hdo
      · ext lit
        simp only [slotClause, seedClause, Finset.mem_filter, Finset.mem_univ, true_and]
        dsimp only [slotMember, s]
        simp only [hsv_ltK, hsv_lt2w, ↓reduceIte, ↓reduceDIte]
        have heq_f : ∀ (dl : Nat) (hdl : dl < w) (hdl_eq : dl = d_lev) (i1 : Fin (2 ^ dl)),
            i1.val = idx.val →
            (if hv : lit.1.val < dl then
              if !(i1.val.testBit lit.1.val) == lit.2 then seedMaskAt hn hKlo dl (by omega) x i1 ⟨lit.1.val, hv⟩
              else false else false) =
            (if hv : lit.1.val < d_lev then
              if !(idx.val.testBit lit.1.val) == lit.2 then seedMaskAt hn hKlo d_lev (by omega) x idx ⟨lit.1.val, hv⟩
              else false else false) := by
          intro dl hdl hdl_eq i1 hi1
          subst hdl_eq
          have : i1 = idx := Fin.ext hi1
          subst this; rfl
        rw [heq_f (Nat.log2 (sv + 1)) (by rw [hlog]; exact hd) hlog ⟨sv + 1 - 2 ^ Nat.log2 (sv + 1), _⟩
          (by dsimp only; rw [hlog, hidx_eq])]

private theorem lines_isRefutation_and_width {n w K : Nat} (hn : 0 < n) (hwn : w ≤ n)
    (hKlo : 2 ^ w ≤ K) (hKhi : K ≤ 4 ^ w)
    (table : Fin n → (Fin (w + 1) → Bool) → Bool)
    (hReached : ∀ h ≤ n - w, (reachedOf hn w table h).card ≤ K)
    (hEval : evalOutFn (K := K) hn (tableInputVec hn table) = true) :
    let x := tableInputVec hn table
    IsRefutation (formulaOf hn w table) (linesFrom hn hKlo x 0) ∧
    ∀ D ∈ linesFrom hn hKlo x 0, D.card ≤ 2 * w + 1 := by
  intro x
  let S := (3 * (n - w) + 2) * K
  have hInvAll := fwdLayer_inv hn hwn hKlo hKhi table hReached
  have hNoSurv : ∀ i : Fin K, survivesFn hn x i = false := by
    intro i
    dsimp only [evalOutFn] at hEval
    rw [Bool.not_eq_true', Bool.eq_false_iff] at hEval
    by_contra hne
    have ht : survivesFn hn x i = true := Bool.eq_true_of_not_eq_false hne
    exact hEval ((anyNat_eq_true (fun idx x' => if h : idx < K then survivesFn hn x' ⟨idx, h⟩ else false) x K).mpr
      ⟨i.val, i.isLt, by simp only [i.isLt, ↓reduceDIte]; exact ht⟩)
  have hcastMem : ∀ (a b : Nat) (hab : a = b) (ha : a ≤ w) (i1 : Fin (2 ^ a)),
      seedClause (n := n) a i1 (seedMaskAt hn hKlo a ha x i1) ∈ linesFrom hn hKlo x (2 ^ a - 1) →
      seedClause (n := n) b ⟨i1.val, hab ▸ i1.isLt⟩
        (seedMaskAt hn hKlo b (hab ▸ ha) x ⟨i1.val, hab ▸ i1.isLt⟩) ∈ linesFrom hn hKlo x (2 ^ b - 1) := by
    intro a b hab ha i1 hm; subst hab; exact hm
  have hDeriv : ∀ m ≤ S, IsDerivation (formulaOf hn w table) (linesFrom hn hKlo x (S - m)) := by
    intro m
    induction m with
    | zero =>
      intro _
      simp only [Nat.sub_zero]
      dsimp only [S]
      rw [linesFrom_end]
      exact IsDerivation.nil
    | succ m ih =>
      intro hm
      let t := S - (m + 1)
      have ht : t < S := by dsimp [t]; omega
      have hsucc : t + 1 = S - m := by dsimp [t]; omega
      have hprev := ih (by omega)
      rw [← hsucc] at hprev
      rw [linesFrom_succ_eq hn hKlo x ht]
      cases hen : slotEnable hn hKlo ⟨t, ht⟩ x
      · simp only [Bool.false_eq_true, ↓reduceIte]; exact hprev
      · simp only [↓reduceIte]
        by_cases ht1 : t < K
        · by_cases htSeed : t + 1 < 2 ^ w
          · let d_lev := Nat.log2 (t + 1)
            have hd : d_lev < w := by
              by_contra hge
              have hp := Nat.pow_le_pow_right Nat.zero_lt_two (show w ≤ d_lev by omega)
              have hl := Nat.log2_self_le (show t + 1 ≠ 0 by omega)
              dsimp [d_lev] at hp hl; omega
            let idx : Fin (2 ^ d_lev) := ⟨t + 1 - 2 ^ d_lev, by
              have hlt := Nat.lt_log2_self (n := t + 1)
              have hle := Nat.log2_self_le (show t + 1 ≠ 0 by omega)
              rw [Nat.pow_succ] at hlt; dsimp [d_lev] at hlt hle ⊢; omega⟩
            have hdo : seedDoRes hn hKlo d_lev hd x idx = true := by
              dsimp only [slotEnable] at hen
              simp only [ht1, htSeed, ↓reduceIte, ↓reduceDIte] at hen
              exact hen
            have hcl : slotClause hn hKlo x ⟨t, ht⟩ =
                seedClause d_lev idx (seedMaskAt hn hKlo d_lev (by omega) x idx) := by
              ext lit
              simp only [slotClause, seedClause, Finset.mem_filter, Finset.mem_univ, true_and]
              dsimp only [slotMember, d_lev, idx]
              simp only [ht1, htSeed, ↓reduceIte, ↓reduceDIte]
            rw [hcl]
            let idxL : Fin (2 ^ (d_lev + 1)) := ⟨idx.val, idx.isLt.trans (Nat.pow_lt_pow_right (by omega) (by omega))⟩
            let idxR : Fin (2 ^ (d_lev + 1)) := ⟨idx.val + 2 ^ d_lev, by have := idx.isLt; rw [Nat.pow_succ]; omega⟩
            have hres := (seedStep_spec hn hwn hKlo x hd idx).1 hdo
            have hwr : w - (w - (d_lev + 1)) = d_lev + 1 := by omega
            have ht_le : t + 1 ≤ 2 ^ (d_lev + 1) - 1 := by
              have hlt := Nat.lt_log2_self (n := t + 1)
              dsimp [d_lev] at hlt ⊢; omega
            have hmemL : seedClause (n := n) (d_lev + 1) idxL
                (seedMaskAt hn hKlo (d_lev + 1) (by omega) x idxL) ∈ linesFrom hn hKlo x (t + 1) :=
              linesFrom_mono hn hKlo x ht_le
                (hcastMem (w - (w - (d_lev + 1))) (d_lev + 1) hwr (by omega) ⟨idxL.val, hwr.symm ▸ idxL.isLt⟩
                  (linesFrom_seed_mem hn hwn hKlo hKhi table hReached (w - (d_lev + 1)) (by omega)
                    ⟨idxL.val, hwr.symm ▸ idxL.isLt⟩))
            have hmemR : seedClause (n := n) (d_lev + 1) idxR
                (seedMaskAt hn hKlo (d_lev + 1) (by omega) x idxR) ∈ linesFrom hn hKlo x (t + 1) :=
              linesFrom_mono hn hKlo x ht_le
                (hcastMem (w - (w - (d_lev + 1))) (d_lev + 1) hwr (by omega) ⟨idxR.val, hwr.symm ▸ idxR.isLt⟩
                  (linesFrom_seed_mem hn hwn hKlo hKhi table hReached (w - (d_lev + 1)) (by omega)
                    ⟨idxR.val, hwr.symm ▸ idxR.isLt⟩))
            exact IsDerivation.res hprev hmemL hmemR hres
          · dsimp only [slotEnable] at hen; simp [ht1, htSeed] at hen
        · by_cases ht2 : t < K + (n - w) * (3 * K)
          · have hKpos : 0 < K := (Nat.two_pow_pos w).trans_le hKlo
            let rem := t - K
            let h := rem / (3 * K)
            let inH := rem % (3 * K)
            let kind := inH / K
            let i : Fin K := ⟨inH % K, Nat.mod_lt _ hKpos⟩
            have hh : h < n - w := (Nat.div_lt_iff_lt_mul (by omega)).mpr (by dsimp [rem]; omega)
            let st : LayerState w K := fwdLayer hn h x
            dsimp only [slotEnable] at hen
            simp only [ht1, ht2, ↓reduceIte, ↓reduceDIte] at hen
            by_cases hk0 : kind = 0
            · have hk0' : (t - K) % (3 * K) / K = 0 := hk0
              simp only [hk0', ↓reduceIte, Bool.and_eq_true] at hen
              rcases hen with ⟨hiV, hdo⟩
              have hcl : slotClause hn hKlo x ⟨t, ht⟩ =
                  clauseOf h (st i).2.1 (st i).2.2 (bwdMask hn h x i) := by
                ext lit
                simp only [slotClause, clauseOf, Finset.mem_filter, Finset.mem_univ, true_and]
                dsimp only [slotMember, st, h, i, inH, rem]
                simp only [ht1, ht2, hk0', ↓reduceIte, ↓reduceDIte]
              have hbwd_eq : bwdMask hn h x i = (parentStep hn h (bwdMask hn (h + 1) x) x i).1 := by
                have hr_eq : n - w - h = (n - w - (h + 1)) + 1 :=
                  (show ∀ a b : Nat, b < a → a - b = (a - (b + 1)) + 1 from fun a b hab => by omega) (n - w) h hh
                have hr_back : n - w - ((n - w - (h + 1)) + 1) = h :=
                  (show ∀ a b : Nat, b < a → a - ((a - (b + 1)) + 1) = b from fun a b hab => by omega) (n - w) h hh
                funext j
                simp only [bwdMask, hr_eq, bwdMaskAux]
                rw [hr_back]
              rw [hcl, hbwd_eq]
              have hres := (parentStep_spec hn table hh (bwdMask hn (h + 1) x) i).1 hdo
              have hRoute := (fwdStep_inv_and_route hn hKlo hKhi table hh (hInvAll h (by omega))
                (hReached (h + 1) (by omega))).2
              have ht_le : t + 1 ≤ K + h * (3 * K) + K := by
                have h1 : rem = h * (3 * K) + inH := by
                  dsimp [h, inH]; rw [Nat.mul_comm, Nat.div_add_mod]
                have h2 : inH < K := by
                  have hlt : inH / K = 0 := hk0
                  have hda := Nat.div_add_mod inH K
                  have hml := Nat.mod_lt inH hKpos
                  rw [hlt, Nat.mul_zero, Nat.zero_add] at hda
                  omega
                dsimp [rem] at h1; omega
              have hChildMem : ∀ b : Bool,
                  let cIdx : Fin (2 * K) := ⟨2 * i.val + b.toNat, by have := i.isLt; cases b <;> (dsimp; omega)⟩
                  (if childLookup hn h st x cIdx then
                    clauseOf (h + 1) (st i).2.1 (nextZ (st i).2.2 b)
                      (childClauseMask (K := K) hn h (bwdMask (K := K) hn (h + 1) x) x cIdx.val)
                  else axiomOf h (st i).2.2 b) ∈ linesFrom hn hKlo x (t + 1) := by
                intro b cIdx
                apply linesFrom_mono hn hKlo x ht_le
                cases hok : childLookup hn h st x cIdx
                · simp only [Bool.false_eq_true, ↓reduceIte]
                  let kd : Nat := if b then 2 else 1
                  have hkd_lt : kd < 3 := by cases b <;> simp [kd]
                  rcases slot_layer_eq hn hKlo x hh kd hkd_lt i with ⟨hdiv, hkd, hmd⟩
                  let s : Fin S := ⟨K + h * (3 * K) + kd * K + i.val, by
                    have := i.isLt
                    have h1 : (h + 1) * (3 * K) ≤ (n - w) * (3 * K) := Nat.mul_le_mul_right _ (by omega)
                    have h2 : S = K + (n - w) * (3 * K) + K := by dsimp [S]; ring
                    have h3 : kd * K + i.val < 3 * K := by
                      have : kd * K ≤ 2 * K := Nat.mul_le_mul_right K (by omega); omega
                    rw [Nat.add_mul, Nat.one_mul] at h1; omega⟩
                  have hs_div : (s.val - K) / (3 * K) = h := hdiv
                  have hs_kd : (s.val - K) % (3 * K) / K = kd := hkd
                  have hs_md : (s.val - K) % (3 * K) % K = i.val := hmd
                  have hs1 : ¬(s.val < K) := by dsimp [s]; omega
                  have hs2 : s.val < K + (n - w) * (3 * K) := by
                    have := i.isLt
                    have h1 : (h + 1) * (3 * K) ≤ (n - w) * (3 * K) := Nat.mul_le_mul_right _ (by omega)
                    have h3 : kd * K + i.val < 3 * K := by
                      have : kd * K ≤ 2 * K := Nat.mul_le_mul_right K (by omega); omega
                    rw [Nat.add_mul, Nat.one_mul] at h1; dsimp [s]; omega
                  have hi_eq : (⟨(s.val - K) % (3 * K) % K, Nat.mod_lt _ hKpos⟩ : Fin K) = i := Fin.ext hmd
                  rw [mem_linesFrom_iff]
                  refine ⟨s, ?_, ?_, ?_⟩
                  · cases b
                    · dsimp only [s, kd]; simp only [Bool.false_eq_true, ↓reduceIte]; omega
                    · dsimp only [s, kd]; simp only [↓reduceIte]; omega
                  · dsimp only [slotEnable]
                    simp only [hs1, hs2, ↓reduceIte, ↓reduceDIte, hs_div, hs_kd, hi_eq]
                    cases b
                    · simp only [kd, Bool.false_eq_true, ↓reduceIte, show (1 : Nat) ≠ 0 by omega]
                      exact (Bool.and_eq_true _ _).mpr ⟨hiV, by rw [Bool.not_eq_true']; simp only [hs_md]; exact hok⟩
                    · simp only [kd, ↓reduceIte, show (2 : Nat) ≠ 0 by omega, show (2 : Nat) ≠ 1 by omega]
                      exact (Bool.and_eq_true _ _).mpr ⟨hiV, by rw [Bool.not_eq_true']; simp only [hs_md]; exact hok⟩
                  · ext lit
                    simp only [slotClause, axiomOf, Finset.mem_filter, Finset.mem_univ, true_and]
                    dsimp only [slotMember]
                    simp only [hs1, hs2, ↓reduceIte, ↓reduceDIte, hs_div, hs_kd, hi_eq]
                    cases b <;> (simp [kd]; rfl)
                · simp only [↓reduceIte]
                  rcases hRoute (bwdMask hn (h + 1) x) i b hiV hok with ⟨j, hjV, hja, hjz, hcm⟩
                  rw [hcm, ← hja, ← hjz]
                  have hle_nw : n - w - (h + 1) ≤ n - w := Nat.sub_le _ _
                  have heq : n - w - (n - w - (h + 1)) = h + 1 :=
                    (show ∀ a b : Nat, b < a → a - (a - (b + 1)) = b + 1 from fun a b hab => by omega) (n - w) h hh
                  have hbm := linesFrom_bwd_mem hn hwn hKlo hKhi table hReached (n - w - (h + 1)) hle_nw j
                    (by rwa [heq])
                  rw [heq] at hbm
                  exact linesFrom_mono hn hKlo x (by rw [Nat.add_mul, Nat.one_mul]; omega) hbm
              exact IsDerivation.res hprev (hChildMem false) (hChildMem true) hres
            · have hk0' : (t - K) % (3 * K) / K ≠ 0 := hk0
              by_cases hk1 : kind = 1
              · have hk1' : (t - K) % (3 * K) / K = 1 := hk1
                simp only [hk0', ↓reduceIte] at hen
                simp only [hk1', ↓reduceIte, Bool.and_eq_true, Bool.not_eq_true'] at hen
                have hcl : slotClause hn hKlo x ⟨t, ht⟩ = axiomOf h (st i).2.2 false := by
                  ext lit
                  simp only [slotClause, axiomOf, Finset.mem_filter, Finset.mem_univ, true_and]
                  dsimp only [slotMember, st, h, i, inH, rem]
                  simp only [ht1, ht2, hk0', ↓reduceIte, ↓reduceDIte]
                  simp only [hk1', ↓reduceIte]
                rw [hcl]
                have htab : table (posFn n hn h) (extPat (st i).2.2 false) = false := by
                  have hcl0 := hen.2
                  dsimp only [childLookup] at hcl0
                  rw [tabEval_tableInputVec] at hcl0
                  have hdiv : 2 * i.val / 2 = i.val := by omega
                  have hmod : decide (2 * i.val % 2 = 1) = false := decide_eq_false (by omega)
                  have hpeq : (⟨2 * i.val / 2, (Nat.div_lt_iff_lt_mul (by omega)).mpr (by have := i.isLt; omega)⟩ : Fin K) = i :=
                    Fin.ext hdiv
                  change table (posFn n hn h) (extPat (st ⟨2 * i.val / 2, _⟩).2.2 (decide (2 * i.val % 2 = 1))) = false at hcl0
                  rw [hpeq, hmod] at hcl0
                  exact hcl0
                exact IsDerivation.ax hprev (axiomOf_mem_formula hn table hh (st i).2.2 false htab)
              · have hk1' : (t - K) % (3 * K) / K ≠ 1 := hk1
                simp only [hk0', hk1', ↓reduceIte, Bool.and_eq_true, Bool.not_eq_true'] at hen
                have hcl : slotClause hn hKlo x ⟨t, ht⟩ = axiomOf h (st i).2.2 true := by
                  ext lit
                  simp only [slotClause, axiomOf, Finset.mem_filter, Finset.mem_univ, true_and]
                  dsimp only [slotMember, st, h, i, inH, rem]
                  simp only [ht1, ht2, hk0', hk1', ↓reduceIte, ↓reduceDIte]
                rw [hcl]
                have htab : table (posFn n hn h) (extPat (st i).2.2 true) = false := by
                  have hcl1 := hen.2
                  dsimp only [childLookup] at hcl1
                  rw [tabEval_tableInputVec] at hcl1
                  have hdiv : (2 * i.val + 1) / 2 = i.val := by omega
                  have hmod : decide ((2 * i.val + 1) % 2 = 1) = true := decide_eq_true (by omega)
                  have hpeq : (⟨(2 * i.val + 1) / 2, (Nat.div_lt_iff_lt_mul (by omega)).mpr (by have := i.isLt; omega)⟩ : Fin K) = i :=
                    Fin.ext hdiv
                  change table (posFn n hn h) (extPat (st ⟨(2 * i.val + 1) / 2, _⟩).2.2 (decide ((2 * i.val + 1) % 2 = 1))) = false at hcl1
                  rw [hpeq, hmod] at hcl1
                  exact hcl1
                exact IsDerivation.ax hprev (axiomOf_mem_formula hn table hh (st i).2.2 true htab)
          · let i : Fin K := ⟨t - (K + (n - w) * (3 * K)), by
              have hS : S = K + (n - w) * (3 * K) + K := by dsimp [S]; ring
              omega⟩
            have hiV : (fwdLayer hn (n - w) x i).1 = true := by
              dsimp only [slotEnable] at hen
              simp only [ht1, ht2, ↓reduceIte, ↓reduceDIte] at hen
              exact hen
            have hcl : slotClause hn hKlo x ⟨t, ht⟩ =
                clauseOf (n - w) (fwdLayer hn (n - w) x i).2.1 (fwdLayer hn (n - w) x i).2.2
                  (termMask hn x i) := by
              ext lit
              simp only [slotClause, clauseOf, Finset.mem_filter, Finset.mem_univ, true_and]
              dsimp only [slotMember, i]
              simp only [ht1, ht2, ↓reduceIte, ↓reduceDIte]
            rw [hcl]
            have hns := hNoSurv i
            dsimp only [survivesFn] at hns
            rw [hiV, Bool.true_and] at hns
            have hts := termScan_spec hn x i w le_rfl
            have hts1 : (termScan hn i w x).1 = true := by
              by_contra hne
              have hf : (termScan hn i w x).1 = false := Bool.eq_false_iff.mpr hne
              have hall : allNat (fun off x' => if h : off < w then wrapLookup hn x' ⟨off, h⟩ i else true) w x = true :=
                (allNat_eq_true _ x w).mpr fun k hk => by simp only [hk, ↓reduceDIte]; exact hts.1 hf k hk
              rw [hall] at hns; cases hns
            rcases hts.2 hts1 with ⟨m0, hm0, hwl, hmask⟩
            have hm_eq : termMask hn x i =
                (fun j => if j.val < w then decide (j.val ≤ m0) else decide (m0 ≤ j.val - w)) :=
              funext hmask
            rw [hm_eq]
            have hfalse : table (posFn n hn (n - w + m0))
                (wrapPat (fwdLayer hn (n - w) x i).2.1 (fwdLayer hn (n - w) x i).2.2 ⟨m0, hm0⟩) = false := by
              dsimp only [wrapLookup] at hwl
              rwa [tabEval_tableInputVec] at hwl
            exact IsDerivation.ax hprev
              (termClause_mem_formula hn hwn table ((hInvAll (n - w) le_rfl).sound i hiV) ⟨m0, hm0⟩ hfalse)
  have hEmpty : (∅ : Clause (Fin n)) ∈ linesFrom hn hKlo x 0 := by
    have h0 := linesFrom_seed_mem hn hwn hKlo hKhi table hReached w le_rfl
      ⟨0, by simp⟩
    have hemp : seedClause (n := n) (w - w) ⟨0, by simp⟩ (seedMaskAt hn hKlo (w - w) (by omega) x ⟨0, by simp⟩) = ∅ := by
      ext lit; simp [seedClause]
    rw [hemp] at h0
    simpa using h0
  refine ⟨⟨by simpa using hDeriv S le_rfl, hEmpty⟩, ?_⟩
  intro D hD
  rw [mem_linesFrom_iff] at hD
  rcases hD with ⟨s, _, hen, rfl⟩
  by_cases hs1 : s.val < K
  · by_cases hsSeed : s.val + 1 < 2 ^ w
    · let d_lev := Nat.log2 (s.val + 1)
      have hd : d_lev < w := by
        by_contra hge
        have hp := Nat.pow_le_pow_right Nat.zero_lt_two (show w ≤ d_lev by omega)
        have hl := Nat.log2_self_le (show s.val + 1 ≠ 0 by omega)
        dsimp [d_lev] at hp hl; omega
      let idx : Fin (2 ^ d_lev) := ⟨s.val + 1 - 2 ^ d_lev, by
        have hlt := Nat.lt_log2_self (n := s.val + 1)
        have hle := Nat.log2_self_le (show s.val + 1 ≠ 0 by omega)
        rw [Nat.pow_succ] at hlt; dsimp [d_lev] at hlt hle ⊢; omega⟩
      have hcl : slotClause hn hKlo x s =
          seedClause d_lev idx (seedMaskAt hn hKlo d_lev (by omega) x idx) := by
        ext lit
        simp only [slotClause, seedClause, Finset.mem_filter, Finset.mem_univ, true_and]
        dsimp only [slotMember, d_lev, idx]
        simp only [hs1, hsSeed, ↓reduceIte, ↓reduceDIte]
      rw [hcl]
      exact (seedClause_card_le d_lev idx _).trans (by omega)
    · dsimp only [slotEnable] at hen; simp [hs1, hsSeed] at hen
  · by_cases hs2 : s.val < K + (n - w) * (3 * K)
    · have hKpos : 0 < K := (Nat.two_pow_pos w).trans_le hKlo
      let h := (s.val - K) / (3 * K)
      let kind := (s.val - K) % (3 * K) / K
      let i : Fin K := ⟨(s.val - K) % (3 * K) % K, Nat.mod_lt _ hKpos⟩
      have hh : h < n - w := (Nat.div_lt_iff_lt_mul (by omega)).mpr (by omega)
      by_cases hk0 : kind = 0
      · have hk0' : (s.val - K) % (3 * K) / K = 0 := hk0
        have hcl : slotClause hn hKlo x s =
            clauseOf h (fwdLayer hn h x i).2.1 (fwdLayer hn h x i).2.2 (bwdMask hn h x i) := by
          ext lit
          simp only [slotClause, clauseOf, Finset.mem_filter, Finset.mem_univ, true_and]
          dsimp only [slotMember, h, i]
          simp only [hs1, hs2, hk0', ↓reduceIte, ↓reduceDIte]
        rw [hcl]
        exact (clauseOf_card_le hn hwn (by omega) _ _ _).trans (by omega)
      · have hk0' : (s.val - K) % (3 * K) / K ≠ 0 := hk0
        by_cases hk1 : kind = 1
        · have hk1' : (s.val - K) % (3 * K) / K = 1 := hk1
          have hcl : slotClause hn hKlo x s = axiomOf h (fwdLayer hn h x i).2.2 false := by
            ext lit
            simp only [slotClause, axiomOf, Finset.mem_filter, Finset.mem_univ, true_and]
            dsimp only [slotMember, h, i]
            simp only [hs1, hs2, hk0', ↓reduceIte, ↓reduceDIte]
            simp only [hk1', ↓reduceIte]
          rw [hcl]
          exact (axiomOf_card_le hn hh _ _).trans (by omega)
        · have hk1' : (s.val - K) % (3 * K) / K ≠ 1 := hk1
          have hcl : slotClause hn hKlo x s = axiomOf h (fwdLayer hn h x i).2.2 true := by
            ext lit
            simp only [slotClause, axiomOf, Finset.mem_filter, Finset.mem_univ, true_and]
            dsimp only [slotMember, h, i]
            simp only [hs1, hs2, hk0', hk1', ↓reduceIte, ↓reduceDIte]
          rw [hcl]
          exact (axiomOf_card_le hn hh _ _).trans (by omega)
    · let i : Fin K := ⟨s.val - (K + (n - w) * (3 * K)), by
        have := s.isLt
        have hS : (3 * (n - w) + 2) * K = K + (n - w) * (3 * K) + K := by ring
        omega⟩
      have hcl : slotClause hn hKlo x s =
          clauseOf (n - w) (fwdLayer hn (n - w) x i).2.1 (fwdLayer hn (n - w) x i).2.2 (termMask hn x i) := by
        ext lit
        simp only [slotClause, clauseOf, Finset.mem_filter, Finset.mem_univ, true_and]
        dsimp only [slotMember, i]
        simp only [hs1, hs2, ↓reduceIte, ↓reduceDIte]
      rw [hcl]
      exact (clauseOf_card_le hn hwn le_rfl _ _ _).trans (by omega)

end PcxSem

end PEqualNP.Outside.L_pcx_220_aux

theorem PEqualNP.Outside.L_pcx_220 :
    ∀ (n w K : ℕ) (hn : 0 < n), w ≤ n → 2 ^ w ≤ K → K ≤ 4 ^ w →
      let I := n * 2 ^ (w + 1)
      let S := (3 * (n - w) + 2) * K
      ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (enable : Fin S → ℕ)
        (memberWire : Fin S → PEqualNP.ProofComplexity.Literal (Fin n) → ℕ),
        PEqualNP.MetaComplexity.FanInTwo C ∧
        PEqualNP.MetaComplexity.NestedCover.ReadsBack I C ∧
        C.size ≤ 262144 * (n + 1) ^ 4 * K ∧ C.output < I + C.size ∧
        (∀ slot, enable slot < I + C.size) ∧
        (∀ slot lit, memberWire slot lit < I + C.size) ∧
        ∀ table : Fin n → (Fin (w + 1) → Bool) → Bool,
          let pos := fun (v : ℕ) => (⟨v % n, Nat.mod_lt _ hn⟩ : Fin n)
          let reached := fun (h : ℕ) =>
            ((Finset.univ : Finset (Fin n → Bool)).filter (fun word =>
              ∀ t : Fin h, table (pos t.val)
                (fun j => word (pos (t.val + j.val))) = true)).image
              (fun x => ((fun a : Fin w => x (pos a.val)),
                         (fun z : Fin w => x (pos (h + z.val)))))
          (∀ h ≤ n - w, (reached h).card ≤ K) →
          let inputs := List.ofFn (fun a : Fin I =>
            table (pos (a.val / 2 ^ (w + 1))) (fun bit => a.val.testBit bit.val))
          let F : Set (PEqualNP.ProofComplexity.Clause (Fin n)) :=
            {D | ∃ (i : Fin n) (p : Fin (w + 1) → Bool), table i p = false ∧
              D = Finset.univ.image (fun k : Fin (w + 1) => (pos (i.val + k.val), !(p k)))}
          let wireVal := fun wire : ℕ => (C.wires inputs).getD wire false
          let lines := ((List.finRange S).filter (fun s => wireVal (enable s))).map
            (fun s => Finset.univ.filter (fun lit => wireVal (memberWire s lit) = true))
          (C.eval inputs = true ↔ ¬ PEqualNP.ProofComplexity.Satisfiable F) ∧
            (C.eval inputs = true → PEqualNP.ProofComplexity.IsRefutation F lines ∧
              ∀ D ∈ lines, D.card ≤ 2 * w + 1) := by
  intro n w K hn hwn hKlo hKhi I S
  obtain ⟨c, hc, gs, hlen, hrb, hfit, hsch⟩ :=
    PEqualNP.Outside.L_pcx_220_aux.PcxBuild.build_all_outputs hn hwn hKlo hKhi
  obtain ⟨outW, houtW_lt, houtW_val⟩ :=
    hsch (PEqualNP.Outside.L_pcx_220_aux.PcxAlgo.evalOutFn (K := K) hn) (Or.inl (Or.inl rfl))
  have hEnAll : ∀ s : Fin S, ∃ wi < I + c,
      ∀ x : Fin I → Bool,
        ((PEqualNP.CircuitLowerBounds.Circuit.mk gs 0).wires (List.ofFn x)).getD wi false =
          PEqualNP.Outside.L_pcx_220_aux.PcxAlgo.slotEnable hn hKlo s x :=
    fun s => hsch _ (Or.inl (Or.inr ⟨s, rfl⟩))
  have hMemAll : ∀ (s : Fin S) (lit : PEqualNP.ProofComplexity.Literal (Fin n)), ∃ wi < I + c,
      ∀ x : Fin I → Bool,
        ((PEqualNP.CircuitLowerBounds.Circuit.mk gs 0).wires (List.ofFn x)).getD wi false =
          PEqualNP.Outside.L_pcx_220_aux.PcxAlgo.slotMember hn hKlo s lit x :=
    fun s lit => hsch _ (Or.inr ⟨s, lit, rfl⟩)
  classical
  let enable : Fin S → ℕ := fun s => Classical.choose (hEnAll s)
  let memberWire : Fin S → PEqualNP.ProofComplexity.Literal (Fin n) → ℕ :=
    fun s lit => Classical.choose (hMemAll s lit)
  let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨gs, outW⟩
  have hCsize : C.size = c := hlen
  have hCwires : ∀ w0, C.wires w0 = (PEqualNP.CircuitLowerBounds.Circuit.mk gs 0).wires w0 :=
    fun _ => rfl
  refine ⟨C, enable, memberWire, hfit, hrb, hCsize.symm ▸ hc, hCsize.symm ▸ houtW_lt,
    fun s => hCsize.symm ▸ (Classical.choose_spec (hEnAll s)).1,
    fun s lit => hCsize.symm ▸ (Classical.choose_spec (hMemAll s lit)).1, ?_⟩
  intro table pos reached hReached inputs F wireVal lines
  let x := PEqualNP.Outside.L_pcx_220_aux.PcxSem.tableInputVec hn table
  have hinputs : inputs = List.ofFn x := rfl
  have hCeval : C.eval inputs = PEqualNP.Outside.L_pcx_220_aux.PcxAlgo.evalOutFn (K := K) hn x := by
    change (C.wires inputs).getD outW false = _
    rw [hinputs, hCwires]
    exact houtW_val x
  have hlines_eq : lines = PEqualNP.Outside.L_pcx_220_aux.PcxSem.linesFrom hn hKlo x 0 := by
    dsimp only [lines, PEqualNP.Outside.L_pcx_220_aux.PcxSem.linesFrom]
    rw [List.drop_zero]
    have hen_eq : (fun s => wireVal (enable s)) =
        (fun s => PEqualNP.Outside.L_pcx_220_aux.PcxAlgo.slotEnable hn hKlo s x) := by
      funext s
      dsimp only [wireVal]
      rw [hinputs, hCwires]
      exact (Classical.choose_spec (hEnAll s)).2 x
    have hmem_eq : (fun s => Finset.univ.filter (fun lit => wireVal (memberWire s lit) = true)) =
        PEqualNP.Outside.L_pcx_220_aux.PcxSem.slotClause hn hKlo x := by
      funext s
      dsimp only [PEqualNP.Outside.L_pcx_220_aux.PcxSem.slotClause]
      congr 1; funext lit
      dsimp only [wireVal]
      rw [hinputs, hCwires, (Classical.choose_spec (hMemAll s lit)).2 x]
    rw [hen_eq, hmem_eq]
  rw [hCeval, hlines_eq]
  exact ⟨PEqualNP.Outside.L_pcx_220_aux.PcxSem.evalOut_iff_unsat hn hwn hKlo hKhi table hReached,
    fun hEv => PEqualNP.Outside.L_pcx_220_aux.PcxSem.lines_isRefutation_and_width
      hn hwn hKlo hKhi table hReached hEv⟩
