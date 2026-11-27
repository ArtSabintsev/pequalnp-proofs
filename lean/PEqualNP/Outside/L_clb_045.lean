import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_clb_045_aux

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (FanInTwo)
open PEqualNP.MetaComplexity.NestedCover (ReadsBack gateAt)

abbrev Sig (N : ℕ) := (Fin N → Bool) → Bool

private def Scheduled (N : ℕ) (k : ℕ) (S : Set (Sig N)) : Prop :=
  ∃ gs : List Gate, gs.length = k ∧ ReadsBack N ⟨gs, 0⟩ ∧ FanInTwo ⟨gs, 0⟩ ∧
    ∀ a ∈ S, ∃ i : ℕ, i < N + k ∧
      ∀ x : Fin N → Bool, ((Circuit.mk gs 0).wires (List.ofFn x)).getD i false = a x

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

private theorem startSched (N : ℕ) :
    Scheduled N 0 (Set.range (fun i : Fin N => fun x : Fin N → Bool => x i)) := by
  refine ⟨[], rfl, by simp [ReadsBack], by simp [FanInTwo], ?_⟩
  intro a ha
  obtain ⟨i, rfl⟩ := Set.mem_range.mp ha
  refine ⟨i.val, by simp, fun x => ?_⟩
  change (List.ofFn x).getD i.val false = x i
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]

private theorem realizeDeps {N k : ℕ} {S : Set (Sig N)} {gs : List Gate}
    (hw : ∀ a ∈ S, ∃ i : ℕ, i < N + k ∧
      ∀ x : Fin N → Bool, ((Circuit.mk gs 0).wires (List.ofFn x)).getD i false = a x)
    (deps : List (Sig N)) (hdeps : ∀ a ∈ deps, a ∈ S) :
    ∃ is : List ℕ, is.length = deps.length ∧ (∀ i ∈ is, i < N + k) ∧
      ∀ x : Fin N → Bool,
        is.map (fun i => ((Circuit.mk gs 0).wires (List.ofFn x)).getD i false) =
          deps.map (fun a => a x) := by
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

private theorem pushSched {N k : ℕ} {S : Set (Sig N)}
    (h : Scheduled N k S) (op : GateOp) (deps : List (Sig N)) (out : Sig N)
    (hop : op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hlen : deps.length ≤ 2) (hdeps : ∀ a ∈ deps, a ∈ S)
    (hval : ∀ x, out x = op.eval (deps.map fun a => a x)) :
    Scheduled N (k + 1) (insert out S) := by
  obtain ⟨gs, hgs, hr, hf, hw⟩ := h
  obtain ⟨is, his, hbound, hvalues⟩ := realizeDeps hw deps hdeps
  let g : Gate := ⟨op, is⟩
  have hlength (x : Fin N → Bool) :
      ((Circuit.mk gs 0).wires (List.ofFn x)).length = N + k := by
    rw [wireLength]; simpa using congrArg (N + ·) hgs
  have hsnoc (x : Fin N → Bool) :
      (Circuit.mk (gs ++ [g]) 0).wires (List.ofFn x) =
        (Circuit.mk gs 0).wires (List.ofFn x) ++ [out x] := by
    simp only [Circuit.wires, List.foldl_append, List.foldl_cons, List.foldl_nil]
    change (Circuit.mk gs 0).wires (List.ofFn x) ++
      [op.eval (is.map fun i => ((Circuit.mk gs 0).wires (List.ofFn x)).getD i false)] =
        (Circuit.mk gs 0).wires (List.ofFn x) ++ [out x]
    rw [hvalues x, hval x]
  refine ⟨gs ++ [g], by simp [hgs], ?_, ?_, ?_⟩
  · intro j hj i hi
    change j < (gs ++ [g]).length at hj
    change i ∈ ((gs ++ [g]).getD j ⟨GateOp.or, []⟩).inputs at hi
    by_cases hj' : j < gs.length
    · rw [List.getD_append _ _ _ _ hj'] at hi
      exact hr j hj' i hi
    · have heq : j = gs.length := by simp at hj; omega
      subst j
      rw [List.getD_append_right _ _ _ _ le_rfl] at hi
      have hi' : i ∈ is := by simpa [g] using hi
      simpa [hgs] using hbound i hi'
  · intro g' hg'
    rcases List.mem_append.mp hg' with hg' | hg'
    · exact hf g' hg'
    · rw [List.mem_singleton.mp hg']
      exact ⟨hop, by change is.length ≤ 2; simpa only [his] using hlen⟩
  · intro a ha
    rcases Set.mem_insert_iff.mp ha with rfl | ha
    · refine ⟨N + k, by omega, fun x => ?_⟩
      rw [hsnoc x, List.getD_append_right _ _ _ _ (by simp [hlength x])]
      simp [hlength x]
    · obtain ⟨i, hi, hval'⟩ := hw a ha
      refine ⟨i, by omega, fun x => ?_⟩
      rw [hsnoc x, List.getD_append _ _ _ _ (by simpa [hlength x] using hi), hval' x]

private theorem finishBits {N k L : ℕ} {S : Set (Sig N)} (hL : 0 < L)
    (h : Scheduled N k S) (bits : Fin L → Sig N) (hbits : ∀ p, bits p ∈ S) :
    ∃ (C : Circuit) (outBit : Fin L → ℕ),
      FanInTwo C ∧ ReadsBack N C ∧ C.size = k ∧
      C.output = outBit ⟨0, hL⟩ ∧ (∀ j, outBit j < N + C.size) ∧
      ∀ (p : Fin L) (x : Fin N → Bool),
        (C.wires (List.ofFn x)).getD (outBit p) false = bits p x := by
  obtain ⟨gs, hgs, hr, hf, hw⟩ := h
  have hcho : ∀ p : Fin L, ∃ i : ℕ, i < N + gs.length ∧
      ∀ x : Fin N → Bool, ((Circuit.mk gs 0).wires (List.ofFn x)).getD i false = bits p x := by
    intro p
    obtain ⟨i, hi, hv⟩ := hw (bits p) (hbits p)
    exact ⟨i, by omega, hv⟩
  choose outBit hlt houtBit using hcho
  refine ⟨⟨gs, outBit ⟨0, hL⟩⟩, outBit, hf, hr, hgs, rfl, hlt, ?_⟩
  intro p x
  exact houtBit p x

private structure Build {N : ℕ} (A B : Set (Sig N)) (b : ℕ) : Prop where
  run : ∀ {k : ℕ} {S : Set (Sig N)}, Scheduled N k S → A ⊆ S →
    ∃ c ≤ b, Scheduled N (k + c) (S ∪ B)

private theorem idleB {N : ℕ} {A B : Set (Sig N)} (h : B ⊆ A) : Build A B 0 :=
  ⟨fun hs ha => ⟨0, le_rfl, by simpa [Set.union_eq_left.mpr (h.trans ha)] using hs⟩⟩

private theorem relaxB {N : ℕ} {A A' B B' : Set (Sig N)} {b b' : ℕ}
    (H : Build A B b) (hA : A ⊆ A') (hB : B' ⊆ A' ∪ B) (hb : b ≤ b') : Build A' B' b' :=
  ⟨fun hs ha => by
    obtain ⟨c, hc, hsc⟩ := H.run hs (hA.trans ha)
    obtain ⟨gs, hgs, hr, hf, hw⟩ := hsc
    refine ⟨c, hc.trans hb, gs, hgs, hr, hf, fun a hmem => ?_⟩
    rcases hmem with h1 | h2
    · exact hw a (Or.inl h1)
    · rcases hB h2 with h2a | h2b
      · exact hw a (Or.inl (ha h2a))
      · exact hw a (Or.inr h2b)⟩

private theorem seqB {N : ℕ} {A B C : Set (Sig N)} {b c : ℕ}
    (H1 : Build A B b) (H2 : Build (A ∪ B) C c) : Build A (B ∪ C) (b + c) :=
  ⟨fun hs ha => by
    obtain ⟨c1, hc1, hs1⟩ := H1.run hs ha
    obtain ⟨c2, hc2, hs2⟩ := H2.run hs1
      (Set.union_subset (ha.trans Set.subset_union_left) Set.subset_union_right)
    refine ⟨c1 + c2, Nat.add_le_add hc1 hc2, ?_⟩
    simpa [Nat.add_assoc, Set.union_assoc] using hs2⟩

private theorem gateB {N : ℕ} {A : Set (Sig N)} (op : GateOp) (deps : List (Sig N)) (out : Sig N)
    (hop : op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hlen : deps.length ≤ 2) (hdeps : ∀ a ∈ deps, a ∈ A)
    (hval : ∀ x, out x = op.eval (deps.map fun a => a x)) :
    Build A {out} 1 :=
  ⟨fun hs ha => ⟨1, le_rfl, by
    simpa [Set.union_singleton] using
      pushSched hs op deps out hop hlen (fun a hm => ha (hdeps a hm)) hval⟩⟩

private theorem constB {N : ℕ} {A : Set (Sig N)} (b : Bool) : Build A {fun _ => b} 1 := by
  cases b with
  | false => exact gateB .or [] (fun _ => false) (by simp) (by simp) (by simp) (fun _ => rfl)
  | true => exact gateB .and [] (fun _ => true) (by simp) (by simp) (by simp) (fun _ => rfl)

private theorem notB {N : ℕ} {A : Set (Sig N)} {f : Sig N} (hf : f ∈ A) :
    Build A {fun x => !(f x)} 1 :=
  gateB .not [f] (fun x => !(f x)) (by simp) (by simp) (by simpa using hf) (fun _ => rfl)

private theorem andB {N : ℕ} {A : Set (Sig N)} {f g : Sig N} (hf : f ∈ A) (hg : g ∈ A) :
    Build A {fun x => f x && g x} 1 :=
  gateB .and [f, g] (fun x => f x && g x) (by simp) (by simp)
    (by intro a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha; rcases ha with rfl | rfl <;> assumption)
    (fun _ => by simp [GateOp.eval])

private theorem orB {N : ℕ} {A : Set (Sig N)} {f g : Sig N} (hf : f ∈ A) (hg : g ∈ A) :
    Build A {fun x => f x || g x} 1 :=
  gateB .or [f, g] (fun x => f x || g x) (by simp) (by simp)
    (by intro a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha; rcases ha with rfl | rfl <;> assumption)
    (fun _ => by simp [GateOp.eval])

private theorem listB {N : ℕ} {α : Type*} {A : Set (Sig N)} (F : α → Set (Sig N)) (c : ℕ)
    (xs : List α) (h : ∀ a ∈ xs, Build A (F a) c) :
    Build A (⋃ a ∈ xs, F a) (xs.length * c) := by
  induction xs with
  | nil =>
    simp only [List.length_nil, Nat.zero_mul]
    exact idleB (by simp)
  | cons a xs ih =>
    have h1 := h a List.mem_cons_self
    have h2 : Build (A ∪ F a) (⋃ b ∈ xs, F b) (xs.length * c) :=
      relaxB (ih (fun b hb => h b (List.mem_cons_of_mem a hb)))
        Set.subset_union_left Set.subset_union_right le_rfl
    have hseq := seqB h1 h2
    refine relaxB hseq le_rfl ?_ (by simp [Nat.succ_mul, Nat.add_comm])
    intro f hf
    simp only [Set.mem_iUnion, List.mem_cons] at hf
    rcases hf with ⟨b, rfl | hb, hfb⟩
    · exact Or.inr (Or.inl hfb)
    · exact Or.inr (Or.inr (Set.mem_iUnion.mpr ⟨b, Set.mem_iUnion.mpr ⟨hb, hfb⟩⟩))

private theorem andListB {N : ℕ} {A : Set (Sig N)} (xs : List (Sig N))
    (hxs : ∀ f ∈ xs, f ∈ A) (htrue : (fun _ => true) ∈ A) :
    Build A {fun x => xs.all (fun f => f x)} xs.length := by
  induction xs with
  | nil =>
    exact idleB (by simpa using htrue)
  | cons f xs ih =>
    have h1 := ih (fun g hg => hxs g (List.mem_cons_of_mem f hg))
    have h2 : Build (A ∪ {fun x => xs.all (fun g => g x)})
        {fun x => (f :: xs).all (fun g => g x)} 1 := by
      have heq : (fun x => (f :: xs).all (fun g => g x)) =
          (fun x => f x && xs.all (fun g => g x)) := by
        funext x; simp [List.all_cons]
      rw [heq]
      exact andB (Or.inl (hxs f List.mem_cons_self)) (Or.inr rfl)
    exact relaxB (seqB h1 h2) le_rfl (by intro a ha; exact Or.inr (Or.inr ha)) (by simp)

private def faSum (a b c : Bool) : Bool := xor (xor a b) c

private def faCarry (a b c : Bool) : Bool := (a && b) || (xor a b && c)

private theorem xor_eq_or_and_not_and (a b : Bool) :
    xor a b = ((a || b) && !(a && b)) := by
  cases a <;> cases b <;> rfl

private theorem fullAdderB {N : ℕ} {A : Set (Sig N)} {fa fb fc : Sig N}
    (ha : fa ∈ A) (hb : fb ∈ A) (hc : fc ∈ A) :
    Build A ({fun x => faSum (fa x) (fb x) (fc x), fun x => faCarry (fa x) (fb x) (fc x)}) 9 := by
  let abOr : Sig N := fun x => fa x || fb x
  let abAnd : Sig N := fun x => fa x && fb x
  let abNand : Sig N := fun x => !(abAnd x)
  let t1 : Sig N := fun x => abOr x && abNand x
  let tcOr : Sig N := fun x => t1 x || fc x
  let tcAnd : Sig N := fun x => t1 x && fc x
  let tcNand : Sig N := fun x => !(tcAnd x)
  let sOut : Sig N := fun x => tcOr x && tcNand x
  let cOut : Sig N := fun x => abAnd x || tcAnd x
  have h1 : Build A {abOr} 1 := orB ha hb
  have h2 : Build (A ∪ {abOr}) {abAnd} 1 := andB (Or.inl ha) (Or.inl hb)
  have h3 : Build (A ∪ ({abOr} ∪ {abAnd})) {abNand} 1 := notB (Or.inr (Or.inr rfl))
  have h4 : Build (A ∪ (({abOr} ∪ {abAnd}) ∪ {abNand})) {t1} 1 :=
    andB (Or.inr (Or.inl (Or.inl rfl))) (Or.inr (Or.inr rfl))
  have h5 : Build (A ∪ ((({abOr} ∪ {abAnd}) ∪ {abNand}) ∪ {t1})) {tcOr} 1 :=
    orB (Or.inr (Or.inr rfl)) (Or.inl hc)
  have h6 : Build (A ∪ (((({abOr} ∪ {abAnd}) ∪ {abNand}) ∪ {t1}) ∪ {tcOr})) {tcAnd} 1 :=
    andB (Or.inr (Or.inl (Or.inr rfl))) (Or.inl hc)
  have h7 : Build (A ∪ ((((({abOr} ∪ {abAnd}) ∪ {abNand}) ∪ {t1}) ∪ {tcOr}) ∪ {tcAnd})) {tcNand} 1 :=
    notB (Or.inr (Or.inr rfl))
  have h8 : Build (A ∪ (((((({abOr} ∪ {abAnd}) ∪ {abNand}) ∪ {t1}) ∪ {tcOr}) ∪ {tcAnd}) ∪ {tcNand})) {sOut} 1 :=
    andB (Or.inr (Or.inl (Or.inl (Or.inr rfl)))) (Or.inr (Or.inr rfl))
  have h9 : Build (A ∪ ((((((({abOr} ∪ {abAnd}) ∪ {abNand}) ∪ {t1}) ∪ {tcOr}) ∪ {tcAnd}) ∪ {tcNand}) ∪ {sOut})) {cOut} 1 :=
    orB (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr rfl))))))))
        (Or.inr (Or.inl (Or.inl (Or.inr rfl))))
  have hall := seqB (seqB (seqB (seqB (seqB (seqB (seqB (seqB h1 h2) h3) h4) h5) h6) h7) h8) h9
  have hsEq : sOut = fun x => faSum (fa x) (fb x) (fc x) := by
    funext x
    simp only [sOut, tcOr, tcNand, tcAnd, t1, abOr, abNand, abAnd, faSum]
    rw [xor_eq_or_and_not_and (fa x) (fb x), xor_eq_or_and_not_and _ (fc x)]
  have hcEq : cOut = fun x => faCarry (fa x) (fb x) (fc x) := by
    funext x
    simp only [cOut, tcAnd, t1, abOr, abNand, abAnd, faCarry]
    rw [xor_eq_or_and_not_and (fa x) (fb x)]
  refine relaxB hall le_rfl ?_ (by omega)
  intro f hf
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hf
  rcases hf with rfl | rfl
  · rw [← hsEq]
    exact Or.inr (Or.inl (Or.inr rfl))
  · rw [← hcEq]
    exact Or.inr (Or.inr rfl)

private def rippleCarry (a b : ℕ) : ℕ → Bool
  | 0 => false
  | j + 1 => faCarry (a.testBit j) (b.testBit j) (rippleCarry a b j)

private theorem testBit_eq_decide_div_mod (x j : ℕ) :
    x.testBit j = decide ((x / 2 ^ j) % 2 = 1) := by
  rw [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.one_and_eq_mod_two]
  have hlt : (x / 2 ^ j) % 2 < 2 := Nat.mod_lt _ (by omega)
  have hcases : (x / 2 ^ j) % 2 = 0 ∨ (x / 2 ^ j) % 2 = 1 := by omega
  rcases hcases with h | h <;> simp [h]

private theorem mod_two_pow_succ_eq (a j : ℕ) :
    a % 2 ^ (j + 1) = a % 2 ^ j + (if a.testBit j then 2 ^ j else 0) := by
  have hpos : 0 < 2 ^ j := Nat.two_pow_pos j
  have hdiv1 := Nat.div_add_mod a (2 ^ j)
  have hdiv2 := Nat.div_add_mod (a / 2 ^ j) 2
  have ha_eq : a = (a % 2 ^ j + 2 ^ j * ((a / 2 ^ j) % 2)) + 2 ^ (j + 1) * (a / 2 ^ j / 2) := by
    rw [Nat.pow_succ]
    have h1 : 2 ^ j * (a / 2 ^ j) = 2 ^ j * (2 * (a / 2 ^ j / 2) + (a / 2 ^ j) % 2) := by
      rw [hdiv2]
    rw [Nat.mul_add] at h1
    have h2 : 2 ^ j * (2 * (a / 2 ^ j / 2)) = 2 ^ j * 2 * (a / 2 ^ j / 2) := by ring
    omega
  have hlt_rem : a % 2 ^ j + 2 ^ j * ((a / 2 ^ j) % 2) < 2 ^ (j + 1) := by
    have h1 : a % 2 ^ j < 2 ^ j := Nat.mod_lt _ hpos
    have h2 : (a / 2 ^ j) % 2 ≤ 1 := by have := Nat.mod_lt (a / 2 ^ j) (by omega : 0 < 2); omega
    have h3 : 2 ^ j * ((a / 2 ^ j) % 2) ≤ 2 ^ j := by
      calc 2 ^ j * ((a / 2 ^ j) % 2) ≤ 2 ^ j * 1 := Nat.mul_le_mul_left _ h2
        _ = 2 ^ j := Nat.mul_one _
    rw [Nat.pow_succ]; omega
  have h1 : a % 2 ^ (j + 1) = a % 2 ^ j + 2 ^ j * ((a / 2 ^ j) % 2) := by
    conv_lhs => rw [ha_eq]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt_rem]
  rw [h1, testBit_eq_decide_div_mod a j]
  have hcases : (a / 2 ^ j) % 2 = 0 ∨ (a / 2 ^ j) % 2 = 1 := by
    have := Nat.mod_lt (a / 2 ^ j) (by omega : 0 < 2); omega
  rcases hcases with h | h <;> simp [h]

private theorem rippleCarry_spec (a b : ℕ) :
    ∀ j : ℕ,
      rippleCarry a b j = decide (2 ^ j ≤ a % 2 ^ j + b % 2 ^ j) ∧
      (a + b).testBit j = faSum (a.testBit j) (b.testBit j) (rippleCarry a b j) := by
  intro j
  have hcarry : ∀ k : ℕ, rippleCarry a b k = decide (2 ^ k ≤ a % 2 ^ k + b % 2 ^ k) := by
    intro k
    induction k with
    | zero => simp [rippleCarry, Nat.mod_one]
    | succ k ih =>
      unfold rippleCarry
      rw [ih, mod_two_pow_succ_eq a k, mod_two_pow_succ_eq b k]
      have ha_lt : a % 2 ^ k < 2 ^ k := Nat.mod_lt _ (Nat.two_pow_pos k)
      have hb_lt : b % 2 ^ k < 2 ^ k := Nat.mod_lt _ (Nat.two_pow_pos k)
      have hp : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
      cases h1 : a.testBit k <;> cases h2 : b.testBit k <;>
        by_cases h3 : 2 ^ k ≤ a % 2 ^ k + b % 2 ^ k <;>
        simp [faCarry, h3, hp] <;> omega
  refine ⟨hcarry j, ?_⟩
  rw [hcarry j]
  have hdiv : (a + b) / 2 ^ j =
      a / 2 ^ j + b / 2 ^ j + (a % 2 ^ j + b % 2 ^ j) / 2 ^ j := by
    have ha := Nat.div_add_mod a (2 ^ j)
    have hb := Nat.div_add_mod b (2 ^ j)
    have hpos : 0 < 2 ^ j := Nat.two_pow_pos j
    have hsum : a + b = (a % 2 ^ j + b % 2 ^ j) + (a / 2 ^ j + b / 2 ^ j) * 2 ^ j := by
      have : 2 ^ j * (a / 2 ^ j) = (a / 2 ^ j) * 2 ^ j := Nat.mul_comm _ _
      have : 2 ^ j * (b / 2 ^ j) = (b / 2 ^ j) * 2 ^ j := Nat.mul_comm _ _
      rw [Nat.add_mul]; omega
    rw [hsum, Nat.add_mul_div_right _ _ hpos]
    omega
  have hcdiv : (a % 2 ^ j + b % 2 ^ j) / 2 ^ j = if 2 ^ j ≤ a % 2 ^ j + b % 2 ^ j then 1 else 0 := by
    have ha_lt : a % 2 ^ j < 2 ^ j := Nat.mod_lt _ (Nat.two_pow_pos j)
    have hb_lt : b % 2 ^ j < 2 ^ j := Nat.mod_lt _ (Nat.two_pow_pos j)
    by_cases hle : 2 ^ j ≤ a % 2 ^ j + b % 2 ^ j
    · simp only [hle, ↓reduceIte]
      have hsub : a % 2 ^ j + b % 2 ^ j = (a % 2 ^ j + b % 2 ^ j - 2 ^ j) + 1 * 2 ^ j := by omega
      rw [hsub, Nat.add_mul_div_right _ _ (Nat.two_pow_pos j), Nat.div_eq_of_lt (by omega)]
    · simp only [hle, ↓reduceIte]
      exact Nat.div_eq_of_lt (by omega)
  rw [testBit_eq_decide_div_mod (a + b) j, testBit_eq_decide_div_mod a j,
    testBit_eq_decide_div_mod b j, hdiv, hcdiv]
  have ha2 : (a / 2 ^ j) % 2 = 0 ∨ (a / 2 ^ j) % 2 = 1 := by
    have := Nat.mod_lt (a / 2 ^ j) (by omega : 0 < 2); omega
  have hb2 : (b / 2 ^ j) % 2 = 0 ∨ (b / 2 ^ j) % 2 = 1 := by
    have := Nat.mod_lt (b / 2 ^ j) (by omega : 0 < 2); omega
  have hmod : (a / 2 ^ j + b / 2 ^ j + if 2 ^ j ≤ a % 2 ^ j + b % 2 ^ j then 1 else 0) % 2 =
      ((a / 2 ^ j) % 2 + (b / 2 ^ j) % 2 + if 2 ^ j ≤ a % 2 ^ j + b % 2 ^ j then 1 else 0) % 2 := by
    omega
  rw [hmod]
  by_cases hc : 2 ^ j ≤ a % 2 ^ j + b % 2 ^ j <;>
  rcases ha2 with ha | ha <;>
  rcases hb2 with hb | hb <;>
  simp [faSum, hc, ha, hb]

private def bitsOf {N : ℕ} (L : ℕ) (F : (Fin N → Bool) → ℕ) : Fin L → Sig N :=
  fun j x => (F x).testBit j.val

private theorem rippleB {N : ℕ} {A : Set (Sig N)} (F G : (Fin N → Bool) → ℕ)
    (hfalse : (fun _ => false) ∈ A) :
    ∀ L : ℕ,
      (∀ j : Fin L, (fun x => (F x).testBit j.val) ∈ A) →
      (∀ j : Fin L, (fun x => (G x).testBit j.val) ∈ A) →
      Build A
        ((Set.range (bitsOf L (fun x => F x + G x))) ∪ {fun x => rippleCarry (F x) (G x) L})
        (9 * L) := by
  intro L
  induction L with
  | zero =>
    intro _ _
    simp only [Nat.mul_zero]
    apply idleB
    intro f hf
    rcases hf with ⟨j, _⟩ | rfl
    · exact Fin.elim0 j
    · exact hfalse
  | succ L ih =>
    intro hF hG
    have hprev := ih (fun j => hF j.castSucc) (fun j => hG j.castSucc)
    have hstep : Build
        (A ∪ (Set.range (bitsOf L (fun x => F x + G x)) ∪ {fun x => rippleCarry (F x) (G x) L}))
        ({fun x => faSum ((F x).testBit L) ((G x).testBit L) (rippleCarry (F x) (G x) L),
          fun x => faCarry ((F x).testBit L) ((G x).testBit L) (rippleCarry (F x) (G x) L)}) 9 :=
      fullAdderB (Or.inl (hF (Fin.last L))) (Or.inl (hG (Fin.last L))) (Or.inr (Or.inr rfl))
    have hseq := seqB hprev hstep
    refine relaxB hseq le_rfl ?_ (by omega)
    intro f hf
    rcases hf with ⟨j, rfl⟩ | rfl
    · by_cases hj : j.val < L
      · have hjeq : bitsOf (L + 1) (fun x => F x + G x) j =
            bitsOf L (fun x => F x + G x) ⟨j.val, hj⟩ := rfl
        rw [hjeq]
        exact Or.inr (Or.inl (Or.inl ⟨⟨j.val, hj⟩, rfl⟩))
      · have hjeq : j.val = L := by omega
        have hfeq : bitsOf (L + 1) (fun x => F x + G x) j =
            fun x => faSum ((F x).testBit L) ((G x).testBit L) (rippleCarry (F x) (G x) L) := by
          funext x
          unfold bitsOf
          rw [hjeq]
          exact (rippleCarry_spec (F x) (G x) L).2
        rw [hfeq]
        exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))

private theorem sumTwoB {N : ℕ} {A : Set (Sig N)} (L : ℕ) (F G : (Fin N → Bool) → ℕ)
    (hfalse : (fun _ => false) ∈ A)
    (hF : ∀ j : Fin L, bitsOf L F j ∈ A)
    (hG : ∀ j : Fin L, bitsOf L G j ∈ A) :
    Build A (Set.range (bitsOf L (fun x => F x + G x))) (9 * L) :=
  relaxB (rippleB F G hfalse L hF hG) le_rfl
    (fun _ hf => Or.inr (Or.inl hf)) le_rfl

private theorem maskB {N : ℕ} {A : Set (Sig N)} (L : ℕ) (f : Sig N) (F : (Fin N → Bool) → ℕ)
    (hf : f ∈ A) (hF : ∀ j : Fin L, bitsOf L F j ∈ A) :
    Build A (Set.range (bitsOf L (fun x => if f x then F x else 0))) L := by
  have h1 := listB (A := A) (fun j : Fin L => {fun x => f x && bitsOf L F j x}) 1
    (List.finRange L) (fun j _ => andB hf (hF j))
  refine relaxB h1 le_rfl ?_ (by simp)
  intro g hg
  obtain ⟨j, rfl⟩ := Set.mem_range.mp hg
  have heq : bitsOf L (fun x => if f x then F x else 0) j = fun x => f x && bitsOf L F j x := by
    funext x
    unfold bitsOf
    cases hf' : f x <;> simp [hf']
  rw [heq]
  exact Or.inr (Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨List.mem_finRange j, rfl⟩⟩)

private theorem maskPairAddB {N : ℕ} {A : Set (Sig N)} (L : ℕ)
    (f0 f1 : Sig N) (F0 F1 : (Fin N → Bool) → ℕ)
    (hfalse : (fun _ => false) ∈ A)
    (hf0 : f0 ∈ A) (hf1 : f1 ∈ A)
    (hF0 : ∀ j : Fin L, bitsOf L F0 j ∈ A)
    (hF1 : ∀ j : Fin L, bitsOf L F1 j ∈ A) :
    Build A
      (Set.range (bitsOf L (fun x => (if f0 x then F0 x else 0) + (if f1 x then F1 x else 0))))
      (11 * L) := by
  let M0 := fun x => if f0 x then F0 x else 0
  let M1 := fun x => if f1 x then F1 x else 0
  have h1 : Build A (Set.range (bitsOf L M0)) L := maskB L f0 F0 hf0 hF0
  have h2 : Build (A ∪ Set.range (bitsOf L M0)) (Set.range (bitsOf L M1)) L :=
    maskB L f1 F1 (Or.inl hf1) (fun j => Or.inl (hF1 j))
  have h3 : Build (A ∪ (Set.range (bitsOf L M0) ∪ Set.range (bitsOf L M1)))
      (Set.range (bitsOf L (fun x => M0 x + M1 x))) (9 * L) :=
    sumTwoB L M0 M1 (Or.inl hfalse)
      (fun j => Or.inr (Or.inl ⟨j, rfl⟩))
      (fun j => Or.inr (Or.inr ⟨j, rfl⟩))
  exact relaxB (seqB (seqB h1 h2) h3) le_rfl
    (fun _ hf => Or.inr (Or.inr hf)) (by omega)

private def sumListVal {N : ℕ} : List ((Fin N → Bool) → ℕ) → (Fin N → Bool) → ℕ
  | [] => fun _ => 0
  | f :: fs => fun x => f x + sumListVal fs x

private theorem sumListVal_eq_sum {N : ℕ} (fs : List ((Fin N → Bool) → ℕ)) (x : Fin N → Bool) :
    sumListVal fs x = (fs.map (fun f => f x)).sum := by
  induction fs with
  | nil => rfl
  | cons f fs ih => simp [sumListVal, ih]

private theorem sumListB {N : ℕ} {A : Set (Sig N)} (L : ℕ) (fs : List ((Fin N → Bool) → ℕ))
    (hfalse : (fun _ => false) ∈ A)
    (hfs : ∀ f ∈ fs, ∀ j : Fin L, bitsOf L f j ∈ A) :
    Build A (Set.range (bitsOf L (sumListVal fs))) (fs.length * (9 * L)) := by
  induction fs with
  | nil =>
    simp only [List.length_nil, Nat.zero_mul]
    apply idleB
    intro g hg
    obtain ⟨j, rfl⟩ := Set.mem_range.mp hg
    have : bitsOf (N := N) L (sumListVal []) j = fun _ => false := by
      funext x; simp [bitsOf, sumListVal]
    rw [this]; exact hfalse
  | cons f fs ih =>
    have h1 := ih (fun g hg => hfs g (List.mem_cons_of_mem f hg))
    have h2 : Build (A ∪ Set.range (bitsOf L (sumListVal fs)))
        (Set.range (bitsOf L (fun x => f x + sumListVal fs x))) (9 * L) :=
      sumTwoB L f (sumListVal fs) (Or.inl hfalse)
        (fun j => Or.inl (hfs f List.mem_cons_self j))
        (fun j => Or.inr ⟨j, rfl⟩)
    exact relaxB (seqB h1 h2) le_rfl (fun _ hg => Or.inr (Or.inr hg))
      (by simp only [List.length_cons, Nat.succ_mul]; exact le_rfl)

private def encodeBits {k : ℕ} (f : Fin k → Bool) : Fin (2 ^ k) :=
  ⟨∑ t : Fin k, if f t then 2 ^ t.val else 0, by
    induction k with
    | zero => simp
    | succ k' ih =>
      rw [Fin.sum_univ_castSucc, Nat.pow_succ]
      simp only [Fin.val_castSucc, Fin.val_last]
      have h1 := ih (fun t : Fin k' => f t.castSucc)
      have h2 : (if f (Fin.last k') = true then 2 ^ k' else 0) ≤ 2 ^ k' := by
        split_ifs <;> omega
      omega⟩

private theorem encodeBits_testBit {k : ℕ} (f : Fin k → Bool) (t : ℕ) (ht : t < k) :
    (encodeBits f).val.testBit t = f ⟨t, ht⟩ := by
  induction k with
  | zero => omega
  | succ k' ih =>
    have hsplit : (encodeBits f).val =
        (encodeBits (fun j : Fin k' => f j.castSucc)).val +
        (if f (Fin.last k') then 2 ^ k' else 0) := by
      unfold encodeBits
      simp only [Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last]
    rw [hsplit]
    have hlt := (encodeBits (fun j : Fin k' => f j.castSucc)).isLt
    cases hf : f (Fin.last k') with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      by_cases htk : t < k'
      · exact ih (fun j => f j.castSucc) htk
      · have hteq : t = k' := by omega
        subst hteq
        rw [Nat.testBit_lt_two_pow hlt]
        have : (⟨t, ht⟩ : Fin (t + 1)) = Fin.last t := Fin.ext rfl
        rw [this, hf]
    | true =>
      simp only [↓reduceIte]
      rw [Nat.add_comm]
      by_cases htk : t < k'
      · rw [Nat.testBit_two_pow_add_gt htk]
        exact ih (fun j => f j.castSucc) htk
      · have hteq : t = k' := by omega
        subst hteq
        rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hlt]
        have : (⟨t, ht⟩ : Fin (t + 1)) = Fin.last t := Fin.ext rfl
        rw [this, hf]
        rfl

private def winIdx (d : ℕ) (s : Fin (2 ^ d)) (b : Bool) : ℕ :=
  s.val + if b then 2 ^ d else 0

private theorem winIdx_lt (d : ℕ) (s : Fin (2 ^ d)) (b : Bool) :
    winIdx d s b < 2 ^ (d + 1) := by
  unfold winIdx
  have hs := s.isLt
  rw [Nat.pow_succ]
  cases b <;> simp <;> omega

private theorem winIdx_testBit (d : ℕ) (s : Fin (2 ^ d)) (b : Bool) (t : ℕ) (ht : t < d + 1) :
    (winIdx d s b).testBit t = if t < d then s.val.testBit t else b := by
  unfold winIdx
  cases b with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
    split_ifs with h
    · rfl
    · have hteq : t = d := by omega
      rw [hteq]
      exact Nat.testBit_lt_two_pow s.isLt
  | true =>
    simp only [↓reduceIte]
    rw [Nat.add_comm]
    split_ifs with h
    · exact Nat.testBit_two_pow_add_gt h s.val
    · have hteq : t = d := by omega
      rw [hteq, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow s.isLt]
      rfl

private def nextS {d : ℕ} (s : Fin (2 ^ d)) (b : Bool) : Fin (2 ^ d) :=
  ⟨winIdx d s b / 2, by
    have h := winIdx_lt d s b
    rw [Nat.pow_succ] at h
    omega⟩

private theorem nextS_testBit {d : ℕ} (s : Fin (2 ^ d)) (b : Bool) (t : ℕ) (ht : t < d) :
    (nextS s b).val.testBit t = if t + 1 < d then s.val.testBit (t + 1) else b := by
  change (winIdx d s b / 2).testBit t = _
  rw [Nat.testBit_div_two]
  exact winIdx_testBit d s b (t + 1) (by omega)

private def topBit {d' : ℕ} (t : Fin (2 ^ (d' + 1))) : Bool :=
  decide (2 ^ d' ≤ t.val)

private def pred0 {d' : ℕ} (t : Fin (2 ^ (d' + 1))) : Fin (2 ^ (d' + 1)) :=
  ⟨2 * (if 2 ^ d' ≤ t.val then t.val - 2 ^ d' else t.val), by
    have ht := t.isLt
    have hp : 2 ^ (d' + 1) = 2 ^ d' * 2 := Nat.pow_succ 2 d'
    split_ifs <;> omega⟩

private def pred1 {d' : ℕ} (t : Fin (2 ^ (d' + 1))) : Fin (2 ^ (d' + 1)) :=
  ⟨2 * (if 2 ^ d' ≤ t.val then t.val - 2 ^ d' else t.val) + 1, by
    have ht := t.isLt
    have hp : 2 ^ (d' + 1) = 2 ^ d' * 2 := Nat.pow_succ 2 d'
    split_ifs <;> omega⟩

private theorem pred0_ne_pred1 {d' : ℕ} (t : Fin (2 ^ (d' + 1))) : pred0 t ≠ pred1 t := by
  intro h
  have := congrArg Fin.val h
  simp only [pred0, pred1] at this
  omega

private theorem nextS_eq_iff_pred {d' : ℕ} (s t : Fin (2 ^ (d' + 1))) (b : Bool) :
    nextS s b = t ↔ b = topBit t ∧ (s = pred0 t ∨ s = pred1 t) := by
  have hs := s.isLt
  have ht := t.isLt
  have hp : 2 ^ (d' + 1) = 2 ^ d' * 2 := Nat.pow_succ 2 d'
  simp only [Fin.ext_iff, nextS, winIdx, topBit, pred0, pred1]
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] <;>
    split_ifs <;> (simp; omega)

private def perIdx (n w : ℕ) (s : Fin (2 ^ min w (n - 1))) (b : Bool) : Fin (2 ^ (w + 1)) :=
  encodeBits (fun p : Fin (w + 1) => (winIdx (min w (n - 1)) s b).testBit (p.val % n))

private def tblWireIdx (n m w : ℕ) (i : Fin m) (s : Fin (2 ^ min w (n - 1))) (b : Bool) :
    Fin (m * 2 ^ (w + 1) + 2 * n) :=
  ⟨i.val * 2 ^ (w + 1) + (perIdx n w s b).val, by
    have hp := (perIdx n w s b).isLt
    have h1 : (i.val + 1) * 2 ^ (w + 1) ≤ m * 2 ^ (w + 1) := Nat.mul_le_mul_right _ i.isLt
    rw [Nat.add_mul, Nat.one_mul] at h1
    omega⟩

private def allowWireIdx (n m w : ℕ) (j : Fin n) (b : Bool) :
    Fin (m * 2 ^ (w + 1) + 2 * n) :=
  ⟨m * 2 ^ (w + 1) + (2 * j.val + if b then 1 else 0), by
    have hj := j.isLt
    cases b with
    | false => simp only [Bool.false_eq_true, ↓reduceIte]; omega
    | true => simp only [↓reduceIte]; omega⟩

private def tblSig (n m w : ℕ) (i : Fin m) (s : Fin (2 ^ min w (n - 1))) (b : Bool) :
    Sig (m * 2 ^ (w + 1) + 2 * n) :=
  fun x => x (tblWireIdx n m w i s b)

private def allowSig (n m w : ℕ) (j : Fin n) (b : Bool) :
    Sig (m * 2 ^ (w + 1) + 2 * n) :=
  fun x => x (allowWireIdx n m w j b)

private def wiresInFn {n m w : ℕ} (hn : 0 < n) (hm : 0 < m)
    (table : Fin m → (Fin (w + 1) → Bool) → Bool) (allow : Fin n → Bool → Bool) :
    Fin (m * 2 ^ (w + 1) + 2 * n) → Bool :=
  fun a =>
    if a.val < m * 2 ^ (w + 1) then
      table ⟨(a.val / 2 ^ (w + 1)) % m, Nat.mod_lt _ hm⟩
        (fun b => (a.val % 2 ^ (w + 1)).testBit b.val)
    else
      let t := a.val - m * 2 ^ (w + 1)
      allow ⟨(t / 2) % n, Nat.mod_lt _ hn⟩ (decide (t % 2 = 1))

private theorem tblSig_wiresInFn {n m w : ℕ} (hn : 0 < n) (hm : 0 < m)
    (table : Fin m → (Fin (w + 1) → Bool) → Bool) (allow : Fin n → Bool → Bool)
    (i : Fin m) (s : Fin (2 ^ min w (n - 1))) (b : Bool) :
    tblSig n m w i s b (wiresInFn hn hm table allow) =
      table i (fun p => (winIdx (min w (n - 1)) s b).testBit (p.val % n)) := by
  unfold tblSig wiresInFn tblWireIdx
  have hp := (perIdx n w s b).isLt
  have h1 : (i.val + 1) * 2 ^ (w + 1) ≤ m * 2 ^ (w + 1) := Nat.mul_le_mul_right _ i.isLt
  rw [Nat.add_mul, Nat.one_mul] at h1
  have hlt : i.val * 2 ^ (w + 1) + (perIdx n w s b).val < m * 2 ^ (w + 1) := by omega
  simp only [hlt, ↓reduceIte]
  have hpos : 0 < 2 ^ (w + 1) := Nat.two_pow_pos _
  have hdiv : (i.val * 2 ^ (w + 1) + (perIdx n w s b).val) / 2 ^ (w + 1) = i.val := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hp, Nat.zero_add]
  have hmod1 : ((i.val * 2 ^ (w + 1) + (perIdx n w s b).val) / 2 ^ (w + 1)) % m = i.val := by
    rw [hdiv, Nat.mod_eq_of_lt i.isLt]
  have hmod2 : (i.val * 2 ^ (w + 1) + (perIdx n w s b).val) % 2 ^ (w + 1) = (perIdx n w s b).val := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hp]
  have hfin : (⟨((i.val * 2 ^ (w + 1) + (perIdx n w s b).val) / 2 ^ (w + 1)) % m,
      Nat.mod_lt _ hm⟩ : Fin m) = i := Fin.ext hmod1
  rw [hfin]
  congr 1
  funext p
  rw [hmod2]
  exact encodeBits_testBit _ p.val p.isLt

private theorem allowSig_wiresInFn {n m w : ℕ} (hn : 0 < n) (hm : 0 < m)
    (table : Fin m → (Fin (w + 1) → Bool) → Bool) (allow : Fin n → Bool → Bool)
    (j : Fin n) (b : Bool) :
    allowSig n m w j b (wiresInFn hn hm table allow) = allow j b := by
  unfold allowSig wiresInFn allowWireIdx
  have hnot : ¬ (m * 2 ^ (w + 1) + (2 * j.val + if b then 1 else 0) < m * 2 ^ (w + 1)) := by omega
  simp only [hnot, ↓reduceIte, Nat.add_sub_cancel_left]
  have hj := j.isLt
  cases b with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
    have hdiv : (2 * j.val) / 2 = j.val := by omega
    have hmod : (2 * j.val) % 2 = 0 := by omega
    have hfin : (⟨((2 * j.val) / 2) % n, Nat.mod_lt _ hn⟩ : Fin n) = j := by
      apply Fin.ext; dsimp only; rw [hdiv, Nat.mod_eq_of_lt hj]
    rw [hfin, hmod]
    rfl
  | true =>
    simp only [↓reduceIte]
    have hdiv : (2 * j.val + 1) / 2 = j.val := by omega
    have hmod : (2 * j.val + 1) % 2 = 1 := by omega
    have hfin : (⟨((2 * j.val + 1) / 2) % n, Nat.mod_lt _ hn⟩ : Fin n) = j := by
      apply Fin.ext; dsimp only; rw [hdiv, Nat.mod_eq_of_lt hj]
    rw [hfin, hmod]
    rfl

private def sliceBits (y start len : ℕ) : Fin (2 ^ len) :=
  encodeBits (fun t : Fin len => y.testBit (start + t.val))

private theorem sliceBits_testBit (y start len t : ℕ) (ht : t < len) :
    (sliceBits y start len).val.testBit t = y.testBit (start + t) :=
  encodeBits_testBit _ t ht

private def initFlag {n m w : ℕ} (hn : 0 < n)
    (r : Fin (2 ^ (m + min w (n - 1) - n))) (s : Fin (2 ^ min w (n - 1))) :
    Sig (m * 2 ^ (w + 1) + 2 * n) :=
  fun x =>
    decide (∀ t : Fin (m + min w (n - 1) - n), s.val.testBit t.val = r.val.testBit t.val) &&
      (List.finRange (min w (n - 1))).all
        (fun t : Fin (min w (n - 1)) =>
          allowSig n m w ⟨t.val, by have := t.isLt; omega⟩ (s.val.testBit t.val) x)

private def stepFlag0 {n m w : ℕ} (hn : 0 < n) (k : Fin m) (s : Fin (2 ^ min w (n - 1))) :
    Sig (m * 2 ^ (w + 1) + 2 * n) :=
  fun x =>
    if hd0 : min w (n - 1) = 0 then
      tblSig n m w k s false x &&
        allowSig n m w ⟨(k.val + min w (n - 1)) % n, Nat.mod_lt _ hn⟩ false x
    else
      let d' := min w (n - 1) - 1
      have hpow : 2 ^ min w (n - 1) = 2 ^ (d' + 1) := congrArg (2 ^ ·) (by omega)
      let sCast : Fin (2 ^ (d' + 1)) := Fin.cast hpow s
      let b := topBit sCast
      let p0 : Fin (2 ^ min w (n - 1)) := Fin.cast hpow.symm (pred0 sCast)
      tblSig n m w k p0 b x &&
        allowSig n m w ⟨(k.val + min w (n - 1)) % n, Nat.mod_lt _ hn⟩ b x

private def stepFlag1 {n m w : ℕ} (hn : 0 < n) (k : Fin m) (s : Fin (2 ^ min w (n - 1))) :
    Sig (m * 2 ^ (w + 1) + 2 * n) :=
  fun x =>
    if hd0 : min w (n - 1) = 0 then
      tblSig n m w k s true x &&
        allowSig n m w ⟨(k.val + min w (n - 1)) % n, Nat.mod_lt _ hn⟩ true x
    else
      let d' := min w (n - 1) - 1
      have hpow : 2 ^ min w (n - 1) = 2 ^ (d' + 1) := congrArg (2 ^ ·) (by omega)
      let sCast : Fin (2 ^ (d' + 1)) := Fin.cast hpow s
      let b := topBit sCast
      let p1 : Fin (2 ^ min w (n - 1)) := Fin.cast hpow.symm (pred1 sCast)
      tblSig n m w k p1 b x &&
        allowSig n m w ⟨(k.val + min w (n - 1)) % n, Nat.mod_lt _ hn⟩ b x

private def stepPred0 {n w : ℕ} (s : Fin (2 ^ min w (n - 1))) : Fin (2 ^ min w (n - 1)) :=
  if hd0 : min w (n - 1) = 0 then s
  else
    let d' := min w (n - 1) - 1
    have hpow : 2 ^ min w (n - 1) = 2 ^ (d' + 1) := congrArg (2 ^ ·) (by omega)
    Fin.cast hpow.symm (pred0 (Fin.cast hpow s))

private def stepPred1 {n w : ℕ} (s : Fin (2 ^ min w (n - 1))) : Fin (2 ^ min w (n - 1)) :=
  if hd0 : min w (n - 1) = 0 then s
  else
    let d' := min w (n - 1) - 1
    have hpow : 2 ^ min w (n - 1) = 2 ^ (d' + 1) := congrArg (2 ^ ·) (by omega)
    Fin.cast hpow.symm (pred1 (Fin.cast hpow s))

private def dpVal {n m w : ℕ} (hn : 0 < n) :
    ℕ → Fin (2 ^ (m + min w (n - 1) - n)) → Fin (2 ^ min w (n - 1)) →
      (Fin (m * 2 ^ (w + 1) + 2 * n) → Bool) → ℕ
  | 0, r, s, x => if initFlag hn r s x then 1 else 0
  | k + 1, r, s, x =>
    if hk : k < m then
      let kf : Fin m := ⟨k, hk⟩
      (if stepFlag0 hn kf s x then dpVal hn k r (stepPred0 s) x else 0) +
      (if stepFlag1 hn kf s x then dpVal hn k r (stepPred1 s) x else 0)
    else 0

private def matchEnd {n m w : ℕ}
    (r : Fin (2 ^ (m + min w (n - 1) - n))) (s : Fin (2 ^ min w (n - 1))) : Bool :=
  decide (∀ t : Fin (m + min w (n - 1) - n),
    s.val.testBit (min w (n - 1) - (m + min w (n - 1) - n) + t.val) = r.val.testBit t.val)

private def allPairs2 (A B : ℕ) : List (Fin A × Fin B) :=
  (List.finRange A).flatMap fun a => (List.finRange B).map fun b => (a, b)

private theorem allPairs2_length (A B : ℕ) : (allPairs2 A B).length = A * B := by
  unfold allPairs2
  rw [List.length_flatMap]
  have hmap : (List.finRange A).map (fun a => ((List.finRange B).map fun b => (a, b)).length) =
      List.replicate A B := by
    apply List.ext_getElem (by simp)
    intro i hi1 hi2
    simp
  rw [hmap, List.sum_replicate, smul_eq_mul]

private theorem allPairs2_nodup (A B : ℕ) : (allPairs2 A B).Nodup := by
  unfold allPairs2
  rw [List.nodup_flatMap]
  refine ⟨?_, ?_⟩
  · intro a _
    exact (List.nodup_finRange B).map (fun _ _ h => (Prod.mk.inj h).2)
  · exact (List.nodup_finRange A).imp (fun {a1 a2} hne => by
      dsimp only [Function.onFun]
      rw [List.disjoint_left]
      intro p hp1 hp2
      obtain ⟨b1, _, rfl⟩ := List.mem_map.mp hp1
      obtain ⟨b2, _, h2⟩ := List.mem_map.mp hp2
      exact hne (Prod.mk.inj h2).1.symm)

private theorem mem_allPairs2 {A B : ℕ} (p : Fin A × Fin B) : p ∈ allPairs2 A B := by
  unfold allPairs2
  simp

private def sumEndList {n m w : ℕ} (hn : 0 < n) :
    List ((Fin (m * 2 ^ (w + 1) + 2 * n) → Bool) → ℕ) :=
  (allPairs2 (2 ^ (m + min w (n - 1) - n)) (2 ^ min w (n - 1))).map
    (fun p => if matchEnd p.1 p.2 then dpVal hn m p.1 p.2 else fun _ => 0)

private def sumEndVal {n m w : ℕ} (hn : 0 < n) :
    (Fin (m * 2 ^ (w + 1) + 2 * n) → Bool) → ℕ :=
  sumListVal (sumEndList hn)

private theorem sumEndVal_eq_finset {n m w : ℕ} (hn : 0 < n)
    (x : Fin (m * 2 ^ (w + 1) + 2 * n) → Bool) :
    sumEndVal hn x =
      ∑ p : Fin (2 ^ (m + min w (n - 1) - n)) × Fin (2 ^ min w (n - 1)),
        if matchEnd p.1 p.2 then dpVal hn m p.1 p.2 x else 0 := by
  unfold sumEndVal sumEndList
  rw [sumListVal_eq_sum, List.map_map]
  have hcomp : ((fun f : (Fin (m * 2 ^ (w + 1) + 2 * n) → Bool) → ℕ => f x) ∘
      fun p : Fin (2 ^ (m + min w (n - 1) - n)) × Fin (2 ^ min w (n - 1)) =>
        if matchEnd p.1 p.2 then dpVal hn m p.1 p.2 else fun _ => 0) =
      (fun p => if matchEnd p.1 p.2 then dpVal hn m p.1 p.2 x else 0) := by
    funext p
    simp only [Function.comp_apply]
    split_ifs <;> rfl
  rw [hcomp]
  have hto : (allPairs2 (2 ^ (m + min w (n - 1) - n)) (2 ^ min w (n - 1))).toFinset = Finset.univ := by
    ext p
    simp [mem_allPairs2]
  rw [← hto, List.sum_toFinset _ (allPairs2_nodup _ _)]

private def extVal {n m w : ℕ} (hn : 0 < n) :
    ℕ → (Fin (m * 2 ^ (w + 1) + 2 * n) → Bool) → ℕ
  | 0, x => sumEndVal hn x
  | u + 1, x =>
    let pos : Fin n := ⟨(m + min w (n - 1) + u) % n, Nat.mod_lt _ hn⟩
    (if allowSig n m w pos false x then extVal hn u x else 0) +
    (if allowSig n m w pos true x then extVal hn u x else 0)

private def validWords {n m w : ℕ} (hn : 0 < n)
    (x : Fin (m * 2 ^ (w + 1) + 2 * n) → Bool)
    (k : ℕ) (hk : k ≤ m)
    (r : Fin (2 ^ (m + min w (n - 1) - n)))
    (s : Fin (2 ^ min w (n - 1))) :
    Finset (Fin (2 ^ (k + min w (n - 1)))) :=
  Finset.univ.filter (fun y : Fin (2 ^ (k + min w (n - 1))) =>
    (∀ t : Fin (m + min w (n - 1) - n), y.val.testBit t.val = r.val.testBit t.val) ∧
    (∀ t : Fin (min w (n - 1)), y.val.testBit (k + t.val) = s.val.testBit t.val) ∧
    (∀ j : Fin (k + min w (n - 1)),
      allowSig n m w ⟨j.val % n, Nat.mod_lt _ hn⟩ (y.val.testBit j.val) x = true) ∧
    (∀ i : Fin k,
      tblSig n m w ⟨i.val, by omega⟩ (sliceBits y.val i.val (min w (n - 1)))
        (y.val.testBit (i.val + min w (n - 1))) x = true))

private theorem dpVal_eq_card {n m w : ℕ} (hn : 0 < n) (hmn : m ≤ n)
    (x : Fin (m * 2 ^ (w + 1) + 2 * n) → Bool) :
    ∀ (k : ℕ) (hk : k ≤ m)
      (r : Fin (2 ^ (m + min w (n - 1) - n)))
      (s : Fin (2 ^ min w (n - 1))),
      dpVal hn k r s x = (validWords hn x k hk r s).card := by
  set d := min w (n - 1)
  set e := m + d - n
  have hed : e ≤ d := by omega
  have hdn : d < n := by omega
  intro k
  induction k with
  | zero =>
    intro hk r s
    have hzero : 0 + d = d := Nat.zero_add d
    let s0 : Fin (2 ^ (0 + d)) := Fin.cast (by rw [hzero]) s
    have hcard : (validWords hn x 0 hk r s).card = if initFlag hn r s x then 1 else 0 := by
      by_cases hif : initFlag hn r s x = true
      · simp only [hif, ↓reduceIte]
        have hsing : validWords hn x 0 hk r s = {s0} := by
          ext y
          simp only [validWords, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
          constructor
          · rintro ⟨_, hs, _, _⟩
            apply Fin.ext
            apply Nat.eq_of_testBit_eq
            intro t
            by_cases htd : t < d
            · simpa [s0] using hs ⟨t, htd⟩
            · have hge : 2 ^ d ≤ 2 ^ t := Nat.pow_le_pow_right Nat.zero_lt_two (by omega)
              have hy : y.val < 2 ^ d := by simpa [hzero] using y.isLt
              have hs0 : s0.val < 2 ^ d := s.isLt
              rw [Nat.testBit_lt_two_pow (hy.trans_le hge), Nat.testBit_lt_two_pow (hs0.trans_le hge)]
          · rintro rfl
            unfold initFlag at hif
            simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
              List.mem_finRange, true_implies] at hif
            refine ⟨?_, ?_, ?_, fun i => Fin.elim0 i⟩
            · intro t; simpa [s0] using hif.1 t
            · intro t; simp [s0]
            · intro j
              have hjd : j.val < d := by have := j.isLt; omega
              have hmod : j.val % n = j.val := Nat.mod_eq_of_lt (by omega)
              have hfin : (⟨j.val % n, Nat.mod_lt _ hn⟩ : Fin n) = ⟨j.val, by omega⟩ :=
                Fin.ext hmod
              rw [hfin]
              simpa [s0] using hif.2 ⟨j.val, hjd⟩
        rw [hsing, Finset.card_singleton]
      · have hf : initFlag hn r s x = false := Bool.eq_false_iff.mpr hif
        simp only [hf, Bool.false_eq_true, ↓reduceIte]
        rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
        intro y hy
        simp only [validWords, Finset.mem_filter, Finset.mem_univ, true_and] at hy
        obtain ⟨hr, hs, hall, _⟩ := hy
        have hys : ∀ t : Fin d, y.val.testBit t.val = s.val.testBit t.val := fun t => by
          simpa using hs t
        apply hif
        unfold initFlag
        simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
          List.mem_finRange, true_implies]
        refine ⟨?_, ?_⟩
        · intro t
          have htd : t.val < d := by have := t.isLt; omega
          rw [← hys ⟨t.val, htd⟩]
          exact hr t
        · intro t
          have htd : t.val < 0 + d := by have := t.isLt; omega
          have hmod : t.val % n = t.val := Nat.mod_eq_of_lt (by omega)
          have h1 := hall ⟨t.val, htd⟩
          have hfin : (⟨t.val % n, Nat.mod_lt _ hn⟩ : Fin n) = ⟨t.val, by omega⟩ := Fin.ext hmod
          rw [hfin] at h1
          rwa [hys t] at h1
    simpa [dpVal] using hcard.symm
  | succ k ih =>
    intro hk r s
    have hkm : k < m := by omega
    let kf : Fin m := ⟨k, hkm⟩
    let pos : Fin n := ⟨(k + d) % n, Nat.mod_lt _ hn⟩
    let extBit (b : Bool) (y : Fin (2 ^ (k + d))) : Fin (2 ^ (k + 1 + d)) :=
      ⟨y.val + if b then 2 ^ (k + d) else 0, by
        have hy := y.isLt
        have hp : 2 ^ (k + 1 + d) = 2 ^ (k + d) * 2 := by
          rw [show k + 1 + d = (k + d) + 1 by omega, Nat.pow_succ]
        cases b <;> simp <;> omega⟩
    have hext_testBit : ∀ (b : Bool) (y : Fin (2 ^ (k + d))) (t : ℕ) (ht : t < k + 1 + d),
        (extBit b y).val.testBit t = if t < k + d then y.val.testBit t else b := by
      intro b y t ht
      exact winIdx_testBit (k + d) y b t (by omega)
    have hext_inj : ∀ b : Bool, Function.Injective (extBit b) := by
      intro b y1 y2 h
      have hv := congrArg Fin.val h
      simp only [extBit] at hv
      apply Fin.ext
      cases b <;> simp at hv <;> omega
    have hext_iff : ∀ (b : Bool) (p : Fin (2 ^ d)) (y : Fin (2 ^ (k + d))),
        y ∈ validWords hn x k (by omega) r p →
        (extBit b y ∈ validWords hn x (k + 1) hk r s ↔
          nextS p b = s ∧ tblSig n m w kf p b x = true ∧ allowSig n m w pos b x = true) := by
      intro b p y hy
      simp only [validWords, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      obtain ⟨hyr, hys, hyall, hytbl⟩ := hy
      have hslice_p : sliceBits y.val k d = p := by
        apply Fin.ext
        apply Nat.eq_of_testBit_eq
        intro t
        by_cases htd : t < d
        · rw [sliceBits_testBit y.val k d t htd]
          exact hys ⟨t, htd⟩
        · have hge : 2 ^ d ≤ 2 ^ t := Nat.pow_le_pow_right Nat.zero_lt_two (by omega)
          rw [Nat.testBit_lt_two_pow ((sliceBits y.val k d).isLt.trans_le hge),
            Nat.testBit_lt_two_pow (p.isLt.trans_le hge)]
      have hslice_ext : ∀ i : ℕ, i ≤ k →
          sliceBits (extBit b y).val i d = sliceBits y.val i d := by
        intro i hi
        apply Fin.ext
        apply Nat.eq_of_testBit_eq
        intro t
        by_cases htd : t < d
        · rw [sliceBits_testBit _ i d t htd, sliceBits_testBit _ i d t htd,
            hext_testBit b y (i + t) (by omega)]
          have hlt : i + t < k + d := by omega
          simp [hlt]
        · have hge : 2 ^ d ≤ 2 ^ t := Nat.pow_le_pow_right Nat.zero_lt_two (by omega)
          rw [Nat.testBit_lt_two_pow ((sliceBits _ i d).isLt.trans_le hge),
            Nat.testBit_lt_two_pow ((sliceBits _ i d).isLt.trans_le hge)]
      constructor
      · rintro ⟨_, hs', hall', htbl'⟩
        refine ⟨?_, ?_, ?_⟩
        · apply Fin.ext
          apply Nat.eq_of_testBit_eq
          intro t
          by_cases htd : t < d
          · rw [nextS_testBit p b t htd]
            have h1 := hs' ⟨t, htd⟩
            rw [hext_testBit b y (k + 1 + t) (by omega)] at h1
            split_ifs at h1 with hlt
            · have hlt2 : t + 1 < d := by omega
              simp only [hlt2, ↓reduceIte]
              rw [← hys ⟨t + 1, hlt2⟩]
              simpa [show k + (t + 1) = k + 1 + t by omega] using h1
            · have hnot2 : ¬ (t + 1 < d) := by omega
              simp only [hnot2, ↓reduceIte]
              exact h1
          · have hge : 2 ^ d ≤ 2 ^ t := Nat.pow_le_pow_right Nat.zero_lt_two (by omega)
            rw [Nat.testBit_lt_two_pow ((nextS p b).isLt.trans_le hge),
              Nat.testBit_lt_two_pow (s.isLt.trans_le hge)]
        · have hk1 := htbl' ⟨k, by omega⟩
          rw [hslice_ext k le_rfl, hslice_p, hext_testBit b y (k + d) (by omega)] at hk1
          simpa [kf] using hk1
        · have hj1 := hall' ⟨k + d, by omega⟩
          rw [hext_testBit b y (k + d) (by omega)] at hj1
          simpa [pos] using hj1
      · rintro ⟨hnext, htblk, hallk⟩
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro t
          rw [hext_testBit b y t.val (by have := t.isLt; omega)]
          have hlt : t.val < k + d := by have := t.isLt; omega
          simp only [hlt, ↓reduceIte]
          exact hyr t
        · intro t
          rw [hext_testBit b y (k + 1 + t.val) (by have := t.isLt; omega), ← hnext,
            nextS_testBit p b t.val t.isLt]
          by_cases hlt : t.val + 1 < d
          · simp only [hlt, ↓reduceIte, show k + 1 + t.val < k + d by omega]
            simpa [show k + (t.val + 1) = k + 1 + t.val by omega] using hys ⟨t.val + 1, hlt⟩
          · have hnot : ¬ (k + 1 + t.val < k + d) := by omega
            simp [hlt, hnot]
        · intro j
          rw [hext_testBit b y j.val j.isLt]
          by_cases hjk : j.val < k + d
          · simp only [hjk, ↓reduceIte]
            exact hyall ⟨j.val, hjk⟩
          · have hjeq : j.val = k + d := by have := j.isLt; omega
            simp only [hjk, ↓reduceIte]
            simpa [pos, hjeq] using hallk
        · intro i
          by_cases hik : i.val < k
          · rw [hslice_ext i.val (by omega), hext_testBit b y (i.val + d) (by omega)]
            have hlt : i.val + d < k + d := by omega
            simp only [hlt, ↓reduceIte]
            exact hytbl ⟨i.val, hik⟩
          · have hieq : i.val = k := by have := i.isLt; omega
            have hfin : (⟨i.val, by omega⟩ : Fin m) = kf := Fin.ext hieq
            rw [hfin, hieq, hslice_ext k le_rfl, hslice_p, hext_testBit b y (k + d) (by omega)]
            simpa using htblk
    have hsplit_y' : ∀ y' : Fin (2 ^ (k + 1 + d)),
        ∃ (y : Fin (2 ^ (k + d))) (b : Bool), y' = extBit b y := by
      intro y'
      let y : Fin (2 ^ (k + d)) := ⟨y'.val % 2 ^ (k + d), Nat.mod_lt _ (Nat.two_pow_pos _)⟩
      let b : Bool := y'.val.testBit (k + d)
      refine ⟨y, b, ?_⟩
      apply Fin.ext
      have h1 := mod_two_pow_succ_eq y'.val (k + d)
      have hlt : y'.val < 2 ^ (k + d + 1) := by
        have h1 : k + d + 1 = k + 1 + d := by omega
        rw [h1]; exact y'.isLt
      rw [Nat.mod_eq_of_lt hlt] at h1
      exact h1
    have hparent : ∀ (y : Fin (2 ^ (k + d))) (b : Bool),
        extBit b y ∈ validWords hn x (k + 1) hk r s →
        y ∈ validWords hn x k (by omega) r (sliceBits y.val k d) := by
      intro y b hy'
      simp only [validWords, Finset.mem_filter, Finset.mem_univ, true_and] at hy' ⊢
      obtain ⟨hr', _, hall', htbl'⟩ := hy'
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro t
        have h1 := hr' t
        rw [hext_testBit b y t.val (by have := t.isLt; omega)] at h1
        have hlt : t.val < k + d := by have := t.isLt; omega
        simpa [hlt] using h1
      · intro t
        exact (sliceBits_testBit y.val k d t.val t.isLt).symm
      · intro j
        have h1 := hall' ⟨j.val, by have := j.isLt; omega⟩
        rw [hext_testBit b y j.val (by have := j.isLt; omega)] at h1
        have hj : j.val < k + d := j.isLt
        simp only [hj, ↓reduceIte] at h1
        exact h1
      · intro i
        have h1 := htbl' ⟨i.val, by have := i.isLt; omega⟩
        have hslice : sliceBits (extBit b y).val i.val d = sliceBits y.val i.val d := by
          apply Fin.ext; apply Nat.eq_of_testBit_eq; intro t
          by_cases htd : t < d
          · rw [sliceBits_testBit _ i.val d t htd, sliceBits_testBit _ i.val d t htd,
              hext_testBit b y (i.val + t) (by have := i.isLt; omega)]
            have hlt : i.val + t < k + d := by have := i.isLt; omega
            simp [hlt]
          · have hge : 2 ^ d ≤ 2 ^ t := Nat.pow_le_pow_right Nat.zero_lt_two (by omega)
            rw [Nat.testBit_lt_two_pow ((sliceBits _ i.val d).isLt.trans_le hge),
              Nat.testBit_lt_two_pow ((sliceBits _ i.val d).isLt.trans_le hge)]
        rw [hslice, hext_testBit b y (i.val + d) (by have := i.isLt; omega)] at h1
        have hlt : i.val + d < k + d := by have := i.isLt; omega
        simpa [hlt] using h1
    unfold dpVal
    simp only [hkm, ↓reduceDIte]
    rw [ih (by omega) r (stepPred0 s), ih (by omega) r (stepPred1 s)]
    by_cases hd0 : min w (n - 1) = 0
    · have hpow0 : 2 ^ min w (n - 1) = 1 := by rw [hd0, Nat.pow_zero]
      have hf0 : stepFlag0 hn kf s x = (tblSig n m w kf s false x && allowSig n m w pos false x) := by
        unfold stepFlag0; simp only [hd0, ↓reduceDIte]
        congr 2; ext; simp [pos, kf, d, hd0]
      have hf1 : stepFlag1 hn kf s x = (tblSig n m w kf s true x && allowSig n m w pos true x) := by
        unfold stepFlag1; simp only [hd0, ↓reduceDIte]
        congr 2; ext; simp [pos, kf, d, hd0]
      have hp0 : stepPred0 s = s := by unfold stepPred0; simp only [hd0, ↓reduceDIte]
      have hp1 : stepPred1 s = s := by unfold stepPred1; simp only [hd0, ↓reduceDIte]
      rw [hf0, hf1, hp0, hp1]
      set S0 := if tblSig n m w kf s false x && allowSig n m w pos false x then
        (validWords hn x k (by omega) r s).image (extBit false) else ∅
      set S1 := if tblSig n m w kf s true x && allowSig n m w pos true x then
        (validWords hn x k (by omega) r s).image (extBit true) else ∅
      have hdisj : Disjoint S0 S1 := by
        rw [Finset.disjoint_left]
        intro y' h0 h1
        simp only [S0, S1] at h0 h1
        split_ifs at h0 h1
        · obtain ⟨y0, _, rfl⟩ := Finset.mem_image.mp h0
          obtain ⟨y1, _, heq⟩ := Finset.mem_image.mp h1
          have htb0 := hext_testBit false y0 (k + d) (by omega)
          have htb1 := hext_testBit true y1 (k + d) (by omega)
          rw [← heq] at htb0
          simp at htb0 htb1
          rw [htb0] at htb1
          cases htb1
        · exact False.elim (Finset.notMem_empty y' h1)
        · exact False.elim (Finset.notMem_empty y' h0)
        · exact False.elim (Finset.notMem_empty y' h0)
      have hunion : validWords hn x (k + 1) hk r s = S0 ∪ S1 := by
        ext y'
        simp only [Finset.mem_union, S0, S1]
        constructor
        · intro hy'
          obtain ⟨y, b, rfl⟩ := hsplit_y' y'
          have hp_eq : sliceBits y.val k d = s := by
            apply Fin.ext
            have h1 : (sliceBits y.val k d).val < 1 := Nat.lt_of_lt_of_eq (sliceBits y.val k d).isLt hpow0
            have h2 : s.val < 1 := Nat.lt_of_lt_of_eq s.isLt hpow0
            omega
          have hy := hparent y b hy'
          rw [hp_eq] at hy
          obtain ⟨_, htb, hal⟩ := (hext_iff b s y hy).mp hy'
          cases b with
          | false =>
            left
            simp only [htb, hal, Bool.and_self, ↓reduceIte]
            exact Finset.mem_image_of_mem _ hy
          | true =>
            right
            simp only [htb, hal, Bool.and_self, ↓reduceIte]
            exact Finset.mem_image_of_mem _ hy
        · rintro (h0 | h1)
          · split_ifs at h0 with hcond
            · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp h0
              have ⟨htb, hal⟩ := Bool.and_eq_true_iff.mp hcond
              have hnext : nextS s false = s := by
                apply Fin.ext
                have h1 : (nextS s false).val < 1 := Nat.lt_of_lt_of_eq (nextS s false).isLt hpow0
                have h2 : s.val < 1 := Nat.lt_of_lt_of_eq s.isLt hpow0
                omega
              exact (hext_iff false s y hy).mpr ⟨hnext, htb, hal⟩
            · simp at h0
          · split_ifs at h1 with hcond
            · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp h1
              have ⟨htb, hal⟩ := Bool.and_eq_true_iff.mp hcond
              have hnext : nextS s true = s := by
                apply Fin.ext
                have h1 : (nextS s true).val < 1 := Nat.lt_of_lt_of_eq (nextS s true).isLt hpow0
                have h2 : s.val < 1 := Nat.lt_of_lt_of_eq s.isLt hpow0
                omega
              exact (hext_iff true s y hy).mpr ⟨hnext, htb, hal⟩
            · simp at h1
      rw [hunion, Finset.card_union_of_disjoint hdisj]
      have hc0 : S0.card = if tblSig n m w kf s false x && allowSig n m w pos false x then
          (validWords hn x k (by omega) r s).card else 0 := by
        dsimp only [S0]; split_ifs
        · exact Finset.card_image_of_injective _ (hext_inj false)
        · rfl
      have hc1 : S1.card = if tblSig n m w kf s true x && allowSig n m w pos true x then
          (validWords hn x k (by omega) r s).card else 0 := by
        dsimp only [S1]; split_ifs
        · exact Finset.card_image_of_injective _ (hext_inj true)
        · rfl
      rw [hc0, hc1]
    · set d' := min w (n - 1) - 1
      have hpow : 2 ^ min w (n - 1) = 2 ^ (d' + 1) := congrArg (2 ^ ·) (by omega)
      let sCast : Fin (2 ^ (d' + 1)) := Fin.cast hpow s
      let b := topBit sCast
      let p0 : Fin (2 ^ d) := Fin.cast hpow.symm (pred0 sCast)
      let p1 : Fin (2 ^ d) := Fin.cast hpow.symm (pred1 sCast)
      have hp0_eq : stepPred0 s = p0 := by
        unfold stepPred0; simp only [hd0, ↓reduceDIte]; rfl
      have hp1_eq : stepPred1 s = p1 := by
        unfold stepPred1; simp only [hd0, ↓reduceDIte]; rfl
      have hf0_eq : stepFlag0 hn kf s x = (tblSig n m w kf p0 b x && allowSig n m w pos b x) := by
        unfold stepFlag0; simp only [hd0, ↓reduceDIte]; rfl
      have hf1_eq : stepFlag1 hn kf s x = (tblSig n m w kf p1 b x && allowSig n m w pos b x) := by
        unfold stepFlag1; simp only [hd0, ↓reduceDIte]; rfl
      rw [hp0_eq, hp1_eq, hf0_eq, hf1_eq]
      have hp_ne : p0 ≠ p1 := by
        intro h
        apply pred0_ne_pred1 sCast
        have hv := congrArg Fin.val h
        exact Fin.ext hv
      have hnext_iff : ∀ (p : Fin (2 ^ d)) (b' : Bool),
          nextS p b' = s ↔ b' = b ∧ (p = p0 ∨ p = p1) := by
        intro p b'
        let pCast : Fin (2 ^ (d' + 1)) := Fin.cast hpow p
        have h1 := nextS_eq_iff_pred pCast sCast b'
        have hcast_next : (nextS p b').val = (nextS pCast b').val := by
          simp only [nextS, winIdx, pCast, Fin.val_cast]
          have hite : (if b' = true then 2 ^ d else 0) = (if b' = true then 2 ^ (d' + 1) else 0) := by
            cases b' <;> simp [d, hpow]
          rw [hite]
        constructor
        · intro hn'
          have h2 : nextS pCast b' = sCast := Fin.ext (hcast_next.symm.trans (congrArg Fin.val hn'))
          obtain ⟨hb', hp' | hp'⟩ := h1.mp h2
          · exact ⟨hb', Or.inl (Fin.ext (by simpa [p0, pCast] using congrArg Fin.val hp'))⟩
          · exact ⟨hb', Or.inr (Fin.ext (by simpa [p1, pCast] using congrArg Fin.val hp'))⟩
        · rintro ⟨hb', hp' | hp'⟩
          · have h2 : nextS pCast b' = sCast :=
              h1.mpr ⟨hb', Or.inl (Fin.ext (by simpa [p0, pCast] using congrArg Fin.val hp'))⟩
            exact Fin.ext (hcast_next.trans (congrArg Fin.val h2))
          · have h2 : nextS pCast b' = sCast :=
              h1.mpr ⟨hb', Or.inr (Fin.ext (by simpa [p1, pCast] using congrArg Fin.val hp'))⟩
            exact Fin.ext (hcast_next.trans (congrArg Fin.val h2))
      set S0 := if tblSig n m w kf p0 b x && allowSig n m w pos b x then
        (validWords hn x k (by omega) r p0).image (extBit b) else ∅
      set S1 := if tblSig n m w kf p1 b x && allowSig n m w pos b x then
        (validWords hn x k (by omega) r p1).image (extBit b) else ∅
      have hdisj : Disjoint S0 S1 := by
        rw [Finset.disjoint_left]
        intro y' h0 h1
        simp only [S0, S1] at h0 h1
        split_ifs at h0 h1
        · obtain ⟨y0, hy0, rfl⟩ := Finset.mem_image.mp h0
          obtain ⟨y1, hy1, heq⟩ := Finset.mem_image.mp h1
          have hy01 : y0 = y1 := hext_inj b heq.symm
          subst hy01
          simp only [validWords, Finset.mem_filter, Finset.mem_univ, true_and] at hy0 hy1
          apply hp_ne
          apply Fin.ext
          apply Nat.eq_of_testBit_eq
          intro t
          by_cases htd : t < d
          · rw [← hy0.2.1 ⟨t, htd⟩, hy1.2.1 ⟨t, htd⟩]
          · have hge : 2 ^ d ≤ 2 ^ t := Nat.pow_le_pow_right Nat.zero_lt_two (by omega)
            rw [Nat.testBit_lt_two_pow (p0.isLt.trans_le hge),
              Nat.testBit_lt_two_pow (p1.isLt.trans_le hge)]
        · exact False.elim (Finset.notMem_empty y' h1)
        · exact False.elim (Finset.notMem_empty y' h0)
        · exact False.elim (Finset.notMem_empty y' h0)
      have hunion : validWords hn x (k + 1) hk r s = S0 ∪ S1 := by
        ext y'
        simp only [Finset.mem_union, S0, S1]
        constructor
        · intro hy'
          obtain ⟨y, b', rfl⟩ := hsplit_y' y'
          set p := sliceBits y.val k d
          have hy : y ∈ validWords hn x k (by omega) r p := hparent y b' hy'
          obtain ⟨hnext, htb, hal⟩ := (hext_iff b' p y hy).mp hy'
          obtain ⟨hb', hp' | hp'⟩ := (hnext_iff p b').mp hnext
          · subst hb'; rw [hp'] at hy htb
            left
            simp only [htb, hal, Bool.and_self, ↓reduceIte]
            exact Finset.mem_image_of_mem _ hy
          · subst hb'; rw [hp'] at hy htb
            right
            simp only [htb, hal, Bool.and_self, ↓reduceIte]
            exact Finset.mem_image_of_mem _ hy
        · rintro (h0 | h1)
          · split_ifs at h0 with hcond
            · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp h0
              have ⟨htb, hal⟩ := Bool.and_eq_true_iff.mp hcond
              exact (hext_iff b p0 y hy).mpr ⟨(hnext_iff p0 b).mpr ⟨rfl, Or.inl rfl⟩, htb, hal⟩
            · simp at h0
          · split_ifs at h1 with hcond
            · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp h1
              have ⟨htb, hal⟩ := Bool.and_eq_true_iff.mp hcond
              exact (hext_iff b p1 y hy).mpr ⟨(hnext_iff p1 b).mpr ⟨rfl, Or.inr rfl⟩, htb, hal⟩
            · simp at h1
      rw [hunion, Finset.card_union_of_disjoint hdisj]
      have hc0 : S0.card = if tblSig n m w kf p0 b x && allowSig n m w pos b x then
          (validWords hn x k (by omega) r p0).card else 0 := by
        dsimp only [S0]; split_ifs
        · exact Finset.card_image_of_injective _ (hext_inj b)
        · rfl
      have hc1 : S1.card = if tblSig n m w kf p1 b x && allowSig n m w pos b x then
          (validWords hn x k (by omega) r p1).card else 0 := by
        dsimp only [S1]; split_ifs
        · exact Finset.card_image_of_injective _ (hext_inj b)
        · rfl
      rw [hc0, hc1]

private theorem extVal_eq_sols {n m w : ℕ} (hn : 0 < n) (hm : 0 < m) (hmn : m ≤ n)
    (table : Fin m → (Fin (w + 1) → Bool) → Bool) (allow : Fin n → Bool → Bool) :
    extVal hn (n - (m + min w (n - 1))) (wiresInFn hn hm table allow) =
      (Finset.univ.filter (fun z : Fin (2 ^ n) =>
        (∀ j : Fin n, allow j (z.val.testBit j.val) = true) ∧
        ∀ i : Fin m, table i (fun p => z.val.testBit ((i.val + p.val) % n)) = true)).card := by
  set d := min w (n - 1)
  set e := m + d - n
  set x := wiresInFn hn hm table allow
  have hed : e ≤ d := by omega
  have hdn : d < n := by omega
  let WEnd : Finset (Fin (2 ^ (m + d))) :=
    Finset.univ.filter (fun y : Fin (2 ^ (m + d)) =>
      (∀ t : Fin e, y.val.testBit (m + (d - e) + t.val) = y.val.testBit t.val) ∧
      (∀ j : Fin (m + d), allowSig n m w ⟨j.val % n, Nat.mod_lt _ hn⟩ (y.val.testBit j.val) x = true) ∧
      (∀ i : Fin m, tblSig n m w i (sliceBits y.val i.val d) (y.val.testBit (i.val + d)) x = true))
  have hsumEnd : sumEndVal hn x = WEnd.card := by
    rw [sumEndVal_eq_finset]
    have hdp : ∀ p : Fin (2 ^ e) × Fin (2 ^ d),
        (if matchEnd p.1 p.2 then dpVal hn m p.1 p.2 x else 0) =
          (if matchEnd p.1 p.2 then validWords hn x m le_rfl p.1 p.2 else ∅).card := by
      intro p
      split_ifs
      · exact dpVal_eq_card hn hmn x m le_rfl p.1 p.2
      · rfl
    simp_rw [hdp]
    rw [← Finset.card_biUnion]
    · congr 1
      ext y
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, WEnd, Finset.mem_filter]
      constructor
      · rintro ⟨⟨r, s⟩, hy⟩
        split_ifs at hy with hme
        · simp only [validWords, Finset.mem_filter, Finset.mem_univ, true_and] at hy
          obtain ⟨hr, hs, hall, htbl⟩ := hy
          simp only [matchEnd, decide_eq_true_eq] at hme
          refine ⟨?_, hall, htbl⟩
          intro t
          have h1 := hs ⟨d - e + t.val, by have := t.isLt; omega⟩
          have h2 := hme t
          have h3 := hr t
          simpa [Nat.add_assoc] using h1.trans (h2.trans h3.symm)
        · simp at hy
      · rintro ⟨hrep, hall, htbl⟩
        let r : Fin (2 ^ e) := sliceBits y.val 0 e
        let s : Fin (2 ^ d) := sliceBits y.val m d
        refine ⟨(r, s), ?_⟩
        have hme : matchEnd r s = true := by
          simp only [matchEnd, decide_eq_true_eq]
          intro t
          rw [sliceBits_testBit y.val m d (d - e + t.val) (by have := t.isLt; omega),
            sliceBits_testBit y.val 0 e t.val t.isLt, Nat.zero_add, ← Nat.add_assoc]
          exact hrep t
        simp only [hme, ↓reduceIte, validWords, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨?_, ?_, hall, htbl⟩
        · intro t
          rw [sliceBits_testBit y.val 0 e t.val t.isLt, Nat.zero_add]
        · intro t
          rw [sliceBits_testBit y.val m d t.val t.isLt]
    · intro p1 _ p2 _ hne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro y h1 h2
      split_ifs at h1 h2 <;> (try simp at h1) <;> (try simp at h2)
      simp only [validWords, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
      apply hne
      apply Prod.ext
      · apply Fin.ext; apply Nat.eq_of_testBit_eq; intro t
        by_cases hte : t < e
        · rw [← h1.1 ⟨t, hte⟩, h2.1 ⟨t, hte⟩]
        · have hge : 2 ^ e ≤ 2 ^ t := Nat.pow_le_pow_right Nat.zero_lt_two (by omega)
          rw [Nat.testBit_lt_two_pow (p1.1.isLt.trans_le hge),
            Nat.testBit_lt_two_pow (p2.1.isLt.trans_le hge)]
      · apply Fin.ext; apply Nat.eq_of_testBit_eq; intro t
        by_cases htd : t < d
        · rw [← h1.2.1 ⟨t, htd⟩, h2.2.1 ⟨t, htd⟩]
        · have hge : 2 ^ d ≤ 2 ^ t := Nat.pow_le_pow_right Nat.zero_lt_two (by omega)
          rw [Nat.testBit_lt_two_pow (p1.2.isLt.trans_le hge),
            Nat.testBit_lt_two_pow (p2.2.isLt.trans_le hge)]
  by_cases hwrap : m + d ≤ n
  · have he0 : e = 0 := by omega
    have hext_gen : ∀ (u : ℕ) (hu : m + d + u ≤ n),
        extVal hn u x =
          (Finset.univ.filter (fun y : Fin (2 ^ (m + d + u)) =>
            (∀ j : Fin (m + d + u), allowSig n m w ⟨j.val, by have := j.isLt; omega⟩ (y.val.testBit j.val) x = true) ∧
            (∀ i : Fin m, tblSig n m w i (sliceBits y.val i.val d) (y.val.testBit (i.val + d)) x = true))).card := by
      intro u
      induction u with
      | zero =>
        intro _
        change sumEndVal hn x = _
        rw [hsumEnd]
        congr 1
        ext y
        simp only [WEnd, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨_, hall, htbl⟩
          refine ⟨fun j => ?_, htbl⟩
          have h1 := hall j
          have hmod : j.val % n = j.val := Nat.mod_eq_of_lt (by have := j.isLt; omega)
          have hfin : (⟨j.val % n, Nat.mod_lt _ hn⟩ : Fin n) = ⟨j.val, by have := j.isLt; omega⟩ :=
            Fin.ext hmod
          rwa [hfin] at h1
        · rintro ⟨hall, htbl⟩
          refine ⟨fun t => by have := t.isLt; omega, fun j => ?_, htbl⟩
          have hmod : j.val % n = j.val := Nat.mod_eq_of_lt (by have := j.isLt; omega)
          have hfin : (⟨j.val % n, Nat.mod_lt _ hn⟩ : Fin n) = ⟨j.val, by have := j.isLt; omega⟩ :=
            Fin.ext hmod
          rw [hfin]
          exact hall j
      | succ u ih =>
        intro hu
        unfold extVal
        rw [ih (by omega)]
        set pos : Fin n := ⟨(m + d + u) % n, Nat.mod_lt _ hn⟩
        have hpos_eq : pos = ⟨m + d + u, by omega⟩ :=
          Fin.ext (Nat.mod_eq_of_lt (by omega))
        let extB (b : Bool) (y : Fin (2 ^ (m + d + u))) : Fin (2 ^ (m + d + (u + 1))) :=
          ⟨y.val + if b then 2 ^ (m + d + u) else 0, by
            have hy := y.isLt
            have hp : 2 ^ (m + d + (u + 1)) = 2 ^ (m + d + u) * 2 := by
              rw [show m + d + (u + 1) = (m + d + u) + 1 by omega, Nat.pow_succ]
            cases b <;> simp <;> omega⟩
        have hext_tb : ∀ (b : Bool) (y : Fin (2 ^ (m + d + u))) (t : ℕ) (ht : t < m + d + (u + 1)),
            (extB b y).val.testBit t = if t < m + d + u then y.val.testBit t else b :=
          fun b y t ht => winIdx_testBit (m + d + u) y b t (by omega)
        have hext_inj : ∀ b : Bool, Function.Injective (extB b) := by
          intro b y1 y2 h
          have hv := congrArg Fin.val h
          simp only [extB] at hv
          apply Fin.ext; cases b <;> simp at hv <;> omega
        set Base := Finset.univ.filter (fun y : Fin (2 ^ (m + d + u)) =>
          (∀ j : Fin (m + d + u), allowSig n m w ⟨j.val, by have := j.isLt; omega⟩ (y.val.testBit j.val) x = true) ∧
          (∀ i : Fin m, tblSig n m w i (sliceBits y.val i.val d) (y.val.testBit (i.val + d)) x = true))
        set S0 := if allowSig n m w pos false x then Base.image (extB false) else ∅
        set S1 := if allowSig n m w pos true x then Base.image (extB true) else ∅
        have hdisj : Disjoint S0 S1 := by
          rw [Finset.disjoint_left]
          intro y' h0 h1
          simp only [S0, S1] at h0 h1
          split_ifs at h0 h1
          · obtain ⟨y0, _, rfl⟩ := Finset.mem_image.mp h0
            obtain ⟨y1, _, heq⟩ := Finset.mem_image.mp h1
            have htb0 := hext_tb false y0 (m + d + u) (by omega)
            have htb1 := hext_tb true y1 (m + d + u) (by omega)
            rw [← heq] at htb0
            simp at htb0 htb1
            rw [htb0] at htb1
            cases htb1
          · exact False.elim (Finset.notMem_empty y' h1)
          · exact False.elim (Finset.notMem_empty y' h0)
          · exact False.elim (Finset.notMem_empty y' h0)
        have hunion : Finset.univ.filter (fun y : Fin (2 ^ (m + d + (u + 1))) =>
            (∀ j : Fin (m + d + (u + 1)), allowSig n m w ⟨j.val, by have := j.isLt; omega⟩ (y.val.testBit j.val) x = true) ∧
            (∀ i : Fin m, tblSig n m w i (sliceBits y.val i.val d) (y.val.testBit (i.val + d)) x = true)) =
            S0 ∪ S1 := by
          ext y'
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, S0, S1]
          have hslice_ext : ∀ (b : Bool) (y : Fin (2 ^ (m + d + u))) (i : Fin m),
              sliceBits (extB b y).val i.val d = sliceBits y.val i.val d := by
            intro b y i
            apply Fin.ext; apply Nat.eq_of_testBit_eq; intro t
            by_cases htd : t < d
            · rw [sliceBits_testBit _ i.val d t htd, sliceBits_testBit _ i.val d t htd,
                hext_tb b y (i.val + t) (by have := i.isLt; omega)]
              have hlt : i.val + t < m + d + u := by have := i.isLt; omega
              simp [hlt]
            · have hge : 2 ^ d ≤ 2 ^ t := Nat.pow_le_pow_right Nat.zero_lt_two (by omega)
              rw [Nat.testBit_lt_two_pow ((sliceBits _ i.val d).isLt.trans_le hge),
                Nat.testBit_lt_two_pow ((sliceBits _ i.val d).isLt.trans_le hge)]
          constructor
          · rintro ⟨hall', htbl'⟩
            let y : Fin (2 ^ (m + d + u)) := ⟨y'.val % 2 ^ (m + d + u), Nat.mod_lt _ (Nat.two_pow_pos _)⟩
            let b : Bool := y'.val.testBit (m + d + u)
            have hy'_eq : y' = extB b y := by
              apply Fin.ext
              have h1 := mod_two_pow_succ_eq y'.val (m + d + u)
              have hlt : y'.val < 2 ^ (m + d + u + 1) := by
                have h2 : m + d + u + 1 = m + d + (u + 1) := by omega
                rw [h2]; exact y'.isLt
              rw [Nat.mod_eq_of_lt hlt] at h1
              exact h1
            have hyBase : y ∈ Base := by
              simp only [Base, Finset.mem_filter, Finset.mem_univ, true_and]
              refine ⟨fun j => ?_, fun i => ?_⟩
              · have h1 := hall' ⟨j.val, by have := j.isLt; omega⟩
                rw [hy'_eq, hext_tb b y j.val (by have := j.isLt; omega)] at h1
                simpa [j.isLt] using h1
              · have h1 := htbl' i
                rw [hy'_eq, hslice_ext b y i, hext_tb b y (i.val + d) (by have := i.isLt; omega)] at h1
                have hlt : i.val + d < m + d + u := by have := i.isLt; omega
                simpa [hlt] using h1
            have hal_b : allowSig n m w pos b x = true := by
              have h1 := hall' ⟨m + d + u, by omega⟩
              rw [hpos_eq]
              exact h1
            rw [hy'_eq]
            cases hb : b with
            | false =>
              rw [hb] at hal_b
              left; simp only [hal_b, ↓reduceIte]; exact Finset.mem_image_of_mem _ hyBase
            | true =>
              rw [hb] at hal_b
              right; simp only [hal_b, ↓reduceIte]; exact Finset.mem_image_of_mem _ hyBase
          · rintro (h0 | h1)
            · split_ifs at h0 with hal
              · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp h0
                simp only [Base, Finset.mem_filter, Finset.mem_univ, true_and] at hy
                refine ⟨fun j => ?_, fun i => ?_⟩
                · rw [hext_tb false y j.val j.isLt]
                  by_cases hju : j.val < m + d + u
                  · simp only [hju, ↓reduceIte]; exact hy.1 ⟨j.val, hju⟩
                  · have hjeq : j.val = m + d + u := by have := j.isLt; omega
                    simp only [hju, ↓reduceIte]
                    rw [hpos_eq] at hal
                    have hfin : (⟨j.val, by omega⟩ : Fin n) = ⟨m + d + u, by omega⟩ := Fin.ext hjeq
                    rw [hfin]; exact hal
                · rw [hslice_ext false y i, hext_tb false y (i.val + d) (by have := i.isLt; omega)]
                  have hlt : i.val + d < m + d + u := by have := i.isLt; omega
                  simp only [hlt, ↓reduceIte]; exact hy.2 i
              · simp at h0
            · split_ifs at h1 with hal
              · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp h1
                simp only [Base, Finset.mem_filter, Finset.mem_univ, true_and] at hy
                refine ⟨fun j => ?_, fun i => ?_⟩
                · rw [hext_tb true y j.val j.isLt]
                  by_cases hju : j.val < m + d + u
                  · simp only [hju, ↓reduceIte]; exact hy.1 ⟨j.val, hju⟩
                  · have hjeq : j.val = m + d + u := by have := j.isLt; omega
                    simp only [hju, ↓reduceIte]
                    rw [hpos_eq] at hal
                    have hfin : (⟨j.val, by omega⟩ : Fin n) = ⟨m + d + u, by omega⟩ := Fin.ext hjeq
                    rw [hfin]; exact hal
                · rw [hslice_ext true y i, hext_tb true y (i.val + d) (by have := i.isLt; omega)]
                  have hlt : i.val + d < m + d + u := by have := i.isLt; omega
                  simp only [hlt, ↓reduceIte]; exact hy.2 i
              · simp at h1
        rw [hunion, Finset.card_union_of_disjoint hdisj]
        have hc0 : S0.card = if allowSig n m w pos false x then Base.card else 0 := by
          dsimp only [S0]; split_ifs
          · exact Finset.card_image_of_injective _ (hext_inj false)
          · rfl
        have hc1 : S1.card = if allowSig n m w pos true x then Base.card else 0 := by
          dsimp only [S1]; split_ifs
          · exact Finset.card_image_of_injective _ (hext_inj true)
          · rfl
        rw [hc0, hc1]
    have hfinal := hext_gen (n - (m + d)) (by omega)
    rw [hfinal]
    have hneq : m + d + (n - (m + d)) = n := by omega
    apply Finset.card_bij (fun y _ => Fin.cast (by rw [hneq]) y)
    · intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      refine ⟨fun j => ?_, fun i => ?_⟩
      · have h1 := hy.1 ⟨j.val, by have := j.isLt; omega⟩
        rw [allowSig_wiresInFn hn hm table allow] at h1
        exact h1
      · have h1 := hy.2 i
        rw [tblSig_wiresInFn hn hm table allow] at h1
        convert h1 using 2
        funext p
        have hp_mod : p.val % n < d + 1 := by
          by_cases hw : w ≤ n - 1
          · have hdw : d = w := by omega
            rw [Nat.mod_eq_of_lt (by have := p.isLt; omega)]; have := p.isLt; omega
          · have hdw : d = n - 1 := by omega
            have := Nat.mod_lt p.val hn; omega
        rw [winIdx_testBit d _ _ (p.val % n) hp_mod]
        have hi_lt : i.val + p.val % n < n := by have := i.isLt; omega
        have hmod_eq : (i.val + p.val) % n = i.val + p.val % n := by
          rw [Nat.add_mod, Nat.mod_eq_of_lt (show i.val < n by have := i.isLt; omega),
            Nat.mod_eq_of_lt hi_lt]
        rw [hmod_eq]
        by_cases hpd : p.val % n < d
        · simp only [hpd, ↓reduceIte, Fin.val_cast]
          exact (sliceBits_testBit y.val i.val d (p.val % n) hpd).symm
        · have hpeq : p.val % n = d := by omega
          simp only [hpd, ↓reduceIte, Fin.val_cast]
          rw [hpeq]
    · intro y1 _ y2 _ h
      exact Fin.ext (by simpa using congrArg Fin.val h)
    · intro z hz
      refine ⟨Fin.cast (by rw [hneq]) z, ?_, by ext; rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
      refine ⟨fun j => ?_, fun i => ?_⟩
      · rw [allowSig_wiresInFn hn hm table allow]
        simpa using hz.1 ⟨j.val, by have := j.isLt; omega⟩
      · rw [tblSig_wiresInFn hn hm table allow]
        convert hz.2 i using 2
        funext p
        have hp_mod : p.val % n < d + 1 := by
          by_cases hw : w ≤ n - 1
          · have hdw : d = w := by omega
            rw [Nat.mod_eq_of_lt (by have := p.isLt; omega)]; have := p.isLt; omega
          · have hdw : d = n - 1 := by omega
            have := Nat.mod_lt p.val hn; omega
        rw [winIdx_testBit d _ _ (p.val % n) hp_mod]
        have hi_lt : i.val + p.val % n < n := by have := i.isLt; omega
        have hmod_eq : (i.val + p.val) % n = i.val + p.val % n := by
          rw [Nat.add_mod, Nat.mod_eq_of_lt (show i.val < n by have := i.isLt; omega),
            Nat.mod_eq_of_lt hi_lt]
        rw [hmod_eq]
        by_cases hpd : p.val % n < d
        · simp only [hpd, ↓reduceIte, Fin.val_cast]
          exact sliceBits_testBit z.val i.val d (p.val % n) hpd
        · have hpeq : p.val % n = d := by omega
          simp only [hpd, ↓reduceIte, Fin.val_cast]
          rw [hpeq]
  · have hsub0 : n - (m + d) = 0 := by omega
    have hmd_eq : m + d = n + e := by omega
    have hmde : m + (d - e) = n := by omega
    rw [hsub0]
    change sumEndVal hn x = _
    rw [hsumEnd]
    apply Finset.card_bij (fun y _ => ⟨y.val % 2 ^ n, Nat.mod_lt _ (Nat.two_pow_pos n)⟩)
    · intro y hy
      simp only [WEnd, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      obtain ⟨hrep, hall, htbl⟩ := hy
      have hy_mod : ∀ t : ℕ, t < m + d → y.val.testBit t = (y.val % 2 ^ n).testBit (t % n) := by
        intro t ht
        by_cases htn : t < n
        · rw [Nat.mod_eq_of_lt htn, Nat.testBit_mod_two_pow]
          simp [htn]
        · have ht_sub : t - n < e := by omega
          have h1 := hrep ⟨t - n, ht_sub⟩
          have heq1 : m + (d - e) + (t - n) = t := by omega
          rw [heq1] at h1
          have hmod_t : t % n = t - n := by
            rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
          rw [h1, hmod_t, Nat.testBit_mod_two_pow]
          have hlt2 : t - n < n := by omega
          simp [hlt2]
      refine ⟨fun j => ?_, fun i => ?_⟩
      · have h1 := hall ⟨j.val, by have := j.isLt; omega⟩
        rw [allowSig_wiresInFn hn hm table allow] at h1
        have hmod : j.val % n = j.val := Nat.mod_eq_of_lt j.isLt
        have hfin : (⟨j.val % n, Nat.mod_lt _ hn⟩ : Fin n) = j := Fin.ext hmod
        rw [hfin] at h1
        have htb := hy_mod j.val (by have := j.isLt; omega)
        rw [hmod] at htb
        rwa [← htb]
      · have h1 := htbl i
        rw [tblSig_wiresInFn hn hm table allow] at h1
        convert h1 using 2
        funext p
        have hp_mod : p.val % n < d + 1 := by
          by_cases hw : w ≤ n - 1
          · have hdw : d = w := by omega
            rw [Nat.mod_eq_of_lt (by have := p.isLt; omega)]; have := p.isLt; omega
          · have hdw : d = n - 1 := by omega
            have := Nat.mod_lt p.val hn; omega
        rw [winIdx_testBit d _ _ (p.val % n) hp_mod]
        have hadd_mod : (i.val + p.val) % n = (i.val + p.val % n) % n := by
          rw [Nat.add_mod, Nat.add_mod i.val (p.val % n), Nat.mod_mod]
        rw [hadd_mod]
        by_cases hpd : p.val % n < d
        · simp only [hpd, ↓reduceIte]
          rw [sliceBits_testBit y.val i.val d (p.val % n) hpd]
          exact (hy_mod (i.val + p.val % n) (by have := i.isLt; omega)).symm
        · have hpeq : p.val % n = d := by omega
          simp only [hpd, ↓reduceIte]
          rw [hpeq]
          exact (hy_mod (i.val + d) (by have := i.isLt; omega)).symm
    · intro y1 hy1 y2 hy2 h
      simp only [WEnd, Finset.mem_filter, Finset.mem_univ, true_and] at hy1 hy2
      have hmod_eq : y1.val % 2 ^ n = y2.val % 2 ^ n := congrArg Fin.val h
      apply Fin.ext
      apply Nat.eq_of_testBit_eq
      intro t
      by_cases ht : t < m + d
      · by_cases htn : t < n
        · have h1 : y1.val.testBit t = (y1.val % 2 ^ n).testBit t := by
            rw [Nat.testBit_mod_two_pow]; simp [htn]
          have h2 : y2.val.testBit t = (y2.val % 2 ^ n).testBit t := by
            rw [Nat.testBit_mod_two_pow]; simp [htn]
          rw [h1, h2, hmod_eq]
        · have ht_sub : t - n < e := by omega
          have h1 := hy1.1 ⟨t - n, ht_sub⟩
          have h2 := hy2.1 ⟨t - n, ht_sub⟩
          have heq1 : m + (d - e) + (t - n) = t := by omega
          rw [heq1] at h1 h2
          rw [h1, h2]
          have hlt2 : t - n < n := by omega
          have h3 : y1.val.testBit (t - n) = (y1.val % 2 ^ n).testBit (t - n) := by
            rw [Nat.testBit_mod_two_pow]; simp [hlt2]
          have h4 : y2.val.testBit (t - n) = (y2.val % 2 ^ n).testBit (t - n) := by
            rw [Nat.testBit_mod_two_pow]; simp [hlt2]
          rw [h3, h4, hmod_eq]
      · have hge : 2 ^ (m + d) ≤ 2 ^ t := Nat.pow_le_pow_right Nat.zero_lt_two (by omega)
        rw [Nat.testBit_lt_two_pow (y1.isLt.trans_le hge),
          Nat.testBit_lt_two_pow (y2.isLt.trans_le hge)]
    · intro z hz
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
      let y : Fin (2 ^ (m + d)) := encodeBits (fun j : Fin (m + d) => z.val.testBit (j.val % n))
      have hy_tb : ∀ t : ℕ, t < m + d → y.val.testBit t = z.val.testBit (t % n) :=
        fun t ht => encodeBits_testBit _ t ht
      refine ⟨y, ?_, ?_⟩
      · simp only [WEnd, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨?_, ?_, ?_⟩
        · intro t
          rw [hy_tb (m + (d - e) + t.val) (by have := t.isLt; omega),
            hy_tb t.val (by have := t.isLt; omega), hmde]
          rw [Nat.add_comm, Nat.add_mod_right]
        · intro j
          rw [allowSig_wiresInFn hn hm table allow, hy_tb j.val j.isLt]
          exact hz.1 ⟨j.val % n, Nat.mod_lt _ hn⟩
        · intro i
          rw [tblSig_wiresInFn hn hm table allow]
          convert hz.2 i using 2
          funext p
          have hp_mod : p.val % n < d + 1 := by
            by_cases hw : w ≤ n - 1
            · have hdw : d = w := by omega
              rw [Nat.mod_eq_of_lt (by have := p.isLt; omega)]; have := p.isLt; omega
            · have hdw : d = n - 1 := by omega
              have := Nat.mod_lt p.val hn; omega
          rw [winIdx_testBit d _ _ (p.val % n) hp_mod]
          have hadd_mod : (i.val + p.val) % n = (i.val + p.val % n) % n := by
            rw [Nat.add_mod, Nat.add_mod i.val (p.val % n), Nat.mod_mod]
          rw [hadd_mod]
          by_cases hpd : p.val % n < d
          · simp only [hpd, ↓reduceIte]
            rw [sliceBits_testBit y.val i.val d (p.val % n) hpd,
              hy_tb (i.val + p.val % n) (by have := i.isLt; omega)]
          · have hpeq : p.val % n = d := by omega
            simp only [hpd, ↓reduceIte]
            rw [hpeq, hy_tb (i.val + d) (by have := i.isLt; omega)]
      · apply Fin.ext
        apply Nat.eq_of_testBit_eq
        intro t
        by_cases htn : t < n
        · rw [Nat.testBit_mod_two_pow]
          simp only [htn, decide_true, Bool.true_and]
          rw [hy_tb t (by omega), Nat.mod_eq_of_lt htn]
        · have hge : 2 ^ n ≤ 2 ^ t := Nat.pow_le_pow_right Nat.zero_lt_two (by omega)
          rw [Nat.testBit_lt_two_pow ((Nat.mod_lt _ (Nat.two_pow_pos n)).trans_le hge),
            Nat.testBit_lt_two_pow (z.isLt.trans_le hge)]

private theorem buildInit {n m w : ℕ} (hn : 0 < n)
    (A0 : Set (Sig (m * 2 ^ (w + 1) + 2 * n)))
    (hAllow : ∀ (j : Fin n) (b : Bool), allowSig n m w j b ∈ A0)
    (hF : (fun _ => false) ∈ A0) (hT : (fun _ => true) ∈ A0) :
    let d := min w (n - 1)
    let e := m + d - n
    Build A0
      (⋃ r : Fin (2 ^ e), ⋃ s : Fin (2 ^ d), Set.range (bitsOf (n + 1) (dpVal hn 0 r s)))
      (2 ^ (d + e) * d) := by
  intro d e
  let pairs := allPairs2 (2 ^ e) (2 ^ d)
  have hbuild := listB (A := A0)
    (fun p : Fin (2 ^ e) × Fin (2 ^ d) => Set.range (bitsOf (n + 1) (dpVal hn 0 p.1 p.2)))
    d pairs (fun p _ => by
      by_cases hmatch : ∀ t : Fin e, p.2.val.testBit t.val = p.1.val.testBit t.val
      · let ls : List (Sig (m * 2 ^ (w + 1) + 2 * n)) :=
          (List.finRange d).map (fun t : Fin d =>
            allowSig n m w ⟨t.val, by have := t.isLt; omega⟩ (p.2.val.testBit t.val))
        have hand : Build A0 {fun x => ls.all (fun f => f x)} ls.length :=
          andListB ls (fun f hf => by
            obtain ⟨t, _, rfl⟩ := List.mem_map.mp hf
            exact hAllow _ _) hT
        have hlen : ls.length = d := by simp [ls]
        refine relaxB hand le_rfl ?_ (by omega)
        intro g hg
        obtain ⟨j, rfl⟩ := Set.mem_range.mp hg
        by_cases hj0 : j.val = 0
        · have hbit : bitsOf (n + 1) (dpVal hn 0 p.1 p.2) j = fun x => ls.all (fun f => f x) := by
            funext x
            unfold bitsOf dpVal initFlag
            rw [hj0]
            have hm' : decide (∀ t : Fin (m + min w (n - 1) - n),
                p.2.val.testBit t.val = p.1.val.testBit t.val) = true := decide_eq_true hmatch
            rw [hm', Bool.true_and]
            simp only [ls, List.all_map]
            change (if (List.finRange d).all (fun t : Fin d =>
                allowSig n m w ⟨t.val, by have := t.isLt; omega⟩ (p.2.val.testBit t.val) x) = true
                then 1 else 0).testBit 0 =
              (List.finRange d).all (fun t : Fin d =>
                allowSig n m w ⟨t.val, by have := t.isLt; omega⟩ (p.2.val.testBit t.val) x)
            cases (List.finRange d).all (fun t : Fin d =>
                allowSig n m w ⟨t.val, by have := t.isLt; omega⟩ (p.2.val.testBit t.val) x) <;> rfl
          rw [hbit]
          exact Or.inr rfl
        · have hbit : bitsOf (n + 1) (dpVal hn 0 p.1 p.2) j = fun _ => false := by
            funext x
            unfold bitsOf dpVal
            cases initFlag hn p.1 p.2 x
            · simp
            · have hgt : 1 < 2 ^ j.val := Nat.one_lt_two_pow (by omega)
              exact Nat.testBit_lt_two_pow hgt
          rw [hbit]
          exact Or.inl hF
      · refine relaxB (idleB (A := A0) (B := ∅) (Set.empty_subset _)) le_rfl ?_ (Nat.zero_le d)
        intro g hg
        obtain ⟨j, rfl⟩ := Set.mem_range.mp hg
        have hbit : bitsOf (n + 1) (dpVal hn 0 p.1 p.2) j = fun _ => false := by
          funext x
          unfold bitsOf dpVal initFlag
          have hmf : decide (∀ t : Fin (m + min w (n - 1) - n),
              p.2.val.testBit t.val = p.1.val.testBit t.val) = false := decide_eq_false hmatch
          simp [hmf]
        rw [hbit]
        exact Or.inl hF)
  have hplen : pairs.length = 2 ^ (d + e) := by
    rw [allPairs2_length, Nat.pow_add, Nat.mul_comm]
  refine relaxB hbuild le_rfl ?_ (by rw [hplen])
  intro g hg
  simp only [Set.mem_iUnion] at hg
  obtain ⟨r, s, hmem⟩ := hg
  exact Or.inr (Set.mem_iUnion.mpr ⟨(r, s), Set.mem_iUnion.mpr ⟨mem_allPairs2 (r, s), hmem⟩⟩)

private theorem buildStep {n m w : ℕ} (hn : 0 < n) (k : Fin m)
    (A0 : Set (Sig (m * 2 ^ (w + 1) + 2 * n)))
    (hTbl : ∀ (i : Fin m) (s : Fin (2 ^ min w (n - 1))) (b : Bool), tblSig n m w i s b ∈ A0)
    (hAllow : ∀ (j : Fin n) (b : Bool), allowSig n m w j b ∈ A0)
    (hF : (fun _ => false) ∈ A0) :
    let d := min w (n - 1)
    let e := m + d - n
    Build
      (A0 ∪ ⋃ r : Fin (2 ^ e), ⋃ s : Fin (2 ^ d), Set.range (bitsOf (n + 1) (dpVal hn k.val r s)))
      (⋃ r : Fin (2 ^ e), ⋃ s : Fin (2 ^ d), Set.range (bitsOf (n + 1) (dpVal hn (k.val + 1) r s)))
      (2 ^ (d + e) * (11 * (n + 1) + 2)) := by
  intro d e
  set Ak := A0 ∪ ⋃ r : Fin (2 ^ e), ⋃ s : Fin (2 ^ d), Set.range (bitsOf (n + 1) (dpVal hn k.val r s))
  let pairs := allPairs2 (2 ^ e) (2 ^ d)
  have hbuild := listB (A := Ak)
    (fun p : Fin (2 ^ e) × Fin (2 ^ d) => Set.range (bitsOf (n + 1) (dpVal hn (k.val + 1) p.1 p.2)))
    (11 * (n + 1) + 2) pairs (fun p _ => by
      have hf0 : Build Ak {stepFlag0 hn k p.2} 1 := by
        by_cases hd0 : min w (n - 1) = 0
        · have heq : stepFlag0 hn k p.2 =
              fun x => tblSig n m w k p.2 false x &&
                allowSig n m w ⟨(k.val + min w (n - 1)) % n, Nat.mod_lt _ hn⟩ false x := by
            funext x; unfold stepFlag0; simp only [hd0, ↓reduceDIte]
          rw [heq]
          exact andB (Or.inl (hTbl k p.2 false)) (Or.inl (hAllow _ false))
        · set d' := min w (n - 1) - 1
          have hpow : 2 ^ min w (n - 1) = 2 ^ (d' + 1) := congrArg (2 ^ ·) (by omega)
          let sCast : Fin (2 ^ (d' + 1)) := Fin.cast hpow p.2
          let b := topBit sCast
          let pr0 : Fin (2 ^ min w (n - 1)) := Fin.cast hpow.symm (pred0 sCast)
          have heq : stepFlag0 hn k p.2 =
              fun x => tblSig n m w k pr0 b x &&
                allowSig n m w ⟨(k.val + min w (n - 1)) % n, Nat.mod_lt _ hn⟩ b x := by
            funext x; unfold stepFlag0; simp only [hd0, ↓reduceDIte]; rfl
          rw [heq]
          exact andB (Or.inl (hTbl k pr0 b)) (Or.inl (hAllow _ b))
      have hf1 : Build (Ak ∪ {stepFlag0 hn k p.2}) {stepFlag1 hn k p.2} 1 := by
        by_cases hd0 : min w (n - 1) = 0
        · have heq : stepFlag1 hn k p.2 =
              fun x => tblSig n m w k p.2 true x &&
                allowSig n m w ⟨(k.val + min w (n - 1)) % n, Nat.mod_lt _ hn⟩ true x := by
            funext x; unfold stepFlag1; simp only [hd0, ↓reduceDIte]
          rw [heq]
          exact andB (Or.inl (Or.inl (hTbl k p.2 true))) (Or.inl (Or.inl (hAllow _ true)))
        · set d' := min w (n - 1) - 1
          have hpow : 2 ^ min w (n - 1) = 2 ^ (d' + 1) := congrArg (2 ^ ·) (by omega)
          let sCast : Fin (2 ^ (d' + 1)) := Fin.cast hpow p.2
          let b := topBit sCast
          let pr1 : Fin (2 ^ min w (n - 1)) := Fin.cast hpow.symm (pred1 sCast)
          have heq : stepFlag1 hn k p.2 =
              fun x => tblSig n m w k pr1 b x &&
                allowSig n m w ⟨(k.val + min w (n - 1)) % n, Nat.mod_lt _ hn⟩ b x := by
            funext x; unfold stepFlag1; simp only [hd0, ↓reduceDIte]; rfl
          rw [heq]
          exact andB (Or.inl (Or.inl (hTbl k pr1 b))) (Or.inl (Or.inl (hAllow _ b)))
      have hcomb := maskPairAddB (A := Ak ∪ ({stepFlag0 hn k p.2} ∪ {stepFlag1 hn k p.2}))
        (n + 1) (stepFlag0 hn k p.2) (stepFlag1 hn k p.2)
        (dpVal hn k.val p.1 (stepPred0 p.2)) (dpVal hn k.val p.1 (stepPred1 p.2))
        (Or.inl (Or.inl hF)) (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl))
        (fun j => Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨p.1, Set.mem_iUnion.mpr ⟨stepPred0 p.2, Set.mem_range.mpr ⟨j, rfl⟩⟩⟩)))
        (fun j => Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨p.1, Set.mem_iUnion.mpr ⟨stepPred1 p.2, Set.mem_range.mpr ⟨j, rfl⟩⟩⟩)))
      have hdp_eq : dpVal hn (k.val + 1) p.1 p.2 =
          fun x => (if stepFlag0 hn k p.2 x then dpVal hn k.val p.1 (stepPred0 p.2) x else 0) +
            (if stepFlag1 hn k p.2 x then dpVal hn k.val p.1 (stepPred1 p.2) x else 0) := by
        funext x; conv_lhs => unfold dpVal; simp [k.isLt]
      rw [hdp_eq]
      exact relaxB (seqB (seqB hf0 hf1) hcomb) le_rfl (fun _ hg => Or.inr (Or.inr hg)) (by omega))
  have hplen : pairs.length = 2 ^ (d + e) := by
    rw [allPairs2_length, Nat.pow_add, Nat.mul_comm]
  refine relaxB hbuild le_rfl ?_ (by rw [hplen])
  intro g hg
  simp only [Set.mem_iUnion] at hg
  obtain ⟨r, s, hmem⟩ := hg
  exact Or.inr (Set.mem_iUnion.mpr ⟨(r, s), Set.mem_iUnion.mpr ⟨mem_allPairs2 (r, s), hmem⟩⟩)

private theorem buildDP {n m w : ℕ} (hn : 0 < n)
    (A0 : Set (Sig (m * 2 ^ (w + 1) + 2 * n)))
    (hTbl : ∀ (i : Fin m) (s : Fin (2 ^ min w (n - 1))) (b : Bool), tblSig n m w i s b ∈ A0)
    (hAllow : ∀ (j : Fin n) (b : Bool), allowSig n m w j b ∈ A0)
    (hF : (fun _ => false) ∈ A0) (hT : (fun _ => true) ∈ A0) :
    let d := min w (n - 1)
    let e := m + d - n
    ∀ k : ℕ, k ≤ m →
      Build A0
        (⋃ r : Fin (2 ^ e), ⋃ s : Fin (2 ^ d), Set.range (bitsOf (n + 1) (dpVal hn k r s)))
        (2 ^ (d + e) * d + k * (2 ^ (d + e) * (11 * (n + 1) + 2))) := by
  intro d e k
  induction k with
  | zero =>
    intro _
    simpa using buildInit hn A0 hAllow hF hT
  | succ k ih =>
    intro hk
    have h1 := ih (by omega)
    have h2 := buildStep hn ⟨k, by omega⟩ A0 hTbl hAllow hF
    exact relaxB (seqB h1 h2) le_rfl (fun _ hg => Or.inr (Or.inr hg))
      (by dsimp only [d, e]; ring_nf; exact le_rfl)

private theorem buildExt {n m w : ℕ} (hn : 0 < n)
    (A0 : Set (Sig (m * 2 ^ (w + 1) + 2 * n)))
    (hAllow : ∀ (j : Fin n) (b : Bool), allowSig n m w j b ∈ A0)
    (hF : (fun _ => false) ∈ A0) :
    ∀ u : ℕ,
      Build (A0 ∪ Set.range (bitsOf (n + 1) (sumEndVal hn)))
        (Set.range (bitsOf (n + 1) (extVal hn u)))
        (u * (11 * (n + 1))) := by
  intro u
  induction u with
  | zero =>
    simp only [Nat.zero_mul]
    exact idleB (fun _ hg => Or.inr hg)
  | succ u ih =>
    let pos : Fin n := ⟨(m + min w (n - 1) + u) % n, Nat.mod_lt _ hn⟩
    have hstep := maskPairAddB
      (A := (A0 ∪ Set.range (bitsOf (n + 1) (sumEndVal hn))) ∪ Set.range (bitsOf (n + 1) (extVal hn u)))
      (n + 1)
      (allowSig n m w pos false) (allowSig n m w pos true)
      (extVal hn u) (extVal hn u)
      (Or.inl (Or.inl hF)) (Or.inl (Or.inl (hAllow pos false))) (Or.inl (Or.inl (hAllow pos true)))
      (fun j => Or.inr (Set.mem_range.mpr ⟨j, rfl⟩))
      (fun j => Or.inr (Set.mem_range.mpr ⟨j, rfl⟩))
    have heq : extVal hn (u + 1) =
        fun x => (if allowSig n m w pos false x then extVal hn u x else 0) +
          (if allowSig n m w pos true x then extVal hn u x else 0) := rfl
    rw [heq]
    exact relaxB (seqB ih hstep) le_rfl (fun _ hg => Or.inr (Or.inr hg))
      (by rw [Nat.add_mul, Nat.one_mul])

private theorem main_aux : ∀ (n m w : Nat) (hn : 0 < n) (hm : 0 < m), m ≤ n →
  let tableInputs := m * 2 ^ (w + 1)
  let inputs := tableInputs + 2 * n
  let d := min w (n - 1)
  ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (outBit : Fin (n + 1) → Nat),
    PEqualNP.MetaComplexity.FanInTwo C ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack inputs C ∧
    C.size ≤ 16 * (n + 1) ^ 2 * 2 ^ (d + (m + d - n)) + 2 ∧
    C.output = outBit 0 ∧ (∀ j, outBit j < inputs + C.size) ∧
    ∀ (table : Fin m → (Fin (w + 1) → Bool) → Bool) (allow : Fin n → Bool → Bool),
      let wiresIn := List.ofFn (fun a : Fin inputs =>
        if a.val < tableInputs then
          table ⟨(a.val / 2 ^ (w + 1)) % m, Nat.mod_lt _ hm⟩
            (fun b => (a.val % 2 ^ (w + 1)).testBit b.val)
        else
          let t := a.val - tableInputs
          allow ⟨(t / 2) % n, Nat.mod_lt _ hn⟩ (decide (t % 2 = 1)))
      let sols := Finset.univ.filter (fun z : Fin (2 ^ n) =>
        (∀ j : Fin n, allow j (z.val.testBit j.val) = true) ∧
        ∀ i : Fin m, table i (fun p => z.val.testBit ((i.val + p.val) % n)) = true)
      ∀ b : Fin (n + 1), (C.wires wiresIn).getD (outBit b) false = sols.card.testBit b.val := by
  intro n m w hn hm hmn tableInputs inputs d
  set e := m + d - n
  let S0 : Set (Sig inputs) := Set.range (fun i : Fin inputs => fun x : Fin inputs → Bool => x i)
  let A0 : Set (Sig inputs) := S0 ∪ ({fun _ => false} ∪ {fun _ => true})
  have hConsts : Build S0 ({fun _ => false} ∪ {fun _ => true}) 2 :=
    seqB (constB false) (constB true)
  have hTblA0 : ∀ (i : Fin m) (s : Fin (2 ^ d)) (b : Bool), tblSig n m w i s b ∈ A0 :=
    fun i s b => Or.inl ⟨tblWireIdx n m w i s b, rfl⟩
  have hAllowA0 : ∀ (j : Fin n) (b : Bool), allowSig n m w j b ∈ A0 :=
    fun j b => Or.inl ⟨allowWireIdx n m w j b, rfl⟩
  have hFA0 : (fun _ => false) ∈ A0 := Or.inr (Or.inl rfl)
  have hTA0 : (fun _ => true) ∈ A0 := Or.inr (Or.inr rfl)
  have hDP := buildDP hn A0 hTblA0 hAllowA0 hFA0 hTA0 m le_rfl
  let DPm : Set (Sig inputs) :=
    ⋃ r : Fin (2 ^ e), ⋃ s : Fin (2 ^ d), Set.range (bitsOf (n + 1) (dpVal hn m r s))
  have hSum : Build (A0 ∪ DPm) (Set.range (bitsOf (n + 1) (sumEndVal hn)))
      ((sumEndList hn).length * (9 * (n + 1))) :=
    sumListB (n + 1) (sumEndList hn) (Or.inl hFA0) (fun f hf j => by
      obtain ⟨p, _, rfl⟩ := List.mem_map.mp hf
      by_cases hme : matchEnd p.1 p.2 = true
      · simp only [hme, ↓reduceIte]
        exact Or.inr (Set.mem_iUnion.mpr ⟨p.1, Set.mem_iUnion.mpr ⟨p.2, ⟨j, rfl⟩⟩⟩)
      · simp only [hme, Bool.false_eq_true, ↓reduceIte]
        have hzero : bitsOf (N := inputs) (n + 1) (fun _ => 0) j = fun _ => false := by
          funext x; simp [bitsOf]
        rw [hzero]; exact Or.inl hFA0)
  have hSumLen : (sumEndList (m := m) (w := w) hn).length = 2 ^ (d + e) := by
    unfold sumEndList
    rw [List.length_map, allPairs2_length, Nat.pow_add, Nat.mul_comm]
  have hExt := buildExt hn A0 hAllowA0 hFA0 (n - (m + d))
  have h12 := seqB hDP hSum
  have h123 := seqB h12 (relaxB hExt (fun f hf => by
    rcases hf with hf | hf
    · exact Or.inl hf
    · exact Or.inr (Or.inr hf)) Set.subset_union_right le_rfl)
  have hFull := seqB hConsts h123
  obtain ⟨c, hc, hsched⟩ := hFull.run (startSched inputs) le_rfl
  have hbits_in : ∀ b : Fin (n + 1),
      bitsOf (n + 1) (extVal hn (n - (m + d))) b ∈
        S0 ∪ (({fun _ => false} ∪ {fun _ => true}) ∪
          ((DPm ∪ Set.range (bitsOf (n + 1) (sumEndVal hn))) ∪
            Set.range (bitsOf (n + 1) (extVal hn (n - (m + d)))))) :=
    fun b => Or.inr (Or.inr (Or.inr ⟨b, rfl⟩))
  obtain ⟨C, outBit, hFan, hRB, hSize, hOut, hOutLt, hEval⟩ :=
    finishBits (Nat.succ_pos n) hsched (bitsOf (n + 1) (extVal hn (n - (m + d)))) hbits_in
  have hSizeLe : C.size ≤ 16 * (n + 1) ^ 2 * 2 ^ (d + e) + 2 := by
    rw [hSize, Nat.zero_add]
    have hposPow : 1 ≤ 2 ^ (d + e) := Nat.one_le_two_pow
    have h11 : 11 * (n + 1) + 2 ≤ 12 * (n + 1) := by omega
    have hsum1 : m * (2 ^ (d + e) * (11 * (n + 1) + 2)) ≤ m * (2 ^ (d + e) * (12 * (n + 1))) :=
      Nat.mul_le_mul_left m (Nat.mul_le_mul_left _ h11)
    have hsum2 : (n - (m + d)) * (11 * (n + 1)) ≤ (n - m) * (2 ^ (d + e) * (12 * (n + 1))) := by
      calc (n - (m + d)) * (11 * (n + 1))
          ≤ (n - m) * (12 * (n + 1)) := Nat.mul_le_mul (by omega) (by omega)
        _ = (n - m) * (1 * (12 * (n + 1))) := by ring
        _ ≤ (n - m) * (2 ^ (d + e) * (12 * (n + 1))) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hposPow)
    have hdle : d ≤ n + 1 := by omega
    have hinit : 2 ^ (d + e) * d ≤ 2 ^ (d + e) * (n + 1) := Nat.mul_le_mul_left _ hdle
    rw [hSumLen] at hc
    change c ≤ 2 + ((2 ^ (d + e) * d + m * (2 ^ (d + e) * (11 * (n + 1) + 2))) +
        2 ^ (d + e) * (9 * (n + 1)) + (n - (m + d)) * (11 * (n + 1))) at hc
    have hcomb : c ≤ 2 + 2 ^ (d + e) * (n + 1) + m * (2 ^ (d + e) * (12 * (n + 1))) +
        2 ^ (d + e) * (9 * (n + 1)) + (n - m) * (2 ^ (d + e) * (12 * (n + 1))) := by omega
    have hmn_sum : m * (2 ^ (d + e) * (12 * (n + 1))) + (n - m) * (2 ^ (d + e) * (12 * (n + 1))) =
        n * (2 ^ (d + e) * (12 * (n + 1))) := by
      rw [← Nat.add_mul, Nat.add_sub_of_le hmn]
    have hfactor : 2 ^ (d + e) * (n + 1) + n * (2 ^ (d + e) * (12 * (n + 1))) +
        2 ^ (d + e) * (9 * (n + 1)) = (12 * n + 10) * (n + 1) * 2 ^ (d + e) := by ring
    have hpoly : (12 * n + 10) * (n + 1) ≤ 16 * (n + 1) ^ 2 := by
      have : 12 * n + 10 ≤ 16 * (n + 1) := by omega
      calc (12 * n + 10) * (n + 1) ≤ 16 * (n + 1) * (n + 1) := Nat.mul_le_mul_right _ this
        _ = 16 * (n + 1) ^ 2 := by ring
    have hmul : (12 * n + 10) * (n + 1) * 2 ^ (d + e) ≤ 16 * (n + 1) ^ 2 * 2 ^ (d + e) :=
      Nat.mul_le_mul_right _ hpoly
    omega
  refine ⟨C, outBit, hFan, hRB, hSizeLe, hOut, hOutLt, ?_⟩
  intro table allow wiresIn sols b
  have h1 := hEval b (wiresInFn hn hm table allow)
  have h2 := extVal_eq_sols hn hm hmn table allow
  change (C.wires (List.ofFn (wiresInFn hn hm table allow))).getD (outBit b) false = sols.card.testBit b.val
  rw [h1]
  unfold bitsOf
  rw [h2]

end PEqualNP.Outside.L_clb_045_aux

theorem PEqualNP.Outside.L_clb_045 : (∀ (n m w : Nat) (hn : 0 < n) (hm : 0 < m), m ≤ n →
  let tableInputs := m * 2 ^ (w + 1)
  let inputs := tableInputs + 2 * n
  let d := min w (n - 1)
  ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (outBit : Fin (n + 1) → Nat),
    PEqualNP.MetaComplexity.FanInTwo C ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack inputs C ∧
    C.size ≤ 16 * (n + 1) ^ 2 * 2 ^ (d + (m + d - n)) + 2 ∧
    C.output = outBit 0 ∧ (∀ j, outBit j < inputs + C.size) ∧
    ∀ (table : Fin m → (Fin (w + 1) → Bool) → Bool) (allow : Fin n → Bool → Bool),
      let wiresIn := List.ofFn (fun a : Fin inputs =>
        if a.val < tableInputs then
          table ⟨(a.val / 2 ^ (w + 1)) % m, Nat.mod_lt _ hm⟩
            (fun b => (a.val % 2 ^ (w + 1)).testBit b.val)
        else
          let t := a.val - tableInputs
          allow ⟨(t / 2) % n, Nat.mod_lt _ hn⟩ (decide (t % 2 = 1)))
      let sols := Finset.univ.filter (fun z : Fin (2 ^ n) =>
        (∀ j : Fin n, allow j (z.val.testBit j.val) = true) ∧
        ∀ i : Fin m, table i (fun p => z.val.testBit ((i.val + p.val) % n)) = true)
      ∀ b : Fin (n + 1), (C.wires wiresIn).getD (outBit b) false = sols.card.testBit b.val) :=
  PEqualNP.Outside.L_clb_045_aux.main_aux
