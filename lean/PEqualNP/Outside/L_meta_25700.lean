import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25700_aux

private lemma testBit_zero_toNat (n : ℕ) : (n.testBit 0).toNat = n % 2 := by
  rw [Nat.testBit_zero]
  have hlt : n % 2 < 2 := Nat.mod_lt n (by decide)
  interval_cases h : n % 2 <;> decide

private lemma fin_div2_lt {k : ℕ} (x : Fin (2 ^ (k + 1))) : x.val / 2 < 2 ^ k := by
  have hlt : x.val < 2 * 2 ^ k := by
    have h1 := x.isLt
    have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
    omega
  omega

private def finPowTwoEquiv : ∀ k : ℕ, Fin (2 ^ k) ≃ (Fin k → Bool)
  | 0 =>
    { toFun := fun _ => Fin.elim0
      invFun := fun _ => ⟨0, by decide⟩
      left_inv := fun x => Fin.ext (by have := x.isLt; simp at this; omega)
      right_inv := fun v => by funext i; exact Fin.elim0 i }
  | k + 1 =>
    let ih := finPowTwoEquiv k
    { toFun := fun x =>
        Fin.cons (x.val.testBit 0) (ih ⟨x.val / 2, fin_div2_lt x⟩)
      invFun := fun v =>
        ⟨(v 0).toNat + 2 * (ih.symm (fun i => v i.succ)).val, by
          have hq := (ih.symm (fun i => v i.succ)).isLt
          have hb : (v 0).toNat ≤ 1 := by cases v 0 <;> decide
          have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
          omega⟩
      left_inv := fun x => by
        apply Fin.ext
        dsimp only
        have hcomp : (fun i : Fin k =>
            (Fin.cons (α := fun _ => Bool) (x.val.testBit 0) (ih ⟨x.val / 2, fin_div2_lt x⟩)) i.succ) =
            ih ⟨x.val / 2, fin_div2_lt x⟩ := by
          funext i
          simp
        rw [hcomp, Equiv.symm_apply_apply]
        dsimp only
        rw [Fin.cons_zero, testBit_zero_toNat]
        exact Nat.mod_add_div x.val 2
      right_inv := fun v => by
        funext i
        refine Fin.cases ?_ ?_ i
        · simp only [Fin.cons_zero]
          have h0 : ((v 0).toNat + 2 * (ih.symm (fun j => v j.succ)).val) % 2 = (v 0).toNat := by
            rw [Nat.add_mul_mod_self_left]
            cases v 0 <;> decide
          rw [Nat.testBit_zero, h0]
          cases v 0 <;> decide
        · intro j
          simp only [Fin.cons_succ]
          have hdiv : ((v 0).toNat + 2 * (ih.symm (fun j => v j.succ)).val) / 2 =
              (ih.symm (fun j => v j.succ)).val := by
            rw [Nat.add_mul_div_left _ _ (by decide : 0 < 2)]
            have : (v 0).toNat / 2 = 0 := by cases v 0 <;> decide
            omega
          have hfin : (⟨((v 0).toNat + 2 * (ih.symm (fun j => v j.succ)).val) / 2,
              by rw [hdiv]; exact (ih.symm (fun j => v j.succ)).isLt⟩ : Fin (2 ^ k)) =
              ih.symm (fun j => v j.succ) := Fin.ext hdiv
          rw [hfin, Equiv.apply_symm_apply] }

private lemma finPowTwoEquiv_apply :
    ∀ (k : ℕ) (x : Fin (2 ^ k)) (i : Fin k),
      finPowTwoEquiv k x i = x.val.testBit i.val := by
  intro k
  induction k with
  | zero => intro x i; exact Fin.elim0 i
  | succ k ih =>
    intro x i
    refine Fin.cases ?_ ?_ i
    · rfl
    · intro j
      change finPowTwoEquiv k ⟨x.val / 2, fin_div2_lt x⟩ j = x.val.testBit (j.val + 1)
      rw [ih]
      exact (Nat.testBit_succ x.val j.val).symm

private lemma le_two_pow_sub_one : ∀ a : ℕ, 1 ≤ a → a ≤ 2 ^ (a - 1) := by
  intro a
  induction a with
  | zero => omega
  | succ k ih =>
    intro _
    cases k with
    | zero => decide
    | succ k' =>
      have hprev := ih (by omega)
      simp only [Nat.add_sub_cancel] at hprev ⊢
      have hpow : 2 ^ (k' + 1) = 2 * 2 ^ k' := by ring
      have h1 : 1 ≤ 2 ^ k' := Nat.one_le_two_pow
      omega

private lemma pow_bernoulli_nat (u : ℕ) :
    ∀ m : ℕ, (u + 2 * m) * u ^ m ≤ u * (u + 2) ^ m := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    have hstep1 : (u + 2 * m) * u ^ m * (u + 2) ≤ u * (u + 2) ^ m * (u + 2) :=
      Nat.mul_le_mul_right (u + 2) ih
    have hrhs : u * (u + 2) ^ m * (u + 2) = u * (u + 2) ^ (m + 1) := by
      rw [pow_succ]; ring
    have hlhs : (u + 2 * m) * u ^ m * (u + 2) =
        (u + 2 * (m + 1)) * u ^ (m + 1) + 4 * m * u ^ m := by
      rw [pow_succ]; ring
    omega

private lemma two_hit_ge_Z (a c : ℕ) (ha : 2 ≤ a) (hca : c < a)
    (h1 : 2 * 2 ^ c ≤ a) :
    let r := 2 ^ a
    let b := 2 ^ c
    let m := 2 ^ (a - 1 - c)
    let Z := 2 ^ (r / 2)
    Z ≤ 2 * (Z - (2 ^ b - 2) ^ m) := by
  intro r b m Z
  have hbm : b * m = r / 2 := by
    dsimp only [b, m, r]
    rw [← pow_add, show c + (a - 1 - c) = a - 1 by omega]
    have hpow : 2 ^ a = 2 ^ (a - 1) * 2 := by
      rw [← pow_succ, show a - 1 + 1 = a by omega]
    omega
  have hZ : Z = (2 ^ b) ^ m := by
    dsimp only [Z]
    rw [← pow_mul, hbm]
  by_cases hc0 : c = 0
  · subst hc0
    have hb1 : b = 1 := rfl
    have hm_pos : 0 < m := Nat.two_pow_pos _
    have hzero : (2 ^ b - 2) ^ m = 0 := by
      rw [hb1]
      exact zero_pow (Nat.ne_of_gt hm_pos)
    rw [hzero, Nat.sub_zero]
    omega
  · have hb2 : 2 ≤ b := by
      dsimp only [b]
      have : 1 ≤ c := Nat.pos_of_ne_zero hc0
      calc
        2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ c := Nat.pow_le_pow_right (by decide) this
    set u := 2 ^ b - 2
    have hu_pos : 0 < u := by
      have : 4 ≤ 2 ^ b := by
        calc
          4 = 2 ^ 2 := by decide
          _ ≤ 2 ^ b := Nat.pow_le_pow_right (by decide) hb2
      omega
    have hu2 : u + 2 = 2 ^ b := by omega
    have h2m_ge : 2 ^ b ≤ 2 * m := by
      have hb_le_pow : b ≤ 2 ^ (b - 1) := le_two_pow_sub_one b (by omega)
      have hb2_le : 2 * b ≤ a := h1
      have hprod : b * 2 ^ b ≤ 2 ^ a := by
        calc
          b * 2 ^ b ≤ 2 ^ (b - 1) * 2 ^ b := Nat.mul_le_mul_right _ hb_le_pow
          _ = 2 ^ (b - 1 + b) := (pow_add 2 _ _).symm
          _ ≤ 2 ^ a := Nat.pow_le_pow_right (by decide) (by omega)
      have h2bm : b * (2 * m) = 2 ^ a := by
        have hpow : 2 ^ a = 2 * 2 ^ (a - 1) := by
          conv_lhs => rw [show a = (a - 1) + 1 by omega]
          rw [pow_succ]; ring
        have : 2 * (b * m) = 2 ^ a := by rw [hbm]; dsimp only [r]; omega
        linarith
      rw [← h2bm] at hprod
      exact Nat.le_of_mul_le_mul_left hprod (by omega)
    have hbern := pow_bernoulli_nat u m
    rw [hu2, ← hZ] at hbern
    have h2u_mul : u * (2 * u ^ m) ≤ u * Z := by
      have h1' : u + u ≤ u + 2 * m := by omega
      calc
        u * (2 * u ^ m) = (u + u) * u ^ m := by ring
        _ ≤ (u + 2 * m) * u ^ m := Nat.mul_le_mul_right _ h1'
        _ ≤ u * Z := hbern
    have h2u : 2 * u ^ m ≤ Z := Nat.le_of_mul_le_mul_left h2u_mul hu_pos
    omega

private def sgn (b : Bool) : ℤ := if b then -1 else 1

private lemma sgn_not (a : Bool) : sgn (!a) = -sgn a := by
  cases a <;> decide

private lemma sum_eq_zero_of_invol {α : Type} [DecidableEq α] (S : Finset α)
    (f : α → ℤ) (τ : α → α)
    (hmem : ∀ x ∈ S, τ x ∈ S)
    (hinv : ∀ x ∈ S, τ (τ x) = x)
    (hneg : ∀ x ∈ S, f (τ x) = -f x) :
    ∑ x ∈ S, f x = 0 := by
  have h1 : ∑ x ∈ S, f (τ x) = ∑ x ∈ S, f x := by
    refine Finset.sum_bij (fun x _ => τ x) hmem ?_ ?_ (fun _ _ => rfl)
    · intro x hx y hy hxy
      have := congrArg τ hxy
      rwa [hinv x hx, hinv y hy] at this
    · intro y hy
      exact ⟨τ y, hmem y hy, hinv y hy⟩
  have h2 : ∑ x ∈ S, f (τ x) = -(∑ x ∈ S, f x) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl hneg
  linarith

private lemma isConst_count (b m : ℕ) (hb : 0 < b) :
    ((Finset.univ : Finset (Fin m → Fin b → Bool)).filter (fun A =>
      ∃ blk : Fin m, ∀ j : Fin b, A blk j = A blk ⟨0, hb⟩)).card =
      2 ^ (b * m) - (2 ^ b - 2) ^ m := by
  have hcompl :
      ((Finset.univ : Finset (Fin m → Fin b → Bool)).filter (fun A =>
        ¬ ∃ blk : Fin m, ∀ j : Fin b, A blk j = A blk ⟨0, hb⟩)).card =
        (2 ^ b - 2) ^ m := by
    let bad : Finset (Fin b → Bool) :=
      (Finset.univ : Finset (Fin b → Bool)).filter (fun f => ¬ ∀ j : Fin b, f j = f ⟨0, hb⟩)
    have hbad_card : bad.card = 2 ^ b - 2 := by
      let good : Finset (Fin b → Bool) :=
        (Finset.univ : Finset (Fin b → Bool)).filter (fun f => ∀ j : Fin b, f j = f ⟨0, hb⟩)
      have hgood_eq : good = {fun _ => false, fun _ => true} := by
        ext f
        simp only [good, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Finset.mem_singleton]
        constructor
        · intro hf
          cases h0 : f ⟨0, hb⟩
          · left; funext j; rw [hf j, h0]
          · right; funext j; rw [hf j, h0]
        · rintro (rfl | rfl) j <;> rfl
      have hgood_card : good.card = 2 := by
        rw [hgood_eq, Finset.card_pair]
        intro h
        have := congrFun h ⟨0, hb⟩
        cases this
      have hsum := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin b → Bool)))
        (p := fun f => ∀ j : Fin b, f j = f ⟨0, hb⟩)
      have huniv : (Finset.univ : Finset (Fin b → Bool)).card = 2 ^ b := by
        simp [Fintype.card_fun]
      change good.card + bad.card = (Finset.univ : Finset (Fin b → Bool)).card at hsum
      omega
    have hset :
        (Finset.univ : Finset (Fin m → Fin b → Bool)).filter (fun A =>
          ¬ ∃ blk : Fin m, ∀ j : Fin b, A blk j = A blk ⟨0, hb⟩) =
        Fintype.piFinset (fun _ : Fin m => bad) := by
      ext A
      simp [bad, Fintype.mem_piFinset]
    rw [hset, Fintype.card_piFinset]
    simp [hbad_card]
  have hsum := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin m → Fin b → Bool)))
    (p := fun A => ∃ blk : Fin m, ∀ j : Fin b, A blk j = A blk ⟨0, hb⟩)
  have huniv : (Finset.univ : Finset (Fin m → Fin b → Bool)).card = 2 ^ (b * m) := by
    simp [Fintype.card_fun, ← pow_mul]
  omega

private def isConstBlk {b m : ℕ} (hb : 0 < b) (A : Fin m → Fin b → Bool) (blk : Fin m) : Bool :=
  decide (∀ j : Fin b, A blk j = A blk ⟨0, hb⟩)

private def firstConstBlk {b m : ℕ} (hb : 0 < b) (hm : 0 < m)
    (A : Fin m → Fin b → Bool) (s : Fin m) : Option (Fin m) :=
  (List.finRange m).find? (fun d => isConstBlk hb A ⟨(s.val + d.val) % m, Nat.mod_lt _ hm⟩)

private def chosenBlk {b m : ℕ} (hb : 0 < b) (hm : 0 < m)
    (A : Fin m → Fin b → Bool) (s : Fin m) : Fin m :=
  match firstConstBlk hb hm A s with
  | some d => ⟨(s.val + d.val) % m, Nat.mod_lt _ hm⟩
  | none => s

private lemma firstConstBlk_isSome_iff {b m : ℕ} (hb : 0 < b) (hm : 0 < m)
    (A : Fin m → Fin b → Bool) (s : Fin m) :
    (firstConstBlk hb hm A s).isSome = true ↔
      ∃ blk : Fin m, ∀ j : Fin b, A blk j = A blk ⟨0, hb⟩ := by
  unfold firstConstBlk
  rw [List.isSome_find?]
  simp only [List.any_eq_true, List.mem_finRange, true_and, isConstBlk, decide_eq_true_eq]
  constructor
  · rintro ⟨d, hd⟩; exact ⟨_, hd⟩
  · rintro ⟨blk, hblk⟩
    let d : Fin m := ⟨(blk.val + m - s.val) % m, Nat.mod_lt _ hm⟩
    refine ⟨d, ?_⟩
    have hmod : (⟨(s.val + d.val) % m, Nat.mod_lt _ hm⟩ : Fin m) = blk := by
      apply Fin.ext
      dsimp only [d]
      rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
      have h1 : s.val + (blk.val + m - s.val) = blk.val + m := by omega
      rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt blk.isLt]
    rwa [hmod]

private lemma chosenBlk_isConst_of_some {b m : ℕ} (hb : 0 < b) (hm : 0 < m)
    (A : Fin m → Fin b → Bool) (s d : Fin m)
    (h : firstConstBlk hb hm A s = some d) :
    ∀ j : Fin b, A (chosenBlk hb hm A s) j = A (chosenBlk hb hm A s) ⟨0, hb⟩ := by
  unfold chosenBlk
  rw [h]
  have hs := List.find?_some h
  simpa [isConstBlk] using hs

private def rotAct {b m : ℕ} (hm : 0 < m) (shift : Fin m)
    (A : Fin m → Fin b → Bool) : Fin m → Fin b → Bool :=
  fun blk => A ⟨(blk.val + m - shift.val) % m, Nat.mod_lt _ hm⟩

private def rotStart {m : ℕ} (hm : 0 < m) (shift s : Fin m) : Fin m :=
  ⟨(s.val + shift.val) % m, Nat.mod_lt _ hm⟩

private lemma rotAct_eval {b m : ℕ} (hm : 0 < m) (shift : Fin m)
    (A : Fin m → Fin b → Bool) (s d : Fin m) :
    rotAct hm shift A ⟨((rotStart hm shift s).val + d.val) % m, Nat.mod_lt _ hm⟩ =
      A ⟨(s.val + d.val) % m, Nat.mod_lt _ hm⟩ := by
  unfold rotAct rotStart
  congr 1
  apply Fin.ext
  dsimp only
  have h1 : ((s.val + shift.val) % m + d.val) % m = (s.val + shift.val + d.val) % m := by
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
  rw [h1]
  have hdiv := Nat.div_add_mod (s.val + shift.val + d.val) m
  set r0 := (s.val + shift.val + d.val) % m
  set q0 := (s.val + shift.val + d.val) / m
  have hmul_comm : q0 * m = m * q0 := mul_comm q0 m
  have hsh_lt : shift.val < m := shift.isLt
  have hsub : (r0 + m - shift.val) + q0 * m = (s.val + d.val) + m := by omega
  have hmod1 : ((r0 + m - shift.val) + q0 * m) % m = (r0 + m - shift.val) % m :=
    Nat.add_mul_mod_self_right _ _ _
  have hmod2 : ((s.val + d.val) + m) % m = (s.val + d.val) % m := Nat.add_mod_right _ _
  rw [← hmod1, hsub, hmod2]

private lemma firstConstBlk_rot {b m : ℕ} (hb : 0 < b) (hm : 0 < m)
    (shift : Fin m) (A : Fin m → Fin b → Bool) (s : Fin m) :
    firstConstBlk hb hm (rotAct hm shift A) (rotStart hm shift s) = firstConstBlk hb hm A s := by
  unfold firstConstBlk
  congr 1
  funext d
  unfold isConstBlk
  rw [rotAct_eval]

private lemma chosenBlk_rot {b m : ℕ} (hb : 0 < b) (hm : 0 < m)
    (shift : Fin m) (A : Fin m → Fin b → Bool) (s : Fin m) :
    chosenBlk hb hm (rotAct hm shift A) (rotStart hm shift s) =
      rotStart hm shift (chosenBlk hb hm A s) := by
  unfold chosenBlk
  rw [firstConstBlk_rot]
  cases firstConstBlk hb hm A s with
  | none => rfl
  | some d =>
    apply Fin.ext
    dsimp only [rotStart]
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    conv_rhs => rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    congr 1
    omega

private lemma rotAct_rotStart_bij {b m : ℕ} (hm : 0 < m) (shift : Fin m) :
    Function.Bijective (fun p : (Fin m → Fin b → Bool) × Fin m =>
      (rotAct hm shift p.1, rotStart hm shift p.2)) := by
  let invShift : Fin m := ⟨(m - shift.val) % m, Nat.mod_lt _ hm⟩
  have hcomp : ∀ (s1 s2 : Fin m) (hsum : (s1.val + s2.val) % m = 0),
      ∀ p : (Fin m → Fin b → Bool) × Fin m,
        (rotAct hm s2 (rotAct hm s1 p.1), rotStart hm s2 (rotStart hm s1 p.2)) = p := by
    intro s1 s2 hsum ⟨A, s⟩
    ext blk j
    · dsimp only [rotAct]
      congr 1
      apply Fin.ext
      dsimp only
      have hlt2 : blk.val < m := blk.isLt
      have hs1_lt : s1.val < m := s1.isLt
      have hs2_lt : s2.val < m := s2.isLt
      have hdiv := Nat.div_add_mod (blk.val + m - s2.val) m
      set r0 := (blk.val + m - s2.val) % m
      set q0 := (blk.val + m - s2.val) / m
      have hdiv2 := Nat.div_add_mod (s1.val + s2.val) m
      rw [hsum, add_zero] at hdiv2
      set q1 := (s1.val + s2.val) / m
      have hdist : (q0 + q1) * m = m * q0 + m * q1 := by ring
      have hsub : (r0 + m - s1.val) + (q0 + q1) * m = blk.val + 2 * m := by omega
      have hmod1 : ((r0 + m - s1.val) + (q0 + q1) * m) % m = (r0 + m - s1.val) % m :=
        Nat.add_mul_mod_self_right _ _ _
      have hmod2 : (blk.val + 2 * m) % m = blk.val := by
        rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt2]
      rw [← hmod1, hsub, hmod2]
    · dsimp only [rotStart]
      rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
      have hdiv2 := Nat.div_add_mod (s1.val + s2.val) m
      rw [hsum, add_zero] at hdiv2
      have hcomm : ((s1.val + s2.val) / m) * m = m * ((s1.val + s2.val) / m) := mul_comm _ _
      have : s.val + s1.val + s2.val = s.val + ((s1.val + s2.val) / m) * m := by omega
      rw [this, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt s.isLt]
  have h1 : (shift.val + invShift.val) % m = 0 := by
    dsimp only [invShift]
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    have : shift.val + (m - shift.val) = m := by omega
    rw [this, Nat.mod_self]
  have h2 : (invShift.val + shift.val) % m = 0 := by rw [Nat.add_comm]; exact h1
  refine ⟨?_, ?_⟩
  · intro p1 p2 heq
    have := congrArg (fun p : (Fin m → Fin b → Bool) × Fin m =>
      (rotAct hm invShift p.1, rotStart hm invShift p.2)) heq
    dsimp only at this
    rwa [hcomp shift invShift h1 p1, hcomp shift invShift h1 p2] at this
  · intro p
    exact ⟨(rotAct hm invShift p.1, rotStart hm invShift p.2), hcomp invShift shift h2 p⟩

private lemma rotStart_inj {m : ℕ} (hm : 0 < m) (shift : Fin m) :
    Function.Injective (rotStart hm shift) := by
  intro u v huv
  have hbij := rotAct_rotStart_bij (b := 1) hm shift
  let p1 : (Fin m → Fin 1 → Bool) × Fin m := (fun _ _ => false, u)
  let p2 : (Fin m → Fin 1 → Bool) × Fin m := (fun _ _ => false, v)
  have heq : p1 = p2 := hbij.1 (Prod.ext rfl huv)
  exact congrArg Prod.snd heq

private lemma chosenBlk_fiber_card {b m : ℕ} (hb : 0 < b) (hm : 0 < m) (blk0 : Fin m) :
    ((Finset.univ : Finset ((Fin m → Fin b → Bool) × Fin m)).filter
      (fun p => chosenBlk hb hm p.1 p.2 = blk0)).card = 2 ^ (b * m) := by
  have heq_fib : ∀ t : Fin m,
      ((Finset.univ : Finset ((Fin m → Fin b → Bool) × Fin m)).filter
        (fun p => chosenBlk hb hm p.1 p.2 = t)).card =
      ((Finset.univ : Finset ((Fin m → Fin b → Bool) × Fin m)).filter
        (fun p => chosenBlk hb hm p.1 p.2 = blk0)).card := by
    intro t
    let sh : Fin m := ⟨(blk0.val + m - t.val) % m, Nat.mod_lt _ hm⟩
    have hrot_t : rotStart hm sh t = blk0 := by
      apply Fin.ext
      dsimp only [rotStart, sh]
      rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
      have : t.val + (blk0.val + m - t.val) = blk0.val + m := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt blk0.isLt]
    have hbij := rotAct_rotStart_bij (b := b) hm sh
    refine Finset.card_bij (fun p _ => (rotAct hm sh p.1, rotStart hm sh p.2)) ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      rw [chosenBlk_rot, hp, hrot_t]
    · intro p1 _ p2 _ heq; exact hbij.1 heq
    · intro q hq
      obtain ⟨p, rfl⟩ := hbij.2 q
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
      refine ⟨p, ?_, rfl⟩
      rw [chosenBlk_rot] at hq
      exact rotStart_inj hm sh (hq.trans hrot_t.symm)
  have hsum := Finset.card_eq_sum_card_fiberwise
    (f := fun p : (Fin m → Fin b → Bool) × Fin m => chosenBlk hb hm p.1 p.2)
    (s := Finset.univ) (t := (Finset.univ : Finset (Fin m)))
    (fun _ _ => Finset.mem_univ _)
  have hsum2 : (∑ t : Fin m, ((Finset.univ : Finset ((Fin m → Fin b → Bool) × Fin m)).filter
      (fun p => chosenBlk hb hm p.1 p.2 = t)).card) =
      m * ((Finset.univ : Finset ((Fin m → Fin b → Bool) × Fin m)).filter
        (fun p => chosenBlk hb hm p.1 p.2 = blk0)).card := by
    rw [Finset.sum_congr rfl fun t _ => heq_fib t, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul]
  have huniv : (Finset.univ : Finset ((Fin m → Fin b → Bool) × Fin m)).card = m * 2 ^ (b * m) := by
    simp [Fintype.card_prod, Fintype.card_fun, ← pow_mul, mul_comm]
  rw [huniv, hsum2] at hsum
  exact Nat.eq_of_mul_eq_mul_left hm hsum.symm

private lemma chosenBlk_hit_fiber_card {b m : ℕ} (hb : 0 < b) (hm : 0 < m) (blk0 : Fin m) :
    ((Finset.univ : Finset ((Fin m → Fin b → Bool) × Fin m)).filter
      (fun p => chosenBlk hb hm p.1 p.2 = blk0 ∧ (firstConstBlk hb hm p.1 p.2).isSome = true)).card =
      2 ^ (b * m) - (2 ^ b - 2) ^ m := by
  have heq_fib : ∀ t : Fin m,
      ((Finset.univ : Finset ((Fin m → Fin b → Bool) × Fin m)).filter
        (fun p => chosenBlk hb hm p.1 p.2 = t ∧ (firstConstBlk hb hm p.1 p.2).isSome = true)).card =
      ((Finset.univ : Finset ((Fin m → Fin b → Bool) × Fin m)).filter
        (fun p => chosenBlk hb hm p.1 p.2 = blk0 ∧ (firstConstBlk hb hm p.1 p.2).isSome = true)).card := by
    intro t
    let sh : Fin m := ⟨(blk0.val + m - t.val) % m, Nat.mod_lt _ hm⟩
    have hrot_t : rotStart hm sh t = blk0 := by
      apply Fin.ext
      dsimp only [rotStart, sh]
      rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
      have : t.val + (blk0.val + m - t.val) = blk0.val + m := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt blk0.isLt]
    have hbij := rotAct_rotStart_bij (b := b) hm sh
    refine Finset.card_bij (fun p _ => (rotAct hm sh p.1, rotStart hm sh p.2)) ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      rw [chosenBlk_rot, hp.1, hrot_t, firstConstBlk_rot, hp.2]
      exact ⟨rfl, rfl⟩
    · intro p1 _ p2 _ heq; exact hbij.1 heq
    · intro q hq
      obtain ⟨p, rfl⟩ := hbij.2 q
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
      refine ⟨p, ?_, rfl⟩
      rw [chosenBlk_rot, firstConstBlk_rot] at hq
      exact ⟨rotStart_inj hm sh (hq.1.trans hrot_t.symm), hq.2⟩
  let hitSet : Finset ((Fin m → Fin b → Bool) × Fin m) :=
    Finset.univ.filter (fun p => (firstConstBlk hb hm p.1 p.2).isSome = true)
  have hhit_card : hitSet.card = m * (2 ^ (b * m) - (2 ^ b - 2) ^ m) := by
    have hprod : hitSet =
        ((Finset.univ : Finset (Fin m → Fin b → Bool)).filter (fun A =>
          ∃ blk : Fin m, ∀ j : Fin b, A blk j = A blk ⟨0, hb⟩)) ×ˢ (Finset.univ : Finset (Fin m)) := by
      ext ⟨A, s⟩
      simp only [hitSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product, and_true]
      exact firstConstBlk_isSome_iff hb hm A s
    rw [hprod, Finset.card_product, isConst_count b m hb, Finset.card_univ, Fintype.card_fin, mul_comm]
  have hsum := Finset.card_eq_sum_card_fiberwise
    (f := fun p : (Fin m → Fin b → Bool) × Fin m => chosenBlk hb hm p.1 p.2)
    (s := hitSet) (t := (Finset.univ : Finset (Fin m)))
    (fun _ _ => Finset.mem_univ _)
  have hflt_eq : ∀ t : Fin m,
      hitSet.filter (fun p => chosenBlk hb hm p.1 p.2 = t) =
        Finset.univ.filter (fun p => chosenBlk hb hm p.1 p.2 = t ∧ (firstConstBlk hb hm p.1 p.2).isSome = true) := by
    intro t
    ext p
    simp only [hitSet, Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  have hsum2 : (∑ t : Fin m, (hitSet.filter (fun p => chosenBlk hb hm p.1 p.2 = t)).card) =
      m * ((Finset.univ : Finset ((Fin m → Fin b → Bool) × Fin m)).filter
        (fun p => chosenBlk hb hm p.1 p.2 = blk0 ∧ (firstConstBlk hb hm p.1 p.2).isSome = true)).card := by
    rw [Finset.sum_congr rfl fun t _ => by rw [hflt_eq t, heq_fib t], Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [hhit_card, hsum2] at hsum
  exact Nat.eq_of_mul_eq_mul_left hm hsum.symm

private lemma bank0_sum_same_blk {b m : ℕ} (hb : 0 < b) (hm : 0 < m)
    (blk0 : Fin m) (off1 : Fin b) :
    ∑ p ∈ (Finset.univ : Finset ((Fin m → Fin b → Bool) × Fin m)).filter
        (fun p => chosenBlk hb hm p.1 p.2 = blk0),
      sgn (xor (p.1 blk0 off1)
        (if (firstConstBlk hb hm p.1 p.2).isSome then p.1 blk0 ⟨0, hb⟩ else false)) =
      ((2 ^ (b * m) - (2 ^ b - 2) ^ m : ℕ) : ℤ) := by
  let S := (Finset.univ : Finset ((Fin m → Fin b → Bool) × Fin m)).filter
    (fun p => chosenBlk hb hm p.1 p.2 = blk0)
  let S1 := S.filter (fun p => (firstConstBlk hb hm p.1 p.2).isSome = true)
  let S0 := S.filter (fun p => (firstConstBlk hb hm p.1 p.2).isSome = false)
  have hpart : S = S1 ∪ S0 := by
    ext p; simp only [S1, S0, Finset.mem_union, Finset.mem_filter]
    cases (firstConstBlk hb hm p.1 p.2).isSome <;> simp
  have hdisj : Disjoint S1 S0 := by
    rw [Finset.disjoint_left]; intro p h1 h0
    have a1 := (Finset.mem_filter.mp h1).2
    have a0 := (Finset.mem_filter.mp h0).2
    rw [a1] at a0; cases a0
  change ∑ p ∈ S, _ = _
  rw [hpart, Finset.sum_union hdisj]
  have hsum1 : ∑ p ∈ S1,
      sgn (xor (p.1 blk0 off1)
        (if (firstConstBlk hb hm p.1 p.2).isSome then p.1 blk0 ⟨0, hb⟩ else false)) =
      (S1.card : ℤ) := by
    have hconst : ∀ p ∈ S1,
        sgn (xor (p.1 blk0 off1)
          (if (firstConstBlk hb hm p.1 p.2).isSome then p.1 blk0 ⟨0, hb⟩ else false)) = 1 := by
      intro p hp
      have hpS : chosenBlk hb hm p.1 p.2 = blk0 := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
      have hsome : (firstConstBlk hb hm p.1 p.2).isSome = true := (Finset.mem_filter.mp hp).2
      rw [Option.isSome_iff_exists] at hsome
      rcases hsome with ⟨d, hd⟩
      have hcb := chosenBlk_isConst_of_some hb hm p.1 p.2 d hd
      rw [hpS] at hcb
      rw [hd]
      simp only [Option.isSome_some, ↓reduceIte, hcb off1, Bool.xor_self]
      rfl
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hsum0 : ∑ p ∈ S0,
      sgn (xor (p.1 blk0 off1)
        (if (firstConstBlk hb hm p.1 p.2).isSome then p.1 blk0 ⟨0, hb⟩ else false)) = 0 := by
    let τ : ((Fin m → Fin b → Bool) × Fin m) → ((Fin m → Fin b → Bool) × Fin m) :=
      fun p => (fun blk j => !(p.1 blk j), p.2)
    have hτ_const : ∀ (A : Fin m → Fin b → Bool) (blk : Fin m),
        isConstBlk hb (fun blk' j => !(A blk' j)) blk = isConstBlk hb A blk := by
      intro A blk
      unfold isConstBlk
      simp only [Bool.not_inj_iff]
    have hτ_fc : ∀ p, firstConstBlk hb hm (τ p).1 (τ p).2 = firstConstBlk hb hm p.1 p.2 := by
      intro p; unfold firstConstBlk; congr 1; funext d; exact hτ_const p.1 _
    have hτ_cb : ∀ p, chosenBlk hb hm (τ p).1 (τ p).2 = chosenBlk hb hm p.1 p.2 := by
      intro p; unfold chosenBlk; rw [hτ_fc]
    refine sum_eq_zero_of_invol S0 _ τ ?_ ?_ ?_
    · intro p hp
      simp only [S0, S, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      rw [hτ_cb, hτ_fc]; exact hp
    · intro p _
      apply Prod.ext
      · funext blk j; simp [τ]
      · rfl
    · intro p hp
      have hnone : (firstConstBlk hb hm p.1 p.2).isSome = false := (Finset.mem_filter.mp hp).2
      rw [hτ_fc, hnone]
      simp only [Bool.false_eq_true, ↓reduceIte, Bool.xor_false, τ]
      exact sgn_not _
  have hS1_eq : S1 = (Finset.univ : Finset ((Fin m → Fin b → Bool) × Fin m)).filter
      (fun p => chosenBlk hb hm p.1 p.2 = blk0 ∧ (firstConstBlk hb hm p.1 p.2).isSome = true) := by
    ext p; simp only [S1, S, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hsum1, hsum0, add_zero, hS1_eq, chosenBlk_hit_fiber_card hb hm blk0]

private lemma bank0_sum_diff_blk {b m : ℕ} (hb : 0 < b) (hm : 0 < m)
    (blk0 blk1 : Fin m) (hne : blk1 ≠ blk0) (off1 : Fin b) :
    ∑ p ∈ (Finset.univ : Finset ((Fin m → Fin b → Bool) × Fin m)).filter
        (fun p => chosenBlk hb hm p.1 p.2 = blk0),
      sgn (xor (p.1 blk1 off1)
        (if (firstConstBlk hb hm p.1 p.2).isSome then p.1 blk0 ⟨0, hb⟩ else false)) = 0 := by
  let S := (Finset.univ : Finset ((Fin m → Fin b → Bool) × Fin m)).filter
    (fun p => chosenBlk hb hm p.1 p.2 = blk0)
  let τ : ((Fin m → Fin b → Bool) × Fin m) → ((Fin m → Fin b → Bool) × Fin m) :=
    fun p => (fun blk j => if blk = blk1 then !(p.1 blk j) else p.1 blk j, p.2)
  have hτ_const : ∀ A blk, isConstBlk hb (fun blk' j => if blk' = blk1 then !(A blk' j) else A blk' j) blk =
      isConstBlk hb A blk := by
    intro A blk
    unfold isConstBlk
    by_cases h : blk = blk1
    · simp only [h, ↓reduceIte, Bool.not_inj_iff]
    · simp only [h, ↓reduceIte]
  have hτ_fc : ∀ p, firstConstBlk hb hm (τ p).1 (τ p).2 = firstConstBlk hb hm p.1 p.2 := by
    intro p; unfold firstConstBlk; congr 1; funext d; exact hτ_const p.1 _
  have hτ_cb : ∀ p, chosenBlk hb hm (τ p).1 (τ p).2 = chosenBlk hb hm p.1 p.2 := by
    intro p; unfold chosenBlk; rw [hτ_fc]
  refine sum_eq_zero_of_invol S _ τ ?_ ?_ ?_
  · intro p hp
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    rw [hτ_cb]; exact hp
  · intro p _
    apply Prod.ext
    · funext blk j; dsimp only [τ]; split_ifs <;> simp
    · rfl
  · intro p _
    rw [hτ_fc]
    dsimp only [τ]
    have hne' : blk0 ≠ blk1 := hne.symm
    simp only [↓reduceIte, hne']
    have hflip : ∀ x y : Bool, sgn (xor (!x) y) = -sgn (xor x y) := by decide
    exact hflip _ _

private lemma glue_fiber_perm {N r : ℕ} (f g : Fin N → Fin r)
    (hcard : ∀ i : Fin r,
      ((Finset.univ : Finset (Fin N)).filter (fun x => f x = i)).card =
      ((Finset.univ : Finset (Fin N)).filter (fun y => g y = i)).card) :
    ∃ π : Equiv.Perm (Fin N), ∀ x : Fin N, g (π x) = f x := by
  let A : Fin r → Finset (Fin N) := fun i => Finset.univ.filter (fun x => f x = i)
  let B : Fin r → Finset (Fin N) := fun i => Finset.univ.filter (fun y => g y = i)
  let ei : ∀ i : Fin r, {x : Fin N // x ∈ A i} ≃ {y : Fin N // y ∈ B i} := fun i =>
    Fintype.equivOfCardEq (by simp only [Fintype.card_coe]; exact hcard i)
  have hmemA : ∀ x : Fin N, x ∈ A (f x) := fun x => by simp [A]
  have hmemB : ∀ y : Fin N, y ∈ B (g y) := fun y => by simp [B]
  let π : Equiv.Perm (Fin N) :=
    { toFun := fun x => (ei (f x) ⟨x, hmemA x⟩).val
      invFun := fun y => ((ei (g y)).symm ⟨y, hmemB y⟩).val
      left_inv := fun x => by
        set y := (ei (f x) ⟨x, hmemA x⟩).val
        have hy : g y = f x := (Finset.mem_filter.mp (ei (f x) ⟨x, hmemA x⟩).property).2
        have hpair : ∀ (i : Fin r) (hi : i = f x) (hyi : y ∈ B i),
            ((ei i).symm ⟨y, hyi⟩).val = x := by
          intro i hi hyi
          subst hi
          have heq : (⟨y, hyi⟩ : {u : Fin N // u ∈ B (f x)}) = ei (f x) ⟨x, hmemA x⟩ :=
            Subtype.ext rfl
          rw [heq, Equiv.symm_apply_apply]
        exact hpair _ hy _
      right_inv := fun y => by
        set x := ((ei (g y)).symm ⟨y, hmemB y⟩).val
        have hx : f x = g y := (Finset.mem_filter.mp ((ei (g y)).symm ⟨y, hmemB y⟩).property).2
        have hpair : ∀ (i : Fin r) (hi : i = g y) (hxi : x ∈ A i),
            (ei i ⟨x, hxi⟩).val = y := by
          intro i hi hxi
          subst hi
          have heq : (⟨x, hxi⟩ : {u : Fin N // u ∈ A (g y)}) = (ei (g y)).symm ⟨y, hmemB y⟩ :=
            Subtype.ext rfl
          rw [heq, Equiv.apply_symm_apply]
        exact hpair _ hx _ }
  refine ⟨π, fun x => ?_⟩
  exact (Finset.mem_filter.mp (ei (f x) ⟨x, hmemA x⟩).property).2

private abbrev PackT (k a c : ℕ) :=
  ((Fin (2 ^ (a - 1 - c)) → Fin (2 ^ c) → Bool) × Fin (2 ^ (a - 1 - c))) ×
    Bool × Fin (2 ^ c) × (Fin (k - (2 ^ a / 2 + a)) → Bool)

private lemma mul_add_lt_r2 {a c : ℕ} (ha : 2 ≤ a) (hca : c < a)
    (blk : Fin (2 ^ (a - 1 - c))) (off : Fin (2 ^ c)) :
    blk.val * 2 ^ c + off.val < 2 ^ a / 2 := by
  have hbm : 2 ^ (a - 1 - c) * 2 ^ c = 2 ^ a / 2 := by
    rw [← pow_add, show a - 1 - c + c = a - 1 by omega]
    have hpow : 2 ^ a = 2 * 2 ^ (a - 1) := by
      conv_lhs => rw [show a = (a - 1) + 1 by omega]
      rw [pow_succ]; ring
    omega
  calc
    blk.val * 2 ^ c + off.val < blk.val * 2 ^ c + 2 ^ c := Nat.add_lt_add_left off.isLt _
    _ = (blk.val + 1) * 2 ^ c := by ring
    _ ≤ 2 ^ (a - 1 - c) * 2 ^ c := Nat.mul_le_mul_right _ blk.isLt
    _ = 2 ^ a / 2 := hbm

private lemma r2_bounds {k a c : ℕ} (ha : 2 ≤ a) (hrk : 2 ^ a ≤ k) (hca : c < a) :
    2 * (2 ^ a / 2) = 2 ^ a ∧ 2 ≤ 2 ^ a / 2 ∧ 2 ^ a / 2 + a ≤ k ∧
      2 ^ c * 2 ^ (a - 1 - c) = 2 ^ a / 2 := by
  have hpow : 2 ^ a = 2 * 2 ^ (a - 1) := by
    conv_lhs => rw [show a = (a - 1) + 1 by omega]
    rw [pow_succ]; ring
  have hge4 : 4 ≤ 2 ^ a := by
    calc 4 = 2 ^ 2 := by decide
      _ ≤ 2 ^ a := Nat.pow_le_pow_right (by decide) ha
  have hale : a ≤ 2 ^ (a - 1) := le_two_pow_sub_one a (by omega)
  have hbm : 2 ^ c * 2 ^ (a - 1 - c) = 2 ^ a / 2 := by
    rw [← pow_add, show c + (a - 1 - c) = a - 1 by omega]
    omega
  refine ⟨by omega, by omega, by omega, hbm⟩

private def packEquiv (k a c : ℕ) (ha : 2 ≤ a) (hrk : 2 ^ a ≤ k) (hca : c < a) :
    (Fin k → Bool) ≃ PackT k a c :=
  let hb := r2_bounds ha hrk hca
  let eM := finPowTwoEquiv (a - 1 - c)
  let eB := finPowTwoEquiv c
  let idxAct : Fin (2 ^ (a - 1 - c)) → Fin (2 ^ c) → Fin k := fun blk off =>
    ⟨blk.val * 2 ^ c + off.val, by have := mul_add_lt_r2 ha hca blk off; omega⟩
  let idxBank : Fin k := ⟨2 ^ a / 2, by omega⟩
  let idxStart : Fin (a - 1 - c) → Fin k := fun i => ⟨2 ^ a / 2 + 1 + i.val, by omega⟩
  let idxOff : Fin c → Fin k := fun i => ⟨2 ^ a / 2 + 1 + (a - 1 - c) + i.val, by omega⟩
  let idxRest : Fin (k - (2 ^ a / 2 + a)) → Fin k := fun i => ⟨2 ^ a / 2 + a + i.val, by omega⟩
  let toP : (Fin k → Bool) → PackT k a c := fun v =>
    (((fun blk off => v (idxAct blk off)), eM.symm (fun i => v (idxStart i))),
     v idxBank,
     eB.symm (fun i => v (idxOff i)),
     fun i => v (idxRest i))
  let ofP : PackT k a c → (Fin k → Bool) := fun p j =>
    if h1 : j.val < 2 ^ a / 2 then
      p.1.1 ⟨j.val / 2 ^ c, (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos c)).mpr (by rw [mul_comm, hb.2.2.2]; exact h1)⟩
        ⟨j.val % 2 ^ c, Nat.mod_lt _ (Nat.two_pow_pos c)⟩
    else if h2 : j.val = 2 ^ a / 2 then p.2.1
    else if h3 : j.val < 2 ^ a / 2 + 1 + (a - 1 - c) then
      eM p.1.2 ⟨j.val - (2 ^ a / 2 + 1), by omega⟩
    else if h4 : j.val < 2 ^ a / 2 + a then
      eB p.2.2.1 ⟨j.val - (2 ^ a / 2 + 1 + (a - 1 - c)), by omega⟩
    else
      p.2.2.2 ⟨j.val - (2 ^ a / 2 + a), by omega⟩
  { toFun := toP
    invFun := ofP
    left_inv := fun v => by
      funext j
      dsimp only [ofP, toP]
      by_cases h1 : j.val < 2 ^ a / 2
      · rw [dif_pos h1]
        congr 1; apply Fin.ext; dsimp only [idxAct]
        rw [mul_comm]; exact Nat.div_add_mod j.val (2 ^ c)
      · rw [dif_neg h1]
        by_cases h2 : j.val = 2 ^ a / 2
        · rw [dif_pos h2]; congr 1; exact Fin.ext h2.symm
        · rw [dif_neg h2]
          by_cases h3 : j.val < 2 ^ a / 2 + 1 + (a - 1 - c)
          · rw [dif_pos h3, Equiv.apply_symm_apply]
            congr 1; apply Fin.ext; dsimp only [idxStart]; omega
          · rw [dif_neg h3]
            by_cases h4 : j.val < 2 ^ a / 2 + a
            · rw [dif_pos h4, Equiv.apply_symm_apply]
              congr 1; apply Fin.ext; dsimp only [idxOff]; omega
            · rw [dif_neg h4]
              congr 1; apply Fin.ext; dsimp only [idxRest]; omega
    right_inv := fun p => by
      rcases p with ⟨⟨A, st⟩, bk, of, rst⟩
      apply Prod.ext
      · apply Prod.ext
        · funext blk off
          dsimp only [toP, ofP, idxAct]
          rw [dif_pos (mul_add_lt_r2 ha hca blk off)]
          have hd : (blk.val * 2 ^ c + off.val) / 2 ^ c = blk.val := by
            rw [Nat.mul_comm, Nat.mul_add_div (Nat.two_pow_pos c), Nat.div_eq_of_lt off.isLt, add_zero]
          have hm' : (blk.val * 2 ^ c + off.val) % 2 ^ c = off.val := by
            rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt off.isLt]
          congr 1
          · exact Fin.ext hd
          · exact Fin.ext hm'
        · dsimp only [toP]
          have hfun : (fun i : Fin (a - 1 - c) => ofP ((A, st), bk, of, rst) (idxStart i)) = eM st := by
            funext i
            dsimp only [ofP, idxStart]
            rw [dif_neg (by omega), dif_neg (by omega), dif_pos (by omega)]
            exact congrArg (eM st) (Fin.ext (by dsimp only; omega))
          rw [hfun, Equiv.symm_apply_apply]
      · apply Prod.ext
        · dsimp only [toP, ofP, idxBank]
          rw [dif_neg (by omega), dif_pos rfl]
        · apply Prod.ext
          · dsimp only [toP]
            have hfun : (fun i : Fin c => ofP ((A, st), bk, of, rst) (idxOff i)) = eB of := by
              funext i
              dsimp only [ofP, idxOff]
              rw [dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), dif_pos (by omega)]
              exact congrArg (eB of) (Fin.ext (by dsimp only; omega))
            rw [hfun, Equiv.symm_apply_apply]
          · funext i
            dsimp only [toP, ofP, idxRest]
            rw [dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), dif_neg (by omega)]
            congr 1; apply Fin.ext; dsimp only; omega }

private def lblOf (k a c : ℕ) (ha : 2 ≤ a) (hrk : 2 ^ a ≤ k) (hca : c < a)
    (p : PackT k a c) : Fin (2 ^ a) :=
  let hb := r2_bounds ha hrk hca
  if p.2.1 = false then
    let blk := chosenBlk (Nat.two_pow_pos c) (Nat.two_pow_pos (a - 1 - c)) p.1.1 p.1.2
    ⟨blk.val * 2 ^ c + p.2.2.1.val, by have := mul_add_lt_r2 ha hca blk p.2.2.1; omega⟩
  else
    ⟨2 ^ a / 2 + p.1.2.val * 2 ^ c + p.2.2.1.val, by have := mul_add_lt_r2 ha hca p.1.2 p.2.2.1; omega⟩

private def flpOf (k a c : ℕ) (ha : 2 ≤ a) (hrk : 2 ^ a ≤ k) (hca : c < a)
    (p : PackT k a c) : Bool :=
  let hb := r2_bounds ha hrk hca
  if p.2.1 = false then
    if (firstConstBlk (Nat.two_pow_pos c) (Nat.two_pow_pos (a - 1 - c)) p.1.1 p.1.2).isSome then
      p.1.1 (chosenBlk (Nat.two_pow_pos c) (Nat.two_pow_pos (a - 1 - c)) p.1.1 p.1.2) ⟨0, Nat.two_pow_pos c⟩
    else false
  else
    xor ((packEquiv k a c ha hrk hca).symm p ⟨0, by omega⟩)
        ((packEquiv k a c ha hrk hca).symm p ⟨1, by omega⟩)

private lemma lblOf_lt_r2_set (k a c : ℕ) (ha : 2 ≤ a) (hrk : 2 ^ a ≤ k) (hca : c < a)
    (i : Fin (2 ^ a)) (hi : i.val < 2 ^ a / 2) :
    let hb := r2_bounds ha hrk hca
    let blk0 : Fin (2 ^ (a - 1 - c)) :=
      ⟨i.val / 2 ^ c, (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos c)).mpr (by rw [mul_comm, hb.2.2.2]; exact hi)⟩
    let off0 : Fin (2 ^ c) := ⟨i.val % 2 ^ c, Nat.mod_lt _ (Nat.two_pow_pos c)⟩
    (Finset.univ : Finset (PackT k a c)).filter (fun p => lblOf k a c ha hrk hca p = i) =
      ((Finset.univ : Finset ((Fin (2 ^ (a - 1 - c)) → Fin (2 ^ c) → Bool) × Fin (2 ^ (a - 1 - c)))).filter
          (fun q => chosenBlk (Nat.two_pow_pos c) (Nat.two_pow_pos (a - 1 - c)) q.1 q.2 = blk0)) ×ˢ
        (({false} : Finset Bool) ×ˢ (({off0} : Finset (Fin (2 ^ c))) ×ˢ
          (Finset.univ : Finset (Fin (k - (2 ^ a / 2 + a)) → Bool)))) := by
  intro hb blk0 off0
  ext ⟨⟨A, st⟩, bk, of, rst⟩
  rw [Finset.mem_filter, Finset.mem_product, Finset.mem_filter, Finset.mem_product,
    Finset.mem_product, Finset.mem_singleton, Finset.mem_singleton]
  simp only [Finset.mem_univ, true_and, and_true]
  constructor
  · intro heq
    have hbk : bk = false := by
      by_contra hne
      have hbt : bk = true := by cases bk <;> simp_all
      have hv := congrArg Fin.val heq
      simp only [lblOf, hbt, Bool.true_eq_false, ↓reduceIte] at hv
      omega
    have hv := congrArg Fin.val heq
    simp only [lblOf, hbk, ↓reduceIte] at hv
    have hd : (chosenBlk (Nat.two_pow_pos c) (Nat.two_pow_pos (a - 1 - c)) A st).val = i.val / 2 ^ c := by
      have := congrArg (· / 2 ^ c) hv
      rw [Nat.mul_comm, Nat.mul_add_div (Nat.two_pow_pos c), Nat.div_eq_of_lt of.isLt, add_zero] at this
      exact this
    have hm' : of.val = i.val % 2 ^ c := by
      have := congrArg (· % 2 ^ c) hv
      rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt of.isLt] at this
      exact this
    exact ⟨Fin.ext hd, hbk, Fin.ext hm'⟩
  · rintro ⟨hcb, rfl, rfl⟩
    apply Fin.ext
    simp only [lblOf, ↓reduceIte, hcb]
    dsimp only [blk0, off0]
    rw [mul_comm]
    exact Nat.div_add_mod i.val (2 ^ c)

private lemma lblOf_ge_r2_set (k a c : ℕ) (ha : 2 ≤ a) (hrk : 2 ^ a ≤ k) (hca : c < a)
    (i : Fin (2 ^ a)) (hi : 2 ^ a / 2 ≤ i.val) :
    let hb := r2_bounds ha hrk hca
    let blk0 : Fin (2 ^ (a - 1 - c)) :=
      ⟨(i.val - 2 ^ a / 2) / 2 ^ c,
        (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos c)).mpr (by rw [mul_comm, hb.2.2.2]; have := i.isLt; omega)⟩
    let off0 : Fin (2 ^ c) := ⟨(i.val - 2 ^ a / 2) % 2 ^ c, Nat.mod_lt _ (Nat.two_pow_pos c)⟩
    (Finset.univ : Finset (PackT k a c)).filter (fun p => lblOf k a c ha hrk hca p = i) =
      ((Finset.univ : Finset (Fin (2 ^ (a - 1 - c)) → Fin (2 ^ c) → Bool)) ×ˢ
          ({blk0} : Finset (Fin (2 ^ (a - 1 - c))))) ×ˢ
        (({true} : Finset Bool) ×ˢ (({off0} : Finset (Fin (2 ^ c))) ×ˢ
          (Finset.univ : Finset (Fin (k - (2 ^ a / 2 + a)) → Bool)))) := by
  intro hb blk0 off0
  ext ⟨⟨A, st⟩, bk, of, rst⟩
  rw [Finset.mem_filter, Finset.mem_product, Finset.mem_product, Finset.mem_product,
    Finset.mem_product, Finset.mem_singleton, Finset.mem_singleton, Finset.mem_singleton]
  simp only [Finset.mem_univ, true_and, and_true]
  constructor
  · intro heq
    have hbk : bk = true := by
      by_contra hne
      have hbf : bk = false := by cases bk <;> simp_all
      have hv := congrArg Fin.val heq
      simp only [lblOf, hbf, ↓reduceIte] at hv
      have := mul_add_lt_r2 ha hca (chosenBlk (Nat.two_pow_pos c) (Nat.two_pow_pos (a - 1 - c)) A st) of
      omega
    have hv := congrArg Fin.val heq
    simp only [lblOf, hbk, Bool.true_eq_false, ↓reduceIte] at hv
    have hv' : st.val * 2 ^ c + of.val = i.val - 2 ^ a / 2 := by omega
    have hd : st.val = (i.val - 2 ^ a / 2) / 2 ^ c := by
      have := congrArg (· / 2 ^ c) hv'
      rw [Nat.mul_comm, Nat.mul_add_div (Nat.two_pow_pos c), Nat.div_eq_of_lt of.isLt, add_zero] at this
      exact this
    have hm' : of.val = (i.val - 2 ^ a / 2) % 2 ^ c := by
      have := congrArg (· % 2 ^ c) hv'
      rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt of.isLt] at this
      exact this
    exact ⟨Fin.ext hd, hbk, Fin.ext hm'⟩
  · rintro ⟨rfl, rfl, rfl⟩
    apply Fin.ext
    simp only [lblOf, Bool.true_eq_false, ↓reduceIte]
    dsimp only [blk0, off0]
    have hdm := Nat.div_add_mod (i.val - 2 ^ a / 2) (2 ^ c)
    have : ((i.val - 2 ^ a / 2) / 2 ^ c) * 2 ^ c + (i.val - 2 ^ a / 2) % 2 ^ c = i.val - 2 ^ a / 2 := by
      rw [mul_comm]; exact hdm
    omega

private lemma lblOf_card (k a c : ℕ) (ha : 2 ≤ a) (hrk : 2 ^ a ≤ k) (hca : c < a) (i : Fin (2 ^ a)) :
    ((Finset.univ : Finset (PackT k a c)).filter (fun p => lblOf k a c ha hrk hca p = i)).card =
      2 ^ (2 ^ a / 2) * 2 ^ (k - (2 ^ a / 2 + a)) := by
  have hb := r2_bounds ha hrk hca
  by_cases hi : i.val < 2 ^ a / 2
  · rw [lblOf_lt_r2_set k a c ha hrk hca i hi,
      Finset.card_product, Finset.card_product, Finset.card_product,
      Finset.card_singleton, Finset.card_singleton,
      chosenBlk_fiber_card (Nat.two_pow_pos c) (Nat.two_pow_pos (a - 1 - c)),
      hb.2.2.2]
    simp [Fintype.card_fun]
  · rw [lblOf_ge_r2_set k a c ha hrk hca i (by omega),
      Finset.card_product, Finset.card_product, Finset.card_product, Finset.card_product,
      Finset.card_singleton, Finset.card_singleton, Finset.card_singleton]
    simp [Fintype.card_fun, ← pow_mul, hb.2.2.2]

private lemma bank1_W_zero (k a c : ℕ) (ha : 2 ≤ a) (hrk : 2 ^ a ≤ k) (hca : c < a)
    (i j : Fin (2 ^ a)) (hi : 2 ^ a / 2 ≤ i.val) :
    ∑ p ∈ (Finset.univ : Finset (PackT k a c)).filter (fun p => lblOf k a c ha hrk hca p = i),
      sgn (xor ((packEquiv k a c ha hrk hca).symm p ⟨j.val, by have := j.isLt; omega⟩)
        (flpOf k a c ha hrk hca p)) = 0 := by
  have hb := r2_bounds ha hrk hca
  have hr2_ge2 : 2 ≤ 2 ^ a / 2 := hb.2.1
  have hr2_k : 2 ^ a / 2 + a ≤ k := hb.2.2.1
  let eP := packEquiv k a c ha hrk hca
  let pos : Fin k := if j.val = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩
  have hpos_lt : pos.val < 2 ^ a / 2 := by
    by_cases hj0 : j.val = 0
    · simp only [pos, hj0, ↓reduceIte]; omega
    · simp only [pos, hj0, ↓reduceIte]; omega
  have hpos_ne : pos.val ≠ j.val := by
    by_cases hj0 : j.val = 0
    · simp only [pos, hj0, ↓reduceIte]; omega
    · simp only [pos, hj0, ↓reduceIte]; omega
  let flipBit : (Fin k → Bool) → (Fin k → Bool) := fun v t => if t = pos then !(v t) else v t
  let τ : PackT k a c → PackT k a c := fun p => eP (flipBit (eP.symm p))
  have hτ_symm : ∀ p t, eP.symm (τ p) t = if t = pos then !(eP.symm p t) else eP.symm p t := by
    intro p t; dsimp only [τ, flipBit]; rw [Equiv.symm_apply_apply]
  have hτ_inv : ∀ p, τ (τ p) = p := by
    intro p
    apply eP.symm.injective
    funext t
    rw [hτ_symm, hτ_symm]
    split_ifs <;> simp
  have hτ_eq_high : ∀ p (t : Fin k), 2 ^ a / 2 ≤ t.val → eP.symm (τ p) t = eP.symm p t := by
    intro p t ht
    rw [hτ_symm, if_neg]
    intro h; have := congrArg Fin.val h; omega
  have hτ_bk : ∀ p, (τ p).2.1 = p.2.1 := by
    intro p
    have h1 : (τ p).2.1 = eP.symm (τ p) ⟨2 ^ a / 2, by omega⟩ := by
      have := congrArg (fun q : PackT k a c => q.2.1) (Equiv.apply_symm_apply eP (τ p))
      exact this.symm
    have h2 : p.2.1 = eP.symm p ⟨2 ^ a / 2, by omega⟩ := by
      have := congrArg (fun q : PackT k a c => q.2.1) (Equiv.apply_symm_apply eP p)
      exact this.symm
    rw [h1, h2]; exact hτ_eq_high p _ le_rfl
  have hτ_st : ∀ p, (τ p).1.2 = p.1.2 := by
    intro p
    have h1 : (τ p).1.2 = (finPowTwoEquiv (a - 1 - c)).symm
        (fun s => eP.symm (τ p) ⟨2 ^ a / 2 + 1 + s.val, by omega⟩) := by
      have := congrArg (fun q : PackT k a c => q.1.2) (Equiv.apply_symm_apply eP (τ p))
      exact this.symm
    have h2 : p.1.2 = (finPowTwoEquiv (a - 1 - c)).symm
        (fun s => eP.symm p ⟨2 ^ a / 2 + 1 + s.val, by omega⟩) := by
      have := congrArg (fun q : PackT k a c => q.1.2) (Equiv.apply_symm_apply eP p)
      exact this.symm
    rw [h1, h2]; congr 1; funext s; exact hτ_eq_high p _ (by dsimp; omega)
  have hτ_of : ∀ p, (τ p).2.2.1 = p.2.2.1 := by
    intro p
    have h1 : (τ p).2.2.1 = (finPowTwoEquiv c).symm
        (fun s => eP.symm (τ p) ⟨2 ^ a / 2 + 1 + (a - 1 - c) + s.val, by omega⟩) := by
      have := congrArg (fun q : PackT k a c => q.2.2.1) (Equiv.apply_symm_apply eP (τ p))
      exact this.symm
    have h2 : p.2.2.1 = (finPowTwoEquiv c).symm
        (fun s => eP.symm p ⟨2 ^ a / 2 + 1 + (a - 1 - c) + s.val, by omega⟩) := by
      have := congrArg (fun q : PackT k a c => q.2.2.1) (Equiv.apply_symm_apply eP p)
      exact this.symm
    rw [h1, h2]; congr 1; funext s; exact hτ_eq_high p _ (by dsimp; omega)
  have hbk_true : ∀ p, lblOf k a c ha hrk hca p = i → p.2.1 = true := by
    intro p hp
    by_contra hne
    have hbf : p.2.1 = false := Bool.eq_false_iff.mpr hne
    have hv := congrArg Fin.val hp
    unfold lblOf at hv
    rw [if_pos hbf] at hv
    dsimp only at hv
    have := mul_add_lt_r2 ha hca
      (chosenBlk (Nat.two_pow_pos c) (Nat.two_pow_pos (a - 1 - c)) p.1.1 p.1.2) p.2.2.1
    omega
  refine sum_eq_zero_of_invol _ _ τ ?_ (fun p _ => hτ_inv p) ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    have hbt : p.2.1 = true := hbk_true p hp
    have hbt' : (τ p).2.1 = true := (hτ_bk p).trans hbt
    rw [← hp]
    apply Fin.ext
    unfold lblOf
    rw [if_neg (by rw [hbt']; decide), if_neg (by rw [hbt]; decide)]
    dsimp only
    rw [hτ_st p, hτ_of p]
  · intro p hp
    have hp_eq : lblOf k a c ha hrk hca p = i := (Finset.mem_filter.mp hp).2
    have hbt : p.2.1 = true := hbk_true p hp_eq
    have hbt' : (τ p).2.1 = true := (hτ_bk p).trans hbt
    have hj_eq : eP.symm (τ p) ⟨j.val, by have := j.isLt; omega⟩ =
        eP.symm p ⟨j.val, by have := j.isLt; omega⟩ := by
      rw [hτ_symm, if_neg]
      intro h; exact hpos_ne (congrArg Fin.val h).symm
    have hflp_neg : flpOf k a c ha hrk hca (τ p) = !(flpOf k a c ha hrk hca p) := by
      unfold flpOf
      rw [if_neg (by rw [hbt']; decide), if_neg (by rw [hbt]; decide)]
      change xor (eP.symm (τ p) ⟨0, by omega⟩) (eP.symm (τ p) ⟨1, by omega⟩) =
        !(xor (eP.symm p ⟨0, by omega⟩) (eP.symm p ⟨1, by omega⟩))
      rw [hτ_symm, hτ_symm]
      by_cases hj0 : j.val = 0
      · have hp1 : pos = ⟨1, by omega⟩ := by simp [pos, hj0]
        have h01 : (⟨0, by omega⟩ : Fin k) ≠ ⟨1, by omega⟩ := by
          intro h; have h' := congrArg Fin.val h; dsimp only at h'; omega
        rw [hp1, if_neg h01, if_pos rfl]
        cases eP.symm p ⟨0, by omega⟩ <;> cases eP.symm p ⟨1, by omega⟩ <;> decide
      · have hp0 : pos = ⟨0, by omega⟩ := by simp [pos, hj0]
        have h10 : (⟨1, by omega⟩ : Fin k) ≠ ⟨0, by omega⟩ := by
          intro h; have h' := congrArg Fin.val h; dsimp only at h'; omega
        rw [hp0, if_pos rfl, if_neg h10]
        cases eP.symm p ⟨0, by omega⟩ <;> cases eP.symm p ⟨1, by omega⟩ <;> decide
    change sgn (xor (eP.symm (τ p) ⟨j.val, by have := j.isLt; omega⟩) (flpOf k a c ha hrk hca (τ p))) =
      -sgn (xor (eP.symm p ⟨j.val, by have := j.isLt; omega⟩) (flpOf k a c ha hrk hca p))
    rw [hj_eq, hflp_neg]
    cases eP.symm p ⟨j.val, by have := j.isLt; omega⟩ <;> cases flpOf k a c ha hrk hca p <;> decide

private lemma bank0_W_val (k a c : ℕ) (ha : 2 ≤ a) (hrk : 2 ^ a ≤ k) (hca : c < a)
    (i j : Fin (2 ^ a)) (hi : i.val < 2 ^ a / 2) (hj : j.val < 2 ^ a / 2) :
    ∑ p ∈ (Finset.univ : Finset (PackT k a c)).filter (fun p => lblOf k a c ha hrk hca p = i),
      sgn (xor ((packEquiv k a c ha hrk hca).symm p ⟨j.val, by have := j.isLt; omega⟩)
        (flpOf k a c ha hrk hca p)) =
      if i.val / 2 ^ c = j.val / 2 ^ c then
        (((2 ^ (2 ^ a / 2) - (2 ^ (2 ^ c) - 2) ^ (2 ^ (a - 1 - c))) *
          2 ^ (k - (2 ^ a / 2 + a)) : ℕ) : ℤ)
      else 0 := by
  have hb := r2_bounds ha hrk hca
  let blk0 : Fin (2 ^ (a - 1 - c)) :=
    ⟨i.val / 2 ^ c, (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos c)).mpr (by rw [mul_comm, hb.2.2.2]; exact hi)⟩
  let off0 : Fin (2 ^ c) := ⟨i.val % 2 ^ c, Nat.mod_lt _ (Nat.two_pow_pos c)⟩
  let blk1 : Fin (2 ^ (a - 1 - c)) :=
    ⟨j.val / 2 ^ c, (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos c)).mpr (by rw [mul_comm, hb.2.2.2]; exact hj)⟩
  let off1 : Fin (2 ^ c) := ⟨j.val % 2 ^ c, Nat.mod_lt _ (Nat.two_pow_pos c)⟩
  rw [lblOf_lt_r2_set k a c ha hrk hca i hi, Finset.sum_product]
  have hinner : ∀ q ∈ (Finset.univ : Finset ((Fin (2 ^ (a - 1 - c)) → Fin (2 ^ c) → Bool) × Fin (2 ^ (a - 1 - c)))).filter
      (fun q => chosenBlk (Nat.two_pow_pos c) (Nat.two_pow_pos (a - 1 - c)) q.1 q.2 = blk0),
      (∑ x ∈ ({false} : Finset Bool) ×ˢ (({off0} : Finset (Fin (2 ^ c))) ×ˢ
          (Finset.univ : Finset (Fin (k - (2 ^ a / 2 + a)) → Bool))),
        sgn (xor ((packEquiv k a c ha hrk hca).symm (q, x) ⟨j.val, by have := j.isLt; omega⟩)
          (flpOf k a c ha hrk hca (q, x)))) =
      (2 ^ (k - (2 ^ a / 2 + a)) : ℤ) *
        sgn (xor (q.1 blk1 off1)
          (if (firstConstBlk (Nat.two_pow_pos c) (Nat.two_pow_pos (a - 1 - c)) q.1 q.2).isSome then
            q.1 blk0 ⟨0, Nat.two_pow_pos c⟩ else false)) := by
    intro q hq
    have hcb : chosenBlk (Nat.two_pow_pos c) (Nat.two_pow_pos (a - 1 - c)) q.1 q.2 = blk0 :=
      (Finset.mem_filter.mp hq).2
    rw [Finset.sum_product, Finset.sum_singleton, Finset.sum_product, Finset.sum_singleton]
    have hconst : ∀ rst : Fin (k - (2 ^ a / 2 + a)) → Bool,
        sgn (xor ((packEquiv k a c ha hrk hca).symm (q, false, off0, rst) ⟨j.val, by have := j.isLt; omega⟩)
          (flpOf k a c ha hrk hca (q, false, off0, rst))) =
        sgn (xor (q.1 blk1 off1)
          (if (firstConstBlk (Nat.two_pow_pos c) (Nat.two_pow_pos (a - 1 - c)) q.1 q.2).isSome then
            q.1 blk0 ⟨0, Nat.two_pow_pos c⟩ else false)) := by
      intro rst
      have hbit : (packEquiv k a c ha hrk hca).symm (q, false, off0, rst) ⟨j.val, by have := j.isLt; omega⟩ =
          q.1 blk1 off1 := by
        simp only [packEquiv, Equiv.coe_fn_symm_mk]
        rw [dif_pos hj]
      have hflp : flpOf k a c ha hrk hca (q, false, off0, rst) =
          if (firstConstBlk (Nat.two_pow_pos c) (Nat.two_pow_pos (a - 1 - c)) q.1 q.2).isSome then
            q.1 blk0 ⟨0, Nat.two_pow_pos c⟩ else false := by
        unfold flpOf
        rw [if_pos rfl, hcb]
      rw [hbit, hflp]
    rw [Finset.sum_congr rfl fun rst _ => hconst rst, Finset.sum_const, Finset.card_univ,
      Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    rfl
  rw [Finset.sum_congr rfl hinner, ← Finset.mul_sum]
  by_cases hdiv : i.val / 2 ^ c = j.val / 2 ^ c
  · rw [if_pos hdiv]
    have hblk_eq : blk1 = blk0 := Fin.ext hdiv.symm
    rw [hblk_eq, bank0_sum_same_blk (Nat.two_pow_pos c) (Nat.two_pow_pos (a - 1 - c)) blk0 off1,
      hb.2.2.2]
    push_cast
    ring
  · rw [if_neg hdiv]
    have hblk_ne : blk1 ≠ blk0 := fun h => hdiv (congrArg Fin.val h).symm
    rw [bank0_sum_diff_blk (Nat.two_pow_pos c) (Nat.two_pow_pos (a - 1 - c)) blk0 blk1 hblk_ne off1,
      mul_zero]

end PEqualNP.Outside.L_meta_25700_aux

theorem PEqualNP.Outside.L_meta_25700 : (∀ (k a c : ℕ), 2 ≤ a → 2^a ≤ k → c < a →
  let N := 2^k
  let r := 2^a
  let b := 2^c
  let m := 2^(a-1-c)
  let Z := 2^(r/2)
  let hit := Z - (2^b-2)^m
  let base := fun (x y : Fin N) => x.val.testBit (y.val % r)
  ∃ (π : Equiv.Perm (Fin N)) (flip : Fin N → Bool),
    let errors := fun (G : Fin N → Fin N → Bool) (decode : Finset (Fin N) → Bool) =>
      (Finset.univ.filter (fun z : Fin N × Fin N =>
        decode ({z.1,z.2} : Finset (Fin N)) ≠ xor (G z.1 (π z.2)) (flip z.1))).card
    let cost := errors base
    ∃ best : Finset (Fin N) → Bool,
      (∀ other : Finset (Fin N) → Bool, cost best ≤ cost other) ∧
      8*r*Z^2*cost best + b*N^2*hit^2 = 2*r*Z^2*N^2 ∧
      (2*b ≤ a → a < 4*b → 128*r*cost best + a*N^2 ≤ 32*r*N^2) ∧
      ∀ (A B : Finset (Fin N)) (T : Fin N → Fin N → Bool),
        (∀ x ∉ A, ∀ y ∉ B, T x y = base x y) →
        errors T best + (N-A.card)*(N-B.card) ≤ cost best + N^2) := by
  intro k a c ha hrk hca N r b m Z hit base
  have hb := PEqualNP.Outside.L_meta_25700_aux.r2_bounds ha hrk hca
  have hr_pos : 0 < r := Nat.two_pow_pos a
  have hb_pos : 0 < b := Nat.two_pow_pos c
  let eBits : Fin N ≃ (Fin k → Bool) := PEqualNP.Outside.L_meta_25700_aux.finPowTwoEquiv k
  let eP := PEqualNP.Outside.L_meta_25700_aux.packEquiv k a c ha hrk hca
  let eAll : Fin N ≃ PEqualNP.Outside.L_meta_25700_aux.PackT k a c := eBits.trans eP
  let lbl := PEqualNP.Outside.L_meta_25700_aux.lblOf k a c ha hrk hca
  let flp := PEqualNP.Outside.L_meta_25700_aux.flpOf k a c ha hrk hca
  let Rcard : ℕ := 2 ^ (k - (r / 2 + a))
  have hN_eq : r * (Z * Rcard) = N := by
    dsimp only [r, Z, Rcard, N]
    rw [← pow_add, ← pow_add]
    congr 1; omega
  have hmod_card : ∀ i : Fin r,
      ((Finset.univ : Finset (Fin N)).filter (fun y => (⟨y.val % r, Nat.mod_lt _ hr_pos⟩ : Fin r) = i)).card =
        Z * Rcard := by
    intro i
    have hbij :
        ((Finset.univ : Finset (Fin N)).filter (fun y => (⟨y.val % r, Nat.mod_lt _ hr_pos⟩ : Fin r) = i)).card =
          (Finset.univ : Finset (Fin (Z * Rcard))).card := by
      refine Finset.card_bij (fun y _ => ⟨y.val / r, (Nat.div_lt_iff_lt_mul hr_pos).mpr (by rw [mul_comm, hN_eq]; exact y.isLt)⟩)
        (fun _ _ => Finset.mem_univ _) ?_ ?_
      · intro y1 hy1 y2 hy2 hdiv
        have hm1 : y1.val % r = i.val := congrArg Fin.val (Finset.mem_filter.mp hy1).2
        have hm2 : y2.val % r = i.val := congrArg Fin.val (Finset.mem_filter.mp hy2).2
        have hd : y1.val / r = y2.val / r := congrArg Fin.val hdiv
        apply Fin.ext
        rw [← Nat.div_add_mod y1.val r, ← Nat.div_add_mod y2.val r, hd, hm1, hm2]
      · intro q _
        let y : Fin N := ⟨q.val * r + i.val, by
          calc
            q.val * r + i.val < q.val * r + r := Nat.add_lt_add_left i.isLt _
            _ = (q.val + 1) * r := by ring
            _ ≤ (Z * Rcard) * r := Nat.mul_le_mul_right r q.isLt
            _ = N := by rw [mul_comm, hN_eq]⟩
        refine ⟨y, ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          apply Fin.ext; dsimp only [y]
          rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt i.isLt]
        · apply Fin.ext; dsimp only [y]
          rw [Nat.mul_comm, Nat.mul_add_div hr_pos, Nat.div_eq_of_lt i.isLt, add_zero]
    rw [hbij, Finset.card_univ, Fintype.card_fin]
  have hfib_eq : ∀ i : Fin r,
      ((Finset.univ : Finset (Fin N)).filter (fun x => lbl (eAll x) = i)).card =
      ((Finset.univ : Finset (Fin N)).filter (fun y => (⟨y.val % r, Nat.mod_lt _ hr_pos⟩ : Fin r) = i)).card := by
    intro i
    rw [hmod_card i]
    have hl := PEqualNP.Outside.L_meta_25700_aux.lblOf_card k a c ha hrk hca i
    rw [← hl]
    refine Finset.card_bij (fun x _ => eAll x) ?_ ?_ ?_
    · intro x hx; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢; exact hx
    · intro x1 _ x2 _ h; exact eAll.injective h
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      exact ⟨eAll.symm p, by simpa using hp, Equiv.apply_symm_apply _ _⟩
  obtain ⟨π, hπ⟩ := PEqualNP.Outside.L_meta_25700_aux.glue_fiber_perm
    (fun x => lbl (eAll x)) (fun y => ⟨y.val % r, Nat.mod_lt _ hr_pos⟩) hfib_eq
  let flip : Fin N → Bool := fun x => flp (eAll x)
  refine ⟨π, flip, ?_⟩
  intro errors cost
  let F : Fin N → Fin N → Bool := fun x y => xor (base x (π y)) (flip x)
  let best : Finset (Fin N) → Bool := fun S =>
    if h : S.Nonempty then F (S.min' h) (S.max' h) else false
  have hbest_pair : ∀ x y : Fin N,
      (if best ({x, y} : Finset (Fin N)) ≠ F x y then 1 else 0) +
      (if best ({y, x} : Finset (Fin N)) ≠ F y x then 1 else 0) =
      if F x y = F y x then 0 else 1 := by
    intro x y
    rw [Finset.pair_comm y x]
    have hne : ({x, y} : Finset (Fin N)).Nonempty := ⟨x, Finset.mem_insert_self _ _⟩
    have hmin_max :
        (({x, y} : Finset (Fin N)).min' hne = x ∧ ({x, y} : Finset (Fin N)).max' hne = y) ∨
        (({x, y} : Finset (Fin N)).min' hne = y ∧ ({x, y} : Finset (Fin N)).max' hne = x) := by
      rcases le_total x y with hxy | hyx
      · left
        exact ⟨le_antisymm (Finset.min'_le _ x (by simp))
            (Finset.le_min' _ _ _ fun z hz => by simp at hz; rcases hz with rfl | rfl <;> [exact le_rfl; exact hxy]),
          le_antisymm (Finset.max'_le _ _ _ fun z hz => by simp at hz; rcases hz with rfl | rfl <;> [exact hxy; exact le_rfl])
            (Finset.le_max' _ y (by simp))⟩
      · right
        exact ⟨le_antisymm (Finset.min'_le _ y (by simp))
            (Finset.le_min' _ _ _ fun z hz => by simp at hz; rcases hz with rfl | rfl <;> [exact hyx; exact le_rfl]),
          le_antisymm (Finset.max'_le _ _ _ fun z hz => by simp at hz; rcases hz with rfl | rfl <;> [exact le_rfl; exact hyx])
            (Finset.le_max' _ x (by simp))⟩
    have hbv : best ({x, y} : Finset (Fin N)) = F x y ∨ best ({x, y} : Finset (Fin N)) = F y x := by
      dsimp only [best]
      rw [dif_pos hne]
      rcases hmin_max with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left; rw [h1, h2]
      · right; rw [h1, h2]
    rcases hbv with hbv1 | hbv2
    · rw [hbv1]; cases F x y <;> cases F y x <;> decide
    · rw [hbv2]; cases F x y <;> cases F y x <;> decide
  have hcost_opt : ∀ other : Finset (Fin N) → Bool, cost best ≤ cost other := by
    intro other
    suffices h2 : 2 * cost best ≤ 2 * cost other by omega
    have hdouble : ∀ dec : Finset (Fin N) → Bool,
        2 * cost dec = ∑ z : Fin N × Fin N,
          ((if dec ({z.1, z.2} : Finset (Fin N)) ≠ F z.1 z.2 then 1 else 0) +
           (if dec ({z.2, z.1} : Finset (Fin N)) ≠ F z.2 z.1 then 1 else 0)) := by
      intro dec
      rw [Finset.sum_add_distrib]
      have h1 : (∑ z : Fin N × Fin N, if dec ({z.1, z.2} : Finset (Fin N)) ≠ F z.1 z.2 then 1 else 0) =
          cost dec := by
        dsimp only [cost, errors, F]; rw [Finset.sum_boole, Nat.cast_id]
      have h2 : (∑ z : Fin N × Fin N, if dec ({z.2, z.1} : Finset (Fin N)) ≠ F z.2 z.1 then 1 else 0) =
          cost dec := by
        rw [← h1]
        exact Equiv.sum_comp (Equiv.prodComm (Fin N) (Fin N))
          (fun z : Fin N × Fin N => if dec ({z.1, z.2} : Finset (Fin N)) ≠ F z.1 z.2 then 1 else 0)
      rw [h1, h2]; ring
    rw [hdouble best, hdouble other]
    refine Finset.sum_le_sum fun z _ => ?_
    rw [hbest_pair z.1 z.2, Finset.pair_comm z.2 z.1]
    cases other ({z.1, z.2} : Finset (Fin N)) <;> cases F z.1 z.2 <;> cases F z.2 z.1 <;> decide
  have htrace_eq : (4 * (cost best : ℤ)) +
      ∑ x : Fin N, ∑ y : Fin N,
        PEqualNP.Outside.L_meta_25700_aux.sgn (F x y) *
        PEqualNP.Outside.L_meta_25700_aux.sgn (F y x) = (N : ℤ) ^ 2 := by
    have h2cost : (2 * (cost best : ℤ)) = ∑ x : Fin N, ∑ y : Fin N,
        (if F x y = F y x then (0 : ℤ) else 1) := by
      have h1 : (cost best : ℤ) = ∑ x : Fin N, ∑ y : Fin N,
          if best ({x, y} : Finset (Fin N)) ≠ F x y then (1 : ℤ) else 0 := by
        dsimp only [cost, errors, F]
        rw [← Fintype.sum_prod_type', Finset.sum_boole]
      have h2 : (cost best : ℤ) = ∑ x : Fin N, ∑ y : Fin N,
          if best ({y, x} : Finset (Fin N)) ≠ F y x then (1 : ℤ) else 0 := by
        rw [h1, Finset.sum_comm]
      have hadd : (2 * (cost best : ℤ)) = ∑ x : Fin N, ∑ y : Fin N,
          ((if best ({x, y} : Finset (Fin N)) ≠ F x y then (1 : ℤ) else 0) +
           (if best ({y, x} : Finset (Fin N)) ≠ F y x then (1 : ℤ) else 0)) := by
        calc
          (2 * (cost best : ℤ)) = (cost best : ℤ) + (cost best : ℤ) := two_mul _
          _ = (∑ x : Fin N, ∑ y : Fin N, if best ({x, y} : Finset (Fin N)) ≠ F x y then (1 : ℤ) else 0) +
              (∑ x : Fin N, ∑ y : Fin N, if best ({y, x} : Finset (Fin N)) ≠ F y x then (1 : ℤ) else 0) :=
            congrArg₂ (· + ·) h1 h2
          _ = _ := by simp_rw [← Finset.sum_add_distrib]
      rw [hadd]
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
      have hnat := hbest_pair x y
      exact_mod_cast hnat
    rw [show (4 * (cost best : ℤ)) = 2 * (2 * (cost best : ℤ)) by ring, h2cost, Finset.mul_sum]
    simp_rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    have hterm : ∀ x y : Fin N,
        2 * (if F x y = F y x then (0 : ℤ) else 1) +
        PEqualNP.Outside.L_meta_25700_aux.sgn (F x y) *
        PEqualNP.Outside.L_meta_25700_aux.sgn (F y x) = 1 := by
      intro x y; cases F x y <;> cases F y x <;> decide
    simp_rw [hterm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    ring
  let Wmat : Fin r → Fin r → ℤ := fun i j =>
    ∑ p ∈ (Finset.univ : Finset (PEqualNP.Outside.L_meta_25700_aux.PackT k a c)).filter (fun p => lbl p = i),
      PEqualNP.Outside.L_meta_25700_aux.sgn
        (xor (eP.symm p ⟨j.val, by have := j.isLt; omega⟩) (flp p))
  have hF_eval : ∀ x y : Fin N,
      F x y = xor (eP.symm (eAll x) ⟨(lbl (eAll y)).val, by have := (lbl (eAll y)).isLt; omega⟩) (flp (eAll x)) := by
    intro x y
    dsimp only [F, base, flip]
    congr 1
    have hmod : (π y).val % r = (lbl (eAll y)).val := congrArg Fin.val (hπ y)
    rw [hmod]
    have hbit := PEqualNP.Outside.L_meta_25700_aux.finPowTwoEquiv_apply k x
      ⟨(lbl (eAll y)).val, by have := (lbl (eAll y)).isLt; omega⟩
    rw [← hbit]
    have hinv : eP.symm (eAll x) = eBits x := Equiv.symm_apply_apply eP (eBits x)
    rw [hinv]
  have htrace_W :
      (∑ x : Fin N, ∑ y : Fin N,
        PEqualNP.Outside.L_meta_25700_aux.sgn (F x y) *
        PEqualNP.Outside.L_meta_25700_aux.sgn (F y x)) =
      ∑ i : Fin r, ∑ j : Fin r, Wmat i j * Wmat j i := by
    have h1 :
        (∑ x : Fin N, ∑ y : Fin N,
          PEqualNP.Outside.L_meta_25700_aux.sgn (F x y) *
          PEqualNP.Outside.L_meta_25700_aux.sgn (F y x)) =
        ∑ p : PEqualNP.Outside.L_meta_25700_aux.PackT k a c,
          ∑ q : PEqualNP.Outside.L_meta_25700_aux.PackT k a c,
            PEqualNP.Outside.L_meta_25700_aux.sgn
              (xor (eP.symm p ⟨(lbl q).val, by have := (lbl q).isLt; omega⟩) (flp p)) *
            PEqualNP.Outside.L_meta_25700_aux.sgn
              (xor (eP.symm q ⟨(lbl p).val, by have := (lbl p).isLt; omega⟩) (flp q)) := by
      simp_rw [hF_eval]
      rw [← Equiv.sum_comp eAll.symm]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [← Equiv.sum_comp eAll.symm]
      simp
    rw [h1]
    have hpart : ∀ f : PEqualNP.Outside.L_meta_25700_aux.PackT k a c → ℤ,
        (∑ p, f p) = ∑ i : Fin r, ∑ p ∈ Finset.univ.filter (fun p => lbl p = i), f p :=
      fun f => (Finset.sum_fiberwise_of_maps_to (fun _ _ => Finset.mem_univ _) f).symm
    rw [hpart]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_congr rfl fun p _ => hpart _, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    dsimp only [Wmat]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q hq => ?_
    have hi : lbl p = i := (Finset.mem_filter.mp hp).2
    have hj : lbl q = j := (Finset.mem_filter.mp hq).2
    have hki : (⟨(lbl p).val, by have := (lbl p).isLt; omega⟩ : Fin k) =
        ⟨i.val, by have := i.isLt; omega⟩ := Fin.ext (congrArg (Fin.val : Fin r → ℕ) hi)
    have hkj : (⟨(lbl q).val, by have := (lbl q).isLt; omega⟩ : Fin k) =
        ⟨j.val, by have := j.isLt; omega⟩ := Fin.ext (congrArg (Fin.val : Fin r → ℕ) hj)
    rw [hki, hkj]
  have hW_trace_val :
      (∑ i : Fin r, ∑ j : Fin r, Wmat i j * Wmat j i) =
        ((m * b * b * (hit * Rcard) ^ 2 : ℕ) : ℤ) := by
    let I0 : Finset (Fin r) := Finset.univ.filter (fun i : Fin r => i.val < r / 2)
    have hsplit : ∀ f : Fin r → ℤ, (∀ i : Fin r, r / 2 ≤ i.val → f i = 0) →
        ∑ i : Fin r, f i = ∑ i ∈ I0, f i := by
      intro f hf
      rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ) (p := fun i : Fin r => i.val < r / 2)]
      have hzero : ∑ i ∈ Finset.univ.filter (fun i : Fin r => ¬ i.val < r / 2), f i = 0 :=
        Finset.sum_eq_zero fun i hi => hf i (by have := (Finset.mem_filter.mp hi).2; omega)
      rw [hzero, add_zero]
    rw [hsplit _ (fun i hi => Finset.sum_eq_zero fun j _ => by
      have hw : Wmat i j = 0 := PEqualNP.Outside.L_meta_25700_aux.bank1_W_zero k a c ha hrk hca i j hi
      rw [hw, zero_mul])]
    have hinner : ∀ i ∈ I0,
        (∑ j : Fin r, Wmat i j * Wmat j i) = ((b * (hit * Rcard) ^ 2 : ℕ) : ℤ) := by
      intro i hi
      have hilt : i.val < r / 2 := (Finset.mem_filter.mp hi).2
      rw [hsplit _ (fun j hj => by
        have hw : Wmat j i = 0 := PEqualNP.Outside.L_meta_25700_aux.bank1_W_zero k a c ha hrk hca j i hj
        rw [hw, mul_zero])]
      have hterm : ∀ j ∈ I0,
          Wmat i j * Wmat j i = if j.val / b = i.val / b then ((hit * Rcard : ℕ) : ℤ) ^ 2 else 0 := by
        intro j hj
        have hjlt : j.val < r / 2 := (Finset.mem_filter.mp hj).2
        have hw1 := PEqualNP.Outside.L_meta_25700_aux.bank0_W_val k a c ha hrk hca i j hilt hjlt
        have hw2 := PEqualNP.Outside.L_meta_25700_aux.bank0_W_val k a c ha hrk hca j i hjlt hilt
        change Wmat i j = _ at hw1
        change Wmat j i = _ at hw2
        rw [hw1, hw2]
        by_cases hd : j.val / b = i.val / b
        · rw [if_pos hd.symm, if_pos hd, if_pos hd, sq]
        · rw [if_neg (Ne.symm hd), if_neg hd, if_neg hd, mul_zero]
      rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      have hblk_card : (I0.filter (fun j : Fin r => j.val / b = i.val / b)).card = b := by
        have hbij : (I0.filter (fun j : Fin r => j.val / b = i.val / b)).card =
            (Finset.univ : Finset (Fin b)).card := by
          refine Finset.card_bij (fun j _ => ⟨j.val % b, Nat.mod_lt _ hb_pos⟩)
            (fun _ _ => Finset.mem_univ _) ?_ ?_
          · intro j1 hj1 j2 hj2 hmod
            have hd1 := (Finset.mem_filter.mp hj1).2
            have hd2 := (Finset.mem_filter.mp hj2).2
            have hm12 : j1.val % b = j2.val % b := congrArg Fin.val hmod
            apply Fin.ext
            rw [← Nat.div_add_mod j1.val b, ← Nat.div_add_mod j2.val b, hd1, hd2, hm12]
          · intro off _
            have hib : i.val / b < m :=
              (Nat.div_lt_iff_lt_mul hb_pos).mpr (by rw [mul_comm, hb.2.2.2]; exact hilt)
            have hlt_j : (i.val / b) * b + off.val < r / 2 :=
              PEqualNP.Outside.L_meta_25700_aux.mul_add_lt_r2 ha hca ⟨i.val / b, hib⟩ off
            let j : Fin r := ⟨(i.val / b) * b + off.val, by omega⟩
            refine ⟨j, ?_, ?_⟩
            · simp only [I0, Finset.mem_filter, Finset.mem_univ, true_and]
              refine ⟨hlt_j, ?_⟩
              dsimp only [j]
              rw [Nat.mul_comm, Nat.mul_add_div hb_pos, Nat.div_eq_of_lt off.isLt, add_zero]
            · apply Fin.ext; dsimp only [j]
              rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt off.isLt]
        rw [hbij, Finset.card_univ, Fintype.card_fin]
      rw [hblk_card]; push_cast; ring
    rw [Finset.sum_congr rfl hinner, Finset.sum_const, nsmul_eq_mul]
    have hI0_card : I0.card = m * b := by
      have hbij : I0.card = (Finset.univ : Finset (Fin (r / 2))).card := by
        refine Finset.card_bij (fun i hi => ⟨i.val, (Finset.mem_filter.mp hi).2⟩)
          (fun _ _ => Finset.mem_univ _)
          (fun _ _ _ _ h => Fin.ext (congrArg (Fin.val : Fin (r / 2) → ℕ) h))
          (fun t _ => ⟨⟨t.val, by omega⟩, by simp [I0, t.isLt], Fin.ext rfl⟩)
      rw [hbij, Finset.card_univ, Fintype.card_fin, mul_comm, hb.2.2.2]
    rw [hI0_card]; push_cast; ring
  have hcost_exact : 8 * r * Z ^ 2 * cost best + b * N ^ 2 * hit ^ 2 = 2 * r * Z ^ 2 * N ^ 2 := by
    have hZ_eq : (4 * (cost best : ℤ)) + ((m * b * b * (hit * Rcard) ^ 2 : ℕ) : ℤ) = (N : ℤ) ^ 2 := by
      rw [← hW_trace_val, ← htrace_W]; exact htrace_eq
    have hnat_eq : 4 * cost best + m * b * b * (hit * Rcard) ^ 2 = N ^ 2 := by exact_mod_cast hZ_eq
    have h2mb : 2 * (m * b) = r := by rw [mul_comm m b, hb.2.2.2, hb.1]
    have h1 : 2 * r * Z ^ 2 * (4 * cost best + m * b * b * (hit * Rcard) ^ 2) =
        2 * r * Z ^ 2 * N ^ 2 := congrArg (2 * r * Z ^ 2 * ·) hnat_eq
    have h2 : 2 * r * Z ^ 2 * (m * b * b * (hit * Rcard) ^ 2) = b * N ^ 2 * hit ^ 2 := by
      calc
        2 * r * Z ^ 2 * (m * b * b * (hit * Rcard) ^ 2)
            = b * (2 * (m * b)) * (r * Z ^ 2 * Rcard ^ 2) * hit ^ 2 := by ring
        _ = b * r * (r * Z ^ 2 * Rcard ^ 2) * hit ^ 2 := by rw [h2mb]
        _ = b * (r * (Z * Rcard)) ^ 2 * hit ^ 2 := by ring
        _ = b * N ^ 2 * hit ^ 2 := by rw [hN_eq]
    have h3 : 2 * r * Z ^ 2 * (4 * cost best + m * b * b * (hit * Rcard) ^ 2) =
        8 * r * Z ^ 2 * cost best + 2 * r * Z ^ 2 * (m * b * b * (hit * Rcard) ^ 2) := by ring
    rw [h3, h2] at h1
    exact h1
  have hcost_bound : 2 * b ≤ a → a < 4 * b → 128 * r * cost best + a * N ^ 2 ≤ 32 * r * N ^ 2 := by
    intro hba hab
    have h2hit : Z ≤ 2 * hit := PEqualNP.Outside.L_meta_25700_aux.two_hit_ge_Z a c ha hca hba
    have hsq : Z ^ 2 ≤ 4 * hit ^ 2 := by
      calc Z ^ 2 = Z * Z := sq Z
        _ ≤ (2 * hit) * (2 * hit) := Nat.mul_le_mul h2hit h2hit
        _ = 4 * hit ^ 2 := by ring
    have ha4b : a * Z ^ 2 ≤ 16 * b * hit ^ 2 := by
      calc a * Z ^ 2 ≤ (4 * b) * Z ^ 2 := Nat.mul_le_mul_right _ (le_of_lt hab)
        _ ≤ (4 * b) * (4 * hit ^ 2) := Nat.mul_le_mul_left _ hsq
        _ = 16 * b * hit ^ 2 := by ring
    have haN : Z ^ 2 * (a * N ^ 2) ≤ 16 * (b * N ^ 2 * hit ^ 2) := by
      calc Z ^ 2 * (a * N ^ 2) = N ^ 2 * (a * Z ^ 2) := by ring
        _ ≤ N ^ 2 * (16 * b * hit ^ 2) := Nat.mul_le_mul_left _ ha4b
        _ = 16 * (b * N ^ 2 * hit ^ 2) := by ring
    have h16 : 16 * (8 * r * Z ^ 2 * cost best + b * N ^ 2 * hit ^ 2) =
        16 * (2 * r * Z ^ 2 * N ^ 2) := congrArg (16 * ·) hcost_exact
    have hmul : Z ^ 2 * (128 * r * cost best + a * N ^ 2) ≤ Z ^ 2 * (32 * r * N ^ 2) := by
      have hl : Z ^ 2 * (128 * r * cost best + a * N ^ 2) =
          16 * (8 * r * Z ^ 2 * cost best) + Z ^ 2 * (a * N ^ 2) := by ring
      have hr : Z ^ 2 * (32 * r * N ^ 2) = 16 * (2 * r * Z ^ 2 * N ^ 2) := by ring
      rw [hl, hr, ← h16, mul_add]
      exact Nat.add_le_add_left haN _
    exact Nat.le_of_mul_le_mul_left hmul (Nat.pos_of_ne_zero (by positivity))
  have hperturb : ∀ (A B : Finset (Fin N)) (T : Fin N → Fin N → Bool),
      (∀ x ∉ A, ∀ y ∉ B, T x y = base x y) →
      errors T best + (N - A.card) * (N - B.card) ≤ cost best + N ^ 2 := by
    intro A B T hT
    let good : Finset (Fin N × Fin N) := Aᶜ ×ˢ (Bᶜ.image π.symm)
    let errT : Finset (Fin N × Fin N) := Finset.univ.filter (fun z : Fin N × Fin N =>
      best ({z.1, z.2} : Finset (Fin N)) ≠ xor (T z.1 (π z.2)) (flip z.1))
    let errB : Finset (Fin N × Fin N) := Finset.univ.filter (fun z : Fin N × Fin N =>
      best ({z.1, z.2} : Finset (Fin N)) ≠ xor (base z.1 (π z.2)) (flip z.1))
    have hsub : errT ∩ good ⊆ errB := by
      intro z hz
      rcases Finset.mem_inter.mp hz with ⟨hzT, hzG⟩
      rcases Finset.mem_product.mp hzG with ⟨hx, hy⟩
      have hxA : z.1 ∉ A := Finset.mem_compl.mp hx
      rcases Finset.mem_image.mp hy with ⟨y0, hy0, hy0_eq⟩
      have hyB : π z.2 ∉ B := by
        have : π z.2 = y0 := by rw [← hy0_eq, Equiv.apply_symm_apply]
        rw [this]
        exact Finset.mem_compl.mp hy0
      simp only [errT, errB, Finset.mem_filter, Finset.mem_univ, true_and] at hzT ⊢
      rwa [hT z.1 hxA (π z.2) hyB] at hzT
    have hgood_card : good.card = (N - A.card) * (N - B.card) := by
      dsimp only [good]
      rw [Finset.card_product, Finset.card_image_of_injective _ π.symm.injective,
        Finset.card_compl, Finset.card_compl, Fintype.card_fin]
    have hunion_le : (errT ∪ good).card ≤ N ^ 2 := by
      calc
        (errT ∪ good).card ≤ (Finset.univ : Finset (Fin N × Fin N)).card :=
          Finset.card_le_card (Finset.subset_univ _)
        _ = N ^ 2 := by simp [Fintype.card_prod, sq]
    have hinc := Finset.card_union_add_card_inter errT good
    have hinter_le : (errT ∩ good).card ≤ errB.card := Finset.card_le_card hsub
    change errT.card + (N - A.card) * (N - B.card) ≤ errB.card + N ^ 2
    omega
  exact ⟨best, hcost_opt, hcost_exact, hcost_bound, hperturb⟩
