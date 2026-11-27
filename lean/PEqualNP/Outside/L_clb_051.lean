import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.L_lib_383

namespace PEqualNP.Outside.L_clb_051_aux

private def xorList : List Bool → Bool
  | [] => false
  | b :: bs => xor b (xorList bs)

private theorem xorList_append (l1 l2 : List Bool) :
    xorList (l1 ++ l2) = xor (xorList l1) (xorList l2) := by
  induction l1 with
  | nil => simp [xorList]
  | cons b bs ih =>
    simp only [List.cons_append, xorList, ih]
    cases b <;> cases xorList bs <;> cases xorList l2 <;> rfl

private theorem xorList_snoc (l : List Bool) (b : Bool) :
    xorList (l ++ [b]) = xor (xorList l) b := by
  rw [xorList_append]
  simp [xorList]

private theorem xor_finRange_shift {k : ℕ} (hk : 0 < k) (seq : ℕ → Bool) (u : ℕ) :
    xor (xorList ((List.finRange k).map (fun j => seq (u + j.val))))
      (xorList ((List.finRange k).map (fun j => seq (u + 1 + j.val)))) =
    xor (seq u) (seq (u + k)) := by
  have h1 : (List.finRange k).map (fun j => seq (u + j.val)) =
      seq u :: (List.finRange (k - 1)).map (fun j => seq (u + 1 + j.val)) := by
    apply List.ext_getElem
    · simp; omega
    · intro i hi1 hi2
      cases i with
      | zero => simp
      | succ i =>
        simp only [List.getElem_map, List.getElem_finRange, List.getElem_cons_succ, Fin.val_cast]
        congr 1; omega
  have h2 : (List.finRange k).map (fun j => seq (u + 1 + j.val)) =
      (List.finRange (k - 1)).map (fun j => seq (u + 1 + j.val)) ++ [seq (u + k)] := by
    apply List.ext_getElem
    · simp; omega
    · intro i hi1 hi2
      by_cases hi : i < k - 1
      · rw [List.getElem_append_left (by simp; omega)]
        simp only [List.getElem_map, List.getElem_finRange, Fin.val_cast]
      · rw [List.getElem_append_right (by simp; omega)]
        have heq : i = k - 1 := by simp at hi1; omega
        simp only [List.getElem_map, List.getElem_finRange, List.length_map, List.length_finRange,
          heq, Nat.sub_self, List.getElem_singleton, Fin.val_cast]
        congr 1; omega
  rw [h1, h2, xorList, xorList_snoc]
  generalize xorList ((List.finRange (k - 1)).map (fun j => seq (u + 1 + j.val))) = mid
  cases seq u <;> cases mid <;> cases seq (u + k) <;> rfl

private theorem xorList_rotate_eq {k : ℕ} (v : Fin (k + 1) → Bool)
    (hsum : xorList ((List.finRange (k + 1)).map v) = false) (u : ℕ) :
    xorList ((List.finRange k).map (fun j => v ⟨(u + j.val) % (k + 1), Nat.mod_lt _ (by omega)⟩)) =
    v ⟨(u + k) % (k + 1), Nat.mod_lt _ (by omega)⟩ := by
  have hfull : ∀ t : ℕ, xorList ((List.finRange (k + 1)).map
      (fun j => v ⟨(t + j.val) % (k + 1), Nat.mod_lt _ (by omega)⟩)) = false := by
    intro t
    induction t with
    | zero =>
      convert hsum using 2
      apply List.ext_getElem
      · simp
      · intro i hi1 hi2
        simp only [List.getElem_map, List.getElem_finRange, zero_add]
        congr 1; ext; dsimp; exact Nat.mod_eq_of_lt (by simp at hi1; omega)
    | succ t ih =>
      have h1 : (List.finRange (k + 1)).map
            (fun j => v ⟨(t + j.val) % (k + 1), Nat.mod_lt _ (by omega)⟩) =
          v ⟨t % (k + 1), Nat.mod_lt _ (by omega)⟩ ::
            (List.finRange k).map
              (fun j => v ⟨(t + 1 + j.val) % (k + 1), Nat.mod_lt _ (by omega)⟩) := by
        apply List.ext_getElem
        · simp
        · intro i hi1 hi2
          cases i with
          | zero => simp
          | succ i =>
            simp only [List.getElem_map, List.getElem_finRange, List.getElem_cons_succ]
            congr 1; ext; dsimp; congr 1; omega
      have h2 : (List.finRange (k + 1)).map
            (fun j => v ⟨(t + 1 + j.val) % (k + 1), Nat.mod_lt _ (by omega)⟩) =
          (List.finRange k).map
              (fun j => v ⟨(t + 1 + j.val) % (k + 1), Nat.mod_lt _ (by omega)⟩) ++
            [v ⟨t % (k + 1), Nat.mod_lt _ (by omega)⟩] := by
        apply List.ext_getElem
        · simp
        · intro i hi1 hi2
          by_cases hi : i < k
          · rw [List.getElem_append_left (by simp; omega)]
            simp only [List.getElem_map, List.getElem_finRange, Fin.val_cast]
          · rw [List.getElem_append_right (by simp; omega)]
            have heq : i = k := by simp at hi1; omega
            simp only [List.getElem_map, List.getElem_finRange, List.length_map,
              List.length_finRange, heq, Nat.sub_self, List.getElem_singleton, Fin.val_cast]
            congr 1; ext; dsimp
            rw [show t + 1 + k = t + (k + 1) by omega, Nat.add_mod_right]
      rw [h1, xorList] at ih
      rw [h2, xorList_snoc, Bool.xor_comm]
      exact ih
  have hu := hfull u
  have hsplit : (List.finRange (k + 1)).map
        (fun j => v ⟨(u + j.val) % (k + 1), Nat.mod_lt _ (by omega)⟩) =
      (List.finRange k).map
          (fun j => v ⟨(u + j.val) % (k + 1), Nat.mod_lt _ (by omega)⟩) ++
        [v ⟨(u + k) % (k + 1), Nat.mod_lt _ (by omega)⟩] := by
    apply List.ext_getElem
    · simp
    · intro i hi1 hi2
      by_cases hi : i < k
      · rw [List.getElem_append_left (by simp; omega)]
        simp only [List.getElem_map, List.getElem_finRange, Fin.val_cast]
      · rw [List.getElem_append_right (by simp; omega)]
        have heq : i = k := by simp at hi1; omega
        simp only [List.getElem_map, List.getElem_finRange, List.length_map,
          List.length_finRange, heq, Nat.sub_self, List.getElem_singleton, Fin.val_cast]
  rw [hsplit, xorList_snoc] at hu
  generalize hx : xorList ((List.finRange k).map
    (fun j => v ⟨(u + j.val) % (k + 1), Nat.mod_lt _ (by omega)⟩)) = xv
  generalize hy : v ⟨(u + k) % (k + 1), Nat.mod_lt _ (by omega)⟩ = yv
  rw [hx, hy] at hu
  cases xv <;> cases yv <;> simp_all

private def padBit {w : ℕ} (dst : Fin w → Bool) (r : Fin (w + 1)) : Bool :=
  if hr : r.val < w then dst ⟨r.val, hr⟩ else xorList ((List.finRange w).map dst)

private theorem padBit_sum {w : ℕ} (dst : Fin w → Bool) :
    xorList ((List.finRange (w + 1)).map (padBit dst)) = false := by
  have hsp : (List.finRange (w + 1)).map (padBit dst) =
      (List.finRange w).map dst ++ [xorList ((List.finRange w).map dst)] := by
    apply List.ext_getElem
    · simp
    · intro i hi1 hi2
      by_cases hi : i < w
      · rw [List.getElem_append_left (by simp; omega)]
        simp only [List.getElem_map, List.getElem_finRange, Fin.val_cast, padBit, hi, ↓reduceDIte]
        rfl
      · rw [List.getElem_append_right (by simp; omega)]
        have heq : i = w := by simp at hi1; omega
        simp only [List.getElem_map, List.getElem_finRange, List.length_map,
          List.length_finRange, heq, Nat.sub_self, List.getElem_singleton, Fin.val_cast, padBit,
          lt_irrefl, ↓reduceDIte]
  rw [hsp, xorList_snoc]
  cases xorList ((List.finRange w).map dst) <;> rfl

private def consBool {d : ℕ} (b : Bool) (u : Fin d → Bool) : Fin (d + 1) → Bool :=
  Fin.cases b u

private theorem main_aux : ∀ d b p q : ℕ,
    let w := d + 1
    let D := Fin d → Bool
    let B := b + 1
    let L := 3 * w * 2 ^ d
    let n := L + B * w + p * w + q * (w + 1)
    let hn : 0 < n := by dsimp [n, L, B, w]; positivity
    let Pattern := Fin (w + 1) → Bool
    ∃ (ctx : (D → D → Bool) → Fin n → Pattern → Bool)
      (probe : D → D → Fin w → Pattern → Bool),
      (∀ M N i, L ≤ i.val → ctx M i = ctx N i) ∧
      ∀ (A : D → D → Bool) (u v : D) (h : Fin B),
        let start := L + h.val * w
        let row := fun (i : Fin n) (pat : Pattern) =>
          if start ≤ i.val ∧ i.val < start + w then
            probe u v (Fin.ofNat (d + 1) (i.val - start)) pat
          else ctx A i pat
        let ok := fun (word : Fin n → Bool) => ∀ s : Fin n,
          row s (fun k => word ⟨(s.val + k.val) % n, Nat.mod_lt _ hn⟩) = true
        (Finset.univ.filter ok).card = (A u v).toNat := by
  intro d b p q w D B L n hn Pattern
  obtain ⟨enc, _, henc⟩ := PEqualNP.Outside.L_lib_383 d
  have hw_pos : 0 < w := by dsimp [w]; omega
  have hB_pos : 0 < B := by dsimp [B]; omega
  have hL_pos : 0 < L := by dsimp [L, w]; positivity
  let M : ℕ := L + B * w + p * w
  have hM_le_n : M ≤ n := by dsimp [M, n]; omega
  have hLw_le_M : L + w ≤ M := by
    have : 1 * w ≤ B * w := Nat.mul_le_mul_right w hB_pos
    dsimp [M]; omega
  let ctx : (D → D → Bool) → Fin n → Pattern → Bool := fun A i pat =>
    if hi : i.val < L then
      enc A ⟨i.val, hi⟩ pat
    else if i.val < M then
      pat (Fin.last w) == pat 0
    else
      pat (Fin.last w) == xorList ((List.finRange w).map (fun j => pat ⟨j.val, by omega⟩))
  let probe : D → D → Fin w → Pattern → Bool := fun u v r pat =>
    (pat 0 == consBool true v r) && (pat (Fin.last w) == consBool false u r)
  refine ⟨ctx, probe, ?_, ?_⟩
  · intro A1 A2 i hi
    funext pat
    have hnot : ¬ (i.val < L) := by omega
    simp [ctx, hnot]
  · intro A u v h start row ok
    let src : Fin w → Bool := consBool true v
    let dst : Fin w → Bool := consBool false u
    have hstart_ge : L ≤ start := by dsimp [start]; omega
    have hstart_end : start + w ≤ L + B * w := by
      have h1 : (h.val + 1) * w ≤ B * w := Nat.mul_le_mul_right w h.isLt
      dsimp [start]; rw [Nat.add_mul, Nat.one_mul] at h1; omega
    have hstart_M : start + w ≤ M := by dsimp [M]; omega
    let okEnc : (Fin (L + w) → Bool) → Prop := fun x =>
      (∀ k : Fin w, x (Fin.ofNat (L + d + 1) k.val) = dst k ∧
        x (Fin.ofNat (L + d + 1) (L + k.val)) = src k) ∧
      ∀ i : Fin L, enc A i (fun offset => x (Fin.ofNat (L + d + 1) (i.val + offset.val))) = true
    have henc_card : (Finset.univ.filter okEnc).card = (A u v).toNat := by
      have hc := henc A dst src
      dsimp only at hc
      have hne : dst ≠ src := by
        intro heq
        have h0 := congrFun heq 0
        simp [dst, src, consBool] at h0
      have hd0 : dst 0 = false := rfl
      have hs0 : src 0 = true := rfl
      have hdt : (fun ia : Fin d => dst ia.succ) = u := by funext ia; rfl
      have hst : (fun ib : Fin d => src ib.succ) = v := by funext ib; rfl
      simp only [hne, ↓reduceIte, hd0, hs0, hdt, hst] at hc
      have hrhs : (0 + if True ∧ True ∧ A u v = true then 1 else 0) = (A u v).toNat := by
        cases A u v <;> simp
      exact hc.trans (by simpa using hrhs)
    let toX : (Fin n → Bool) → (Fin (L + w) → Bool) := fun word i =>
      word ⟨i.val, by omega⟩
    let fromX : (Fin (L + w) → Bool) → (Fin n → Bool) := fun x i =>
      if hi : i.val < L then
        x ⟨i.val, by omega⟩
      else if i.val < start + w then
        src ⟨(i.val - L) % w, Nat.mod_lt _ hw_pos⟩
      else if i.val < M then
        dst ⟨(i.val - L) % w, Nat.mod_lt _ hw_pos⟩
      else
        padBit dst ⟨(i.val - M) % (w + 1), Nat.mod_lt _ (by omega)⟩
    have hword_ok : ∀ word : Fin n → Bool, ok word →
        okEnc (toX word) ∧ fromX (toX word) = word := by
      intro word hok
      have hprobe_at : ∀ r : Fin w,
          word ⟨(start + r.val) % n, Nat.mod_lt _ hn⟩ = src r ∧
          word ⟨(start + w + r.val) % n, Nat.mod_lt _ hn⟩ = dst r := by
        intro r
        have hs_lt : start + r.val < n := by omega
        have hrw := hok ⟨start + r.val, hs_lt⟩
        have hin : start ≤ start + r.val ∧ start + r.val < start + w := ⟨by omega, by omega⟩
        dsimp only [row] at hrw
        simp only [hin, and_self, ↓reduceIte, probe, Bool.and_eq_true, beq_iff_eq] at hrw
        have hfin : Fin.ofNat (d + 1) (start + r.val - start) = r := by
          ext
          change (start + r.val - start) % (d + 1) = r.val
          rw [show start + r.val - start = r.val by omega, Nat.mod_eq_of_lt r.isLt]
        rw [hfin] at hrw
        constructor
        · convert hrw.1 using 2
          ext; simp
        · convert hrw.2 using 2
          ext; dsimp; congr 1; omega
      have hleft_src : ∀ (c : ℕ) (hc : c ≤ h.val) (r : Fin w),
          word ⟨(L + (h.val - c) * w + r.val) % n, Nat.mod_lt _ hn⟩ = src r := by
        intro c hc
        induction c with
        | zero =>
          intro r
          simpa [start] using (hprobe_at r).1
        | succ c ih =>
          intro r
          have hidx_ge : L ≤ L + (h.val - (c + 1)) * w + r.val := by omega
          have hidx_lt_start : L + (h.val - (c + 1)) * w + r.val < start := by
            have h1 : (h.val - (c + 1) + 1) * w ≤ h.val * w := Nat.mul_le_mul_right w (by omega)
            rw [Nat.add_mul, Nat.one_mul] at h1
            dsimp [start]; omega
          have hidx_lt_n : L + (h.val - (c + 1)) * w + r.val < n := by omega
          have hrw := hok ⟨L + (h.val - (c + 1)) * w + r.val, hidx_lt_n⟩
          dsimp only [row, ctx] at hrw
          have hnot_in : ¬ (start ≤ L + (h.val - (c + 1)) * w + r.val ∧
              L + (h.val - (c + 1)) * w + r.val < start + w) := by omega
          have hnot_L : ¬ (L + (h.val - (c + 1)) * w + r.val < L) := by omega
          have hlt_M : L + (h.val - (c + 1)) * w + r.val < M := by omega
          simp only [hnot_in, hnot_L, hlt_M, ↓reduceIte, ↓reduceDIte, beq_iff_eq] at hrw
          have hnext : L + (h.val - (c + 1)) * w + r.val + w = L + (h.val - c) * w + r.val := by
            have hsub : h.val - c = (h.val - (c + 1)) + 1 := by omega
            rw [hsub, Nat.add_mul, Nat.one_mul]; omega
          have heq0 : word ⟨(L + (h.val - (c + 1)) * w + r.val + (0 : Fin (w + 1)).val) % n,
                Nat.mod_lt _ hn⟩ =
              word ⟨(L + (h.val - (c + 1)) * w + r.val) % n, Nat.mod_lt _ hn⟩ := by
            rfl
          have heqw : word ⟨(L + (h.val - (c + 1)) * w + r.val + (Fin.last w).val) % n,
                Nat.mod_lt _ hn⟩ =
              word ⟨(L + (h.val - c) * w + r.val) % n, Nat.mod_lt _ hn⟩ := by
            congr 1; ext; dsimp; congr 1
          rw [heq0, heqw] at hrw
          exact hrw.symm.trans (ih (by omega) r)
      have hsrc_block : ∀ (k0 : ℕ) (hk0 : k0 ≤ h.val) (r : Fin w),
          word ⟨(L + k0 * w + r.val) % n, Nat.mod_lt _ hn⟩ = src r := by
        intro k0 hk0 r
        have := hleft_src (h.val - k0) (by omega) r
        rw [show h.val - (h.val - k0) = k0 by omega] at this
        exact this
      have hright_dst : ∀ (c : ℕ) (hc : h.val + 1 + c ≤ B + p) (r : Fin w),
          word ⟨(L + (h.val + 1 + c) * w + r.val) % n, Nat.mod_lt _ hn⟩ = dst r := by
        intro c hc
        induction c with
        | zero =>
          intro r
          have heq : L + (h.val + 1 + 0) * w + r.val = start + w + r.val := by
            dsimp [start]; rw [Nat.add_zero, Nat.add_mul, Nat.one_mul]; omega
          rw [heq]
          exact (hprobe_at r).2
        | succ c ih =>
          intro r
          have hpos_ge : start + w ≤ L + (h.val + 1 + c) * w + r.val := by
            have h1 : (h.val + 1) * w ≤ (h.val + 1 + c) * w := Nat.mul_le_mul_right w (by omega)
            rw [Nat.add_mul, Nat.one_mul] at h1
            dsimp [start]; omega
          have hpos_lt_M : L + (h.val + 1 + c) * w + r.val < M := by
            have h1 : (h.val + 1 + c) * w + w ≤ B * w + p * w := by
              calc (h.val + 1 + c) * w + w = (h.val + 1 + c + 1) * w := by ring
                _ ≤ (B + p) * w := Nat.mul_le_mul_right w hc
                _ = B * w + p * w := by ring
            dsimp [M]; omega
          have hpos_lt_n : L + (h.val + 1 + c) * w + r.val < n := by omega
          have hrw := hok ⟨L + (h.val + 1 + c) * w + r.val, hpos_lt_n⟩
          dsimp only [row, ctx] at hrw
          have hnot_in : ¬ (start ≤ L + (h.val + 1 + c) * w + r.val ∧
              L + (h.val + 1 + c) * w + r.val < start + w) := by omega
          have hnot_L : ¬ (L + (h.val + 1 + c) * w + r.val < L) := by omega
          simp only [hnot_in, hnot_L, hpos_lt_M, ↓reduceIte, ↓reduceDIte, beq_iff_eq] at hrw
          have hnext : L + (h.val + 1 + c) * w + r.val + w =
              L + (h.val + 1 + (c + 1)) * w + r.val := by ring
          have heq0 : word ⟨(L + (h.val + 1 + c) * w + r.val + (0 : Fin (w + 1)).val) % n,
                Nat.mod_lt _ hn⟩ =
              word ⟨(L + (h.val + 1 + c) * w + r.val) % n, Nat.mod_lt _ hn⟩ := by
            rfl
          have heqw : word ⟨(L + (h.val + 1 + c) * w + r.val + (Fin.last w).val) % n,
                Nat.mod_lt _ hn⟩ =
              word ⟨(L + (h.val + 1 + (c + 1)) * w + r.val) % n, Nat.mod_lt _ hn⟩ := by
            congr 1; ext; dsimp; congr 1
          rw [heq0, heqw] at hrw
          exact hrw.trans (ih (by omega) r)
      have hdst_block : ∀ (k0 : ℕ) (hk0_lo : h.val + 1 ≤ k0) (hk0_hi : k0 ≤ B + p) (r : Fin w),
          word ⟨(L + k0 * w + r.val) % n, Nat.mod_lt _ hn⟩ = dst r := by
        intro k0 hk0_lo hk0_hi r
        have := hright_dst (k0 - (h.val + 1)) (by omega) r
        rw [show h.val + 1 + (k0 - (h.val + 1)) = k0 by omega] at this
        exact this
      have hM_dst : ∀ r : Fin w, word ⟨(M + r.val) % n, Nat.mod_lt _ hn⟩ = dst r := by
        intro r
        have h1 := hdst_block (B + p) (by omega) le_rfl r
        have heq : L + (B + p) * w + r.val = M + r.val := by
          dsimp [M]; rw [Nat.add_mul]; omega
        rw [heq] at h1
        exact h1
      have hpad_step : ∀ (c : ℕ) (hc : c ≤ q),
          (∀ r : Fin w, word ⟨(M + c * (w + 1) + r.val) % n, Nat.mod_lt _ hn⟩ = dst r) ∧
          (∀ (hc' : c < q),
            word ⟨(M + c * (w + 1) + w) % n, Nat.mod_lt _ hn⟩ =
              xorList ((List.finRange w).map dst)) := by
        intro c hc
        induction c with
        | zero =>
          refine ⟨fun r => by simpa using hM_dst r, fun hq0 => ?_⟩
          have hM_lt : M < n := by
            have : 1 * (w + 1) ≤ q * (w + 1) := Nat.mul_le_mul_right _ hq0
            dsimp [M, n] at this ⊢; omega
          have hrw := hok ⟨M, hM_lt⟩
          dsimp only [row, ctx] at hrw
          have hnot_in : ¬ (start ≤ M ∧ M < start + w) := by omega
          have hnot_L : ¬ (M < L) := by omega
          have hnot_M : ¬ (M < M) := lt_irrefl M
          simp only [hnot_in, hnot_L, hnot_M, ↓reduceIte, ↓reduceDIte, beq_iff_eq] at hrw
          have hmap : (List.finRange w).map
                (fun j : Fin w => word ⟨(M + j.val) % n, Nat.mod_lt _ hn⟩) =
              (List.finRange w).map dst := by
            apply List.map_congr_left
            intro j _
            exact hM_dst j
          simpa [hmap] using hrw
        | succ c ih =>
          obtain ⟨ih_dst, ih_par⟩ := ih (by omega)
          let base := M + c * (w + 1)
          let seq : ℕ → Bool := fun z => word ⟨(base + z) % n, Nat.mod_lt _ hn⟩
          have hstep_seq : ∀ u0 : ℕ, u0 ≤ w →
              seq (u0 + w) = xorList ((List.finRange w).map (fun j => seq (u0 + j.val))) := by
            intro u0 hu0
            have hge_M : M ≤ base + u0 := by dsimp [base]; omega
            have hlt_n : base + u0 < n := by
              have : (c + 1) * (w + 1) ≤ q * (w + 1) := Nat.mul_le_mul_right _ hc
              rw [Nat.add_mul, Nat.one_mul] at this
              dsimp [base, M, n] at this ⊢; omega
            have hrw := hok ⟨base + u0, hlt_n⟩
            dsimp only [row, ctx] at hrw
            have hnot_in : ¬ (start ≤ base + u0 ∧ base + u0 < start + w) := by omega
            have hnot_L : ¬ (base + u0 < L) := by omega
            have hnot_M : ¬ (base + u0 < M) := by omega
            simp only [hnot_in, hnot_L, hnot_M, ↓reduceIte, ↓reduceDIte, beq_iff_eq] at hrw
            convert hrw using 1
            · dsimp only [seq]; congr 1; ext; dsimp; congr 1; omega
            · congr 1; apply List.map_congr_left; intro j _
              dsimp only [seq]; congr 1; ext; dsimp; congr 1; omega
          have hnext_dst : ∀ r : Fin w,
              word ⟨(M + (c + 1) * (w + 1) + r.val) % n, Nat.mod_lt _ hn⟩ = dst r := by
            intro r
            have h1 := hstep_seq r.val (by omega)
            have h2 := hstep_seq (r.val + 1) (by omega)
            have hsh := xor_finRange_shift hw_pos seq r.val
            rw [← h1, ← h2] at hsh
            have hseq_eq : seq (r.val + 1 + w) = seq r.val := by
              generalize ha : seq (r.val + w) = va at hsh
              generalize hb : seq (r.val + 1 + w) = vb at hsh
              generalize hc0 : seq r.val = vc at hsh
              cases va <;> cases vb <;> cases vc <;> simp at hsh ⊢
            have hprev := ih_dst r
            have heq_lhs : word ⟨(M + (c + 1) * (w + 1) + r.val) % n, Nat.mod_lt _ hn⟩ =
                seq (r.val + 1 + w) := by
              dsimp only [seq, base]; congr 1; ext; dsimp; congr 1
              rw [Nat.add_mul, Nat.one_mul]; omega
            rw [heq_lhs, hseq_eq]
            exact hprev
          refine ⟨hnext_dst, fun hlt_q => ?_⟩
          have hpos_lt : M + (c + 1) * (w + 1) < n := by
            have : (c + 1 + 1) * (w + 1) ≤ q * (w + 1) := Nat.mul_le_mul_right _ hlt_q
            rw [Nat.add_mul, Nat.one_mul] at this
            dsimp [M, n] at this ⊢; omega
          have hrw := hok ⟨M + (c + 1) * (w + 1), hpos_lt⟩
          dsimp only [row, ctx] at hrw
          have hnot_in : ¬ (start ≤ M + (c + 1) * (w + 1) ∧
              M + (c + 1) * (w + 1) < start + w) := by omega
          have hnot_L : ¬ (M + (c + 1) * (w + 1) < L) := by omega
          have hnot_M : ¬ (M + (c + 1) * (w + 1) < M) := by omega
          simp only [hnot_in, hnot_L, hnot_M, ↓reduceIte, ↓reduceDIte, beq_iff_eq] at hrw
          have hmap : (List.finRange w).map
                (fun j : Fin w => word ⟨(M + (c + 1) * (w + 1) + j.val) % n, Nat.mod_lt _ hn⟩) =
              (List.finRange w).map dst := by
            apply List.map_congr_left
            intro j _
            exact hnext_dst j
          simpa [hmap] using hrw
      have h0_dst : ∀ r : Fin w, word ⟨r.val, by omega⟩ = dst r := by
        intro r
        have hq := (hpad_step q le_rfl).1 r
        have hwrap : (M + q * (w + 1) + r.val) % n = r.val := by
          have heq : M + q * (w + 1) + r.val = r.val + n := by dsimp [M, n]; omega
          rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        convert hq using 2
        ext; exact hwrap.symm
      have hL_src : ∀ r : Fin w, word ⟨L + r.val, by omega⟩ = src r := by
        intro r
        have h0 := hsrc_block 0 (Nat.zero_le _) r
        have hmod : (L + 0 * w + r.val) % n = L + r.val := by
          simp [Nat.mod_eq_of_lt (show L + r.val < n by omega)]
        convert h0 using 2
        ext; exact hmod.symm
      constructor
      · refine ⟨fun r => ⟨?_, ?_⟩, fun i => ?_⟩
        · have hf : (Fin.ofNat (L + d + 1) r.val : Fin (L + w)) = ⟨r.val, by omega⟩ := by
            ext; change r.val % (L + d + 1) = r.val
            exact Nat.mod_eq_of_lt (by dsimp [w] at r ⊢; omega)
          rw [hf]; exact h0_dst r
        · have hf : (Fin.ofNat (L + d + 1) (L + r.val) : Fin (L + w)) = ⟨L + r.val, by omega⟩ := by
            ext; change (L + r.val) % (L + d + 1) = L + r.val
            exact Nat.mod_eq_of_lt (by dsimp [w] at r ⊢; omega)
          rw [hf]; exact hL_src r
        · have hrw := hok ⟨i.val, by omega⟩
          dsimp only [row, ctx] at hrw
          have hnot_in : ¬ (start ≤ i.val ∧ i.val < start + w) := by omega
          simp only [hnot_in, i.isLt, ↓reduceIte, ↓reduceDIte] at hrw
          convert hrw using 2
          funext offset
          dsimp only [toX]
          congr 1
          ext
          change (i.val + offset.val) % (L + d + 1) = (i.val + offset.val) % n
          have ho : offset.val < w + 1 := offset.isLt
          have hi : i.val < L := i.isLt
          rw [Nat.mod_eq_of_lt (by dsimp [w] at ho; omega),
            Nat.mod_eq_of_lt (by dsimp [w] at ho; omega)]
      · funext i
        dsimp only [fromX]
        by_cases hL : i.val < L
        · simp [hL, toX]
        · simp only [hL, ↓reduceDIte]
          by_cases hsw : i.val < start + w
          · simp only [hsw, ↓reduceIte]
            let c := (i.val - L) / w
            let r : Fin w := ⟨(i.val - L) % w, Nat.mod_lt _ hw_pos⟩
            have hc_le : c ≤ h.val := by
              have hlt : i.val - L < (h.val + 1) * w := by
                dsimp [start] at hsw; rw [Nat.add_mul, Nat.one_mul]; omega
              have hdiv : (i.val - L) / w < h.val + 1 := (Nat.div_lt_iff_lt_mul hw_pos).mpr hlt
              omega
            have hdecomp : L + c * w + r.val = i.val := by
              have hdm := Nat.div_add_mod (i.val - L) w
              rw [Nat.mul_comm] at hdm
              dsimp [c, r]; omega
            have h1 := hsrc_block c hc_le r
            have hf : (⟨(L + c * w + r.val) % n, Nat.mod_lt _ hn⟩ : Fin n) = i := by
              ext; dsimp; rw [hdecomp, Nat.mod_eq_of_lt i.isLt]
            rw [hf] at h1
            exact h1.symm
          · simp only [hsw, ↓reduceIte]
            by_cases hM : i.val < M
            · simp only [hM, ↓reduceIte]
              let c := (i.val - L) / w
              let r : Fin w := ⟨(i.val - L) % w, Nat.mod_lt _ hw_pos⟩
              have hc_lo : h.val + 1 ≤ c := by
                have hge : (h.val + 1) * w ≤ i.val - L := by
                  dsimp [start] at hsw; rw [Nat.add_mul, Nat.one_mul]; omega
                exact (Nat.le_div_iff_mul_le hw_pos).mpr hge
              have hc_hi : c ≤ B + p := by
                have hlt : i.val - L < (B + p) * w := by
                  dsimp [M] at hM; rw [Nat.add_mul]; omega
                have hdiv : (i.val - L) / w < B + p := (Nat.div_lt_iff_lt_mul hw_pos).mpr hlt
                omega
              have hdecomp : L + c * w + r.val = i.val := by
                have hdm := Nat.div_add_mod (i.val - L) w
                rw [Nat.mul_comm] at hdm
                dsimp [c, r]; omega
              have h1 := hdst_block c hc_lo hc_hi r
              have hf : (⟨(L + c * w + r.val) % n, Nat.mod_lt _ hn⟩ : Fin n) = i := by
                ext; dsimp; rw [hdecomp, Nat.mod_eq_of_lt i.isLt]
              rw [hf] at h1
              exact h1.symm
            · simp only [hM, ↓reduceIte]
              let c := (i.val - M) / (w + 1)
              let rem : Fin (w + 1) := ⟨(i.val - M) % (w + 1), Nat.mod_lt _ (by omega)⟩
              have hc_lt : c < q := by
                have hlt : i.val - M < q * (w + 1) := by dsimp [M, n] at *; omega
                exact (Nat.div_lt_iff_lt_mul (by omega)).mpr hlt
              have hdecomp : M + c * (w + 1) + rem.val = i.val := by
                have hdm := Nat.div_add_mod (i.val - M) (w + 1)
                rw [Nat.mul_comm] at hdm
                dsimp [c, rem]; omega
              dsimp only [padBit]
              by_cases hrem : rem.val < w
              · simp only [rem, hrem, ↓reduceDIte]
                have h1 := (hpad_step c (by omega)).1 ⟨rem.val, hrem⟩
                dsimp only at h1
                have hf : (⟨(M + c * (w + 1) + rem.val) % n, Nat.mod_lt _ hn⟩ : Fin n) = i := by
                  ext; dsimp; rw [hdecomp, Nat.mod_eq_of_lt i.isLt]
                rw [hf] at h1
                exact h1.symm
              · simp only [rem, hrem, ↓reduceDIte]
                have hreq : rem.val = w := by have := rem.isLt; omega
                have hdecomp' : M + c * (w + 1) + w = i.val := by omega
                have h1 := (hpad_step c (by omega)).2 hc_lt
                have hf : (⟨(M + c * (w + 1) + w) % n, Nat.mod_lt _ hn⟩ : Fin n) = i := by
                  ext; dsimp; rw [hdecomp', Nat.mod_eq_of_lt i.isLt]
                rw [hf] at h1
                exact h1.symm
    have hx_ok : ∀ x : Fin (L + w) → Bool, okEnc x →
        ok (fromX x) ∧ toX (fromX x) = x := by
      intro x hokx
      have hx0 : ∀ r : Fin w, x ⟨r.val, by omega⟩ = dst r := by
        intro r
        have h1 := (hokx.1 r).1
        have hf : (Fin.ofNat (L + d + 1) r.val : Fin (L + w)) = ⟨r.val, by omega⟩ := by
          ext; change r.val % (L + d + 1) = r.val
          exact Nat.mod_eq_of_lt (by dsimp [w] at r ⊢; omega)
        rw [hf] at h1; exact h1
      have hxL : ∀ r : Fin w, x ⟨L + r.val, by omega⟩ = src r := by
        intro r
        have h1 := (hokx.1 r).2
        have hf : (Fin.ofNat (L + d + 1) (L + r.val) : Fin (L + w)) = ⟨L + r.val, by omega⟩ := by
          ext; change (L + r.val) % (L + d + 1) = L + r.val
          exact Nat.mod_eq_of_lt (by dsimp [w] at r ⊢; omega)
        rw [hf] at h1; exact h1
      have hinv : toX (fromX x) = x := by
        funext i
        dsimp only [toX, fromX]
        by_cases hL : i.val < L
        · simp [hL]
        · have hsw : i.val < start + w := by have := i.isLt; omega
          simp only [hL, hsw, ↓reduceDIte, ↓reduceIte]
          have hsub : i.val - L < w := by have := i.isLt; omega
          have hmod : (i.val - L) % w = i.val - L := Nat.mod_eq_of_lt hsub
          have h1 := hxL ⟨i.val - L, hsub⟩
          have hfi : (⟨L + (i.val - L), by omega⟩ : Fin (L + w)) = i := by ext; dsimp; omega
          rw [hfi] at h1
          rw [h1]
          congr 1; ext; exact hmod
      have hfrom_tail : ∀ idx : ℕ, M ≤ idx → idx < n + w →
          fromX x ⟨idx % n, Nat.mod_lt _ hn⟩ =
            padBit dst ⟨(idx - M) % (w + 1), Nat.mod_lt _ (by omega)⟩ := by
        intro idx hge hlt
        by_cases hltn : idx < n
        · rw [show (⟨idx % n, Nat.mod_lt _ hn⟩ : Fin n) = ⟨idx, hltn⟩ from
            Fin.ext (Nat.mod_eq_of_lt hltn)]
          dsimp only [fromX]
          have h1 : ¬ (idx < L) := by omega
          have h2 : ¬ (idx < start + w) := by omega
          have h3 : ¬ (idx < M) := by omega
          simp [h1, h2, h3]
        · have hsub_w : idx - n < w := by omega
          have hsub_L : idx - n < L := by
            have h2d : 1 ≤ 2 ^ d := Nat.one_le_pow d 2 (by omega)
            have hwL : w ≤ L := by dsimp [L]; nlinarith
            omega
          have hsub_n : idx - n < n := by omega
          have hmod_n : idx % n = idx - n := by
            conv_lhs => rw [show idx = (idx - n) + n by omega]
            rw [Nat.add_mod_right, Nat.mod_eq_of_lt hsub_n]
          rw [show (⟨idx % n, Nat.mod_lt _ hn⟩ : Fin n) = ⟨idx - n, hsub_n⟩ from Fin.ext hmod_n]
          dsimp only [fromX]
          simp only [hsub_L, ↓reduceDIte]
          rw [hx0 ⟨idx - n, hsub_w⟩]
          have hmod_w1 : (idx - M) % (w + 1) = idx - n := by
            have heq : idx - M = (idx - n) + q * (w + 1) := by dsimp [M, n]; omega
            rw [heq, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
          dsimp only [padBit]
          have hltw : (idx - M) % (w + 1) < w := by rw [hmod_w1]; exact hsub_w
          simp only [hltw, ↓reduceDIte]
          congr 1; ext; exact hmod_w1.symm
      have hfrom_dst : ∀ idx : ℕ, start + w ≤ idx → idx < M + w →
          fromX x ⟨idx % n, Nat.mod_lt _ hn⟩ =
            dst ⟨(idx - L) % w, Nat.mod_lt _ hw_pos⟩ := by
        intro idx hge hlt
        by_cases hltM : idx < M
        · have hltn : idx < n := by omega
          rw [show (⟨idx % n, Nat.mod_lt _ hn⟩ : Fin n) = ⟨idx, hltn⟩ from
            Fin.ext (Nat.mod_eq_of_lt hltn)]
          dsimp only [fromX]
          have h1 : ¬ (idx < L) := by omega
          have h2 : ¬ (idx < start + w) := by omega
          simp [h1, h2, hltM]
        · rw [hfrom_tail idx (by omega) (by omega)]
          have hsub_w : idx - M < w := by omega
          have hmod_w1 : (idx - M) % (w + 1) = idx - M := Nat.mod_eq_of_lt (by omega)
          have hmod_w : (idx - L) % w = idx - M := by
            have heq : idx - L = (idx - M) + (B + p) * w := by
              have hML : M = L + (B + p) * w := by dsimp [M]; ring
              omega
            rw [heq, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hsub_w]
          dsimp only [padBit]
          have hltw : (idx - M) % (w + 1) < w := by rw [hmod_w1]; exact hsub_w
          simp only [hltw, ↓reduceDIte]
          congr 1; ext; dsimp; rw [hmod_w1, hmod_w]
      have hfrom_src : ∀ idx : ℕ, L ≤ idx → idx < start + w →
          fromX x ⟨idx % n, Nat.mod_lt _ hn⟩ =
            src ⟨(idx - L) % w, Nat.mod_lt _ hw_pos⟩ := by
        intro idx hge hlt
        have hltn : idx < n := by omega
        rw [show (⟨idx % n, Nat.mod_lt _ hn⟩ : Fin n) = ⟨idx, hltn⟩ from
          Fin.ext (Nat.mod_eq_of_lt hltn)]
        dsimp only [fromX]
        have h1 : ¬ (idx < L) := by omega
        simp [h1, hlt]
      refine ⟨?_, hinv⟩
      intro s
      dsimp only [row]
      by_cases hs_in : start ≤ s.val ∧ s.val < start + w
      · simp only [hs_in, and_self, ↓reduceIte, probe, Bool.and_eq_true, beq_iff_eq]
        have h0 : fromX x ⟨(s.val + (0 : Fin (w + 1)).val) % n, Nat.mod_lt _ hn⟩ =
            src ⟨(s.val - L) % w, Nat.mod_lt _ hw_pos⟩ := by
          simpa using hfrom_src s.val (by omega) hs_in.2
        have hw1 : fromX x ⟨(s.val + (Fin.last w).val) % n, Nat.mod_lt _ hn⟩ =
            dst ⟨(s.val + w - L) % w, Nat.mod_lt _ hw_pos⟩ :=
          hfrom_dst (s.val + w) (by omega) (by omega)
        have hmod1 : (s.val - L) % w = s.val - start := by
          have heq : s.val - L = (s.val - start) + h.val * w := by dsimp [start]; omega
          rw [heq, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
        have hmod2 : (s.val + w - L) % w = s.val - start := by
          have heq : s.val + w - L = (s.val - start) + (h.val + 1) * w := by
            dsimp [start]; rw [Nat.add_mul, Nat.one_mul]; omega
          rw [heq, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
        have hfin : (Fin.ofNat (d + 1) (s.val - start) : Fin w) = ⟨s.val - start, by omega⟩ := by
          ext; change (s.val - start) % (d + 1) = s.val - start
          exact Nat.mod_eq_of_lt (by dsimp [w] at hs_in ⊢; omega)
        rw [h0, hw1, hfin]
        constructor
        · congr 1; ext; exact hmod1
        · congr 1; ext; exact hmod2
      · simp only [hs_in, ↓reduceIte, ctx]
        by_cases hsL : s.val < L
        · simp only [hsL, ↓reduceDIte]
          have h1 := hokx.2 ⟨s.val, hsL⟩
          convert h1 using 2
          funext offset
          have hlt_Lw : s.val + offset.val < L + w := by have := offset.isLt; omega
          have hlt_n : s.val + offset.val < n := by omega
          have hto := congrFun hinv ⟨s.val + offset.val, hlt_Lw⟩
          dsimp only [toX] at hto
          have hfn : (⟨(s.val + offset.val) % n, Nat.mod_lt _ hn⟩ : Fin n) =
              ⟨s.val + offset.val, hlt_n⟩ := Fin.ext (Nat.mod_eq_of_lt hlt_n)
          have hfo : (Fin.ofNat (L + d + 1) (s.val + offset.val) : Fin (L + w)) =
              ⟨s.val + offset.val, hlt_Lw⟩ := by
            ext; change (s.val + offset.val) % (L + d + 1) = s.val + offset.val
            exact Nat.mod_eq_of_lt (by dsimp [w] at hlt_Lw ⊢; omega)
          rw [hfn, hto, hfo]
        · simp only [hsL, ↓reduceDIte]
          by_cases hsM : s.val < M
          · simp only [hsM, ↓reduceIte, beq_iff_eq]
            by_cases hlt_start : s.val < start
            · have h0 : fromX x ⟨(s.val + (0 : Fin (w + 1)).val) % n, Nat.mod_lt _ hn⟩ =
                  src ⟨(s.val - L) % w, Nat.mod_lt _ hw_pos⟩ := by
                simpa using hfrom_src s.val (by omega) (by omega)
              have hw1 : fromX x ⟨(s.val + (Fin.last w).val) % n, Nat.mod_lt _ hn⟩ =
                  src ⟨(s.val + w - L) % w, Nat.mod_lt _ hw_pos⟩ :=
                hfrom_src (s.val + w) (by omega) (by omega)
              rw [h0, hw1]
              congr 1; ext; dsimp
              rw [show s.val + w - L = (s.val - L) + w by omega, Nat.add_mod_right]
            · have hge_sw : start + w ≤ s.val := by omega
              have h0 : fromX x ⟨(s.val + (0 : Fin (w + 1)).val) % n, Nat.mod_lt _ hn⟩ =
                  dst ⟨(s.val - L) % w, Nat.mod_lt _ hw_pos⟩ := by
                simpa using hfrom_dst s.val hge_sw (by omega)
              have hw1 : fromX x ⟨(s.val + (Fin.last w).val) % n, Nat.mod_lt _ hn⟩ =
                  dst ⟨(s.val + w - L) % w, Nat.mod_lt _ hw_pos⟩ :=
                hfrom_dst (s.val + w) (by omega) (by omega)
              rw [h0, hw1]
              congr 1; ext; dsimp
              rw [show s.val + w - L = (s.val - L) + w by omega, Nat.add_mod_right]
          · simp only [hsM, ↓reduceIte, beq_iff_eq]
            let u0 := s.val - M
            have hw1 : fromX x ⟨(s.val + (Fin.last w).val) % n, Nat.mod_lt _ hn⟩ =
                padBit dst ⟨(u0 + w) % (w + 1), Nat.mod_lt _ (by omega)⟩ := by
              simp only [Fin.val_last]
              rw [hfrom_tail (s.val + w) (by omega) (by have := s.isLt; omega)]
              congr 1; ext; dsimp [u0]; congr 1; omega
            have hmap : (List.finRange w).map
                  (fun j : Fin w => fromX x ⟨(s.val + j.val) % n, Nat.mod_lt _ hn⟩) =
                (List.finRange w).map
                  (fun j : Fin w => padBit dst ⟨(u0 + j.val) % (w + 1), Nat.mod_lt _ (by omega)⟩) := by
              apply List.map_congr_left
              intro j _
              rw [hfrom_tail (s.val + j.val) (by omega) (by have := s.isLt; have := j.isLt; omega)]
              congr 1; ext; dsimp [u0]; congr 1; omega
            rw [hw1, hmap, xorList_rotate_eq (padBit dst) (padBit_sum dst) u0]
    have hcard_eq : (Finset.univ.filter ok).card = (Finset.univ.filter okEnc).card := by
      apply Finset.card_nbij' toX fromX
      · intro word hmem
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hmem ⊢
        exact (hword_ok word hmem).1
      · intro x hmem
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hmem ⊢
        exact (hx_ok x hmem).1
      · intro word hmem
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
        exact (hword_ok word hmem).2
      · intro x hmem
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
        exact (hx_ok x hmem).2
    exact hcard_eq.trans henc_card

end PEqualNP.Outside.L_clb_051_aux

theorem PEqualNP.Outside.L_clb_051 : (∀ d b p q : ℕ,
  let w := d + 1
  let D := Fin d → Bool
  let B := b + 1
  let L := 3 * w * 2 ^ d
  let n := L + B * w + p * w + q * (w + 1)
  let hn : 0 < n := by dsimp [n, L, B, w]; positivity
  let Pattern := Fin (w + 1) → Bool
  ∃ (ctx : (D → D → Bool) → Fin n → Pattern → Bool)
    (probe : D → D → Fin w → Pattern → Bool),
    (∀ M N i, L ≤ i.val → ctx M i = ctx N i) ∧
    ∀ (A : D → D → Bool) (u v : D) (h : Fin B),
      let start := L + h.val * w
      let row := fun (i : Fin n) (pat : Pattern) =>
        if start ≤ i.val ∧ i.val < start + w then
          probe u v (Fin.ofNat (d + 1) (i.val - start)) pat
        else ctx A i pat
      let ok := fun (word : Fin n → Bool) => ∀ s : Fin n,
        row s (fun k => word ⟨(s.val + k.val) % n, Nat.mod_lt _ hn⟩) = true
      (Finset.univ.filter ok).card = (A u v).toNat) :=
  PEqualNP.Outside.L_clb_051_aux.main_aux
