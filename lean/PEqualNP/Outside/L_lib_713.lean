import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_713_aux

private def sgn (b : Bool) : ℤ := if b then -1 else 1

private theorem sgn_mul_self (b : Bool) : sgn b * sgn b = 1 := by
  cases b <;> rfl

private theorem sgn_sq (b : Bool) : (sgn b) ^ 2 = 1 := by
  cases b <;> rfl

private theorem ind_four_eq (a a' b c c' : Bool) :
    (if Bool.xor a b = c ∧ Bool.xor a' b = c' then (4 : ℤ) else 0) =
    1 + (sgn a * sgn c + sgn a' * sgn c') * sgn b + (sgn a * sgn c) * (sgn a' * sgn c') := by
  cases a <;> cases a' <;> cases b <;> cases c <;> cases c' <;> rfl

private theorem sgn_mul_eq_ite (a b : Bool) :
    sgn a * sgn b = 1 - 2 * (if a ≠ b then (1 : ℤ) else 0) := by
  cases a <;> cases b <;> rfl

private theorem sum_sgn_orth {n m : ℕ} (F : Fin n → Fin m → Bool)
    (horth : ∀ u v : Fin n, u ≠ v →
      2 * ((Finset.univ : Finset (Fin m)).filter (fun x => F u x ≠ F v x)).card = m)
    {u v : Fin n} (huv : u ≠ v) :
    ∑ x : Fin m, sgn (F u x) * sgn (F v x) = 0 := by
  have h1 : ∑ x : Fin m, sgn (F u x) * sgn (F v x) =
      ∑ x : Fin m, ((1 : ℤ) - 2 * (if F u x ≠ F v x then (1 : ℤ) else 0)) :=
    Finset.sum_congr rfl (fun x _ => sgn_mul_eq_ite (F u x) (F v x))
  rw [h1, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one, ← Finset.mul_sum, Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_const, nsmul_eq_mul, mul_one]
  have hm := horth u v huv
  have hmz : (2 : ℤ) * (((Finset.univ : Finset (Fin m)).filter (fun x => F u x ≠ F v x)).card : ℤ) = (m : ℤ) := by
    exact_mod_cast hm
  omega

end PEqualNP.Outside.L_lib_713_aux

theorem PEqualNP.Outside.L_lib_713 : (∀ (n m l : ℕ) (F : Fin n → Fin m → Bool),
  (∀ u v : Fin n, u ≠ v →
    2*((Finset.univ : Finset (Fin m)).filter (fun x => F u x ≠ F v x)).card = m) →
  ∀ (name : Fin l × Bool ↪ Fin n) (H : Fin m → Bool) (p q : Fin l → Bool),
    let e := ∑ i : Fin l, ((Finset.univ : Finset (Fin m)).filter (fun x =>
      Bool.xor (F (name (i,false)) x) (H x) = p i ∧
      Bool.xor (F (name (i,true)) x) (H x) = q i)).card
    (4*(e : ℤ) - (m : ℤ)*(l : ℤ))^2 ≤ 2*(l : ℤ)*(m : ℤ)^2 ∧
      m*l ≤ 2*m + 8*e) := by
  intro n m l F horth name H p q e
  let sgn := PEqualNP.Outside.L_lib_713_aux.sgn
  let c : Fin l × Bool → ℤ := fun z => sgn (if z.2 then q z.1 else p z.1)
  let S : Fin m → ℤ := fun x => ∑ z : Fin l × Bool, sgn (F (name z) x) * c z
  let h : Fin m → ℤ := fun x => sgn (H x)
  have hS_split : ∀ x : Fin m,
      S x = ∑ i : Fin l, (sgn (F (name (i, false)) x) * sgn (p i) +
        sgn (F (name (i, true)) x) * sgn (q i)) := by
    intro x
    unfold S
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp [c, add_comm]
  have hlin : 4 * (e : ℤ) - (m : ℤ) * (l : ℤ) = ∑ x : Fin m, h x * S x := by
    have he4 : 4 * (e : ℤ) =
        ∑ i : Fin l, ∑ x : Fin m,
          (if Bool.xor (F (name (i, false)) x) (H x) = p i ∧
              Bool.xor (F (name (i, true)) x) (H x) = q i then (4 : ℤ) else 0) := by
      have hez : (e : ℤ) = ∑ i : Fin l, (((Finset.univ : Finset (Fin m)).filter (fun x =>
          Bool.xor (F (name (i, false)) x) (H x) = p i ∧
          Bool.xor (F (name (i, true)) x) (H x) = q i)).card : ℤ) := by
        simp only [e, Nat.cast_sum]
      rw [hez, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_comm]
    rw [he4]
    have hexp : (∑ i : Fin l, ∑ x : Fin m,
          (if Bool.xor (F (name (i, false)) x) (H x) = p i ∧
              Bool.xor (F (name (i, true)) x) (H x) = q i then (4 : ℤ) else 0)) =
        ∑ i : Fin l, ∑ x : Fin m,
          ((1 : ℤ) +
            (sgn (F (name (i, false)) x) * sgn (p i) +
             sgn (F (name (i, true)) x) * sgn (q i)) * h x +
            (sgn (F (name (i, false)) x) * sgn (p i)) *
             (sgn (F (name (i, true)) x) * sgn (q i))) :=
      Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun x _ =>
        PEqualNP.Outside.L_lib_713_aux.ind_four_eq _ _ _ _ _))
    rw [hexp]
    have hsplit : (∑ i : Fin l, ∑ x : Fin m,
          ((1 : ℤ) +
            (sgn (F (name (i, false)) x) * sgn (p i) +
             sgn (F (name (i, true)) x) * sgn (q i)) * h x +
            (sgn (F (name (i, false)) x) * sgn (p i)) *
             (sgn (F (name (i, true)) x) * sgn (q i)))) =
        (∑ _i : Fin l, ∑ _x : Fin m, (1 : ℤ)) +
        (∑ i : Fin l, ∑ x : Fin m,
          (sgn (F (name (i, false)) x) * sgn (p i) +
           sgn (F (name (i, true)) x) * sgn (q i)) * h x) +
        (∑ i : Fin l, ∑ x : Fin m,
          (sgn (F (name (i, false)) x) * sgn (p i)) *
           (sgn (F (name (i, true)) x) * sgn (q i))) := by
      simp only [Finset.sum_add_distrib]
    rw [hsplit]
    have hterm1 : (∑ _i : Fin l, ∑ _x : Fin m, (1 : ℤ)) = (m : ℤ) * (l : ℤ) := by
      simp [mul_comm]
    have hterm3 : (∑ i : Fin l, ∑ x : Fin m,
          (sgn (F (name (i, false)) x) * sgn (p i)) *
           (sgn (F (name (i, true)) x) * sgn (q i))) = 0 := by
      refine Finset.sum_eq_zero (fun i _ => ?_)
      have hfac : (∑ x : Fin m,
            (sgn (F (name (i, false)) x) * sgn (p i)) *
             (sgn (F (name (i, true)) x) * sgn (q i))) =
          (sgn (p i) * sgn (q i)) *
            ∑ x : Fin m, sgn (F (name (i, false)) x) * sgn (F (name (i, true)) x) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun x _ => by ring)
      rw [hfac]
      have hne : name (i, false) ≠ name (i, true) := fun h => by
        have := name.injective h
        exact Bool.noConfusion (Prod.mk.inj this).2
      rw [PEqualNP.Outside.L_lib_713_aux.sum_sgn_orth F horth hne, mul_zero]
    have hterm2 : (∑ i : Fin l, ∑ x : Fin m,
          (sgn (F (name (i, false)) x) * sgn (p i) +
           sgn (F (name (i, true)) x) * sgn (q i)) * h x) =
        ∑ x : Fin m, h x * S x := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [hS_split x, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => by ring)
    rw [hterm1, hterm2, hterm3, add_zero]
    ring
  have hhsq : ∑ x : Fin m, (h x) ^ 2 = (m : ℤ) := by
    have hc : ∑ x : Fin m, (h x) ^ 2 = ∑ _x : Fin m, (1 : ℤ) :=
      Finset.sum_congr rfl (fun x _ => PEqualNP.Outside.L_lib_713_aux.sgn_sq (H x))
    rw [hc]; simp
  have hSsq : ∑ x : Fin m, (S x) ^ 2 = 2 * (l : ℤ) * (m : ℤ) := by
    have hexp : ∑ x : Fin m, (S x) ^ 2 =
        ∑ z1 : Fin l × Bool, ∑ z2 : Fin l × Bool,
          (c z1 * c z2) * ∑ x : Fin m, sgn (F (name z1) x) * sgn (F (name z2) x) := by
      have h1 : ∑ x : Fin m, (S x) ^ 2 =
          ∑ x : Fin m, ∑ z1 : Fin l × Bool, ∑ z2 : Fin l × Bool,
            (c z1 * c z2) * (sgn (F (name z1) x) * sgn (F (name z2) x)) := by
        refine Finset.sum_congr rfl (fun x _ => ?_)
        rw [sq, Finset.sum_mul]
        refine Finset.sum_congr rfl (fun z1 _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun z2 _ => by ring)
      rw [h1, Finset.sum_comm]
      refine Finset.sum_congr rfl (fun z1 _ => ?_)
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun z2 _ => ?_)
      rw [Finset.mul_sum]
    rw [hexp]
    have hdiag : ∀ z1 : Fin l × Bool,
        (∑ z2 : Fin l × Bool,
          (c z1 * c z2) * ∑ x : Fin m, sgn (F (name z1) x) * sgn (F (name z2) x)) = (m : ℤ) := by
      intro z1
      rw [Finset.sum_eq_single z1]
      · have hc1 : c z1 * c z1 = 1 := PEqualNP.Outside.L_lib_713_aux.sgn_mul_self _
        have hs1 : ∑ x : Fin m, sgn (F (name z1) x) * sgn (F (name z1) x) = (m : ℤ) := by
          have : ∑ x : Fin m, sgn (F (name z1) x) * sgn (F (name z1) x) = ∑ _x : Fin m, (1 : ℤ) :=
            Finset.sum_congr rfl (fun x _ => PEqualNP.Outside.L_lib_713_aux.sgn_mul_self _)
          rw [this]; simp
        rw [hc1, one_mul, hs1]
      · intro z2 _ hne
        have hname : name z1 ≠ name z2 := fun h => hne (name.injective h).symm
        rw [PEqualNP.Outside.L_lib_713_aux.sum_sgn_orth F horth hname, mul_zero]
      · intro h; exact absurd (Finset.mem_univ z1) h
    rw [Finset.sum_congr rfl (fun z1 _ => hdiag z1), Finset.sum_const, Finset.card_univ,
      Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, nsmul_eq_mul]
    push_cast
    ring
  have hcs : (4 * (e : ℤ) - (m : ℤ) * (l : ℤ)) ^ 2 ≤ 2 * (l : ℤ) * (m : ℤ) ^ 2 := by
    rw [hlin]
    have hraw := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin m)) h S
    rw [hhsq, hSsq] at hraw
    nlinarith
  refine ⟨hcs, ?_⟩
  have hsq : ((l : ℤ) - 2) ^ 2 ≥ 0 := sq_nonneg ((l : ℤ) - 2)
  have hm0 : (0 : ℤ) ≤ m := Nat.cast_nonneg m
  have hl0 : (0 : ℤ) ≤ l := Nat.cast_nonneg l
  have he0 : (0 : ℤ) ≤ e := Nat.cast_nonneg e
  have hlin_z : (m : ℤ) * (l : ℤ) ≤ 2 * (m : ℤ) + 8 * (e : ℤ) := by
    have h4 : (2 * ((m : ℤ) * (l : ℤ) - 4 * (e : ℤ))) ^ 2 ≤ ((m : ℤ) * (l : ℤ) + 2 * (m : ℤ)) ^ 2 := by
      nlinarith
    have hnonneg : 0 ≤ (m : ℤ) * (l : ℤ) + 2 * (m : ℤ) := by nlinarith
    nlinarith
  exact_mod_cast hlin_z
