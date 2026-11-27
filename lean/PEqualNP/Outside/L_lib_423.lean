import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_423_aux

private def zsign (bit : ZMod 2) : ℤ :=
  if bit = 0 then (1 : ℤ) else -1

private lemma zsign_zero : zsign 0 = 1 := rfl

private lemma zsign_add (x y : ZMod 2) : zsign (x + y) = zsign x * zsign y := by
  fin_cases x <;> fin_cases y <;> decide

private lemma zsign_add_one (x : ZMod 2) : zsign (x + 1) = -zsign x := by
  fin_cases x <;> decide

private lemma zmod2_add_self (x : ZMod 2) : x + x = 0 := by
  fin_cases x <;> decide

private lemma zmod2_eq_one_of_ne_zero {x : ZMod 2} (hx : x ≠ 0) : x = 1 := by
  fin_cases x
  · exact False.elim (hx rfl)
  · rfl

private lemma zmod2_add_eq_zero_imp (a b : ZMod 2) : a + b = 0 → b = a := by
  intro hab
  have h1 := congrArg (fun x => a + x) hab
  rw [← add_assoc, zmod2_add_self, zero_add, add_zero] at h1
  exact h1

private lemma vec_add_eq_zero_iff {k : ℕ} (y1 y2 : Fin k → ZMod 2) :
    y1 + y2 = 0 ↔ y2 = y1 := by
  constructor
  · intro h
    funext i
    have hi := congrFun h i
    dsimp only [Pi.add_apply, Pi.zero_apply] at hi
    exact zmod2_add_eq_zero_imp (y1 i) (y2 i) hi
  · rintro rfl
    funext i
    exact zmod2_add_self (y2 i)

private lemma sum_zsign_dot {k : ℕ} (z : Fin k → ZMod 2) :
    (∑ b : Fin k → ZMod 2, zsign (dotProduct b z)) = if z = 0 then (2 : ℤ) ^ k else 0 := by
  by_cases hz : z = 0
  · subst hz
    simp only [↓reduceIte, dotProduct_zero, zsign_zero, Finset.sum_const, Finset.card_univ,
      Fintype.card_fun, ZMod.card, Fintype.card_fin, nsmul_eq_mul, mul_one, Nat.cast_pow,
      Nat.cast_ofNat]
  · simp only [hz, ↓reduceIte]
    have hex : ∃ i : Fin k, z i ≠ 0 := by
      by_contra hall
      apply hz
      funext i
      by_contra hi
      exact hall ⟨i, hi⟩
    rcases hex with ⟨i, hi⟩
    have hzi : z i = 1 := zmod2_eq_one_of_ne_zero hi
    let flip : Equiv.Perm (Fin k → ZMod 2) :=
      { toFun := fun b => Function.update b i (b i + 1)
        invFun := fun b => Function.update b i (b i + 1)
        left_inv := fun b => by
          funext j
          by_cases hji : j = i
          · subst hji
            simp only [Function.update_self]
            have h11 : (1 : ZMod 2) + 1 = 0 := by decide
            rw [add_assoc, h11, add_zero]
          · simp [Function.update_of_ne hji]
        right_inv := fun b => by
          funext j
          by_cases hji : j = i
          · subst hji
            simp only [Function.update_self]
            have h11 : (1 : ZMod 2) + 1 = 0 := by decide
            rw [add_assoc, h11, add_zero]
          · simp [Function.update_of_ne hji] }
    have hdot_flip : ∀ b : Fin k → ZMod 2, dotProduct (flip b) z = dotProduct b z + 1 := by
      intro b
      dsimp only [dotProduct, flip, Equiv.coe_fn_mk]
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
        ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
      have hrest : ∑ j ∈ Finset.univ.erase i, Function.update b i (b i + 1) j * z j =
          ∑ j ∈ Finset.univ.erase i, b j * z j := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
      rw [hrest, Function.update_self, hzi, mul_one, mul_one]
      ring
    have hneg : (∑ b : Fin k → ZMod 2, zsign (dotProduct b z)) =
        -(∑ b : Fin k → ZMod 2, zsign (dotProduct b z)) := by
      calc (∑ b : Fin k → ZMod 2, zsign (dotProduct b z))
          = ∑ b : Fin k → ZMod 2, zsign (dotProduct (flip b) z) :=
              (Equiv.sum_comp flip (fun b => zsign (dotProduct b z))).symm
        _ = ∑ b : Fin k → ZMod 2, -zsign (dotProduct b z) := by
              apply Finset.sum_congr rfl
              intro b _
              rw [hdot_flip b, zsign_add_one]
        _ = -(∑ b : Fin k → ZMod 2, zsign (dotProduct b z)) := by simp [Finset.sum_neg_distrib]
    omega

private theorem main_aux : ∀ r k : ℕ,
    let P := Fin r → ZMod 2
    let T := Fin k → ZMod 2
    let sign := fun (bit : ZMod 2) => if bit = 0 then (1 : ℤ) else -1
    ∀ (h : P → T → ℤ) (a : P),
      (∑ b : T, (∑ x : P, ∑ y : T, h x y * sign (dotProduct a x + dotProduct b y))^2) =
        (2:ℤ)^k * ∑ u : P, ∑ v : P, ∑ y : T,
          h u y * h v y * sign (dotProduct a (u+v)) := by
  intro r k P T sign h a
  change (∑ b : T, (∑ x : P, ∑ y : T, h x y * zsign (dotProduct a x + dotProduct b y)) ^ 2) =
    (2 : ℤ) ^ k * ∑ u : P, ∑ v : P, ∑ y : T, h u y * h v y * zsign (dotProduct a (u + v))
  have hexpand : ∀ b : T,
      (∑ x : P, ∑ y : T, h x y * zsign (dotProduct a x + dotProduct b y)) ^ 2 =
        ∑ u : P, ∑ v : P, ∑ y1 : T, ∑ y2 : T,
          (h u y1 * h v y2 * zsign (dotProduct a (u + v))) * zsign (dotProduct b (y1 + y2)) := by
    intro b
    rw [sq, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro u _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro y1 _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y2 _
    rw [dotProduct_add, dotProduct_add, zsign_add, zsign_add, zsign_add, zsign_add]
    ring
  calc (∑ b : T, (∑ x : P, ∑ y : T, h x y * zsign (dotProduct a x + dotProduct b y)) ^ 2)
      = ∑ b : T, ∑ u : P, ∑ v : P, ∑ y1 : T, ∑ y2 : T,
          (h u y1 * h v y2 * zsign (dotProduct a (u + v))) * zsign (dotProduct b (y1 + y2)) := by
          apply Finset.sum_congr rfl; intro b _; exact hexpand b
    _ = ∑ u : P, ∑ b : T, ∑ v : P, ∑ y1 : T, ∑ y2 : T,
          (h u y1 * h v y2 * zsign (dotProduct a (u + v))) * zsign (dotProduct b (y1 + y2)) :=
          Finset.sum_comm
    _ = ∑ u : P, ∑ v : P, ∑ b : T, ∑ y1 : T, ∑ y2 : T,
          (h u y1 * h v y2 * zsign (dotProduct a (u + v))) * zsign (dotProduct b (y1 + y2)) := by
          apply Finset.sum_congr rfl; intro u _; exact Finset.sum_comm
    _ = ∑ u : P, ∑ v : P, ∑ y1 : T, ∑ b : T, ∑ y2 : T,
          (h u y1 * h v y2 * zsign (dotProduct a (u + v))) * zsign (dotProduct b (y1 + y2)) := by
          apply Finset.sum_congr rfl; intro u _
          apply Finset.sum_congr rfl; intro v _; exact Finset.sum_comm
    _ = ∑ u : P, ∑ v : P, ∑ y1 : T, ∑ y2 : T, ∑ b : T,
          (h u y1 * h v y2 * zsign (dotProduct a (u + v))) * zsign (dotProduct b (y1 + y2)) := by
          apply Finset.sum_congr rfl; intro u _
          apply Finset.sum_congr rfl; intro v _
          apply Finset.sum_congr rfl; intro y1 _; exact Finset.sum_comm
    _ = ∑ u : P, ∑ v : P, ∑ y1 : T,
          (2 : ℤ) ^ k * (h u y1 * h v y1 * zsign (dotProduct a (u + v))) := by
          apply Finset.sum_congr rfl; intro u _
          apply Finset.sum_congr rfl; intro v _
          apply Finset.sum_congr rfl; intro y1 _
          have hinner : ∀ y2 : T,
              (∑ b : T, (h u y1 * h v y2 * zsign (dotProduct a (u + v))) *
                zsign (dotProduct b (y1 + y2))) =
                if y2 = y1 then
                  (2 : ℤ) ^ k * (h u y1 * h v y2 * zsign (dotProduct a (u + v)))
                else 0 := by
            intro y2
            rw [← Finset.mul_sum, sum_zsign_dot]
            by_cases h21 : y2 = y1
            · have h0 : y1 + y2 = 0 := (vec_add_eq_zero_iff y1 y2).mpr h21
              simp only [h0, ↓reduceIte]
              simp only [h21, ↓reduceIte]
              ring
            · have h0 : y1 + y2 ≠ 0 := fun h => h21 ((vec_add_eq_zero_iff y1 y2).mp h)
              simp only [h0, h21, ↓reduceIte, mul_zero]
          simp_rw [hinner]
          simp
    _ = (2 : ℤ) ^ k * ∑ u : P, ∑ v : P, ∑ y : T,
          h u y * h v y * zsign (dotProduct a (u + v)) := by
          simp_rw [← Finset.mul_sum]

end PEqualNP.Outside.L_lib_423_aux

theorem PEqualNP.Outside.L_lib_423 : (∀ r k : ℕ,
  let P := Fin r → ZMod 2
  let T := Fin k → ZMod 2
  let sign := fun (bit : ZMod 2) => if bit = 0 then (1 : ℤ) else -1
  ∀ (h : P → T → ℤ) (a : P),
    (∑ b : T, (∑ x : P, ∑ y : T, h x y * sign (dotProduct a x + dotProduct b y))^2) =
      (2:ℤ)^k * ∑ u : P, ∑ v : P, ∑ y : T,
        h u y * h v y * sign (dotProduct a (u+v))) :=
  PEqualNP.Outside.L_lib_423_aux.main_aux
