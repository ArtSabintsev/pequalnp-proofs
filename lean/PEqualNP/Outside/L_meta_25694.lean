import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.L_lib_420

namespace PEqualNP.Outside.L_meta_25694_aux

theorem z2_add_self (x : ZMod 2) : x + x = 0 := by
  revert x; decide

theorem z2_add_three (x : ZMod 2) : x + x + x = x := by
  revert x; decide

theorem z2_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  revert x; decide

theorem z2_add_eq_zero_iff (x y : ZMod 2) : x + y = 0 ↔ x = y := by
  revert x y; decide

theorem z2_add_cancel_left (x y : ZMod 2) : x + (x + y) = y := by
  revert x y; decide

theorem z2_add_cancel_right (x y : ZMod 2) : x + y + y = x := by
  revert x y; decide

theorem z2_neg_eq (x : ZMod 2) : -x = x := by
  revert x; decide

theorem z2_smul_eq (c x : ZMod 2) : c • x = c * x := rfl

def zmodEquivFin (k : ℕ) [NeZero k] : ZMod k ≃ Fin k where
  toFun x := ⟨x.val, ZMod.val_lt x⟩
  invFun i := (i.val : ZMod k)
  left_inv x := ZMod.natCast_zmod_val x
  right_inv i := Fin.ext (ZMod.val_natCast_of_lt i.isLt)

def vecEquiv (k : ℕ) [NeZero k] : (Fin k → ZMod 2) ≃ (ZMod k → ZMod 2) :=
  Equiv.arrowCongr (zmodEquivFin k).symm (Equiv.refl (ZMod 2))

theorem dotProduct_vecEquiv {k : ℕ} [NeZero k] (a x : Fin k → ZMod 2) :
    dotProduct (vecEquiv k a) (vecEquiv k x) = dotProduct a x := by
  unfold dotProduct vecEquiv
  dsimp [Equiv.arrowCongr]
  exact Fintype.sum_equiv (zmodEquivFin k) _ _ (fun i => rfl)

theorem walsh_zmod (k : ℕ) [NeZero k] (q : (ZMod k → ZMod 2) → ZMod 2)
    (hpol : ∀ u v w : ZMod k → ZMod 2,
      q (u + (v + w)) + q u + q (v + w) + q 0 =
        (q (u + v) + q u + q v + q 0) + (q (u + w) + q u + q w + q 0))
    (a : ZMod k → ZMod 2) :
    let sign := fun (t : ZMod 2) => if t = 0 then (1 : ℤ) else -1
    let radical := Finset.univ.filter (fun d : ZMod k → ZMod 2 =>
      ∀ x : ZMod k → ZMod 2, q (d + x) + q d + q x + q 0 = 0)
    (∑ x : ZMod k → ZMod 2, sign (dotProduct a x + q x)) ^ 2 =
      if ∀ d ∈ radical, q d + q 0 = dotProduct a d
      then (2 : ℤ) ^ k * (radical.card : ℤ) else 0 := by
  dsimp only
  let e := vecEquiv k
  have he_add : ∀ u v : Fin k → ZMod 2, e (u + v) = e u + e v := by
    intro u v; funext i; rfl
  have he_zero : e 0 = 0 := by funext i; rfl
  let q' : (Fin k → ZMod 2) → ZMod 2 := fun x => q (e x)
  have hpol' : ∀ u v w : Fin k → ZMod 2,
      q' (u + (v + w)) + q' u + q' (v + w) + q' 0 =
        (q' (u + v) + q' u + q' v + q' 0) + (q' (u + w) + q' u + q' w + q' 0) := by
    intro u v w
    dsimp only [q']
    rw [he_add, he_add, he_add, he_add, he_zero]
    exact hpol (e u) (e v) (e w)
  have h420 := PEqualNP.Outside.L_lib_420 k q' hpol' (e.symm a)
  dsimp only at h420
  have hsum : (∑ x : ZMod k → ZMod 2, (if dotProduct a x + q x = 0 then (1 : ℤ) else -1)) =
      ∑ x : Fin k → ZMod 2, (if q' x + dotProduct (e.symm a) x = 0 then (1 : ℤ) else -1) := by
    symm
    refine Fintype.sum_equiv e _ _ (fun x => ?_)
    have hdot : dotProduct a (e x) = dotProduct (e.symm a) x := by
      have := dotProduct_vecEquiv (e.symm a) x
      simpa [e] using this
    rw [hdot, add_comm]
  let rad' := Finset.univ.filter (fun d : Fin k → ZMod 2 =>
    ∀ x : Fin k → ZMod 2, q' (d + x) + q' d + q' x + q' 0 = 0)
  let rad := Finset.univ.filter (fun d : ZMod k → ZMod 2 =>
    ∀ x : ZMod k → ZMod 2, q (d + x) + q d + q x + q 0 = 0)
  have hmem_rad : ∀ d : Fin k → ZMod 2, d ∈ rad' ↔ e d ∈ rad := by
    intro d
    simp only [rad', rad, Finset.mem_filter, Finset.mem_univ, true_and, q']
    constructor
    · intro h x
      have hx := h (e.symm x)
      rw [he_add, he_zero] at hx
      simpa [e] using hx
    · intro h x
      rw [he_add, he_zero]
      exact h (e x)
  have hrad_card : rad'.card = rad.card := by
    refine Finset.card_bij (fun d _ => e d) (fun d hd => (hmem_rad d).mp hd)
      (fun d1 _ d2 _ h => e.injective h)
      (fun d hd => ⟨e.symm d, (hmem_rad (e.symm d)).mpr (by simpa [e] using hd), by simp [e]⟩)
  have hcond : (∀ d ∈ rad', q' d + q' 0 = dotProduct (e.symm a) d) ↔
      (∀ d ∈ rad, q d + q 0 = dotProduct a d) := by
    constructor
    · intro h d hd
      have hd' : e.symm d ∈ rad' := (hmem_rad (e.symm d)).mpr (by simpa [e] using hd)
      have h1 := h (e.symm d) hd'
      dsimp only [q'] at h1
      rw [he_zero] at h1
      have hdot : dotProduct a d = dotProduct (e.symm a) (e.symm d) := by
        have := dotProduct_vecEquiv (e.symm a) (e.symm d)
        simpa [e] using this
      simpa [e, hdot] using h1
    · intro h d hd
      have h1 := h (e d) ((hmem_rad d).mp hd)
      dsimp only [q']
      rw [he_zero]
      have hdot : dotProduct a (e d) = dotProduct (e.symm a) d := by
        have := dotProduct_vecEquiv (e.symm a) d
        simpa [e] using this
      rwa [hdot] at h1
  rw [hsum, h420]
  change (if ∀ d ∈ rad', q' d + q' 0 = dotProduct (e.symm a) d then (2 : ℤ) ^ k * (rad'.card : ℤ) else 0) =
    if ∀ d ∈ rad, q d + q 0 = dotProduct a d then (2 : ℤ) ^ k * (rad.card : ℤ) else 0
  rw [hrad_card]
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (hcond.mp h1) h2
  · exact absurd (hcond.mpr h2) h1
  · rfl

def mixFn (k : ℕ) (s : ℕ) (x : ZMod k → ZMod 2) (i : ZMod k) : ZMod 2 :=
  x (i - (s : ZMod k)) + x i + x (i + (s : ZMod k))

def nlFn (k : ℕ) (y : ZMod k → ZMod 2) (j : ZMod k) : ZMod 2 :=
  y j + (1 + y (j + 1)) * y (j + 2)

def edgeFn (k : ℕ) (b w : ZMod k → ZMod 2) (i : ZMod k) : ZMod 2 :=
  b (i - 2) * w (i - 1) + b (i - 1) * w (i + 1)

def mixLM (k : ℕ) (s : ℕ) : (ZMod k → ZMod 2) →ₗ[ZMod 2] (ZMod k → ZMod 2) where
  toFun := mixFn k s
  map_add' u v := by
    funext i
    simp only [mixFn, Pi.add_apply]
    ring
  map_smul' c u := by
    funext i
    simp only [mixFn, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

def edgeLM (k : ℕ) (b : ZMod k → ZMod 2) : (ZMod k → ZMod 2) →ₗ[ZMod 2] (ZMod k → ZMod 2) where
  toFun := edgeFn k b
  map_add' u v := by
    funext i
    simp only [edgeFn, Pi.add_apply]
    ring
  map_smul' c u := by
    funext i
    simp only [edgeFn, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem mixFn_zero (k : ℕ) (x : ZMod k → ZMod 2) : mixFn k 0 x = x := by
  funext i
  simp only [mixFn, Nat.cast_zero, sub_zero, add_zero]
  exact z2_add_three (x i)

theorem mixLM_zero (k : ℕ) : mixLM k 0 = LinearMap.id := by
  ext x i
  exact congrFun (mixFn_zero k x) i

theorem dotProduct_mix_symm (k : ℕ) [NeZero k] (s : ℕ) (u v : ZMod k → ZMod 2) :
    dotProduct u (mixFn k s v) = dotProduct (mixFn k s u) v := by
  unfold dotProduct mixFn
  have h1 : ∑ i : ZMod k, u i * (v (i - (s : ZMod k)) + v i + v (i + (s : ZMod k))) =
      (∑ i : ZMod k, u i * v (i - (s : ZMod k))) +
      (∑ i : ZMod k, u i * v i) +
      (∑ i : ZMod k, u i * v (i + (s : ZMod k))) := by
    simp only [mul_add, Finset.sum_add_distrib]
  have h2 : ∑ i : ZMod k, (u (i - (s : ZMod k)) + u i + u (i + (s : ZMod k))) * v i =
      (∑ i : ZMod k, u (i - (s : ZMod k)) * v i) +
      (∑ i : ZMod k, u i * v i) +
      (∑ i : ZMod k, u (i + (s : ZMod k)) * v i) := by
    simp only [add_mul, Finset.sum_add_distrib]
  have hs1 : ∑ i : ZMod k, u i * v (i - (s : ZMod k)) =
      ∑ j : ZMod k, u (j + (s : ZMod k)) * v j := by
    refine Fintype.sum_equiv (Equiv.subRight (s : ZMod k)) _ _ (fun i => ?_)
    simp [Equiv.subRight]
  have hs2 : ∑ i : ZMod k, u i * v (i + (s : ZMod k)) =
      ∑ j : ZMod k, u (j - (s : ZMod k)) * v j := by
    refine Fintype.sum_equiv (Equiv.addRight (s : ZMod k)) _ _ (fun i => ?_)
    simp [Equiv.addRight]
  rw [h1, h2, hs1, hs2]
  ring

theorem polar_nl_eq (k : ℕ) [NeZero k] (b u v : ZMod k → ZMod 2) :
    dotProduct b (nlFn k (u + v)) + dotProduct b (nlFn k u) + dotProduct b (nlFn k v) =
      dotProduct (edgeFn k b u) v := by
  unfold dotProduct nlFn edgeFn
  have hpoint : ∀ j : ZMod k,
      b j * ((u j + v j) + (1 + (u (j + 1) + v (j + 1))) * (u (j + 2) + v (j + 2))) +
      b j * (u j + (1 + u (j + 1)) * u (j + 2)) +
      b j * (v j + (1 + v (j + 1)) * v (j + 2)) =
      b j * u (j + 1) * v (j + 2) + b j * u (j + 2) * v (j + 1) := by
    intro j
    have h2 : (2 : ZMod 2) = 0 := by decide
    have hdiff :
        b j * ((u j + v j) + (1 + (u (j + 1) + v (j + 1))) * (u (j + 2) + v (j + 2))) +
        b j * (u j + (1 + u (j + 1)) * u (j + 2)) +
        b j * (v j + (1 + v (j + 1)) * v (j + 2)) =
        (b j * u (j + 1) * v (j + 2) + b j * u (j + 2) * v (j + 1)) +
        (2 : ZMod 2) * (b j * (u j + v j + u (j + 2) + v (j + 2) + u (j + 1) * u (j + 2) +
          v (j + 1) * v (j + 2))) := by ring
    rw [hdiff, h2, zero_mul, add_zero]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  have hsum : ∑ j : ZMod k,
      (b j * ((u + v) j + (1 + (u + v) (j + 1)) * (u + v) (j + 2)) +
       b j * (u j + (1 + u (j + 1)) * u (j + 2)) +
       b j * (v j + (1 + v (j + 1)) * v (j + 2))) =
      (∑ j : ZMod k, b j * u (j + 1) * v (j + 2)) +
      (∑ j : ZMod k, b j * u (j + 2) * v (j + 1)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => hpoint j)
  rw [hsum]
  have hs1 : ∑ j : ZMod k, b j * u (j + 1) * v (j + 2) =
      ∑ i : ZMod k, b (i - 2) * u (i - 1) * v i := by
    refine Fintype.sum_equiv (Equiv.addRight (2 : ZMod k)) _ _ (fun j => ?_)
    have h1 : j + 2 - 2 = j := by ring
    have h2 : j + 2 - 1 = j + 1 := by ring
    simp [Equiv.addRight, h1, h2]
  have hs2 : ∑ j : ZMod k, b j * u (j + 2) * v (j + 1) =
      ∑ i : ZMod k, b (i - 1) * u (i + 1) * v i := by
    refine Fintype.sum_equiv (Equiv.addRight (1 : ZMod k)) _ _ (fun j => ?_)
    have h1 : j + 1 - 1 = j := by ring
    have h2 : j + 1 + 1 = j + 2 := by ring
    simp [Equiv.addRight, h1, h2]
  rw [hs1, hs2, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

theorem dotProduct_edge_symm (k : ℕ) [NeZero k] (b u v : ZMod k → ZMod 2) :
    dotProduct (edgeFn k b u) v = dotProduct u (edgeFn k b v) := by
  have h1 := polar_nl_eq k b u v
  have h2 := polar_nl_eq k b v u
  rw [dotProduct_comm u (edgeFn k b v), ← h1, ← h2, add_comm u v]
  ring

def polarLM (k : ℕ) (s : ℕ) (b : ZMod k → ZMod 2) :
    (ZMod k → ZMod 2) →ₗ[ZMod 2] (ZMod k → ZMod 2) :=
  (mixLM k s).comp ((edgeLM k b).comp (mixLM k s))

theorem polarLM_apply (k : ℕ) (s : ℕ) (b u : ZMod k → ZMod 2) :
    polarLM k s b u = mixFn k s (edgeFn k b (mixFn k s u)) := rfl

theorem dotProduct_polarLM_symm (k : ℕ) [NeZero k] (s : ℕ) (b u v : ZMod k → ZMod 2) :
    dotProduct (polarLM k s b u) v = dotProduct u (polarLM k s b v) := by
  rw [polarLM_apply, polarLM_apply, ← dotProduct_mix_symm, dotProduct_edge_symm,
    dotProduct_mix_symm]

theorem q_zero (k : ℕ) [NeZero k] (s : ℕ) (b : ZMod k → ZMod 2) :
    dotProduct b (nlFn k (mixFn k s 0)) = 0 := by
  have h1 : mixFn k s 0 = 0 := by funext i; simp [mixFn]
  have h2 : nlFn k 0 = 0 := by funext j; simp [nlFn]
  rw [h1, h2, dotProduct_zero]

theorem polar_q_eq (k : ℕ) [NeZero k] (s : ℕ) (b u v : ZMod k → ZMod 2) :
    let q := fun x => dotProduct b (nlFn k (mixFn k s x))
    q (u + v) + q u + q v + q 0 = dotProduct (polarLM k s b u) v := by
  dsimp only
  rw [q_zero, add_zero]
  have hmix : mixFn k s (u + v) = mixFn k s u + mixFn k s v := (mixLM k s).map_add u v
  rw [hmix, polar_nl_eq, polarLM_apply, ← dotProduct_mix_symm]

theorem dotProduct_eq_zero_forall_iff (k : ℕ) [NeZero k] (z : ZMod k → ZMod 2) :
    (∀ y : ZMod k → ZMod 2, dotProduct z y = 0) ↔ z = 0 := by
  constructor
  · intro h
    funext i
    have hi := h (Pi.single i 1)
    unfold dotProduct at hi
    rw [Finset.sum_eq_single i] at hi
    · simpa using hi
    · intro j _ hji
      simp [Pi.single_eq_of_ne hji]
    · intro hni
      exact absurd (Finset.mem_univ i) hni
  · intro hz y
    rw [hz, zero_dotProduct]

theorem linear_repr_dotProduct (k : ℕ) [NeZero k] (Φ : (ZMod k → ZMod 2) →ₗ[ZMod 2] ZMod 2) :
    ∃ a : ZMod k → ZMod 2, ∀ x : ZMod k → ZMod 2, Φ x = dotProduct a x := by
  refine ⟨fun i => Φ (Pi.single i 1), fun x => ?_⟩
  have hx : x = ∑ i : ZMod k, x i • Pi.single i (1 : ZMod 2) := by
    funext j
    rw [Finset.sum_apply]
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij
      simp [Pi.single_eq_of_ne (Ne.symm hij)]
    · intro hnj
      exact absurd (Finset.mem_univ j) hnj
  conv_lhs => rw [hx]
  rw [map_sum]
  unfold dotProduct
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [map_smul, smul_eq_mul, mul_comm]

theorem extend_linear_dotProduct (k : ℕ) [NeZero k] (K : Submodule (ZMod 2) (ZMod k → ZMod 2))
    (φ : K →ₗ[ZMod 2] ZMod 2) :
    ∃ a : ZMod k → ZMod 2, ∀ x : K, φ x = dotProduct a x.1 := by
  obtain ⟨W, hW⟩ := Submodule.exists_isCompl K
  let Φ : (ZMod k → ZMod 2) →ₗ[ZMod 2] ZMod 2 := φ.comp (Submodule.projectionOnto K W hW)
  obtain ⟨a, ha⟩ := linear_repr_dotProduct k Φ
  refine ⟨a, fun x => ?_⟩
  have h1 : Φ x.1 = φ x := by
    dsimp only [Φ, LinearMap.comp_apply]
    rw [Submodule.projectionOnto_apply_left hW x]
  rw [← h1, ha x.1]

theorem perp_ker_eq_range (k : ℕ) [NeZero k] (T : (ZMod k → ZMod 2) →ₗ[ZMod 2] (ZMod k → ZMod 2))
    (hsymm : ∀ u v, dotProduct (T u) v = dotProduct u (T v)) :
    ∀ z : ZMod k → ZMod 2, (∀ x ∈ LinearMap.ker T, dotProduct z x = 0) ↔ z ∈ LinearMap.range T := by
  let V := ZMod k → ZMod 2
  let K := LinearMap.ker T
  let perp : Submodule (ZMod 2) V :=
    { carrier := {z | ∀ x ∈ K, dotProduct z x = 0}, add_mem' := fun {a b} ha hb x hx => by
        rw [add_dotProduct, ha x hx, hb x hx, add_zero],
      zero_mem' := fun x _ => zero_dotProduct x,
      smul_mem' := fun c {a} ha x hx => by rw [smul_dotProduct, ha x hx, smul_zero] }
  have hle : LinearMap.range T ≤ perp := by
    rintro z ⟨u, rfl⟩ x hx
    rw [hsymm u x, LinearMap.mem_ker.mp hx, dotProduct_zero]
  let res : V →ₗ[ZMod 2] (K →ₗ[ZMod 2] ZMod 2) :=
    { toFun := fun z =>
        { toFun := fun x => dotProduct z x.1
          map_add' := fun x y => dotProduct_add z x.1 y.1
          map_smul' := fun c x => dotProduct_smul c z x.1 }
      map_add' := fun z1 z2 => by ext x; exact add_dotProduct z1 z2 x.1
      map_smul' := fun c z => by ext x; exact smul_dotProduct c z x.1 }
  have hker_res : LinearMap.ker res = perp := by
    ext z
    simp only [LinearMap.mem_ker, perp, Submodule.mem_mk, AddSubmonoid.mem_mk,
      AddSubsemigroup.mem_mk, Set.mem_ofPred_eq]
    constructor
    · intro hz x hx
      have := congrArg (fun f : K →ₗ[ZMod 2] ZMod 2 => f ⟨x, hx⟩) hz
      exact this
    · intro hz
      ext x
      exact hz x.1 x.2
  have hsurj_res : LinearMap.range res = ⊤ := by
    rw [eq_top_iff]
    intro φ _
    obtain ⟨a, ha⟩ := extend_linear_dotProduct k K φ
    refine ⟨a, ?_⟩
    ext x
    exact (ha x).symm
  have hfin_res := LinearMap.finrank_range_add_finrank_ker res
  rw [hsurj_res, hker_res, finrank_top] at hfin_res
  have hfin_dual : Module.finrank (ZMod 2) (K →ₗ[ZMod 2] ZMod 2) = Module.finrank (ZMod 2) K := by
    rw [Module.finrank_linearMap, Module.finrank_self, mul_one]
  rw [hfin_dual] at hfin_res
  change Module.finrank (ZMod 2) (LinearMap.ker T) + Module.finrank (ZMod 2) perp =
    Module.finrank (ZMod 2) (ZMod k → ZMod 2) at hfin_res
  have hfin_T := LinearMap.finrank_range_add_finrank_ker T
  have heq_fin : Module.finrank (ZMod 2) (LinearMap.range T) = Module.finrank (ZMod 2) perp := by
    omega
  have heq_sub : LinearMap.range T = perp := Submodule.eq_of_le_of_finrank_eq hle heq_fin
  intro z
  change z ∈ perp ↔ z ∈ LinearMap.range T
  rw [heq_sub]

theorem support_affine_and_card (k : ℕ) [NeZero k] (s : ℕ) (b : ZMod k → ZMod 2) :
    let V := ZMod k → ZMod 2
    let sign := fun (t : ZMod 2) => if t = 0 then (1 : ℤ) else -1
    let support := Finset.univ.filter (fun mask : V =>
      (∑ x : V, sign (dotProduct mask x + dotProduct b (nlFn k (mixFn k s x)))) ≠ 0)
    (∃ base : V, ∀ a : V, a ∈ support ↔ ∃ u : V, a = base + polarLM k s b u) ∧
    support.card = 2 ^ Module.finrank (ZMod 2) (LinearMap.range (polarLM k s b)) := by
  classical
  dsimp only
  let V := ZMod k → ZMod 2
  let sign := fun (t : ZMod 2) => if t = 0 then (1 : ℤ) else -1
  let q : V → ZMod 2 := fun x => dotProduct b (nlFn k (mixFn k s x))
  let T := polarLM k s b
  let support := Finset.univ.filter (fun mask : V =>
    (∑ x : V, sign (dotProduct mask x + q x)) ≠ 0)
  have hpol : ∀ u v w : V,
      q (u + (v + w)) + q u + q (v + w) + q 0 =
        (q (u + v) + q u + q v + q 0) + (q (u + w) + q u + q w + q 0) := by
    intro u v w
    rw [polar_q_eq, polar_q_eq, polar_q_eq, dotProduct_add]
  let rad := Finset.univ.filter (fun x : V => ∀ y : V, q (x + y) + q x + q y + q 0 = 0)
  have hrad_ker : ∀ x : V, x ∈ rad ↔ x ∈ LinearMap.ker T := by
    intro x
    simp only [rad, Finset.mem_filter, Finset.mem_univ, true_and, LinearMap.mem_ker]
    have h1 : (∀ y : V, q (x + y) + q x + q y + q 0 = 0) ↔ ∀ y : V, dotProduct (T x) y = 0 := by
      constructor <;> intro h y
      · rw [← polar_q_eq]; exact h y
      · rw [polar_q_eq]; exact h y
    rw [h1, dotProduct_eq_zero_forall_iff]
  have hq0 : q 0 = 0 := q_zero k s b
  have hmem_supp : ∀ a : V, a ∈ support ↔ ∀ x ∈ LinearMap.ker T, q x = dotProduct a x := by
    intro a
    simp only [support, Finset.mem_filter, Finset.mem_univ, true_and]
    have hw := walsh_zmod k q hpol a
    dsimp only at hw
    have hrad_pos : (0 : ℤ) < (2 : ℤ) ^ k * (rad.card : ℤ) := by
      have h0mem : (0 : V) ∈ rad := (hrad_ker 0).mpr (Submodule.zero_mem _)
      have hcard_pos : (0 : ℤ) < (rad.card : ℤ) := Int.natCast_pos.mpr (Finset.card_pos.mpr ⟨0, h0mem⟩)
      have hpow_pos : (0 : ℤ) < (2 : ℤ) ^ k := pow_pos (by norm_num) k
      exact mul_pos hpow_pos hcard_pos
    have hsq_iff : (∑ x : V, sign (dotProduct a x + q x)) ≠ 0 ↔
        (∑ x : V, sign (dotProduct a x + q x)) ^ 2 ≠ 0 := by
      constructor
      · intro h; exact pow_ne_zero 2 h
      · intro h hz; exact h (by simp [hz])
    rw [hsq_iff, hw]
    change (if ∀ d ∈ rad, q d + q 0 = dotProduct a d then (2 : ℤ) ^ k * (rad.card : ℤ) else 0) ≠ 0 ↔
      ∀ x ∈ LinearMap.ker T, q x = dotProduct a x
    split_ifs with hc
    · constructor
      · intro _ x hx
        have := hc x ((hrad_ker x).mpr hx)
        rwa [hq0, add_zero] at this
      · intro _; exact ne_of_gt hrad_pos
    · constructor
      · intro h; exact absurd rfl h
      · intro hx
        exfalso
        apply hc
        intro d hd
        rw [hq0, add_zero]
        exact hx d ((hrad_ker d).mp hd)
  let φ : LinearMap.ker T →ₗ[ZMod 2] ZMod 2 :=
    { toFun := fun x => q x.1
      map_add' := fun x y => by
        have hp : q (x.1 + y.1) + q x.1 + q y.1 + q 0 = 0 := by
          rw [polar_q_eq, LinearMap.mem_ker.mp x.2, zero_dotProduct]
        rw [hq0, add_zero] at hp
        have h := (z2_add_eq_zero_iff (q (x.1 + y.1)) (q x.1 + q y.1)).mp (by rw [← add_assoc]; exact hp)
        exact h
      map_smul' := fun c x => by
        rcases z2_eq_zero_or_one c with rfl | rfl
        · simp only [zero_smul, ZeroMemClass.coe_zero, RingHom.id_apply]
          exact hq0
        · simp }
  obtain ⟨base, hbase⟩ := extend_linear_dotProduct k (LinearMap.ker T) φ
  have haff : ∀ a : V, a ∈ support ↔ ∃ u : V, a = base + T u := by
    intro a
    rw [hmem_supp a]
    have hstep1 : (∀ x ∈ LinearMap.ker T, q x = dotProduct a x) ↔
        ∀ x ∈ LinearMap.ker T, dotProduct (a + base) x = 0 := by
      constructor <;> intro h x hx
      · rw [add_dotProduct, ← h x hx, ← hbase ⟨x, hx⟩]
        exact z2_add_self (q x)
      · have h1 := h x hx
        rw [add_dotProduct, ← hbase ⟨x, hx⟩] at h1
        exact ((z2_add_eq_zero_iff (dotProduct a x) (q x)).mp h1).symm
    rw [hstep1, perp_ker_eq_range k T (dotProduct_polarLM_symm k s b)]
    constructor
    · rintro ⟨u, hu⟩
      refine ⟨u, ?_⟩
      funext i
      have hi : T u i = a i + base i := congrFun hu i
      have h2 := congrArg (fun t => t + base i) hi
      rw [z2_add_cancel_right] at h2
      change a i = base i + T u i
      rw [← h2, add_comm]
    · rintro ⟨u, rfl⟩
      refine ⟨u, ?_⟩
      funext i
      change T u i = base i + T u i + base i
      rw [add_comm (base i), z2_add_cancel_right]
  refine ⟨⟨base, haff⟩, ?_⟩
  let imgFinset : Finset V := Finset.univ.filter (fun v : V => v ∈ LinearMap.range T)
  have hcard_eq : support.card = imgFinset.card := by
    refine Finset.card_bij (fun a _ => a + base) ?_ ?_ ?_
    · intro a ha
      obtain ⟨u, rfl⟩ := (haff a).mp ha
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨u, ?_⟩⟩
      funext i
      change T u i = base i + T u i + base i
      rw [add_comm (base i), z2_add_cancel_right]
    · intro a1 _ a2 _ h
      funext i
      have hi : a1 i + base i = a2 i + base i := congrFun h i
      have h2 := congrArg (fun t => t + base i) hi
      simpa [z2_add_cancel_right] using h2
    · intro v hv
      obtain ⟨u, rfl⟩ := (Finset.mem_filter.mp hv).2
      refine ⟨base + T u, (haff _).mpr ⟨u, rfl⟩, ?_⟩
      funext i
      change base i + T u i + base i = T u i
      rw [add_comm (base i), z2_add_cancel_right]
  rw [hcard_eq]
  have hcard_sub : imgFinset.card = Fintype.card (LinearMap.range T) := by
    rw [Fintype.card_subtype]
  rw [hcard_sub, Module.card_eq_pow_finrank (K := ZMod 2) (V := LinearMap.range T)]
  simp only [ZMod.card]
  rfl

theorem orbit_period3 (k : ℕ) (d : ℕ) (x : ZMod k → ZMod 2)
    (hker : ∀ i : ZMod k, mixFn k d x i = 0) (i0 : ZMod k) :
    ∀ n : ℕ,
      x (i0 + (n : ZMod k) * (d : ZMod k)) =
        if n % 3 = 0 then x i0
        else if n % 3 = 1 then x (i0 + (d : ZMod k))
        else x i0 + x (i0 + (d : ZMod k)) := by
  have hstep : ∀ j : ZMod k,
      x (j + (2 : ZMod k) * (d : ZMod k)) = x j + x (j + (d : ZMod k)) := by
    intro j
    have h0 := hker (j + (d : ZMod k))
    unfold mixFn at h0
    have hsub : j + (d : ZMod k) - (d : ZMod k) = j := by ring
    have hadd : j + (d : ZMod k) + (d : ZMod k) = j + (2 : ZMod k) * (d : ZMod k) := by ring
    rw [hsub, hadd] at h0
    exact ((z2_add_eq_zero_iff _ _).mp h0).symm
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    match n with
    | 0 => simp
    | 1 => simp
    | m + 2 =>
      have hidx : i0 + ((m + 2 : ℕ) : ZMod k) * (d : ZMod k) =
          (i0 + (m : ZMod k) * (d : ZMod k)) + (2 : ZMod k) * (d : ZMod k) := by
        push_cast; ring
      have hidx1 : (i0 + (m : ZMod k) * (d : ZMod k)) + (d : ZMod k) =
          i0 + ((m + 1 : ℕ) : ZMod k) * (d : ZMod k) := by
        push_cast; ring
      rw [hidx, hstep, hidx1, ih m (by omega), ih (m + 1) (by omega)]
      have hmod : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega
      rcases hmod with hm | hm | hm
      · have h1 : (m + 1) % 3 = 1 := by omega
        have h2 : (m + 2) % 3 = 2 := by omega
        simp [hm, h1, h2]
      · have h1 : (m + 1) % 3 = 2 := by omega
        have h2 : (m + 2) % 3 = 0 := by omega
        simp only [hm, h1, h2, ↓reduceIte, show (1 : ℕ) ≠ 0 by decide,
          show (2 : ℕ) ≠ 0 by decide, show (2 : ℕ) ≠ 1 by decide]
        rw [add_comm (x i0), z2_add_cancel_left]
      · have h1 : (m + 1) % 3 = 0 := by omega
        have h2 : (m + 2) % 3 = 1 := by omega
        simp only [hm, h1, h2, ↓reduceIte, show (2 : ℕ) ≠ 0 by decide,
          show (2 : ℕ) ≠ 1 by decide, show (1 : ℕ) ≠ 0 by decide]
        rw [add_comm _ (x i0), z2_add_cancel_left]

theorem finrank_ker_mix_le (k : ℕ) [NeZero k] (d : ℕ) :
    let g := Nat.gcd k d
    let h := if 3 ∣ k / g then 2 * g else 0
    Module.finrank (ZMod 2) (LinearMap.ker (mixLM k d)) ≤ h := by
  classical
  dsimp only
  let g := Nat.gcd k d
  let m := k / g
  let h := if 3 ∣ m then 2 * g else 0
  have hk_pos : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  have hg_dvd_k : g ∣ k := Nat.gcd_dvd_left k d
  have hg_dvd_d : g ∣ d := Nat.gcd_dvd_right k d
  have hg_pos : 0 < g := Nat.gcd_pos_of_pos_left d hk_pos
  have hmd_eq : ((m : ZMod k) * (d : ZMod k)) = 0 := by
    have hmul : m * d = k * (d / g) := by
      have h1 : g * m = k := Nat.mul_div_cancel' hg_dvd_k
      have h2 : g * (d / g) = d := Nat.mul_div_cancel' hg_dvd_d
      calc m * d = m * (g * (d / g)) := by rw [h2]
        _ = (g * m) * (d / g) := by ring
        _ = k * (d / g) := by rw [h1]
    rw [← Nat.cast_mul, hmul, Nat.cast_mul, ZMod.natCast_self, zero_mul]
  have hcard_le : Fintype.card (LinearMap.ker (mixLM k d)) ≤ 2 ^ h := by
    by_cases hdiv : 3 ∣ m
    · have hh : h = 2 * g := by simp [h, hdiv]
      rw [hh]
      have hbez : (g : ZMod k) = ((Nat.gcdB k d : ZMod k).val : ZMod k) * (d : ZMod k) := by
        have hz := Nat.gcd_eq_gcd_ab k d
        have hcast : ((g : ℤ) : ZMod k) =
            ((k : ℤ) * Nat.gcdA k d + (d : ℤ) * Nat.gcdB k d : ℤ) := congrArg Int.cast hz
        push_cast at hcast
        rw [ZMod.natCast_self, zero_mul, zero_add, mul_comm, ← ZMod.natCast_zmod_val (Nat.gcdB k d : ZMod k)] at hcast
        exact hcast
      let c : ℕ := (Nat.gcdB k d : ZMod k).val
      let encode : LinearMap.ker (mixLM k d) → (Fin g → ZMod 2 × ZMod 2) :=
        fun x r => (x.1 (r.val : ZMod k), x.1 ((r.val : ZMod k) + (d : ZMod k)))
      have hinj : Function.Injective encode := by
        intro x y hxy
        apply Subtype.ext
        funext i
        have hkerx : ∀ j, mixFn k d x.1 j = 0 := fun j => congrFun (LinearMap.mem_ker.mp x.2) j
        have hkery : ∀ j, mixFn k d y.1 j = 0 := fun j => congrFun (LinearMap.mem_ker.mp y.2) j
        let r : Fin g := ⟨i.val % g, Nat.mod_lt i.val hg_pos⟩
        let n : ℕ := (i.val / g) * c
        have hi_eq : i = (r.val : ZMod k) + (n : ZMod k) * (d : ZMod k) := by
          have hdm : g * (i.val / g) + i.val % g = i.val := Nat.div_add_mod i.val g
          have hc' : (i.val : ZMod k) = (r.val : ZMod k) + (i.val / g : ZMod k) * (g : ZMod k) := by
            have := congrArg (Nat.cast (R := ZMod k)) hdm.symm
            push_cast at this
            rw [this]
            dsimp only [r]
            ring
          rw [← ZMod.natCast_zmod_val i, hc', hbez]
          dsimp only [n, c]
          push_cast
          ring
        have hr_eq := congrFun hxy r
        dsimp only [encode] at hr_eq
        have h0 : x.1 (r.val : ZMod k) = y.1 (r.val : ZMod k) := congrArg Prod.fst hr_eq
        have h1 : x.1 ((r.val : ZMod k) + (d : ZMod k)) = y.1 ((r.val : ZMod k) + (d : ZMod k)) :=
          congrArg Prod.snd hr_eq
        rw [hi_eq, orbit_period3 k d x.1 hkerx (r.val : ZMod k) n,
          orbit_period3 k d y.1 hkery (r.val : ZMod k) n, h0, h1]
      calc Fintype.card (LinearMap.ker (mixLM k d))
          ≤ Fintype.card (Fin g → ZMod 2 × ZMod 2) := Fintype.card_le_of_injective encode hinj
        _ = (2 * 2) ^ g := by simp
        _ = 2 ^ (2 * g) := by rw [pow_mul]; rfl
    · have hh : h = 0 := by simp [h, hdiv]
      rw [hh, pow_zero]
      have hsub : Subsingleton (LinearMap.ker (mixLM k d)) := by
        constructor
        intro x y
        have hall0 : ∀ z : LinearMap.ker (mixLM k d), z.1 = 0 := by
          intro z
          have hkerz : ∀ j, mixFn k d z.1 j = 0 := fun j => congrFun (LinearMap.mem_ker.mp z.2) j
          funext i
          have hm0 := orbit_period3 k d z.1 hkerz i m
          have hm1 := orbit_period3 k d z.1 hkerz i (m + 1)
          have hidx0 : i + (m : ZMod k) * (d : ZMod k) = i := by rw [hmd_eq, add_zero]
          have hidx1 : i + ((m + 1 : ℕ) : ZMod k) * (d : ZMod k) = i + (d : ZMod k) := by
            push_cast; rw [add_mul, one_mul, ← add_assoc, hmd_eq, add_zero]
          rw [hidx0] at hm0
          rw [hidx1] at hm1
          have hmod : m % 3 = 1 ∨ m % 3 = 2 := by omega
          rcases hmod with hm | hm
          · have hm' : (m + 1) % 3 = 2 := by omega
            simp only [hm, hm', ↓reduceIte,
              show (1 : ℕ) ≠ 0 by decide,
              show (2 : ℕ) ≠ 0 by decide, show (2 : ℕ) ≠ 1 by decide] at hm0 hm1
            have hadd := congrArg (fun t => t + z.1 (i + (d : ZMod k))) hm1
            rw [z2_add_self, z2_add_cancel_right] at hadd
            exact hadd.symm
          · have hm' : (m + 1) % 3 = 0 := by omega
            simp only [hm, hm', ↓reduceIte,
              show (2 : ℕ) ≠ 0 by decide, show (2 : ℕ) ≠ 1 by decide] at hm0 hm1
            have hadd := congrArg (fun t => z.1 i + t) hm0
            rw [z2_add_self, z2_add_cancel_left] at hadd
            exact hm1.symm.trans hadd.symm
        exact Subtype.ext ((hall0 x).trans (hall0 y).symm)
      exact Fintype.card_le_one_iff_subsingleton.mpr hsub
  have hpow := Module.card_eq_pow_finrank (K := ZMod 2) (V := LinearMap.ker (mixLM k d))
  simp only [ZMod.card] at hpow
  rw [hpow] at hcard_le
  exact (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).mp hcard_le

theorem card_ker_edge_all_ones (k : ℕ) [NeZero k] :
    Nat.card (LinearMap.ker (edgeLM k (fun _ => 1))) = 2 ^ Nat.gcd k 2 := by
  have hmem : ∀ w : ZMod k → ZMod 2,
      w ∈ LinearMap.ker (edgeLM k (fun _ => 1)) ↔ ∀ i : ZMod k, w (i + 2) = w i := by
    intro w
    rw [LinearMap.mem_ker]
    constructor
    · intro h i
      have hi := congrFun h (i + 1)
      dsimp only [edgeLM, LinearMap.coe_mk, AddHom.coe_mk, edgeFn, Pi.zero_apply] at hi
      have h1 : i + 1 - 1 = i := by ring
      have h2 : i + 1 + 1 = i + 2 := by ring
      rw [one_mul, one_mul, h1, h2] at hi
      exact ((z2_add_eq_zero_iff _ _).mp hi).symm
    · intro h
      funext i
      dsimp only [edgeLM, LinearMap.coe_mk, AddHom.coe_mk, edgeFn, Pi.zero_apply]
      rw [one_mul, one_mul]
      have h2 : i + 1 = (i - 1) + 2 := by ring
      rw [h2, h (i - 1)]
      exact z2_add_self _
  have hshift : ∀ w : ZMod k → ZMod 2, (∀ i : ZMod k, w (i + 2) = w i) →
      ∀ (i : ZMod k) (n : ℕ), w (i + (2 * n : ℕ)) = w i := by
    intro w hw i n
    induction n with
    | zero => simp
    | succ n ih =>
      have : i + ((2 * (n + 1) : ℕ) : ZMod k) = (i + ((2 * n : ℕ) : ZMod k)) + 2 := by
        push_cast; ring
      rw [this, hw, ih]
  by_cases heven : 2 ∣ k
  · have hgcd : Nat.gcd k 2 = 2 := by
      rw [Nat.gcd_comm]
      exact Nat.gcd_eq_left heven
    rw [hgcd]
    let e : LinearMap.ker (edgeLM k (fun _ => 1)) ≃ ZMod 2 × ZMod 2 :=
      { toFun := fun w => (w.1 0, w.1 1)
        invFun := fun p =>
          ⟨fun i => if i.val % 2 = 0 then p.1 else p.2, by
            rw [hmem]
            intro i
            have hpar : (i + 2).val % 2 = i.val % 2 := by
              have hv2 : (2 : ZMod k).val = 2 % k := by
                simpa using (ZMod.val_natCast k 2)
              have hval : (i + 2).val = (i.val + 2) % k := by
                rw [ZMod.val_add, hv2, Nat.add_mod_mod]
              rw [hval, Nat.mod_mod_of_dvd _ heven]
              omega
            simp [hpar]⟩
        left_inv := fun w => by
          apply Subtype.ext
          funext i
          have hw := (hmem w.1).mp w.2
          have hdm : 2 * (i.val / 2) + i.val % 2 = i.val := Nat.div_add_mod i.val 2
          have hi : i = ((i.val % 2 : ℕ) : ZMod k) + ((2 * (i.val / 2) : ℕ) : ZMod k) := by
            have hc := congrArg (Nat.cast (R := ZMod k)) hdm.symm
            push_cast at hc
            calc i = (i.val : ZMod k) := (ZMod.natCast_zmod_val i).symm
              _ = 2 * ((i.val / 2 : ℕ) : ZMod k) + ((i.val % 2 : ℕ) : ZMod k) := hc
              _ = ((i.val % 2 : ℕ) : ZMod k) + ((2 * (i.val / 2) : ℕ) : ZMod k) := by
                  push_cast; ring
          dsimp only
          have hpar : i.val % 2 = 0 ∨ i.val % 2 = 1 := by omega
          rcases hpar with hp | hp
          · simp only [hp, ite_true]
            conv_rhs => rw [hi, hp]
            simpa using (hshift w.1 hw 0 (i.val / 2)).symm
          · simp only [hp, show (1 : ℕ) ≠ 0 by decide, ite_false]
            conv_rhs => rw [hi, hp]
            simpa using (hshift w.1 hw 1 (i.val / 2)).symm
        right_inv := fun p => by
          have hk2 : 2 ≤ k := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne k)) heven
          have hv0 : (0 : ZMod k).val = 0 := ZMod.val_zero
          have hv1 : (1 : ZMod k).val = 1 := by
            simpa using ZMod.val_natCast_of_lt (show 1 < k by omega)
          ext <;> simp [hv0, hv1] }
    rw [Nat.card_congr e, Nat.card_prod]
    simp
  · have hodd : k % 2 = 1 := by omega
    have hgcd : Nat.gcd k 2 = 1 := by
      have hle : Nat.gcd k 2 ≤ 2 := Nat.gcd_le_right k (by omega)
      have hd2 : Nat.gcd k 2 ∣ 2 := Nat.gcd_dvd_right k 2
      have hdk : Nat.gcd k 2 ∣ k := Nat.gcd_dvd_left k 2
      have hpos : 0 < Nat.gcd k 2 := Nat.gcd_pos_of_pos_right k (by omega)
      have hne2 : Nat.gcd k 2 ≠ 2 := fun h => heven (h ▸ hdk)
      omega
    rw [hgcd, pow_one]
    let e : LinearMap.ker (edgeLM k (fun _ => 1)) ≃ ZMod 2 :=
      { toFun := fun w => w.1 0
        invFun := fun c =>
          ⟨fun _ => c, by rw [hmem]; intro _; rfl⟩
        left_inv := fun w => by
          apply Subtype.ext
          funext i
          have hw := (hmem w.1).mp w.2
          have hstep1 : ∀ j : ZMod k, w.1 (j + 1) = w.1 j := by
            intro j
            have h1 : (2 * ((k + 1) / 2) : ℕ) = k + 1 := by omega
            have hcast : ((2 * ((k + 1) / 2) : ℕ) : ZMod k) = 1 := by
              rw [h1, Nat.cast_add, ZMod.natCast_self, zero_add, Nat.cast_one]
            have hs := hshift w.1 hw j ((k + 1) / 2)
            rwa [hcast] at hs
          have hconst : ∀ n : ℕ, w.1 (n : ZMod k) = w.1 0 := by
            intro n
            induction n with
            | zero => simp
            | succ n ih =>
              rw [Nat.cast_succ, hstep1, ih]
          dsimp only
          rw [← ZMod.natCast_zmod_val i, hconst i.val]
        right_inv := fun _ => rfl }
    rw [Nat.card_congr e]
    simp

def IsPathKer (n : ℕ) (c : ℕ → ZMod 2) (w : Fin n → ZMod 2) : Prop :=
  ∀ t : Fin n,
    (if h : 0 < t.val then c (t.val - 1) * w ⟨t.val - 1, by omega⟩ else 0) +
    (if h : t.val + 1 < n then c t.val * w ⟨t.val + 1, h⟩ else 0) = 0

def runLen (m : ℕ) (c : ℕ → ZMod 2) : ℕ :=
  ((List.range m).takeWhile (fun off => decide (c off = 1))).length

def shiftSeq (s : ℕ) (c : ℕ → ZMod 2) : ℕ → ZMod 2 :=
  fun t => c (t + s)

def pathSum (n : ℕ) (c : ℕ → ZMod 2) : ℕ :=
  ∑ t ∈ Finset.range n,
    if c t = 1 ∧ (t = 0 ∨ c (t - 1) = 0)
    then 2 * ((runLen (n - t) (shiftSeq t c) + 1) / 2) else 0

theorem list_range_succ_eq (m : ℕ) :
    List.range (m + 1) = 0 :: (List.range m).map (· + 1) := by
  exact List.range_succ_eq_map

theorem runLen_zero_of_eq_zero {m : ℕ} {c : ℕ → ZMod 2} (h0 : c 0 = 0) :
    runLen m c = 0 := by
  cases m with
  | zero => simp [runLen]
  | succ m =>
    unfold runLen
    rw [list_range_succ_eq, List.takeWhile_cons]
    have hf : decide (c 0 = 1) = false := by rw [h0]; decide
    simp [hf]

theorem runLen_succ_of_one {m : ℕ} {c : ℕ → ZMod 2} (h0 : c 0 = 1) :
    runLen (m + 1) c = 1 + runLen m (shiftSeq 1 c) := by
  unfold runLen shiftSeq
  rw [list_range_succ_eq, List.takeWhile_cons]
  have ht : decide (c 0 = 1) = true := by rw [h0]; decide
  simp only [ht, ↓reduceIte, List.length_cons, List.takeWhile_map, List.length_map]
  have hfn : (fun off => decide (c off = 1)) ∘ (· + 1) = (fun off => decide (c (off + 1) = 1)) := rfl
  rw [hfn]
  omega

theorem shiftSeq_add (a b : ℕ) (c : ℕ → ZMod 2) :
    shiftSeq a (shiftSeq b c) = shiftSeq (a + b) c := by
  funext t
  simp only [shiftSeq]
  congr 1
  omega

theorem pathSum_zero (c : ℕ → ZMod 2) : pathSum 0 c = 0 := by
  simp [pathSum]

theorem pathSum_step_zero (n : ℕ) (c : ℕ → ZMod 2) (h0 : c 0 = 0) :
    pathSum (n + 1) c = pathSum n (shiftSeq 1 c) := by
  unfold pathSum
  rw [Finset.sum_range_succ']
  have hterm0 : (if c 0 = 1 ∧ (0 = 0 ∨ c (0 - 1) = 0)
      then 2 * ((runLen (n + 1 - 0) (shiftSeq 0 c) + 1) / 2) else 0) = 0 := by
    simp [h0]
  rw [hterm0, add_zero]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  have hsub : n + 1 - (u + 1) = n - u := by omega
  have hsh : shiftSeq (u + 1) c = shiftSeq u (shiftSeq 1 c) := (shiftSeq_add u 1 c).symm
  rw [hsub, hsh]
  cases u with
  | zero =>
    simp [shiftSeq, h0]
  | succ u =>
    simp [shiftSeq]

theorem pathSum_step_one (n : ℕ) (c : ℕ → ZMod 2) (h0 : c 0 = 1) :
    pathSum (n + 2) c = 2 + pathSum n (shiftSeq 2 c) := by
  unfold pathSum
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  have hterm1 : (if c 1 = 1 ∧ (1 = 0 ∨ c (1 - 1) = 0)
      then 2 * ((runLen (n + 2 - 1) (shiftSeq 1 c) + 1) / 2) else 0) = 0 := by
    simp [h0]
  rw [hterm1, add_zero]
  have hterm0 : (if c 0 = 1 ∧ (0 = 0 ∨ c (0 - 1) = 0)
      then 2 * ((runLen (n + 2 - 0) (shiftSeq 0 c) + 1) / 2) else 0) =
      2 * ((runLen (n + 2) c + 1) / 2) := by
    have hsh0 : shiftSeq 0 c = c := by funext t; simp [shiftSeq]
    simp [h0, hsh0]
  rw [hterm0]
  cases hc1 : z2_eq_zero_or_one (c 1) with
  | inl h1 =>
    have hrl : runLen (n + 2) c = 1 := by
      rw [runLen_succ_of_one h0, runLen_zero_of_eq_zero (by simp [shiftSeq, h1])]
    rw [hrl]
    have htail : ∑ x ∈ Finset.range n,
        (if c (x + 2) = 1 ∧ (x + 2 = 0 ∨ c (x + 2 - 1) = 0)
         then 2 * ((runLen (n + 2 - (x + 2)) (shiftSeq (x + 2) c) + 1) / 2) else 0) =
        ∑ x ∈ Finset.range n,
        (if shiftSeq 2 c x = 1 ∧ (x = 0 ∨ shiftSeq 2 c (x - 1) = 0)
         then 2 * ((runLen (n - x) (shiftSeq x (shiftSeq 2 c)) + 1) / 2) else 0) := by
      refine Finset.sum_congr rfl (fun u _ => ?_)
      have hsub : n + 2 - (u + 2) = n - u := by omega
      have hsh : shiftSeq (u + 2) c = shiftSeq u (shiftSeq 2 c) := (shiftSeq_add u 2 c).symm
      rw [hsub, hsh]
      cases u with
      | zero => simp [shiftSeq, h1]
      | succ u => simp [shiftSeq]
    rw [htail]
    omega
  | inr h1 =>
    have hrl : runLen (n + 2) c = 2 + runLen n (shiftSeq 2 c) := by
      rw [runLen_succ_of_one h0, runLen_succ_of_one (by simp [shiftSeq, h1]), shiftSeq_add]
      have h11 : 1 + 1 = 2 := rfl
      rw [h11]
      omega
    rw [hrl]
    cases n with
    | zero =>
      simp [runLen]
    | succ m =>
      rw [Finset.sum_range_succ', Finset.sum_range_succ']
      have h2zero : (if c (0 + 2) = 1 ∧ (0 + 2 = 0 ∨ c (0 + 2 - 1) = 0)
          then 2 * ((runLen (m + 1 + 2 - (0 + 2)) (shiftSeq (0 + 2) c) + 1) / 2) else 0) = 0 := by
        simp [h1]
      rw [h2zero, add_zero]
      have htail : ∑ x ∈ Finset.range m,
          (if c (x + 1 + 2) = 1 ∧ (x + 1 + 2 = 0 ∨ c (x + 1 + 2 - 1) = 0)
           then 2 * ((runLen (m + 1 + 2 - (x + 1 + 2)) (shiftSeq (x + 1 + 2) c) + 1) / 2) else 0) =
          ∑ x ∈ Finset.range m,
          (if shiftSeq 2 c (x + 1) = 1 ∧ (x + 1 = 0 ∨ shiftSeq 2 c (x + 1 - 1) = 0)
           then 2 * ((runLen (m + 1 - (x + 1)) (shiftSeq (x + 1) (shiftSeq 2 c)) + 1) / 2) else 0) := by
        refine Finset.sum_congr rfl (fun u _ => ?_)
        have hsub : m + 1 + 2 - (u + 1 + 2) = m + 1 - (u + 1) := by omega
        have hsh : shiftSeq (u + 1 + 2) c = shiftSeq (u + 1) (shiftSeq 2 c) :=
          (shiftSeq_add (u + 1) 2 c).symm
        rw [hsub, hsh]
        simp [shiftSeq]
      rw [htail]
      have hsh0 : shiftSeq 0 (shiftSeq 2 c) = shiftSeq 2 c := by funext t; simp [shiftSeq]
      have hsub0 : m + 1 - 0 = m + 1 := by omega
      rw [hsh0, hsub0]
      rcases z2_eq_zero_or_one (shiftSeq 2 c 0) with hc2 | hc2
      · have hrl2 : runLen (m + 1) (shiftSeq 2 c) = 0 := runLen_zero_of_eq_zero hc2
        simp [hc2, hrl2]
        omega
      · simp only [hc2, true_or, and_self, ↓reduceIte]
        omega

theorem path_ker_card_and_le :
    ∀ (n : ℕ) (c : ℕ → ZMod 2), (n = 0 ∨ c (n - 1) = 0) →
      pathSum n c ≤ n ∧
      Nat.card {w : Fin n → ZMod 2 // IsPathKer n c w} = 2 ^ (n - pathSum n c) := by
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro c hlast
    match n with
    | 0 =>
      refine ⟨by simp [pathSum], ?_⟩
      have : Unique {w : Fin 0 → ZMod 2 // IsPathKer 0 c w} :=
        ⟨⟨⟨Fin.elim0, fun t => Fin.elim0 t⟩⟩, fun x => Subtype.ext (funext fun t => Fin.elim0 t)⟩
      rw [Nat.card_unique]
      simp [pathSum]
    | m + 1 =>
      rcases z2_eq_zero_or_one (c 0) with h0 | h0
      · have hlast' : m = 0 ∨ shiftSeq 1 c (m - 1) = 0 := by
          cases m with
          | zero => exact Or.inl rfl
          | succ m' =>
            right
            rcases hlast with h | h
            · cases h
            · simpa [shiftSeq] using h
        obtain ⟨hle', hcard'⟩ := ih m (by omega) (shiftSeq 1 c) hlast'
        rw [pathSum_step_zero m c h0]
        refine ⟨by omega, ?_⟩
        let e : {w : Fin (m + 1) → ZMod 2 // IsPathKer (m + 1) c w} ≃
            ZMod 2 × {w : Fin m → ZMod 2 // IsPathKer m (shiftSeq 1 c) w} :=
          { toFun := fun w =>
              (w.1 ⟨0, by omega⟩, ⟨fun t => w.1 ⟨t.val + 1, by omega⟩, by
                intro t
                have ht := w.2 ⟨t.val + 1, by omega⟩
                dsimp only at ht
                by_cases ht0 : t.val = 0
                · simp only [ht0, Nat.zero_lt_one, ↓reduceDIte, h0, zero_mul, zero_add,
                    Nat.lt_irrefl] at ht ⊢
                  by_cases hlt : 1 < m
                  · have hlt' : 0 + 1 + 1 < m + 1 := by omega
                    have hlt'' : 0 + 1 < m := by omega
                    simp only [hlt', hlt'', ↓reduceDIte, shiftSeq] at ht ⊢
                    exact ht
                  · have hlt'' : ¬ (0 + 1 < m) := by omega
                    simp [hlt'']
                · have hpos : 0 < t.val := by omega
                  have hpos1 : 0 < t.val + 1 := by omega
                  simp only [hpos, hpos1, ↓reduceDIte, Nat.add_sub_cancel] at ht ⊢
                  have hsub1 : t.val = t.val - 1 + 1 := by omega
                  have h1 : c t.val * w.1 ⟨t.val, by omega⟩ =
                      shiftSeq 1 c (t.val - 1) * w.1 ⟨t.val - 1 + 1, by omega⟩ := by
                    simp only [shiftSeq, ← hsub1]
                  rw [← h1]
                  by_cases hlt : t.val + 1 < m
                  · have hlt' : t.val + 1 + 1 < m + 1 := by omega
                    simp only [hlt, hlt', ↓reduceDIte, shiftSeq] at ht ⊢
                    exact ht
                  · have hlt' : ¬ (t.val + 1 + 1 < m + 1) := by omega
                    simp only [hlt, hlt', ↓reduceDIte] at ht ⊢
                    exact ht⟩)
            invFun := fun p =>
              ⟨fun t => if ht : t.val = 0 then p.1 else p.2.1 ⟨t.val - 1, by omega⟩, by
                intro t
                by_cases ht0 : t.val = 0
                · simp only [ht0, Nat.lt_irrefl, ↓reduceDIte, zero_add, h0, zero_mul, dite_eq_ite,
                    ite_self]
                · have hpos : 0 < t.val := by omega
                  have htp := p.2.2 ⟨t.val - 1, by omega⟩
                  dsimp only at htp
                  by_cases ht1 : t.val = 1
                  · simp only [ht1, Nat.zero_lt_one, ↓reduceDIte, Nat.sub_self, h0, zero_mul,
                      zero_add, Nat.lt_irrefl] at htp ⊢
                    by_cases hlt : 1 + 1 < m + 1
                    · have hlt' : 0 + 1 < m := by omega
                      simp only [hlt, hlt', ↓reduceDIte, show (1 + 1 ≠ 0) by omega] at htp ⊢
                      simpa [shiftSeq] using htp
                    · simp [hlt]
                  · have hpos' : 0 < t.val - 1 := by omega
                    simp only [hpos, hpos', ↓reduceDIte,
                      show t.val - 1 ≠ 0 by omega, show t.val + 1 ≠ 0 by omega] at htp ⊢
                    have heq1 : c (t.val - 1) = shiftSeq 1 c (t.val - 1 - 1) := by
                      simp only [shiftSeq]; congr 1; omega
                    have hleft : c (t.val - 1) * p.2.1 ⟨t.val - 1 - 1, by omega⟩ =
                        shiftSeq 1 c (t.val - 1 - 1) * p.2.1 ⟨t.val - 1 - 1, by omega⟩ := by
                      rw [heq1]
                    rw [hleft]
                    by_cases hlt : t.val + 1 < m + 1
                    · have hlt' : t.val - 1 + 1 < m := by omega
                      simp only [hlt, hlt', ↓reduceDIte] at htp ⊢
                      have heq3 : c t.val = shiftSeq 1 c (t.val - 1) := by
                        simp only [shiftSeq]; congr 1; omega
                      have heq4 : (⟨t.val + 1 - 1, by omega⟩ : Fin m) = ⟨t.val - 1 + 1, hlt'⟩ :=
                        Fin.ext (by dsimp only; omega)
                      rw [heq3, heq4]
                      exact htp
                    · have hlt' : ¬ (t.val - 1 + 1 < m) := by omega
                      simp only [hlt, hlt', ↓reduceDIte] at htp ⊢
                      exact htp⟩
            left_inv := fun w => by
              apply Subtype.ext; funext t
              by_cases ht0 : t.val = 0
              · simp only [ht0, ↓reduceDIte]
                exact congrArg w.1 (Fin.ext ht0.symm)
              · simp only [ht0, ↓reduceDIte]
                exact congrArg w.1 (Fin.ext (by dsimp only; omega))
            right_inv := fun p => by
              ext
              · simp
              · simp }
        rw [Nat.card_congr e, Nat.card_prod, Nat.card_eq_fintype_card, ZMod.card, hcard']
        have hexp : m + 1 - pathSum m (shiftSeq 1 c) = (m - pathSum m (shiftSeq 1 c)) + 1 := by omega
        rw [hexp, pow_succ, mul_comm]
      · match m with
        | 0 =>
          rcases hlast with h | h
          · cases h
          · simp [h0] at h
        | m' + 1 =>
          have hlast' : m' = 0 ∨ shiftSeq 2 c (m' - 1) = 0 := by
            cases m' with
            | zero => exact Or.inl rfl
            | succ m'' =>
              right
              rcases hlast with h | h
              · cases h
              · simp only [shiftSeq]
                simpa [show m'' + 1 - 1 + 2 = m'' + 1 + 1 + 1 - 1 by omega] using h
          obtain ⟨hle', hcard'⟩ := ih m' (by omega) (shiftSeq 2 c) hlast'
          rw [pathSum_step_one m' c h0]
          refine ⟨by omega, ?_⟩
          let e : {w : Fin (m' + 2) → ZMod 2 // IsPathKer (m' + 2) c w} ≃
              {w : Fin m' → ZMod 2 // IsPathKer m' (shiftSeq 2 c) w} :=
            { toFun := fun w =>
                ⟨fun t => w.1 ⟨t.val + 2, by omega⟩, by
                  intro t
                  have hw1 : w.1 ⟨1, by omega⟩ = 0 := by
                    have h := w.2 ⟨0, by omega⟩
                    simpa [h0] using h
                  have ht := w.2 ⟨t.val + 2, by omega⟩
                  dsimp only at ht
                  by_cases ht0 : t.val = 0
                  · simp only [ht0, Nat.lt_irrefl, ↓reduceDIte, zero_add,
                      show (0 < 2) by omega] at ht ⊢
                    have hidx1 : (⟨2 - 1, by omega⟩ : Fin (m' + 2)) = ⟨1, by omega⟩ := rfl
                    rw [hidx1, hw1, mul_zero, zero_add] at ht
                    by_cases hlt : 1 < m'
                    · have hlt' : 2 + 1 < m' + 2 := by omega
                      have hlt'' : 0 + 1 < m' := by omega
                      simp only [hlt', hlt'', ↓reduceDIte, shiftSeq] at ht ⊢
                      exact ht
                    · have hlt'' : ¬ (0 + 1 < m') := by omega
                      simp [hlt'']
                  · have hpos : 0 < t.val := by omega
                    have hpos2 : 0 < t.val + 2 := by omega
                    simp only [hpos, hpos2, ↓reduceDIte] at ht ⊢
                    have hleft : c (t.val + 2 - 1) * w.1 ⟨t.val + 2 - 1, by omega⟩ =
                        shiftSeq 2 c (t.val - 1) * w.1 ⟨t.val - 1 + 2, by omega⟩ := by
                      simp only [shiftSeq]
                      exact congrArg₂ (· * ·) (congrArg c (by omega))
                        (congrArg w.1 (Fin.ext (by dsimp only; omega)))
                    rw [hleft] at ht
                    by_cases hlt : t.val + 1 < m'
                    · have hlt' : t.val + 2 + 1 < m' + 2 := by omega
                      simp only [hlt, hlt', ↓reduceDIte, shiftSeq] at ht ⊢
                      have h2 : (⟨t.val + 2 + 1, hlt'⟩ : Fin (m' + 2)) = ⟨t.val + 1 + 2, by omega⟩ :=
                        rfl
                      rw [h2] at ht
                      exact ht
                    · have hlt' : ¬ (t.val + 2 + 1 < m' + 2) := by omega
                      simp only [hlt, hlt', ↓reduceDIte] at ht ⊢
                      exact ht⟩
              invFun := fun w =>
                ⟨fun t =>
                  if ht0 : t.val = 0 then
                    if h2 : 0 < m' then c 1 * w.1 ⟨0, h2⟩ else 0
                  else if ht1 : t.val = 1 then 0
                  else w.1 ⟨t.val - 2, by omega⟩, by
                  intro t
                  by_cases ht0 : t.val = 0
                  · simp [ht0]
                  · by_cases ht1 : t.val = 1
                    · simp only [ht1, Nat.zero_lt_one, ↓reduceDIte, Nat.sub_self, h0, one_mul]
                      by_cases h2 : 0 < m'
                      · have hlt : 1 + 1 < m' + 2 := by omega
                        simp only [h2, hlt, ↓reduceDIte, show (1 + 1 ≠ 0) by omega,
                          show (1 + 1 ≠ 1) by omega]
                        have : (⟨1 + 1 - 2, by omega⟩ : Fin m') = ⟨0, h2⟩ := rfl
                        rw [this]
                        exact z2_add_self _
                      · have hlt : ¬ (1 + 1 < m' + 2) := by omega
                        simp [h2, hlt]
                    · have hpos : 0 < t.val := by omega
                      have htp := w.2 ⟨t.val - 2, by omega⟩
                      dsimp only at htp
                      by_cases ht2 : t.val = 2
                      · simp only [ht2, Nat.lt_irrefl, ↓reduceDIte, Nat.sub_self,
                          show 0 < 2 by omega, show (2 - 1 ≠ 0) by omega,
                          show (2 - 1 = 1) by omega, mul_zero, zero_add] at htp ⊢
                        by_cases hlt : 2 + 1 < m' + 2
                        · have hlt' : 0 + 1 < m' := by omega
                          simp only [hlt, hlt', ↓reduceDIte, show (2 + 1 ≠ 0) by omega,
                            show (2 + 1 ≠ 1) by omega] at htp ⊢
                          simpa [shiftSeq] using htp
                        · simp [hlt]
                      · have hpos' : 0 < t.val - 2 := by omega
                        simp only [hpos, hpos', ↓reduceDIte,
                          show t.val - 1 ≠ 0 by omega, show t.val - 1 ≠ 1 by omega,
                          show t.val + 1 ≠ 0 by omega, show t.val + 1 ≠ 1 by omega] at htp ⊢
                        have heq1 : c (t.val - 1) = shiftSeq 2 c (t.val - 2 - 1) := by
                          simp only [shiftSeq]; congr 1; omega
                        have heq2 : (⟨t.val - 1 - 2, by omega⟩ : Fin m') = ⟨t.val - 2 - 1, by omega⟩ :=
                          Fin.ext (by dsimp only; omega)
                        rw [heq1, heq2]
                        by_cases hlt : t.val + 1 < m' + 2
                        · have hlt' : t.val - 2 + 1 < m' := by omega
                          simp only [hlt, hlt', ↓reduceDIte] at htp ⊢
                          have heq3 : c t.val = shiftSeq 2 c (t.val - 2) := by
                            simp only [shiftSeq]; congr 1; omega
                          have heq4 : (⟨t.val + 1 - 2, by omega⟩ : Fin m') = ⟨t.val - 2 + 1, hlt'⟩ :=
                            Fin.ext (by dsimp only; omega)
                          rw [heq3, heq4]
                          exact htp
                        · have hlt' : ¬ (t.val - 2 + 1 < m') := by omega
                          simp only [hlt, hlt', ↓reduceDIte] at htp ⊢
                          exact htp⟩
              left_inv := fun w => by
                apply Subtype.ext; funext t
                have hw1 : w.1 ⟨1, by omega⟩ = 0 := by
                  have h := w.2 ⟨0, by omega⟩
                  simpa [h0] using h
                have hw0 : w.1 ⟨0, by omega⟩ = if h2 : 0 < m' then c 1 * w.1 ⟨2, by omega⟩ else 0 := by
                  have h := w.2 ⟨1, by omega⟩
                  dsimp only at h
                  simp only [Nat.zero_lt_one, ↓reduceDIte, Nat.sub_self, h0, one_mul] at h
                  by_cases h2 : 0 < m'
                  · have hlt : 1 + 1 < m' + 2 := by omega
                    simp only [h2, hlt, ↓reduceDIte] at h ⊢
                    exact (z2_add_eq_zero_iff _ _).mp h
                  · have hlt : ¬ (1 + 1 < m' + 2) := by omega
                    simp only [h2, hlt, ↓reduceDIte, add_zero] at h ⊢
                    exact h
                by_cases ht0 : t.val = 0
                · simp only [ht0, ↓reduceDIte]
                  have ht_eq : t = ⟨0, by omega⟩ := Fin.ext ht0
                  rw [ht_eq, hw0]
                · by_cases ht1 : t.val = 1
                  · simp only [ht1, show (1 : ℕ) ≠ 0 by decide, ↓reduceDIte]
                    have ht_eq : t = ⟨1, by omega⟩ := Fin.ext ht1
                    rw [ht_eq, hw1]
                  · simp only [ht0, ht1, ↓reduceDIte]
                    exact congrArg w.1 (Fin.ext (by dsimp only; omega))
              right_inv := fun w => by
                apply Subtype.ext; funext t
                simp only [show t.val + 2 ≠ 0 by omega, show t.val + 2 ≠ 1 by omega, ↓reduceDIte]
                exact congrArg w.1 (Fin.ext (by dsimp only; omega)) }
          rw [Nat.card_congr e, hcard']
          have hexp : m' + 2 - (2 + pathSum m' (shiftSeq 2 c)) = m' - pathSum m' (shiftSeq 2 c) := by omega
          rw [hexp]

theorem takeWhile_range_eq_of_zero {k : ℕ} (f : ℕ → Bool) (m : ℕ) (hm_pos : 0 < m) (hm : m ≤ k)
    (hz : f (m - 1) = false) :
    ((List.range k).takeWhile f).length = ((List.range m).takeWhile f).length := by
  have htake : List.range k = List.range m ++ (List.range (k - m)).map (m + ·) := by
    have := @List.range_add m (k - m)
    rw [Nat.add_sub_cancel' hm] at this
    exact this
  have hnot_all : ¬ ∀ x ∈ List.range m, f x = true := by
    intro hall
    have ht := hall (m - 1) (List.mem_range.mpr (by omega))
    rw [hz] at ht
    cases ht
  rw [htake]
  have htw : ∀ (l1 l2 : List ℕ), (¬ ∀ x ∈ l1, f x = true) →
      (l1 ++ l2).takeWhile f = l1.takeWhile f := by
    intro l1 l2
    induction l1 with
    | nil => intro h; exact absurd (fun _ hx => by simp at hx) h
    | cons a tl ih =>
      intro h
      cases hfa : f a
      · simp [hfa]
      · simp only [List.cons_append, List.takeWhile_cons, hfa, ↓reduceIte]
        congr 1
        apply ih
        intro hall_tl
        apply h
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hxt
        · exact hfa
        · exact hall_tl x hxt
  rw [htw _ _ hnot_all]

theorem card_ker_edge_proper (k : ℕ) [NeZero k] (b : ZMod k → ZMod 2)
    (i0 : ZMod k) (hi0 : b i0 = 0) :
    let run := fun (i : ZMod k) =>
      ((List.range k).takeWhile (fun offset => decide (b (i + (offset : ZMod k)) = 1))).length
    let r := ∑ i : ZMod k, if b i = 1 ∧ b (i - 1) = 0 then 2 * ((run i + 1) / 2) else 0
    r ≤ k ∧ Nat.card (LinearMap.ker (edgeLM k b)) = 2 ^ (k - r) := by
  dsimp only
  let run := fun (i : ZMod k) =>
    ((List.range k).takeWhile (fun offset => decide (b (i + (offset : ZMod k)) = 1))).length
  let r := ∑ i : ZMod k, if b i = 1 ∧ b (i - 1) = 0 then 2 * ((run i + 1) / 2) else 0
  let c : ℕ → ZMod 2 := fun t => b (i0 + 1 + (t : ZMod k))
  have hk_pos : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  have hlast : k = 0 ∨ c (k - 1) = 0 := by
    right
    dsimp only [c]
    have h1 : (1 : ZMod k) + ((k - 1 : ℕ) : ZMod k) = 0 := by
      have : 1 + (k - 1) = k := by omega
      have hcast : ((1 + (k - 1) : ℕ) : ZMod k) = 0 := by rw [this, ZMod.natCast_self]
      simpa using hcast
    rw [add_assoc, h1, add_zero, hi0]
  have hr_eq : r = pathSum k c := by
    let idxEquiv : Fin k ≃ ZMod k :=
      (zmodEquivFin k).symm.trans (Equiv.addLeft (i0 + 1))
    have hsum1 : r = ∑ t : Fin k,
        if b (i0 + 1 + (t.val : ZMod k)) = 1 ∧ b (i0 + 1 + (t.val : ZMod k) - 1) = 0
        then 2 * ((run (i0 + 1 + (t.val : ZMod k)) + 1) / 2) else 0 := by
      symm
      exact Fintype.sum_equiv idxEquiv _ _ (fun t => by rfl)
    rw [hsum1, Fin.sum_univ_eq_sum_range (fun t =>
      if b (i0 + 1 + (t : ZMod k)) = 1 ∧ b (i0 + 1 + (t : ZMod k) - 1) = 0
      then 2 * ((run (i0 + 1 + (t : ZMod k)) + 1) / 2) else 0) k]
    unfold pathSum
    refine Finset.sum_congr rfl (fun t ht => ?_)
    have htk : t < k := Finset.mem_range.mp ht
    have hprev : (b (i0 + 1 + (t : ZMod k) - 1) = 0) ↔ (t = 0 ∨ c (t - 1) = 0) := by
      cases t with
      | zero =>
        simp [hi0]
      | succ u =>
        have h1 : i0 + 1 + ((u + 1 : ℕ) : ZMod k) - 1 = i0 + 1 + (u : ZMod k) := by
          push_cast; ring
        rw [h1]
        simp [c]
    have hrun_eq : run (i0 + 1 + (t : ZMod k)) = runLen (k - t) (shiftSeq t c) := by
      unfold run runLen shiftSeq
      have hcoer : (do let a ← List.range k; pure (a : ZMod k)) =
          (List.range k).map (Nat.cast : ℕ → ZMod k) := by
        have hfm : ∀ l : List ℕ, l.flatMap (fun a : ℕ => [(a : ZMod k)]) =
            l.map (Nat.cast : ℕ → ZMod k) := by
          intro l
          induction l with
          | nil => rfl
          | cons a tl ih => simp [List.flatMap_cons, ih]
        simpa [Bind.bind, Pure.pure] using hfm (List.range k)
      rw [hcoer, List.takeWhile_map, List.length_map]
      have hfn : ((fun offset : ZMod k => decide (b (i0 + 1 + (t : ZMod k) + offset) = 1)) ∘
          (Nat.cast : ℕ → ZMod k)) =
          (fun off : ℕ => decide (c (off + t) = 1)) := by
        funext off
        dsimp only [Function.comp_apply, c]
        congr 2
        push_cast; ring
      rw [hfn]
      apply takeWhile_range_eq_of_zero _ (k - t) (by omega) (by omega)
      have hidx : k - t - 1 + t = k - 1 := by omega
      rw [hidx]
      rcases hlast with h | hc_last
      · omega
      · rw [hc_last]; decide
    have hcond_eq : (b (i0 + 1 + (t : ZMod k)) = 1 ∧ b (i0 + 1 + (t : ZMod k) - 1) = 0) ↔
        (c t = 1 ∧ (t = 0 ∨ c (t - 1) = 0)) := by
      dsimp only [c]
      rw [hprev]
    by_cases hcond : c t = 1 ∧ (t = 0 ∨ c (t - 1) = 0)
    · simp [hcond_eq.mpr hcond, hcond, hrun_eq]
    · simp [show ¬(b (i0 + 1 + (t : ZMod k)) = 1 ∧ b (i0 + 1 + (t : ZMod k) - 1) = 0) from
        fun h => hcond (hcond_eq.mp h), hcond]
  obtain ⟨hle, hcard⟩ := path_ker_card_and_le k c hlast
  change r ≤ k ∧ Nat.card (LinearMap.ker (edgeLM k b)) = 2 ^ (k - r)
  rw [hr_eq]
  refine ⟨hle, ?_⟩
  let vEquiv : Fin k ≃ ZMod k :=
    (zmodEquivFin k).symm.trans (Equiv.addLeft (i0 + 2))
  have hv_apply : ∀ t : Fin k, vEquiv t = i0 + 2 + (t.val : ZMod k) := fun _ => rfl
  let kerEquiv : LinearMap.ker (edgeLM k b) ≃ {w : Fin k → ZMod 2 // IsPathKer k c w} :=
    { toFun := fun w =>
        ⟨fun t => w.1 (vEquiv t), by
          intro t
          have hw := congrFun (LinearMap.mem_ker.mp w.2) (vEquiv t)
          dsimp only [edgeLM, LinearMap.coe_mk, AddHom.coe_mk, edgeFn, Pi.zero_apply] at hw
          rw [hv_apply] at hw
          have hleft : b (i0 + 2 + (t.val : ZMod k) - 2) * w.1 (i0 + 2 + (t.val : ZMod k) - 1) =
              if h : 0 < t.val then c (t.val - 1) * w.1 (vEquiv ⟨t.val - 1, by omega⟩) else 0 := by
            by_cases ht0 : 0 < t.val
            · simp only [ht0, ↓reduceDIte, hv_apply, c]
              have h1 : i0 + 2 + (t.val : ZMod k) - 2 = i0 + 1 + ((t.val - 1 : ℕ) : ZMod k) := by
                have ht1 : t.val = (t.val - 1) + 1 := by omega
                conv_lhs => rw [ht1]
                push_cast; ring
              have h2 : i0 + 2 + (t.val : ZMod k) - 1 = i0 + 2 + ((t.val - 1 : ℕ) : ZMod k) := by
                have ht1 : t.val = (t.val - 1) + 1 := by omega
                conv_lhs => rw [ht1]
                push_cast; ring
              rw [h1, h2]
            · have ht_eq : t.val = 0 := by omega
              simp only [ht_eq, Nat.lt_irrefl, ↓reduceDIte, Nat.cast_zero, add_zero, add_sub_cancel_right, hi0, zero_mul]
          have hright : b (i0 + 2 + (t.val : ZMod k) - 1) * w.1 (i0 + 2 + (t.val : ZMod k) + 1) =
              if h : t.val + 1 < k then c t.val * w.1 (vEquiv ⟨t.val + 1, h⟩) else 0 := by
            by_cases htk : t.val + 1 < k
            · simp only [htk, ↓reduceDIte, hv_apply, c]
              have h1 : i0 + 2 + (t.val : ZMod k) - 1 = i0 + 1 + (t.val : ZMod k) := by ring
              have h2 : i0 + 2 + (t.val : ZMod k) + 1 = i0 + 2 + ((t.val + 1 : ℕ) : ZMod k) := by
                push_cast; ring
              rw [h1, h2]
            · have ht_eq : t.val = k - 1 := by omega
              simp only [htk, ↓reduceDIte]
              have h1 : i0 + 2 + (t.val : ZMod k) - 1 = i0 + 1 + ((k - 1 : ℕ) : ZMod k) := by
                rw [ht_eq]; ring
              rw [h1]
              rcases hlast with h | hc_last
              · omega
              · dsimp only [c] at hc_last
                rw [hc_last, zero_mul]
          rw [← hleft, ← hright]
          exact hw⟩
      invFun := fun w =>
        ⟨fun i => w.1 (vEquiv.symm i), by
          rw [LinearMap.mem_ker]
          funext i
          dsimp only [edgeLM, LinearMap.coe_mk, AddHom.coe_mk, edgeFn, Pi.zero_apply]
          let t := vEquiv.symm i
          have hi : i = vEquiv t := (vEquiv.apply_symm_apply i).symm
          rw [hi, hv_apply]
          have hwt := w.2 t
          have hleft : b (i0 + 2 + (t.val : ZMod k) - 2) * w.1 (vEquiv.symm (i0 + 2 + (t.val : ZMod k) - 1)) =
              if h : 0 < t.val then c (t.val - 1) * w.1 ⟨t.val - 1, by omega⟩ else 0 := by
            by_cases ht0 : 0 < t.val
            · simp only [ht0, ↓reduceDIte, c]
              have h1 : i0 + 2 + (t.val : ZMod k) - 2 = i0 + 1 + ((t.val - 1 : ℕ) : ZMod k) := by
                have ht1 : t.val = (t.val - 1) + 1 := by omega
                conv_lhs => rw [ht1]
                push_cast; ring
              have h2 : i0 + 2 + (t.val : ZMod k) - 1 = vEquiv ⟨t.val - 1, by omega⟩ := by
                rw [hv_apply]
                have ht1 : t.val = (t.val - 1) + 1 := by omega
                conv_lhs => rw [ht1]
                push_cast; ring
              rw [h1, h2, Equiv.symm_apply_apply]
            · have ht_eq : t.val = 0 := by omega
              simp only [ht_eq, Nat.lt_irrefl, ↓reduceDIte, Nat.cast_zero, add_zero, add_sub_cancel_right, hi0, zero_mul]
          have hright : b (i0 + 2 + (t.val : ZMod k) - 1) * w.1 (vEquiv.symm (i0 + 2 + (t.val : ZMod k) + 1)) =
              if h : t.val + 1 < k then c t.val * w.1 ⟨t.val + 1, h⟩ else 0 := by
            by_cases htk : t.val + 1 < k
            · simp only [htk, ↓reduceDIte, c]
              have h1 : i0 + 2 + (t.val : ZMod k) - 1 = i0 + 1 + (t.val : ZMod k) := by ring
              have h2 : i0 + 2 + (t.val : ZMod k) + 1 = vEquiv ⟨t.val + 1, htk⟩ := by
                rw [hv_apply]; push_cast; ring
              rw [h1, h2, Equiv.symm_apply_apply]
            · have ht_eq : t.val = k - 1 := by omega
              simp only [htk, ↓reduceDIte]
              have h1 : i0 + 2 + (t.val : ZMod k) - 1 = i0 + 1 + ((k - 1 : ℕ) : ZMod k) := by
                rw [ht_eq]; ring
              rw [h1]
              rcases hlast with h | hc_last
              · omega
              · dsimp only [c] at hc_last
                rw [hc_last, zero_mul]
          rw [hleft, hright]
          exact hwt⟩
      left_inv := fun w => by
        apply Subtype.ext; funext i
        simp
      right_inv := fun w => by
        apply Subtype.ext; funext t
        simp }
  rw [Nat.card_congr kerEquiv, hcard]

theorem finrank_range_edge (k : ℕ) [NeZero k] (b : ZMod k → ZMod 2) :
    let run := fun (i : ZMod k) =>
      ((List.range k).takeWhile (fun offset => decide (b (i + (offset : ZMod k)) = 1))).length
    let r := if ∀ i : ZMod k, b i = 1 then k - Nat.gcd k 2 else
      ∑ i : ZMod k, if b i = 1 ∧ b (i - 1) = 0 then 2 * ((run i + 1) / 2) else 0
    Module.finrank (ZMod 2) (LinearMap.range (edgeLM k b)) = r := by
  classical
  dsimp only
  have hfinV : Module.finrank (ZMod 2) (ZMod k → ZMod 2) = k := by
    rw [Module.finrank_pi, ZMod.card]
  have hrn := LinearMap.finrank_range_add_finrank_ker (edgeLM k b)
  rw [hfinV] at hrn
  have hpow : Nat.card (LinearMap.ker (edgeLM k b)) =
      2 ^ Module.finrank (ZMod 2) (LinearMap.ker (edgeLM k b)) := by
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2)]
    simp
  split_ifs with hall
  · have hb_eq : b = fun _ => 1 := funext hall
    rw [hb_eq] at hpow hrn ⊢
    have hcard := card_ker_edge_all_ones k
    rw [hpow] at hcard
    have hker : Module.finrank (ZMod 2) (LinearMap.ker (edgeLM k (fun _ => 1))) = Nat.gcd k 2 :=
      Nat.pow_right_injective (by omega : 1 < 2) hcard
    omega
  · have hex : ∃ i0 : ZMod k, b i0 = 0 := by
      push Not at hall
      obtain ⟨i0, hi0⟩ := hall
      rcases z2_eq_zero_or_one (b i0) with h0 | h1
      · exact ⟨i0, h0⟩
      · exact absurd h1 hi0
    obtain ⟨i0, hi0⟩ := hex
    obtain ⟨hle, hcard⟩ := card_ker_edge_proper k b i0 hi0
    dsimp only at hle hcard
    rw [hpow] at hcard
    have hker : Module.finrank (ZMod 2) (LinearMap.ker (edgeLM k b)) =
        k - ∑ i : ZMod k,
          if b i = 1 ∧ b (i - 1) = 0
          then 2 * ((((List.range k).takeWhile (fun offset => decide (b (i + (offset : ZMod k)) = 1))).length + 1) / 2)
          else 0 :=
      Nat.pow_right_injective (by omega : 1 < 2) hcard
    omega

theorem finrank_ker_comp_le {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (f g : V →ₗ[K] V) :
    Module.finrank K (LinearMap.ker (f.comp g)) ≤
      Module.finrank K (LinearMap.ker f) + Module.finrank K (LinearMap.ker g) := by
  let S := LinearMap.ker (f.comp g)
  let gS : S →ₗ[K] V := g.comp S.subtype
  have hrn := LinearMap.finrank_range_add_finrank_ker gS
  change Module.finrank K (LinearMap.range gS) + Module.finrank K (LinearMap.ker gS) =
    Module.finrank K (LinearMap.ker (f.comp g)) at hrn
  have hrg : LinearMap.range gS ≤ LinearMap.ker f := by
    rintro y ⟨⟨x, hx⟩, rfl⟩
    exact LinearMap.mem_ker.mp hx
  have hker_le : Module.finrank K (LinearMap.ker gS) ≤ Module.finrank K (LinearMap.ker g) := by
    let φ : LinearMap.ker gS →ₗ[K] LinearMap.ker g :=
      { toFun := fun x => ⟨x.1.1, LinearMap.mem_ker.mp (LinearMap.mem_ker.mp x.2)⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hφ_inj : Function.Injective φ := fun a b h =>
      Subtype.ext (Subtype.ext (congrArg (fun z : LinearMap.ker g => z.1) h))
    exact LinearMap.finrank_le_finrank_of_injective hφ_inj
  have hrg_le : Module.finrank K (LinearMap.range gS) ≤ Module.finrank K (LinearMap.ker f) :=
    Submodule.finrank_mono hrg
  omega

theorem main : ∀ (k : ℕ) [NeZero k] (d : ℕ),
    let I := ZMod k
    let B := ZMod 2
    let V := I → B
    let sign := fun (t : B) => if t = 0 then (1 : ℤ) else -1
    let mix := fun (s : ℕ) (x : V) (i : I) => x (i - (s : I)) + x i + x (i + (s : I))
    let nl := fun (y : V) (j : I) => y j + (1 + y (j + 1)) * y (j + 2)
    let coeff := fun (s : ℕ) (a b : V) =>
      ∑ x : V, sign (dotProduct a x + dotProduct b (nl (mix s x)))
    let support := fun (s : ℕ) (b : V) => Finset.univ.filter (fun mask : V => coeff s mask b ≠ 0)
    let g := Nat.gcd k d
    let h := if 3 ∣ k / g then 2 * g else 0
    ∀ b : V,
      let edge := fun (w : V) (i : I) => b (i - 2) * w (i - 1) + b (i - 1) * w (i + 1)
      let run := fun (i : I) =>
        ((List.range k).takeWhile (fun offset => decide (b (i + (offset : I)) = 1))).length
      let r := if ∀ i : I, b i = 1 then k - Nat.gcd k 2 else
        ∑ i : I, if b i = 1 ∧ b (i - 1) = 0 then 2 * ((run i + 1) / 2) else 0
      (∃ base : V, ∀ a : V, a ∈ support d b ↔
        ∃ u : V, a = base + mix d (edge (mix d u))) ∧
      (support 0 b).card = 2 ^ r ∧
      (support d b).card ≤ 2 ^ r ∧ 2 ^ r ≤ 2 ^ (2 * h) * (support d b).card := by
  intro k _ d I B V sign mix nl coeff support g h b edge run r
  obtain ⟨haff_d, hcard_d⟩ := support_affine_and_card k d b
  obtain ⟨_, hcard_0⟩ := support_affine_and_card k 0 b
  dsimp only at haff_d hcard_d hcard_0
  have hT0 : polarLM k 0 b = edgeLM k b := by
    ext u i
    simp [polarLM, mixLM_zero]
  have hrank_E : Module.finrank (ZMod 2) (LinearMap.range (edgeLM k b)) = r :=
    finrank_range_edge k b
  have hcard_0' : (support 0 b).card = 2 ^ r := by
    change (Finset.univ.filter (fun mask : V =>
      (∑ x : V, sign (dotProduct mask x + dotProduct b (nlFn k (mixFn k 0 x)))) ≠ 0)).card = 2 ^ r
    rw [hcard_0, hT0, hrank_E]
  have hrank_le : Module.finrank (ZMod 2) (LinearMap.range (polarLM k d b)) ≤ r := by
    rw [← hrank_E]
    have h1 : Module.finrank (ZMod 2) (LinearMap.range (polarLM k d b)) ≤
        Module.finrank (ZMod 2) (LinearMap.range ((edgeLM k b).comp (mixLM k d))) := by
      have hmap : LinearMap.range (polarLM k d b) =
          Submodule.map (mixLM k d) (LinearMap.range ((edgeLM k b).comp (mixLM k d))) := by
        rw [polarLM, LinearMap.range_comp]
      rw [hmap]
      exact Submodule.finrank_map_le _ _
    have h2 : Module.finrank (ZMod 2) (LinearMap.range ((edgeLM k b).comp (mixLM k d))) ≤
        Module.finrank (ZMod 2) (LinearMap.range (edgeLM k b)) :=
      Submodule.finrank_mono (LinearMap.range_comp_le_range _ _)
    exact h1.trans h2
  have hcard_d_le : (support d b).card ≤ 2 ^ r := by
    change (Finset.univ.filter (fun mask : V =>
      (∑ x : V, sign (dotProduct mask x + dotProduct b (nlFn k (mixFn k d x)))) ≠ 0)).card ≤ 2 ^ r
    rw [hcard_d]
    exact Nat.pow_le_pow_right (by omega) hrank_le
  have hker_mix : Module.finrank (ZMod 2) (LinearMap.ker (mixLM k d)) ≤ h :=
    finrank_ker_mix_le k d
  have hker_T : Module.finrank (ZMod 2) (LinearMap.ker (polarLM k d b)) ≤
      Module.finrank (ZMod 2) (LinearMap.ker (edgeLM k b)) + 2 * h := by
    have h1 := finrank_ker_comp_le (mixLM k d) ((edgeLM k b).comp (mixLM k d))
    have h2 := finrank_ker_comp_le (edgeLM k b) (mixLM k d)
    have h3 : (mixLM k d).comp ((edgeLM k b).comp (mixLM k d)) = polarLM k d b := rfl
    rw [h3] at h1
    omega
  have hrn_E := LinearMap.finrank_range_add_finrank_ker (edgeLM k b)
  have hrn_T := LinearMap.finrank_range_add_finrank_ker (polarLM k d b)
  have hrank_lb : r ≤ 2 * h + Module.finrank (ZMod 2) (LinearMap.range (polarLM k d b)) := by
    omega
  have hcard_d_lb : 2 ^ r ≤ 2 ^ (2 * h) * (support d b).card := by
    change 2 ^ r ≤ 2 ^ (2 * h) * (Finset.univ.filter (fun mask : V =>
      (∑ x : V, sign (dotProduct mask x + dotProduct b (nlFn k (mixFn k d x)))) ≠ 0)).card
    rw [hcard_d, ← pow_add]
    exact Nat.pow_le_pow_right (by omega) hrank_lb
  exact ⟨haff_d, hcard_0', hcard_d_le, hcard_d_lb⟩

end PEqualNP.Outside.L_meta_25694_aux

theorem PEqualNP.Outside.L_meta_25694 : (∀ (k : ℕ) [NeZero k] (d : ℕ),
  let I := ZMod k
  let B := ZMod 2
  let V := I → B
  let sign := fun (t : B) => if t = 0 then (1 : ℤ) else -1
  let mix := fun (s : ℕ) (x : V) (i : I) => x (i-(s : I)) + x i + x (i+(s : I))
  let nl := fun (y : V) (j : I) => y j + (1+y (j+1))*y (j+2)
  let coeff := fun (s : ℕ) (a b : V) =>
    ∑ x : V, sign (dotProduct a x + dotProduct b (nl (mix s x)))
  let support := fun (s : ℕ) (b : V) => Finset.univ.filter (fun mask : V => coeff s mask b ≠ 0)
  let g := Nat.gcd k d
  let h := if 3 ∣ k/g then 2*g else 0
  ∀ b : V,
    let edge := fun (w : V) (i : I) => b (i-2)*w (i-1) + b (i-1)*w (i+1)
    let run := fun (i : I) =>
      ((List.range k).takeWhile (fun offset => decide (b (i+(offset : I)) = 1))).length
    let r := if ∀ i : I, b i = 1 then k - Nat.gcd k 2 else
      ∑ i : I, if b i = 1 ∧ b (i-1) = 0 then 2*((run i + 1)/2) else 0
    (∃ base : V, ∀ a : V, a ∈ support d b ↔
      ∃ u : V, a = base + mix d (edge (mix d u))) ∧
    (support 0 b).card = 2^r ∧
    (support d b).card ≤ 2^r ∧ 2^r ≤ 2^(2*h) * (support d b).card) :=
  PEqualNP.Outside.L_meta_25694_aux.main
