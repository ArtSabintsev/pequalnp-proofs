import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_548_aux

private theorem foldl_linear_add {K : Type} [Field K] {q d : ℕ}
    (A : Fin q → (Fin d → K) →ₗ[K] (Fin d → K)) :
    ∀ (v : List (Fin q)) (x y : Fin d → K),
      v.foldl (fun z a => A a z) (x + y) =
        v.foldl (fun z a => A a z) x + v.foldl (fun z a => A a z) y
  | [], _, _ => rfl
  | a :: v, x, y => by
    simp only [List.foldl_cons, map_add]
    exact foldl_linear_add A v (A a x) (A a y)

private theorem foldl_linear_smul {K : Type} [Field K] {q d : ℕ}
    (A : Fin q → (Fin d → K) →ₗ[K] (Fin d → K)) :
    ∀ (v : List (Fin q)) (c : K) (x : Fin d → K),
      v.foldl (fun z a => A a z) (c • x) = c • v.foldl (fun z a => A a z) x
  | [], _, _ => rfl
  | a :: v, c, x => by
    simp only [List.foldl_cons, map_smul]
    exact foldl_linear_smul A v c (A a x)

private theorem main_core (K : Type) [Field K] (q : ℕ) (f : List (Fin q) → K) :
    let R := Submodule.span K (Set.range (fun u : List (Fin q) => fun v : List (Fin q) => f (u ++ v)))
    ∀ d : ℕ, (Module.Finite K R ∧ Module.finrank K R ≤ d) ↔
      ∃ (s : Fin d → K) (A : Fin q → (Fin d → K) →ₗ[K] (Fin d → K))
        (g : (Fin d → K) →ₗ[K] K),
        ∀ w : List (Fin q), g (w.foldl (fun x a => A a x) s) = f w := by
  intro R d
  constructor
  · rintro ⟨hfinR, hrank⟩
    haveI : Module.Finite K R := hfinR
    set r := Module.finrank K R
    let b : Module.Basis (Fin r) K R := Module.finBasis K R
    let ι : R →ₗ[K] (Fin d → K) :=
      { toFun := fun x i => if h : i.val < r then b.repr x ⟨i.val, h⟩ else 0
        map_add' := fun x y => by
          funext i
          by_cases h : i.val < r <;> simp [h]
        map_smul' := fun c x => by
          funext i
          by_cases h : i.val < r <;> simp [h] }
    let π : (Fin d → K) →ₗ[K] R :=
      { toFun := fun v => ∑ j : Fin r, v ⟨j.val, lt_of_lt_of_le j.isLt hrank⟩ • b j
        map_add' := fun v w => by
          simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
        map_smul' := fun c v => by
          simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply] }
    have hπι : ∀ x : R, π (ι x) = x := by
      intro x
      change ∑ j : Fin r, (if h : j.val < r then b.repr x ⟨j.val, h⟩ else 0) • b j = x
      have hterm : ∑ j : Fin r, (if h : j.val < r then b.repr x ⟨j.val, h⟩ else 0) • b j =
          ∑ j : Fin r, (b.repr x j) • b j := by
        apply Finset.sum_congr rfl
        intro j _
        rw [dif_pos j.isLt]
      rw [hterm]
      exact b.sum_repr x
    have hshift_mem : ∀ (a : Fin q) (h : List (Fin q) → K), h ∈ R →
        (fun v : List (Fin q) => h (a :: v)) ∈ R := by
      intro a h hh
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hh
      · rintro _ ⟨u, rfl⟩
        apply Submodule.subset_span
        refine ⟨u ++ [a], ?_⟩
        funext v
        simp [List.append_assoc]
      · exact Submodule.zero_mem R
      · intro x y _ _ hx hy
        exact Submodule.add_mem R hx hy
      · intro c x _ hx
        exact Submodule.smul_mem R c hx
    let shiftR : Fin q → R →ₗ[K] R := fun a =>
      { toFun := fun x => ⟨fun v => x.1 (a :: v), hshift_mem a x.1 x.2⟩
        map_add' := fun x y => Subtype.ext rfl
        map_smul' := fun c x => Subtype.ext rfl }
    let evalNil : R →ₗ[K] K :=
      { toFun := fun x => x.1 []
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    let res : List (Fin q) → R := fun u =>
      ⟨fun v => f (u ++ v), Submodule.subset_span ⟨u, rfl⟩⟩
    let s : Fin d → K := ι (res [])
    let A : Fin q → (Fin d → K) →ₗ[K] (Fin d → K) := fun a => ι.comp ((shiftR a).comp π)
    let g : (Fin d → K) →ₗ[K] K := evalNil.comp π
    refine ⟨s, A, g, ?_⟩
    have hfold : ∀ (w u : List (Fin q)),
        w.foldl (fun x a => A a x) (ι (res u)) = ι (res (u ++ w)) := by
      intro w
      induction w with
      | nil =>
        intro u
        simp [List.append_nil]
      | cons a w ih =>
        intro u
        simp only [List.foldl_cons]
        have hstep : A a (ι (res u)) = ι (res (u ++ [a])) := by
          dsimp only [A]
          rw [LinearMap.comp_apply, LinearMap.comp_apply, hπι]
          congr 1
          apply Subtype.ext
          funext v
          simp [shiftR, res, List.append_assoc]
        rw [hstep, ih (u ++ [a])]
        congr 1
        apply Subtype.ext
        funext v
        simp [res, List.append_assoc]
    intro w
    have hw := hfold w []
    simp only [List.nil_append] at hw
    change g (w.foldl (fun x a => A a x) (ι (res []))) = f w
    rw [hw]
    dsimp only [g]
    rw [LinearMap.comp_apply, hπι]
    simp [evalNil, res]
  · rintro ⟨s, A, g, h⟩
    let Φ : (Fin d → K) →ₗ[K] (List (Fin q) → K) :=
      { toFun := fun x v => g (v.foldl (fun y a => A a y) x)
        map_add' := fun x y => by
          funext v
          simp only [Pi.add_apply, foldl_linear_add, map_add]
        map_smul' := fun c x => by
          funext v
          simp only [Pi.smul_apply, foldl_linear_smul, map_smul, RingHom.id_apply] }
    have hle : R ≤ LinearMap.range Φ := by
      rw [Submodule.span_le]
      rintro _ ⟨u, rfl⟩
      refine ⟨u.foldl (fun y a => A a y) s, ?_⟩
      funext v
      change g (v.foldl (fun y a => A a y) (u.foldl (fun y a => A a y) s)) = f (u ++ v)
      rw [← List.foldl_append, h (u ++ v)]
    have hfin_range : Module.Finite K (LinearMap.range Φ) := Module.Finite.range Φ
    have hinj : Function.Injective (Submodule.inclusion hle) := Submodule.inclusion_injective hle
    have hfinR : Module.Finite K R := Module.Finite.of_injective (Submodule.inclusion hle) hinj
    have hle1 : Module.finrank K R ≤ Module.finrank K (LinearMap.range Φ) :=
      LinearMap.finrank_le_finrank_of_injective hinj
    have hle2 : Module.finrank K (LinearMap.range Φ) ≤ Module.finrank K (Fin d → K) :=
      LinearMap.finrank_range_le Φ
    rw [Module.finrank_fin_fun] at hle2
    exact ⟨hfinR, le_trans hle1 hle2⟩

end PEqualNP.Outside.L_lib_548_aux

theorem PEqualNP.Outside.L_lib_548 : (∀ (K : Type) [Field K] (q : ℕ) (f : List (Fin q) → K),
  let R := Submodule.span K (Set.range (fun u : List (Fin q) => fun v : List (Fin q) => f (u ++ v)))
  ∀ d : ℕ, (Module.Finite K R ∧ Module.finrank K R ≤ d) ↔
    ∃ (s : Fin d → K) (A : Fin q → (Fin d → K) →ₗ[K] (Fin d → K))
      (g : (Fin d → K) →ₗ[K] K),
      ∀ w : List (Fin q), g (w.foldl (fun x a => A a x) s) = f w) := by
  intro K _ q f R d
  exact PEqualNP.Outside.L_lib_548_aux.main_core K q f d
