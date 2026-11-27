import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_507_aux

open PEqualNP.CircuitLowerBounds

private def toZ2 (b : Bool) : ZMod 2 :=
  if b then 1 else 0

private theorem zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  fin_cases a <;> decide

private theorem zmod2_vec_add_self {n : ℕ} (x : Fin n → ZMod 2) : x + x = 0 := by
  funext i
  exact zmod2_add_self (x i)

private theorem zmod2_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

private theorem toZ2_decide_eq_one (a : ZMod 2) : toZ2 (decide (a = 1)) = a := by
  rcases zmod2_eq_zero_or_one a with rfl | rfl <;> decide

private theorem toZ2_not (b : Bool) : toZ2 (!b) = toZ2 b + 1 := by
  cases b <;> decide

private theorem toZ2_and (b₁ b₂ : Bool) : toZ2 (b₁ && b₂) = toZ2 b₁ * toZ2 b₂ := by
  cases b₁ <;> cases b₂ <;> decide

private theorem toZ2_mod2_nil : toZ2 (GateOp.eval (GateOp.mod 2) []) = 1 := by
  decide

private theorem toZ2_mod2_one (b₁ : Bool) :
    toZ2 (GateOp.eval (GateOp.mod 2) [b₁]) = toZ2 b₁ + 1 := by
  cases b₁ <;> decide

private theorem toZ2_mod2_two (b₁ b₂ : Bool) :
    toZ2 (GateOp.eval (GateOp.mod 2) [b₁, b₂]) = toZ2 b₁ + toZ2 b₂ + 1 := by
  cases b₁ <;> cases b₂ <;> decide

private def wiresOf (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

private theorem wiresOf_length (gs : List Gate) (x : List Bool) :
    (wiresOf gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [wiresOf]
  | cons g gs ih =>
    simp only [wiresOf, List.foldl_cons] at ih ⊢
    rw [ih, List.length_append, List.length_singleton, List.length_cons]
    omega

private theorem wiresOf_append_singleton (gs : List Gate) (g : Gate) (x : List Bool) :
    wiresOf (gs ++ [g]) x =
      wiresOf gs x ++ [g.op.eval (g.inputs.map fun i => (wiresOf gs x).getD i false)] := by
  simp [wiresOf, List.foldl_append]

private theorem getD_append_singleton (w : List Bool) (v : Bool) (i : ℕ) :
    (w ++ [v]).getD i false = if i = w.length then v else w.getD i false := by
  by_cases hi : i = w.length
  · subst hi
    simp [List.getD]
  · by_cases hlt : i < w.length
    · have hlt2 : i < (w ++ [v]).length := by simp; omega
      rw [if_neg hi, List.getD_eq_getElem _ _ hlt2, List.getD_eq_getElem _ _ hlt,
        List.getElem_append_left hlt]
    · have hge : (w ++ [v]).length ≤ i := by simp; omega
      have hge1 : w.length ≤ i := by omega
      rw [if_neg hi, List.getD_eq_default _ _ hge, List.getD_eq_default _ _ hge1]

private noncomputable def andCount (gs : List Gate) : ℕ :=
  gs.countP (fun g => @decide (g.op = .and) (Classical.propDecidable _))

private theorem andCount_append_and (gs : List Gate) (g : Gate) (h : g.op = .and) :
    andCount (gs ++ [g]) = andCount gs + 1 := by
  unfold andCount
  rw [List.countP_append, List.countP_cons, List.countP_nil]
  simp [h]

private theorem andCount_append_not_and (gs : List Gate) (g : Gate) (h : g.op ≠ .and) :
    andCount (gs ++ [g]) = andCount gs := by
  unfold andCount
  rw [List.countP_append, List.countP_cons, List.countP_nil]
  simp [h]

private def inputBits {n : ℕ} (x : Fin n → ZMod 2) : List Bool :=
  List.ofFn (fun i : Fin n => decide (x i = 1))

private theorem getD_inputBits {n : ℕ} (x : Fin n → ZMod 2) (i : ℕ) :
    toZ2 ((inputBits x).getD i false) =
      dotProduct (if h : i < n then Pi.single ⟨i, h⟩ (1 : ZMod 2) else 0) x := by
  by_cases h : i < n
  · rw [dif_pos h]
    have hlt : i < (inputBits x).length := by simp [inputBits, h]
    have hget : (inputBits x).getD i false = decide (x ⟨i, h⟩ = 1) := by
      rw [List.getD_eq_getElem _ _ hlt]
      simp [inputBits]
    rw [hget, toZ2_decide_eq_one]
    simp only [dotProduct]
    rw [Finset.sum_eq_single ⟨i, h⟩]
    · simp
    · intro j _ hj
      simp [Pi.single_eq_of_ne hj]
    · intro hmem
      exact absurd (Finset.mem_univ _) hmem
  · rw [dif_neg h]
    have hge : (inputBits x).length ≤ i := by simp [inputBits]; omega
    rw [List.getD_eq_default _ _ hge, zero_dotProduct]
    rfl

private theorem affine_flat_exists (n : ℕ) (gs : List Gate)
    (hadm : ∀ g ∈ gs,
      (g.op = .and ∧ g.inputs.length = 2) ∨
      (g.op = .mod 2 ∧ g.inputs.length ≤ 2) ∨
      (g.op = .not ∧ g.inputs.length = 1)) :
    ∃ (x₀ : Fin n → ZMod 2) (U : Submodule (ZMod 2) (Fin n → ZMod 2))
      (a : ℕ → (Fin n → ZMod 2)) (b : ℕ → ZMod 2),
      n - andCount gs ≤ Module.finrank (ZMod 2) U ∧
      ∀ (i : ℕ) (u : Fin n → ZMod 2), u ∈ U →
        toZ2 ((wiresOf gs (inputBits (x₀ + u))).getD i false) =
          dotProduct (a i) (x₀ + u) + b i := by
  classical
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨0, ⊤, fun i => if h : i < n then Pi.single ⟨i, h⟩ 1 else 0, fun _ => 0, ?_, ?_⟩
    · have htop : Module.finrank (ZMod 2) (⊤ : Submodule (ZMod 2) (Fin n → ZMod 2)) = n := by
        rw [finrank_top, Module.finrank_fin_fun]
      rw [htop]
      omega
    · intro i u _
      simp only [wiresOf, List.foldl_nil, add_zero]
      exact getD_inputBits (0 + u) i
  | append_singleton gs g ih =>
    have hadm_gs : ∀ g' ∈ gs,
        (g'.op = .and ∧ g'.inputs.length = 2) ∨
        (g'.op = .mod 2 ∧ g'.inputs.length ≤ 2) ∨
        (g'.op = .not ∧ g'.inputs.length = 1) :=
      fun g' hg' => hadm g' (List.mem_append_left [g] hg')
    have hg := hadm g (List.mem_append_right gs (List.mem_singleton_self g))
    obtain ⟨x₀, U, a, b, hdim, hinv⟩ := ih hadm_gs
    set N := n + gs.length
    have hlen : ∀ x : Fin n → ZMod 2, (wiresOf gs (inputBits x)).length = N := fun x => by
      rw [wiresOf_length]; simp [inputBits, N]
    rcases hg with ⟨hop, hlen_in⟩ | ⟨hop, hlen_in⟩ | ⟨hop, hlen_in⟩
    · have hs' : andCount (gs ++ [g]) = andCount gs + 1 :=
        andCount_append_and gs g hop
      rcases hlist : g.inputs with _ | ⟨i₁, _ | ⟨i₂, _ | _⟩⟩
      · simp [hlist] at hlen_in
      · simp [hlist] at hlen_in
      · let φ : U →ₗ[ZMod 2] ZMod 2 :=
          { toFun := fun u => dotProduct (a i₁) u.1
            map_add' := fun u v => dotProduct_add (a i₁) u.1 v.1
            map_smul' := fun c u => dotProduct_smul c (a i₁) u.1 }
        let U' : Submodule (ZMod 2) (Fin n → ZMod 2) :=
          (LinearMap.ker φ).map U.subtype
        have hU'_le : U' ≤ U := by
          rintro x ⟨u, _, rfl⟩
          exact u.2
        have hU'_dot : ∀ u ∈ U', dotProduct (a i₁) u = 0 := by
          rintro x ⟨u, hu, rfl⟩
          exact hu
        have hdim' : n - andCount (gs ++ [g]) ≤ Module.finrank (ZMod 2) U' := by
          have hrn := LinearMap.finrank_range_add_finrank_ker φ
          have hrange : Module.finrank (ZMod 2) (LinearMap.range φ) ≤ 1 := by
            have h1 := Submodule.finrank_le (LinearMap.range φ)
            simpa using h1
          let emb : LinearMap.ker φ →ₗ[ZMod 2] U' :=
            { toFun := fun x => ⟨x.1.1, ⟨x.1, x.2, rfl⟩⟩
              map_add' := fun _ _ => Subtype.ext rfl
              map_smul' := fun _ _ => Subtype.ext rfl }
          have hemb_inj : Function.Injective emb := by
            intro x y h
            apply Subtype.ext
            apply Subtype.ext
            exact congrArg (fun t : U' => t.1) h
          have hker_le : Module.finrank (ZMod 2) (LinearMap.ker φ) ≤ Module.finrank (ZMod 2) U' :=
            LinearMap.finrank_le_finrank_of_injective hemb_inj
          omega
        set c := dotProduct (a i₁) x₀ + b i₁
        let a' : ℕ → (Fin n → ZMod 2) := fun i =>
          if i = N then (if c = 0 then 0 else a i₂) else a i
        let b' : ℕ → ZMod 2 := fun i =>
          if i = N then (if c = 0 then 0 else b i₂) else b i
        refine ⟨x₀, U', a', b', hdim', ?_⟩
        intro i u hu
        rw [wiresOf_append_singleton, getD_append_singleton, hlen (x₀ + u)]
        by_cases hi : i = N
        · rw [if_pos hi]
          dsimp only [a', b']
          rw [if_pos hi, if_pos hi, hop, hlist]
          simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil,
            id_eq, Bool.and_true]
          rw [toZ2_and, hinv i₁ u (hU'_le hu), hinv i₂ u (hU'_le hu), dotProduct_add,
            hU'_dot u hu, add_zero]
          rcases zmod2_eq_zero_or_one c with hc | hc
          · rw [if_pos hc, if_pos hc, show dotProduct (a i₁) x₀ + b i₁ = 0 from hc,
              zero_mul, zero_dotProduct, add_zero]
          · have hne : c ≠ 0 := by rw [hc]; decide
            rw [if_neg hne, if_neg hne, show dotProduct (a i₁) x₀ + b i₁ = 1 from hc, one_mul]
        · rw [if_neg hi]
          dsimp only [a', b']
          rw [if_neg hi, if_neg hi]
          exact hinv i u (hU'_le hu)
      · simp [hlist] at hlen_in
    · have hne : g.op ≠ .and := by rw [hop]; intro h; cases h
      have hs' : andCount (gs ++ [g]) = andCount gs :=
        andCount_append_not_and gs g hne
      rcases hlist : g.inputs with _ | ⟨i₁, _ | ⟨i₂, _ | _⟩⟩
      · refine ⟨x₀, U, fun i => if i = N then 0 else a i,
          fun i => if i = N then 1 else b i, by omega, ?_⟩
        intro i u hu
        rw [wiresOf_append_singleton, getD_append_singleton, hlen (x₀ + u)]
        by_cases hi : i = N
        · simp only [if_pos hi, zero_dotProduct, zero_add, hop, hlist]
          exact toZ2_mod2_nil
        · simp only [if_neg hi]
          exact hinv i u hu
      · refine ⟨x₀, U, fun i => if i = N then a i₁ else a i,
          fun i => if i = N then b i₁ + 1 else b i, by omega, ?_⟩
        intro i u hu
        rw [wiresOf_append_singleton, getD_append_singleton, hlen (x₀ + u)]
        by_cases hi : i = N
        · simp only [if_pos hi, hop, hlist, List.map_cons, List.map_nil]
          rw [toZ2_mod2_one, hinv i₁ u hu]
          ring
        · simp only [if_neg hi]
          exact hinv i u hu
      · refine ⟨x₀, U, fun i => if i = N then a i₁ + a i₂ else a i,
          fun i => if i = N then b i₁ + b i₂ + 1 else b i, by omega, ?_⟩
        intro i u hu
        rw [wiresOf_append_singleton, getD_append_singleton, hlen (x₀ + u)]
        by_cases hi : i = N
        · simp only [if_pos hi, hop, hlist, List.map_cons, List.map_nil]
          rw [toZ2_mod2_two, hinv i₁ u hu, hinv i₂ u hu, add_dotProduct]
          ring
        · simp only [if_neg hi]
          exact hinv i u hu
      · simp [hlist] at hlen_in
    · have hne : g.op ≠ .and := by rw [hop]; intro h; cases h
      have hs' : andCount (gs ++ [g]) = andCount gs :=
        andCount_append_not_and gs g hne
      rcases hlist : g.inputs with _ | ⟨i₁, _ | _⟩
      · simp [hlist] at hlen_in
      · refine ⟨x₀, U, fun i => if i = N then a i₁ else a i,
          fun i => if i = N then b i₁ + 1 else b i, by omega, ?_⟩
        intro i u hu
        rw [wiresOf_append_singleton, getD_append_singleton, hlen (x₀ + u)]
        by_cases hi : i = N
        · simp only [if_pos hi, hop, hlist, List.map_cons, List.map_nil, GateOp.eval,
            List.headD_cons]
          rw [toZ2_not, hinv i₁ u hu]
          ring
        · simp only [if_neg hi]
          exact hinv i u hu
      · simp [hlist] at hlen_in

private theorem exists_ortho_eval_one {n : ℕ} (U : Submodule (ZMod 2) (Fin n → ZMod 2))
    (v : Fin n → ZMod 2) (hv : v ∉ U) :
    ∃ w : Fin n → ZMod 2, (∀ u ∈ U, dotProduct w u = 0) ∧ dotProduct w v = 1 := by
  let q : (Fin n → ZMod 2) ⧸ U := U.mkQ v
  have hq : q ≠ 0 := by
    intro h0
    apply hv
    exact (Submodule.Quotient.mk_eq_zero U).1 h0
  let B := Module.finBasis (ZMod 2) ((Fin n → ZMod 2) ⧸ U)
  have hex : ∃ k, B.repr q k ≠ 0 := by
    by_contra hall
    push_neg at hall
    apply hq
    have hr : B.repr q = 0 := by
      ext k
      exact hall k
    exact B.repr.injective (by simp [hr])
  obtain ⟨k, hk⟩ := hex
  have hk1 : B.repr q k = 1 := by
    rcases zmod2_eq_zero_or_one (B.repr q k) with h0 | h1
    · exact absurd h0 hk
    · exact h1
  let ψ : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2 := (B.coord k).comp U.mkQ
  let w : Fin n → ZMod 2 := fun i => ψ (Pi.single i 1)
  have hψ : ∀ x : Fin n → ZMod 2, dotProduct w x = ψ x := by
    intro x
    have hx_eq : x = ∑ i : Fin n, x i • Pi.single i (1 : ZMod 2) := by
      funext j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_eq_single j]
      · simp
      · intro l _ hlj
        simp [Pi.single_eq_of_ne (Ne.symm hlj)]
      · intro hj
        exact absurd (Finset.mem_univ j) hj
    conv_rhs => rw [hx_eq, map_sum]
    simp only [dotProduct, w, map_smul, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  refine ⟨w, ?_, ?_⟩
  · intro u hu
    rw [hψ u]
    dsimp only [ψ]
    rw [LinearMap.comp_apply, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero U).2 hu, map_zero]
  · rw [hψ v]
    dsimp only [ψ]
    rw [LinearMap.comp_apply]
    exact hk1

private theorem main_core (n : ℕ) (C : Circuit) (f : (Fin n → ZMod 2) → ZMod 2)
    (hadm : ∀ g ∈ C.gates,
      (g.op = .and ∧ g.inputs.length = 2) ∨
      (g.op = .mod 2 ∧ g.inputs.length ≤ 2) ∨
      (g.op = .not ∧ g.inputs.length = 1))
    (heval : ∀ x : Fin n → ZMod 2, C.eval (inputBits x) = decide (f x = 1)) :
    ∃ (a : Fin n → ZMod 2) (b : ZMod 2),
      2 * ((Finset.univ : Finset (Fin n → ZMod 2)).filter
        (fun z => f z ≠ dotProduct a z + b)).card + 2 ^ (n - andCount C.gates) ≤ 2 ^ n := by
  classical
  obtain ⟨x₀, U, aW, bW, hdim, hinv⟩ := affine_flat_exists n C.gates hadm
  set a₀ := aW C.output
  set b₀ := bW C.output
  have hflat_eq : ∀ u ∈ U, f (x₀ + u) = dotProduct a₀ (x₀ + u) + b₀ := by
    intro u hu
    have h1 := hinv C.output u hu
    have h2 : toZ2 (C.eval (inputBits (x₀ + u))) = f (x₀ + u) := by
      rw [heval (x₀ + u), toZ2_decide_eq_one]
    rw [← h2]
    exact h1
  let F : Finset (Fin n → ZMod 2) := Finset.univ.filter (fun z => z + x₀ ∈ U)
  let O : Finset (Fin n → ZMod 2) := Finset.univ.filter (fun w => ∀ u ∈ U, dotProduct w u = 0)
  have hO_pos : 0 < O.card := by
    apply Finset.card_pos.2
    refine ⟨0, Finset.mem_filter.2 ⟨Finset.mem_univ 0, fun u _ => zero_dotProduct u⟩⟩
  have hF_card : F.card = 2 ^ Module.finrank (ZMod 2) U := by
    have hbij : F.card = Fintype.card U := by
      refine Finset.card_bij (fun (z : Fin n → ZMod 2) (hz : z ∈ F) => (⟨z + x₀, (Finset.mem_filter.1 hz).2⟩ : U))
        ?_ ?_ ?_
      · intro z _
        exact Finset.mem_univ _
      · intro z₁ _ z₂ _ h
        have hv : z₁ + x₀ = z₂ + x₀ := congrArg Subtype.val h
        have h1 : z₁ = z₁ + x₀ + x₀ := by rw [add_assoc, zmod2_vec_add_self, add_zero]
        have h2 : z₂ = z₂ + x₀ + x₀ := by rw [add_assoc, zmod2_vec_add_self, add_zero]
        rw [h1, h2, hv]
      · intro u _
        refine ⟨x₀ + u.1, ?_, ?_⟩
        · refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
          have h1 : x₀ + u.1 + x₀ = u.1 := by
            rw [add_comm x₀ u.1, add_assoc, zmod2_vec_add_self, add_zero]
          rw [h1]
          exact u.2
        · apply Subtype.ext
          change x₀ + u.1 + x₀ = u.1
          rw [add_comm x₀ u.1, add_assoc, zmod2_vec_add_self, add_zero]
    rw [hbij, Module.card_eq_pow_finrank (K := ZMod 2) (V := U), ZMod.card 2]
  have hF_ge : 2 ^ (n - andCount C.gates) ≤ F.card := by
    rw [hF_card]
    exact Nat.pow_le_pow_right (by omega) hdim
  have hF_le : F.card ≤ 2 ^ n := by
    have h1 : F.card ≤ (Finset.univ : Finset (Fin n → ZMod 2)).card := Finset.card_le_univ F
    simpa [Fintype.card_pi, ZMod.card] using h1
  let dis : (Fin n → ZMod 2) → (Fin n → ZMod 2) → Prop := fun w z =>
    f z ≠ dotProduct (a₀ + w) z + (b₀ + dotProduct w x₀)
  have hsum_eq : ∑ w ∈ O, 2 * ((Finset.univ : Finset (Fin n → ZMod 2)).filter (dis w)).card =
      (2 ^ n - F.card) * O.card := by
    have h1 : ∑ w ∈ O, 2 * ((Finset.univ : Finset (Fin n → ZMod 2)).filter (dis w)).card =
        ∑ z : Fin n → ZMod 2, 2 * (O.filter (fun w => dis w z)).card := by
      have hL : ∑ w ∈ O, 2 * ((Finset.univ : Finset (Fin n → ZMod 2)).filter (dis w)).card =
          2 * ∑ w ∈ O, ∑ z : Fin n → ZMod 2, if dis w z then (1 : ℕ) else 0 := by
        rw [← Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro w _
        rw [Finset.card_filter]
      have hR : ∑ z : Fin n → ZMod 2, 2 * (O.filter (fun w => dis w z)).card =
          2 * ∑ z : Fin n → ZMod 2, ∑ w ∈ O, if dis w z then (1 : ℕ) else 0 := by
        rw [← Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro z _
        rw [Finset.card_filter]
      rw [hL, hR, Finset.sum_comm]
    rw [h1]
    have hterm : ∀ z : Fin n → ZMod 2,
        2 * (O.filter (fun w => dis w z)).card = if z ∈ F then 0 else O.card := by
      intro z
      by_cases hzF : z ∈ F
      · rw [if_pos hzF]
        have hu : z + x₀ ∈ U := (Finset.mem_filter.1 hzF).2
        have hzero : O.filter (fun w => dis w z) = ∅ := by
          rw [Finset.filter_eq_empty_iff]
          intro w hw
          have hwO : ∀ u ∈ U, dotProduct w u = 0 := (Finset.mem_filter.1 hw).2
          dsimp only [dis]
          rw [not_ne_iff]
          have hzx : x₀ + (z + x₀) = z := by
            rw [add_comm z x₀, ← add_assoc, zmod2_vec_add_self, zero_add]
          have hf := hflat_eq (z + x₀) hu
          rw [hzx] at hf
          rw [hf, add_dotProduct]
          have hwu : dotProduct w (z + x₀) = 0 := hwO (z + x₀) hu
          rw [dotProduct_add] at hwu
          have hwz : dotProduct w z + dotProduct w x₀ = 0 := hwu
          calc
            dotProduct a₀ z + b₀
              = dotProduct a₀ z + b₀ + (dotProduct w z + dotProduct w x₀) := by rw [hwz, add_zero]
            _ = dotProduct a₀ z + dotProduct w z + (b₀ + dotProduct w x₀) := by ring
        rw [hzero]; simp
      · rw [if_neg hzF]
        have hnotU : z + x₀ ∉ U := fun h => hzF (Finset.mem_filter.2 ⟨Finset.mem_univ z, h⟩)
        obtain ⟨w₀, hw₀U, hw₀v⟩ := exists_ortho_eval_one U (z + x₀) hnotU
        have hcomp_eq : (O.filter (fun w => dis w z)).card =
            (O.filter (fun w => ¬ dis w z)).card := by
          refine Finset.card_bij (fun w _ => w + w₀) ?_ ?_ ?_
          · intro w hw
            have hwO := (Finset.mem_filter.1 (Finset.mem_filter.1 hw).1).2
            have hdis : dis w z := (Finset.mem_filter.1 hw).2
            refine Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩, ?_⟩
            · intro u hu
              rw [add_dotProduct, hwO u hu, hw₀U u hu, add_zero]
            · intro hdis'
              have hval : dotProduct (a₀ + (w + w₀)) z + (b₀ + dotProduct (w + w₀) x₀) =
                  dotProduct (a₀ + w) z + (b₀ + dotProduct w x₀) + 1 := by
                have hadd : dotProduct w₀ z + dotProduct w₀ x₀ = 1 := by
                  rw [← dotProduct_add]; exact hw₀v
                rw [add_dotProduct a₀ (w + w₀) z, add_dotProduct w w₀ z, add_dotProduct w w₀ x₀, add_dotProduct a₀ w z]
                calc
                  dotProduct a₀ z + (dotProduct w z + dotProduct w₀ z) +
                      (b₀ + (dotProduct w x₀ + dotProduct w₀ x₀))
                    = dotProduct a₀ z + dotProduct w z + (b₀ + dotProduct w x₀) +
                      (dotProduct w₀ z + dotProduct w₀ x₀) := by ring
                  _ = dotProduct a₀ z + dotProduct w z + (b₀ + dotProduct w x₀) + 1 := by rw [hadd]
              dsimp only [dis] at hdis hdis'
              have hne1 : f z ≠ dotProduct (a₀ + w) z + (b₀ + dotProduct w x₀) := hdis
              have hne2 : f z ≠ dotProduct (a₀ + w) z + (b₀ + dotProduct w x₀) + 1 := by
                rwa [hval] at hdis'
              generalize f z = c1 at hne1 hne2
              generalize dotProduct (a₀ + w) z + (b₀ + dotProduct w x₀) = c2 at hne1 hne2
              revert hne1 hne2 c1 c2
              decide
          · intro w₁ _ w₂ _ h
            have h1 : w₁ = w₁ + w₀ + w₀ := by rw [add_assoc, zmod2_vec_add_self, add_zero]
            have h2 : w₂ = w₂ + w₀ + w₀ := by rw [add_assoc, zmod2_vec_add_self, add_zero]
            rw [h1, h2, h]
          · intro w hw
            have hwO := (Finset.mem_filter.1 (Finset.mem_filter.1 hw).1).2
            have hndis : ¬ dis w z := (Finset.mem_filter.1 hw).2
            refine ⟨w + w₀, Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩, ?_⟩, ?_⟩
            · intro u hu
              rw [add_dotProduct, hwO u hu, hw₀U u hu, add_zero]
            · dsimp only [dis] at hndis ⊢
              rw [not_ne_iff] at hndis
              have hadd : dotProduct w₀ z + dotProduct w₀ x₀ = 1 := by
                rw [← dotProduct_add]; exact hw₀v
              rw [hndis, add_dotProduct, add_dotProduct, add_dotProduct, add_dotProduct]
              intro heq
              have h01 : (0 : ZMod 2) = 1 := by
                have hdiff := congrArg (fun t => t + (dotProduct a₀ z + dotProduct w z + (b₀ + dotProduct w x₀))) heq
                have hL : dotProduct a₀ z + dotProduct w z + (b₀ + dotProduct w x₀) +
                    (dotProduct a₀ z + dotProduct w z + (b₀ + dotProduct w x₀)) = 0 := zmod2_add_self _
                have hR : dotProduct a₀ z + (dotProduct w z + dotProduct w₀ z) +
                    (b₀ + (dotProduct w x₀ + dotProduct w₀ x₀)) +
                    (dotProduct a₀ z + dotProduct w z + (b₀ + dotProduct w x₀)) = 1 := by
                  calc
                    dotProduct a₀ z + (dotProduct w z + dotProduct w₀ z) +
                        (b₀ + (dotProduct w x₀ + dotProduct w₀ x₀)) +
                        (dotProduct a₀ z + dotProduct w z + (b₀ + dotProduct w x₀))
                      = (dotProduct a₀ z + dotProduct w z + (b₀ + dotProduct w x₀) +
                          (dotProduct a₀ z + dotProduct w z + (b₀ + dotProduct w x₀))) +
                        (dotProduct w₀ z + dotProduct w₀ x₀) := by ring
                    _ = 1 := by rw [hL, zero_add, hadd]
                rw [hL, hR] at hdiff
                exact hdiff
              exact zero_ne_one h01
            · rw [add_assoc, zmod2_vec_add_self, add_zero]
        have hpart : (O.filter (fun w => dis w z)).card + (O.filter (fun w => ¬ dis w z)).card = O.card := by
          rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
          have h1 : ∑ w ∈ O, ((if dis w z then 1 else 0) + (if ¬ dis w z then 1 else 0)) = ∑ _w ∈ O, 1 := by
            apply Finset.sum_congr rfl
            intro w _
            by_cases h : dis w z <;> simp [h]
          rw [h1]
          simp
        omega
    simp_rw [hterm]
    have hsum_compl : ∑ z : Fin n → ZMod 2, (if z ∈ F then 0 else O.card) =
        ((Finset.univ : Finset (Fin n → ZMod 2)) \ F).card * O.card := by
      rw [← Finset.sum_filter_not_add_sum_filter Finset.univ (fun z => z ∈ F)]
      have hA : ∑ x ∈ Finset.univ.filter (fun z => z ∉ F), (if x ∈ F then 0 else O.card) =
          ((Finset.univ : Finset (Fin n → ZMod 2)) \ F).card * O.card := by
        have hfeq : Finset.univ.filter (fun z : Fin n → ZMod 2 => z ∉ F) = Finset.univ \ F := by
          ext z; simp
        rw [hfeq]
        have hconst : ∑ x ∈ Finset.univ \ F, (if x ∈ F then 0 else O.card) =
            ∑ _x ∈ Finset.univ \ F, O.card := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [if_neg (Finset.mem_sdiff.1 hx).2]
        rw [hconst, Finset.sum_const, smul_eq_mul]
      have hB : ∑ x ∈ Finset.univ.filter (fun z => z ∈ F), (if x ∈ F then 0 else O.card) = 0 := by
        apply Finset.sum_eq_zero
        intro x hx
        rw [if_pos (Finset.mem_filter.1 hx).2]
      rw [hA, hB, add_zero]
    rw [hsum_compl, Finset.card_sdiff, Finset.inter_univ]
    have huniv : (Finset.univ : Finset (Fin n → ZMod 2)).card = 2 ^ n := by
      simp [Fintype.card_pi, ZMod.card]
    rw [huniv]
  have hex_w : ∃ w ∈ O, 2 * ((Finset.univ : Finset (Fin n → ZMod 2)).filter (dis w)).card ≤
      2 ^ n - F.card := by
    by_contra hall
    push_neg at hall
    have hgt : (2 ^ n - F.card + 1) * O.card ≤
        ∑ w ∈ O, 2 * ((Finset.univ : Finset (Fin n → ZMod 2)).filter (dis w)).card := by
      have h1 : ∑ _w ∈ O, (2 ^ n - F.card + 1) ≤
          ∑ w ∈ O, 2 * ((Finset.univ : Finset (Fin n → ZMod 2)).filter (dis w)).card :=
        Finset.sum_le_sum (fun w hw => hall w hw)
      simpa [Finset.sum_const, smul_eq_mul, mul_comm] using h1
    rw [hsum_eq] at hgt
    have hlt : (2 ^ n - F.card) * O.card < (2 ^ n - F.card + 1) * O.card := by
      nlinarith
    omega
  obtain ⟨w, _, hw_le⟩ := hex_w
  refine ⟨a₀ + w, b₀ + dotProduct w x₀, ?_⟩
  dsimp only [dis] at hw_le
  omega

end PEqualNP.Outside.L_lib_507_aux

theorem PEqualNP.Outside.L_lib_507 : (∀ n : ℕ,
  let V := Fin n → ZMod 2
  let admissible := fun (C : PEqualNP.CircuitLowerBounds.Circuit) =>
    PEqualNP.MetaComplexity.NestedCover.ReadsBack n C ∧
    (∀ g ∈ C.gates,
      (g.op = .and ∧ g.inputs.length = 2) ∨
      (g.op = .mod 2 ∧ g.inputs.length ≤ 2) ∨
      (g.op = .not ∧ g.inputs.length = 1))
  let cost := fun (C : PEqualNP.CircuitLowerBounds.Circuit) =>
    C.gates.countP (fun g => @decide (g.op = .and) (Classical.propDecidable _))
  let input := fun (x : V) => List.ofFn (fun i : Fin n => decide (x i = 1))
  ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (f : V → ZMod 2),
    admissible C → (∀ x : V, C.eval (input x) = decide (f x = 1)) →
    ∃ (a : V) (b : ZMod 2),
      2*((Finset.univ : Finset V).filter (fun z => f z ≠ dotProduct a z + b)).card + 2^(n - cost C) ≤ 2^n) := by
  intro n V admissible cost input C f hadm heval
  exact PEqualNP.Outside.L_lib_507_aux.main_core n C f hadm.2 heval
