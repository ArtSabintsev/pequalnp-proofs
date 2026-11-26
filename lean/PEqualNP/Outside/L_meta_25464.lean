import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25464_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

private def runGates (w : List Bool) (gs : List Gate) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

private theorem circuit_wires_eq (C : Circuit) (x : List Bool) :
    C.wires x = runGates x C.gates := rfl

private theorem runGates_nil (w : List Bool) : runGates w [] = w := rfl

private theorem runGates_cons (w : List Bool) (g : Gate) (gs : List Gate) :
    runGates w (g :: gs) =
      runGates (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) gs := rfl

private theorem runGates_append (w : List Bool) (gs1 gs2 : List Gate) :
    runGates w (gs1 ++ gs2) = runGates (runGates w gs1) gs2 := by
  simp [runGates, List.foldl_append]

private theorem runGates_length (w : List Bool) (gs : List Gate) :
    (runGates w gs).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [runGates]
  | cons g gs ih =>
    rw [runGates_cons, ih]
    simp
    omega

private theorem getD_append_left {α : Type*} (l1 l2 : List α) (i : ℕ) (d : α)
    (hi : i < l1.length) : (l1 ++ l2).getD i d = l1.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private theorem getD_append_right {α : Type*} (l1 l2 : List α) (i : ℕ) (d : α)
    (hi : l1.length ≤ i) : (l1 ++ l2).getD i d = l2.getD (i - l1.length) d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right hi]

private theorem getD_of_ge {α : Type*} (l : List α) (i : ℕ) (d : α)
    (hi : l.length ≤ i) : l.getD i d = d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

private theorem runGates_getD_lt (w : List Bool) (gs : List Gate) (i : ℕ)
    (hi : i < w.length) : (runGates w gs).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [runGates_cons]
    have hlt : i < (w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]).length := by
      simp; omega
    rw [ih _ hlt, getD_append_left _ _ _ _ hi]

private def remapGate (r : ℕ → ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map r⟩

private theorem runGates_remap_getD_clean
    (w1 w2 : List Bool) (r : ℕ → ℕ) (tot : ℕ) (gs : List Gate)
    (htot : gs.length ≤ tot)
    (hbase : ∀ i < w1.length, w1.getD i false = w2.getD (r i) false)
    (hbase_lt : ∀ i < w1.length, r i < w2.length ∨ w2.length + tot ≤ r i)
    (hshift : ∀ k < tot, r (w1.length + k) = w2.length + k)
    (hge : ∀ i, w1.length + tot ≤ i → w2.length + tot ≤ r i) :
    ∀ i : ℕ, (runGates w1 gs).getD i false = (runGates w2 (gs.map (remapGate r))).getD (r i) false := by
  induction gs generalizing w1 w2 tot with
  | nil =>
    intro i
    simp only [List.map_nil, runGates_nil]
    by_cases hi : i < w1.length
    · exact hbase i hi
    · rw [getD_of_ge w1 i false (by omega)]
      by_cases hi2 : i < w1.length + tot
      · have hk : i - w1.length < tot := by omega
        have hEq : w1.length + (i - w1.length) = i := by omega
        have hr : r i = w2.length + (i - w1.length) := by simpa [hEq] using hshift _ hk
        rw [hr, getD_of_ge w2 _ false (by omega)]
      · have hr : w2.length + tot ≤ r i := hge i (by omega)
        rw [getD_of_ge w2 _ false (by omega)]
  | cons g gs ih =>
    simp only [List.map_cons, runGates_cons]
    have hcur : ∀ i : ℕ, w1.getD i false = w2.getD (r i) false := by
      intro i
      by_cases hi : i < w1.length
      · exact hbase i hi
      · rw [getD_of_ge w1 i false (by omega)]
        by_cases hi2 : i < w1.length + tot
        · have hk : i - w1.length < tot := by omega
          have hEq : w1.length + (i - w1.length) = i := by omega
          have hr : r i = w2.length + (i - w1.length) := by simpa [hEq] using hshift _ hk
          rw [hr, getD_of_ge w2 _ false (by omega)]
        · have hr : w2.length + tot ≤ r i := hge i (by omega)
          rw [getD_of_ge w2 _ false (by omega)]
    have hval :
        g.op.eval (g.inputs.map fun i => w1.getD i false) =
        (remapGate r g).op.eval ((remapGate r g).inputs.map fun i => w2.getD i false) := by
      simp only [remapGate, List.map_map, Function.comp_def]
      congr 1
      apply List.map_congr_left
      intro a _
      exact hcur a
    set v := g.op.eval (g.inputs.map fun i => w1.getD i false)
    rw [← hval]
    have htot_pos : 0 < tot := by simp at htot; omega
    have htot' : gs.length ≤ tot - 1 := by simp at htot; omega
    apply ih (w1 ++ [v]) (w2 ++ [v]) (tot - 1) htot'
    · intro i hi
      simp only [List.length_append, List.length_singleton] at hi
      by_cases hlt : i < w1.length
      · rw [getD_append_left w1 [v] i false hlt, hbase i hlt]
        rcases hbase_lt i hlt with hrlt | hrge
        · rw [getD_append_left w2 [v] (r i) false hrlt]
        · rw [getD_of_ge w2 (r i) false (by omega),
              getD_of_ge (w2 ++ [v]) (r i) false (by simp; omega)]
      · have heq : i = w1.length := by omega
        subst heq
        have h0 : r (w1.length + 0) = w2.length + 0 := hshift 0 htot_pos
        simp only [Nat.add_zero] at h0
        rw [h0, getD_append_right w1 [v] w1.length false (le_refl _),
            getD_append_right w2 [v] w2.length false (le_refl _)]
        simp
    · intro i hi
      simp only [List.length_append, List.length_singleton] at hi ⊢
      by_cases hlt : i < w1.length
      · rcases hbase_lt i hlt with hrlt | hrge
        · left; omega
        · right; omega
      · have heq : i = w1.length := by omega
        subst heq
        have h0 : r (w1.length + 0) = w2.length + 0 := hshift 0 htot_pos
        simp only [Nat.add_zero] at h0
        left; omega
    · intro k hk
      simp only [List.length_append, List.length_singleton]
      have h1 : w1.length + 1 + k = w1.length + (k + 1) := by omega
      have h2 : w2.length + 1 + k = w2.length + (k + 1) := by omega
      rw [h1, h2]
      exact hshift (k + 1) (by omega)
    · intro i hi
      simp only [List.length_append, List.length_singleton] at hi ⊢
      have h1 : w1.length + tot ≤ i := by omega
      have h2 := hge i h1
      omega

private theorem oneEach_length {n m : ℕ} (u : Fin n) (v : Fin m) :
    (oneEach u v).length = n + m := by
  simp [oneEach]

private theorem oneEach_getD_left {n m : ℕ} (u : Fin n) (v : Fin m) (i : ℕ) (hi : i < n) :
    (oneEach u v).getD i false = decide (⟨i, hi⟩ = u) := by
  unfold oneEach
  rw [getD_append_left _ _ _ _ (by simp; exact hi)]
  simp [List.getD_eq_getElem?_getD, hi]

private theorem oneEach_getD_right {n m : ℕ} (u : Fin n) (v : Fin m) (j : ℕ) (hj : j < m) :
    (oneEach u v).getD (n + j) false = decide (⟨j, hj⟩ = v) := by
  unfold oneEach
  rw [getD_append_right _ _ _ _ (by simp)]
  have hsub : n + j - (List.ofFn (fun i : Fin n => decide (i = u))).length = j := by simp
  rw [hsub]
  simp [List.getD_eq_getElem?_getD, hj]

private def orChainAux (cur nextWire : ℕ) : List ℕ → List Gate × ℕ
  | [] => ([], cur)
  | a :: rest =>
      let res := orChainAux nextWire (nextWire + 1) rest
      (⟨GateOp.or, [cur, a]⟩ :: res.1, res.2)

private theorem orChainAux_length (cur nextWire : ℕ) (rest : List ℕ) :
    (orChainAux cur nextWire rest).1.length = rest.length := by
  induction rest generalizing cur nextWire with
  | nil => rfl
  | cons a rs ih =>
    simp [orChainAux, ih]

private theorem orChainAux_mono (cur nextWire : ℕ) (rest : List ℕ) :
    ∀ g ∈ (orChainAux cur nextWire rest).1,
      g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  induction rest generalizing cur nextWire with
  | nil => intro g hg; simp [orChainAux] at hg
  | cons a rs ih =>
    intro g hg
    simp only [orChainAux, List.mem_cons] at hg
    rcases hg with rfl | hg'
    · exact ⟨by simp, by simp⟩
    · exact ih nextWire (nextWire + 1) g hg'

private theorem orChainAux_out_lt (cur nextWire : ℕ) (rest : List ℕ) (hcur : cur < nextWire) :
    (orChainAux cur nextWire rest).2 < nextWire + rest.length := by
  induction rest generalizing cur nextWire with
  | nil => simpa [orChainAux] using hcur
  | cons a rs ih =>
    simp only [orChainAux, List.length_cons]
    have h := ih nextWire (nextWire + 1) (by omega)
    omega

private theorem orChainAux_eval (cur nextWire : ℕ) (rest : List ℕ) (w : List Bool)
    (hlen : w.length = nextWire) (hrest : ∀ a ∈ rest, a < nextWire) :
    (runGates w (orChainAux cur nextWire rest).1).getD (orChainAux cur nextWire rest).2 false =
      (w.getD cur false || rest.any (fun a => w.getD a false)) := by
  induction rest generalizing cur nextWire w with
  | nil => simp [orChainAux, runGates]
  | cons a rs ih =>
    simp only [orChainAux, runGates_cons, List.any_cons]
    set v := GateOp.or.eval ([cur, a].map fun i => w.getD i false)
    have hv : v = (w.getD cur false || w.getD a false) := by
      simp [v, GateOp.eval]
    have hlen1 : (w ++ [v]).length = nextWire + 1 := by simp [hlen]
    have hrest1 : ∀ b ∈ rs, b < nextWire + 1 := fun b hb => by
      have := hrest b (List.mem_cons_of_mem a hb); omega
    rw [ih nextWire (nextWire + 1) (w ++ [v]) hlen1 hrest1]
    have hnw : (w ++ [v]).getD nextWire false = v := by
      rw [getD_append_right w [v] nextWire false (by omega)]
      simp [hlen]
    have hrs : rs.any (fun b => (w ++ [v]).getD b false) = rs.any (fun b => w.getD b false) := by
      apply Bool.eq_iff_iff.mpr
      simp only [List.any_eq_true]
      constructor
      · rintro ⟨b, hb, hbv⟩
        have hblt : b < w.length := by rw [hlen]; exact hrest b (List.mem_cons_of_mem a hb)
        rw [getD_append_left w [v] b false hblt] at hbv
        exact ⟨b, hb, hbv⟩
      · rintro ⟨b, hb, hbv⟩
        have hblt : b < w.length := by rw [hlen]; exact hrest b (List.mem_cons_of_mem a hb)
        exact ⟨b, hb, by rwa [getD_append_left w [v] b false hblt]⟩
    rw [hnw, hrs, hv, Bool.or_assoc]

private def buildFibers (nextWire : ℕ) : List (List ℕ) → List Gate × List ℕ
  | [] => ([], [])
  | [] :: rest => buildFibers nextWire rest
  | (a :: as) :: rest =>
      let r1 := orChainAux a nextWire as
      let r2 := buildFibers (nextWire + as.length) rest
      (r1.1 ++ r2.1, r1.2 :: r2.2)

private theorem buildFibers_length (nextWire : ℕ) (fibs : List (List ℕ)) :
    (buildFibers nextWire fibs).1.length = (fibs.map fun L => L.length - 1).sum := by
  induction fibs generalizing nextWire with
  | nil => rfl
  | cons L rest ih =>
    cases L with
    | nil => simp [buildFibers, ih]
    | cons a as =>
      simp [buildFibers, orChainAux_length, ih]

private theorem buildFibers_outs_length (nextWire : ℕ) (fibs : List (List ℕ))
    (hne : ∀ L ∈ fibs, L ≠ []) :
    (buildFibers nextWire fibs).2.length = fibs.length := by
  induction fibs generalizing nextWire with
  | nil => rfl
  | cons L rest ih =>
    cases L with
    | nil => exact absurd rfl (hne [] (List.mem_cons_self ..))
    | cons a as =>
      simp only [buildFibers, List.length_cons]
      rw [ih (nextWire + as.length) (fun M hM => hne M (List.mem_cons_of_mem _ hM))]

private theorem buildFibers_mono (nextWire : ℕ) (fibs : List (List ℕ)) :
    ∀ g ∈ (buildFibers nextWire fibs).1,
      g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  induction fibs generalizing nextWire with
  | nil => intro g hg; simp [buildFibers] at hg
  | cons L rest ih =>
    cases L with
    | nil => exact ih nextWire
    | cons a as =>
      intro g hg
      simp only [buildFibers, List.mem_append] at hg
      rcases hg with h1 | h2
      · exact orChainAux_mono a nextWire as g h1
      · exact ih (nextWire + as.length) g h2

private theorem buildFibers_out_lt (nextWire : ℕ) (fibs : List (List ℕ))
    (hne : ∀ L ∈ fibs, L ≠ [])
    (hlt : ∀ L ∈ fibs, ∀ x ∈ L, x < nextWire) :
    ∀ k < fibs.length,
      (buildFibers nextWire fibs).2.getD k 0 < nextWire + (buildFibers nextWire fibs).1.length := by
  induction fibs generalizing nextWire with
  | nil => intro k hk; simp at hk
  | cons L rest ih =>
    cases L with
    | nil => exact absurd rfl (hne [] (List.mem_cons_self ..))
    | cons a as =>
      intro k hk
      simp only [buildFibers, List.length_append, orChainAux_length]
      cases k with
      | zero =>
        simp only [List.getD_cons_zero]
        have ha : a < nextWire := hlt (a :: as) (List.mem_cons_self ..) a (List.mem_cons_self ..)
        have h1 := orChainAux_out_lt a nextWire as ha
        omega
      | succ k' =>
        simp only [List.getD_cons_succ]
        have hne' : ∀ M ∈ rest, M ≠ [] := fun M hM => hne M (List.mem_cons_of_mem _ hM)
        have hlt' : ∀ M ∈ rest, ∀ x ∈ M, x < nextWire + as.length := fun M hM x hx => by
          have := hlt M (List.mem_cons_of_mem _ hM) x hx; omega
        have hk' : k' < rest.length := by simp at hk; omega
        have h2 := ih (nextWire + as.length) hne' hlt' k' hk'
        omega

private theorem buildFibers_eval (nextWire : ℕ) (fibs : List (List ℕ)) (w : List Bool)
    (hlen : w.length = nextWire)
    (hne : ∀ L ∈ fibs, L ≠ [])
    (hlt : ∀ L ∈ fibs, ∀ x ∈ L, x < nextWire) :
    ∀ k (hk : k < fibs.length),
      (runGates w (buildFibers nextWire fibs).1).getD ((buildFibers nextWire fibs).2.getD k 0) false =
        (fibs[k]).any (fun x => w.getD x false) := by
  induction fibs generalizing nextWire w with
  | nil => intro k hk; simp at hk
  | cons L rest ih =>
    cases L with
    | nil => exact absurd rfl (hne [] (List.mem_cons_self ..))
    | cons a as =>
      intro k hk
      simp only [buildFibers, runGates_append]
      set r1 := orChainAux a nextWire as
      set w1 := runGates w r1.1
      have hw1_len : w1.length = nextWire + as.length := by
        simp [w1, r1, runGates_length, hlen, orChainAux_length]
      have ha : a < nextWire := hlt (a :: as) (List.mem_cons_self ..) a (List.mem_cons_self ..)
      have has : ∀ x ∈ as, x < nextWire := fun x hx =>
        hlt (a :: as) (List.mem_cons_self ..) x (List.mem_cons_of_mem a hx)
      cases k with
      | zero =>
        simp only [List.getD_cons_zero, List.getElem_cons_zero, List.any_cons]
        have hout_lt : r1.2 < w1.length := by
          rw [hw1_len]; exact orChainAux_out_lt a nextWire as ha
        rw [runGates_getD_lt w1 (buildFibers (nextWire + as.length) rest).1 r1.2 hout_lt]
        exact orChainAux_eval a nextWire as w hlen has
      | succ k' =>
        simp only [List.getD_cons_succ, List.getElem_cons_succ]
        have hne' : ∀ M ∈ rest, M ≠ [] := fun M hM => hne M (List.mem_cons_of_mem _ hM)
        have hlt' : ∀ M ∈ rest, ∀ x ∈ M, x < nextWire + as.length := fun M hM x hx => by
          have := hlt M (List.mem_cons_of_mem _ hM) x hx; omega
        have hk' : k' < rest.length := by simp at hk; omega
        rw [ih (nextWire + as.length) w1 hw1_len hne' hlt' k' hk']
        apply Bool.eq_iff_iff.mpr
        simp only [List.any_eq_true]
        constructor
        · rintro ⟨x, hx, hxv⟩
          have hxlt : x < w.length := by
            rw [hlen]; exact hlt rest[k'] (List.mem_cons_of_mem _ (List.getElem_mem hk')) x hx
          rw [runGates_getD_lt w r1.1 x hxlt] at hxv
          exact ⟨x, hx, hxv⟩
        · rintro ⟨x, hx, hxv⟩
          have hxlt : x < w.length := by
            rw [hlen]; exact hlt rest[k'] (List.mem_cons_of_mem _ (List.getElem_mem hk')) x hx
          exact ⟨x, hx, by rwa [runGates_getD_lt w r1.1 x hxlt]⟩

private theorem sum_fiber_lengths {n n0 : ℕ} (f : Fin n → Fin n0) :
    ((List.finRange n0).map fun i => ((List.finRange n).filter fun u => decide (f u = i)).length).sum = n := by
  have h1 : ∀ l : List (Fin n),
      ((List.finRange n0).map fun i => (l.filter fun u => decide (f u = i)).length).sum = l.length := by
    intro l
    induction l with
    | nil => simp
    | cons u us ih =>
      have hnd := List.nodup_finRange n0
      have hstep' :
          ∀ xs : List (Fin n0), xs.Nodup →
            (xs.map fun i => ((u :: us).filter fun x => decide (f x = i)).length).sum =
            (xs.map fun i => (us.filter fun x => decide (f x = i)).length).sum +
            (if f u ∈ xs then 1 else 0) := by
        intro xs hxs
        induction xs with
        | nil => simp
        | cons y ys ihy =>
          rw [List.nodup_cons] at hxs
          simp only [List.map_cons, List.sum_cons, List.mem_cons]
          rw [ihy hxs.2]
          by_cases hfy : f u = y
          · subst hfy
            have hnot : f u ∉ ys := hxs.1
            have hhd : ((u :: us).filter fun x => decide (f x = f u)).length =
                (us.filter fun x => decide (f x = f u)).length + 1 := by
              simp
            rw [hhd]
            simp only [true_or, ↓reduceIte, hnot]
            omega
          · have hhd : ((u :: us).filter fun x => decide (f x = y)).length =
                (us.filter fun x => decide (f x = y)).length := by
              simp [hfy]
            rw [hhd]
            simp only [hfy, false_or]
            omega
      rw [hstep' (List.finRange n0) hnd, ih]
      simp [List.mem_finRange]
  simpa [List.length_finRange] using h1 (List.finRange n)

private theorem length_le_sum_of_pos (l : List ℕ) (hpos : ∀ x ∈ l, 1 ≤ x) :
    l.length ≤ l.sum := by
  induction l with
  | nil => simp
  | cons a as ih =>
    have ha : 1 ≤ a := hpos a (List.mem_cons_self ..)
    have h1 := ih (fun y hy => hpos y (List.mem_cons_of_mem a hy))
    simp; omega

private theorem sum_sub_one (l : List ℕ) (hpos : ∀ x ∈ l, 1 ≤ x) :
    (l.map fun x => x - 1).sum = l.sum - l.length := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    have hx : 1 ≤ x := hpos x (List.mem_cons_self ..)
    have hxs : ∀ y ∈ xs, 1 ≤ y := fun y hy => hpos y (List.mem_cons_of_mem x hy)
    have hsum_ge : xs.length ≤ xs.sum := length_le_sum_of_pos xs hxs
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    rw [ih hxs]
    omega

private theorem part_a (n m n0 m0 s : ℕ) (Q : Fin n0 → Fin m0 → Bool)
    (f : Fin n → Fin n0) (g : Fin m → Fin m0)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hQ : RepSizeAtMost Q s) :
    RepSizeAtMost (fun (u : Fin n) (v : Fin m) => Q (f u) (g v)) (s + (n - n0) + (m - m0)) := by
  rcases hQ with ⟨C, hCmono, hCsize, hCrep⟩
  let rowFibs : List (List ℕ) :=
    (List.finRange n0).map fun i =>
      ((List.finRange n).filter fun u => decide (f u = i)).map Fin.val
  let colFibs : List (List ℕ) :=
    (List.finRange m0).map fun j =>
      ((List.finRange m).filter fun v => decide (g v = j)).map (fun v => n + v.val)
  let fibs : List (List ℕ) := rowFibs ++ colFibs
  have hrow_ne : ∀ L ∈ rowFibs, L ≠ [] := by
    intro L hL
    simp only [rowFibs, List.mem_map, List.mem_finRange, true_and] at hL
    rcases hL with ⟨i, rfl⟩
    rcases hf i with ⟨u, hu⟩
    intro hnil
    have hmem : u.val ∈ ((List.finRange n).filter fun x => decide (f x = i)).map Fin.val := by
      refine List.mem_map.mpr ⟨u, List.mem_filter.mpr ⟨List.mem_finRange u, ?_⟩, rfl⟩
      simp [hu]
    rw [hnil] at hmem
    simp at hmem
  have hcol_ne : ∀ L ∈ colFibs, L ≠ [] := by
    intro L hL
    simp only [colFibs, List.mem_map, List.mem_finRange, true_and] at hL
    rcases hL with ⟨j, rfl⟩
    rcases hg j with ⟨v, hv⟩
    intro hnil
    have hmem : n + v.val ∈ ((List.finRange m).filter fun x => decide (g x = j)).map (fun v => n + v.val) := by
      refine List.mem_map.mpr ⟨v, List.mem_filter.mpr ⟨List.mem_finRange v, ?_⟩, rfl⟩
      simp [hv]
    rw [hnil] at hmem
    simp at hmem
  have hfibs_ne : ∀ L ∈ fibs, L ≠ [] := by
    intro L hL
    simp only [fibs, List.mem_append] at hL
    rcases hL with h1 | h2
    · exact hrow_ne L h1
    · exact hcol_ne L h2
  have hfibs_lt : ∀ L ∈ fibs, ∀ x ∈ L, x < n + m := by
    intro L hL x hx
    simp only [fibs, List.mem_append] at hL
    rcases hL with h1 | h2
    · simp only [rowFibs, List.mem_map, List.mem_finRange, true_and] at h1
      rcases h1 with ⟨i, rfl⟩
      rcases List.mem_map.mp hx with ⟨u, _, rfl⟩
      omega
    · simp only [colFibs, List.mem_map, List.mem_finRange, true_and] at h2
      rcases h2 with ⟨j, rfl⟩
      rcases List.mem_map.mp hx with ⟨v, _, rfl⟩
      omega
  let bf := buildFibers (n + m) fibs
  let preGates := bf.1
  let outs := bf.2
  have hrow_sum : (rowFibs.map fun L => L.length - 1).sum = n - n0 := by
    have hpos : ∀ x ∈ rowFibs.map List.length, 1 ≤ x := by
      intro x hx
      rcases List.mem_map.mp hx with ⟨L, hL, rfl⟩
      have hne := hrow_ne L hL
      cases L with
      | nil => exact absurd rfl hne
      | cons _ _ => simp
    have hmap : (rowFibs.map fun L => L.length - 1) = (rowFibs.map List.length).map (fun x => x - 1) := by
      simp [List.map_map]
    rw [hmap, sum_sub_one _ hpos]
    have hlen : (rowFibs.map List.length).length = n0 := by simp [rowFibs]
    have hsum : (rowFibs.map List.length).sum = n := by
      have : (rowFibs.map List.length) =
          (List.finRange n0).map fun i => ((List.finRange n).filter fun u => decide (f u = i)).length := by
        simp [rowFibs, List.map_map, Function.comp_def]
      rw [this]
      exact sum_fiber_lengths f
    rw [hlen, hsum]
  have hcol_sum : (colFibs.map fun L => L.length - 1).sum = m - m0 := by
    have hpos : ∀ x ∈ colFibs.map List.length, 1 ≤ x := by
      intro x hx
      rcases List.mem_map.mp hx with ⟨L, hL, rfl⟩
      have hne := hcol_ne L hL
      cases L with
      | nil => exact absurd rfl hne
      | cons _ _ => simp
    have hmap : (colFibs.map fun L => L.length - 1) = (colFibs.map List.length).map (fun x => x - 1) := by
      simp [List.map_map]
    rw [hmap, sum_sub_one _ hpos]
    have hlen : (colFibs.map List.length).length = m0 := by simp [colFibs]
    have hsum : (colFibs.map List.length).sum = m := by
      have : (colFibs.map List.length) =
          (List.finRange m0).map fun j => ((List.finRange m).filter fun v => decide (g v = j)).length := by
        simp [colFibs, List.map_map, Function.comp_def]
      rw [this]
      exact sum_fiber_lengths g
    rw [hlen, hsum]
  have hpre_len : preGates.length = (n - n0) + (m - m0) := by
    simp only [preGates, bf, buildFibers_length, fibs, List.map_append, List.sum_append,
      hrow_sum, hcol_sum]
  let base2 := n + m + preGates.length
  let r : ℕ → ℕ := fun w =>
    if w < n0 + m0 then outs.getD w 0
    else if w < n0 + m0 + C.gates.length then base2 + (w - (n0 + m0))
    else base2 + C.gates.length
  let C' : Circuit := ⟨preGates ++ C.gates.map (remapGate r), r C.output⟩
  refine ⟨C', ?_, ?_, ?_⟩
  · intro gt hgt
    simp only [C', List.mem_append, List.mem_map] at hgt
    rcases hgt with h1 | ⟨gt0, hgt0, rfl⟩
    · exact buildFibers_mono (n + m) fibs gt h1
    · rcases hCmono gt0 hgt0 with ⟨hop, hlen⟩
      exact ⟨hop, by simp [remapGate, hlen]⟩
  · simp only [Circuit.size, C', List.length_append, List.length_map, hpre_len]
    simp only [Circuit.size] at hCsize
    omega
  · intro u v
    change (runGates (oneEach u v) (preGates ++ C.gates.map (remapGate r))).getD (r C.output) false =
      Q (f u) (g v)
    rw [runGates_append]
    set w1 := oneEach (f u) (g v)
    set w2 := runGates (oneEach u v) preGates
    have hw1_len : w1.length = n0 + m0 := oneEach_length (f u) (g v)
    have hw2_len : w2.length = base2 := by
      simp [w2, base2, runGates_length, oneEach_length]
    have hfibs_len : fibs.length = n0 + m0 := by simp [fibs, rowFibs, colFibs]
    have heq := runGates_remap_getD_clean w1 w2 r C.gates.length C.gates (le_refl _)
      (by
        intro i hi
        rw [hw1_len] at hi
        have hri : r i = outs.getD i 0 := by simp [r, hi]
        rw [hri]
        have hev := buildFibers_eval (n + m) fibs (oneEach u v) (oneEach_length u v) hfibs_ne hfibs_lt
          i (by rw [hfibs_len]; exact hi)
        change w1.getD i false = (runGates (oneEach u v) bf.1).getD (bf.2.getD i 0) false
        rw [hev]
        by_cases hil : i < n0
        · rw [oneEach_getD_left (f u) (g v) i hil]
          have hget : fibs[i]'(by rw [hfibs_len]; exact hi) =
              ((List.finRange n).filter fun x => decide (f x = ⟨i, hil⟩)).map Fin.val := by
            simp [fibs, rowFibs, List.getElem_append_left, hil]
          rw [hget, List.any_map]
          apply Bool.eq_iff_iff.mpr
          simp only [decide_eq_true_eq, List.any_eq_true, List.mem_filter, List.mem_finRange,
            true_and, Function.comp_def]
          constructor
          · intro hfu
            refine ⟨u, hfu.symm, ?_⟩
            rw [oneEach_getD_left u v u.val u.isLt]
            simp
          · rintro ⟨x, hfx, hx⟩
            rw [oneEach_getD_left u v x.val x.isLt] at hx
            have hxu : x = u := by simpa using hx
            subst hxu
            exact hfx.symm
        · have hij : i - n0 < m0 := by omega
          have h1 : w1.getD i false = decide (⟨i - n0, hij⟩ = g v) := by
            have h2 := oneEach_getD_right (f u) (g v) (i - n0) hij
            have hi_eq : n0 + (i - n0) = i := by omega
            rwa [hi_eq] at h2
          rw [h1]
          have hget : fibs[i]'(by rw [hfibs_len]; exact hi) =
              ((List.finRange m).filter fun y => decide (g y = ⟨i - n0, hij⟩)).map (fun y => n + y.val) := by
            have hrl : rowFibs.length = n0 := by simp [rowFibs]
            simp only [fibs, List.getElem_append_right (by omega : rowFibs.length ≤ i), hrl]
            simp [colFibs]
          rw [hget, List.any_map]
          apply Bool.eq_iff_iff.mpr
          simp only [decide_eq_true_eq, List.any_eq_true, List.mem_filter, List.mem_finRange,
            true_and, Function.comp_def]
          constructor
          · intro hgv
            refine ⟨v, hgv.symm, ?_⟩
            rw [oneEach_getD_right u v v.val v.isLt]
            simp
          · rintro ⟨y, hgy, hy⟩
            rw [oneEach_getD_right u v y.val y.isLt] at hy
            have hyv : y = v := by simpa using hy
            subst hyv
            exact hgy.symm)
      (by
        intro i hi
        rw [hw1_len] at hi
        left
        have hri : r i = outs.getD i 0 := by simp [r, hi]
        rw [hri, hw2_len]
        exact buildFibers_out_lt (n + m) fibs hfibs_ne hfibs_lt i (by rw [hfibs_len]; exact hi))
      (by
        intro k hk
        rw [hw1_len, hw2_len]
        have h1 : ¬ (n0 + m0 + k < n0 + m0) := by omega
        have h2 : n0 + m0 + k < n0 + m0 + C.gates.length := by omega
        simp [r, h1, h2])
      (by
        intro i hi
        rw [hw1_len] at hi
        rw [hw2_len]
        have h1 : ¬ (i < n0 + m0) := by omega
        have h2 : ¬ (i < n0 + m0 + C.gates.length) := by omega
        simp [r, h1, h2])
      C.output
    rw [← heq]
    exact hCrep (f u) (g v)

private theorem part_b (n m n0 m0 t : ℕ) (Q : Fin n0 → Fin m0 → Bool)
    (f : Fin n → Fin n0) (g : Fin m → Fin m0)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hCex : ∃ C : Circuit, FanInTwo C ∧ C.size ≤ t ∧
      Represents (fun (u : Fin n) (v : Fin m) => Q (f u) (g v)) C) :
    ∃ C' : Circuit, FanInTwo C' ∧ C'.size ≤ t ∧ Represents Q C' := by
  classical
  rcases hCex with ⟨C, hCfan, hCsize, hCrep⟩
  let rf : Fin n0 → Fin n := Function.surjInv hf
  let rg : Fin m0 → Fin m := Function.surjInv hg
  have hrf : ∀ i : Fin n0, f (rf i) = i := Function.surjInv_eq hf
  have hrg : ∀ j : Fin m0, g (rg j) = j := Function.surjInv_eq hg
  have hrf_inj : Function.Injective rf := by
    intro a b hab
    have := congrArg f hab
    rwa [hrf a, hrf b] at this
  have hrg_inj : Function.Injective rg := by
    intro a b hab
    have := congrArg g hab
    rwa [hrg a, hrg b] at this
  let dead := n0 + m0 + C.gates.length
  let r : ℕ → ℕ := fun w =>
    if w < n then
      if h : ∃ i : Fin n0, (rf i).val = w then (Classical.choose h).val else dead
    else if w < n + m then
      if h : ∃ j : Fin m0, (rg j).val = w - n then n0 + (Classical.choose h).val else dead
    else if w < n + m + C.gates.length then
      n0 + m0 + (w - (n + m))
    else
      dead
  let C' : Circuit := ⟨C.gates.map (remapGate r), r C.output⟩
  refine ⟨C', ?_, ?_, ?_⟩
  · intro gt hgt
    rcases List.mem_map.mp hgt with ⟨gt0, hgt0, rfl⟩
    rcases hCfan gt0 hgt0 with ⟨hop, hlen⟩
    exact ⟨hop, by simp [remapGate, hlen]⟩
  · simp only [Circuit.size, C', List.length_map]
    exact hCsize
  · intro u0 v0
    change (runGates (oneEach u0 v0) (C.gates.map (remapGate r))).getD (r C.output) false = Q u0 v0
    set w1 := oneEach (rf u0) (rg v0)
    set w2 := oneEach u0 v0
    have hw1_len : w1.length = n + m := oneEach_length (rf u0) (rg v0)
    have hw2_len : w2.length = n0 + m0 := oneEach_length u0 v0
    have heq := runGates_remap_getD_clean w1 w2 r C.gates.length C.gates (le_refl _)
      (by
        intro i hi
        rw [hw1_len] at hi
        by_cases hil : i < n
        · rw [oneEach_getD_left (rf u0) (rg v0) i hil]
          by_cases hex : ∃ a : Fin n0, (rf a).val = i
          · have hri : r i = (Classical.choose hex).val := by simp [r, hil, hex]
            set a := Classical.choose hex
            have ha : (rf a).val = i := Classical.choose_spec hex
            rw [hri, oneEach_getD_left u0 v0 a.val a.isLt]
            apply Bool.eq_iff_iff.mpr
            simp only [decide_eq_true_eq]
            constructor
            · intro h1
              have h2 : rf a = rf u0 := Fin.ext (ha.trans (congrArg Fin.val h1))
              exact hrf_inj h2
            · intro h1
              subst h1
              exact Fin.ext ha.symm
          · have hri : r i = dead := by simp [r, hil, hex]
            rw [hri, getD_of_ge w2 dead false (by rw [hw2_len]; omega)]
            apply Bool.eq_iff_iff.mpr
            simp only [decide_eq_true_eq, Bool.false_eq_true, iff_false]
            intro h1
            exact hex ⟨u0, (congrArg Fin.val h1).symm⟩
        · have hij : i - n < m := by omega
          have h1 : w1.getD i false = decide (⟨i - n, hij⟩ = rg v0) := by
            have h2 := oneEach_getD_right (rf u0) (rg v0) (i - n) hij
            have hi_eq : n + (i - n) = i := by omega
            rwa [hi_eq] at h2
          rw [h1]
          by_cases hex : ∃ b : Fin m0, (rg b).val = i - n
          · have hri : r i = n0 + (Classical.choose hex).val := by simp [r, hil, hi, hex]
            set b := Classical.choose hex
            have hb : (rg b).val = i - n := Classical.choose_spec hex
            rw [hri, oneEach_getD_right u0 v0 b.val b.isLt]
            apply Bool.eq_iff_iff.mpr
            simp only [decide_eq_true_eq]
            constructor
            · intro h2
              have h3 : rg b = rg v0 := Fin.ext (hb.trans (congrArg Fin.val h2))
              exact hrg_inj h3
            · intro h2
              subst h2
              exact Fin.ext hb.symm
          · have hri : r i = dead := by simp [r, hil, hi, hex]
            rw [hri, getD_of_ge w2 dead false (by rw [hw2_len]; omega)]
            apply Bool.eq_iff_iff.mpr
            simp only [decide_eq_true_eq, Bool.false_eq_true, iff_false]
            intro h2
            exact hex ⟨v0, (congrArg Fin.val h2).symm⟩)
      (by
        intro i hi
        rw [hw1_len] at hi
        rw [hw2_len]
        by_cases hil : i < n
        · by_cases hex : ∃ a : Fin n0, (rf a).val = i
          · left; simp [r, hil, hex]; omega
          · right; simp [r, hil, hex, dead]
        · by_cases hex : ∃ b : Fin m0, (rg b).val = i - n
          · left; simp [r, hil, hi, hex]
          · right; simp [r, hil, hi, hex, dead])
      (by
        intro k hk
        rw [hw1_len, hw2_len]
        have h1 : ¬ (n + m + k < n) := by omega
        have h2 : ¬ (n + m + k < n + m) := by omega
        have h3 : n + m + k < n + m + C.gates.length := by omega
        simp [r, h1, h2, h3])
      (by
        intro i hi
        rw [hw1_len] at hi
        rw [hw2_len]
        have h1 : ¬ (i < n) := by omega
        have h2 : ¬ (i < n + m) := by omega
        have h3 : ¬ (i < n + m + C.gates.length) := by omega
        simp [r, h1, h2, h3, dead])
      C.output
    rw [← heq]
    have hrep := hCrep (rf u0) (rg v0)
    dsimp only at hrep
    rwa [hrf u0, hrg v0] at hrep

end PEqualNP.Outside.L_meta_25464_aux

theorem PEqualNP.Outside.L_meta_25464 : ∀ (n m n0 m0 s t : ℕ) (Q : Fin n0 → Fin m0 → Bool) (f : Fin n → Fin n0) (g : Fin m → Fin m0), Function.Surjective f → Function.Surjective g → (PEqualNP.Represents.RepSizeAtMost Q s → PEqualNP.Represents.RepSizeAtMost (fun (u : Fin n) (v : Fin m) => Q (f u) (g v)) (s + (n - n0) + (m - m0))) ∧ ((∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ t ∧ PEqualNP.Represents.Represents (fun (u : Fin n) (v : Fin m) => Q (f u) (g v)) C) → ∃ C' : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C' ∧ C'.size ≤ t ∧ PEqualNP.Represents.Represents Q C') := by
  intro n m n0 m0 s t Q f g hf hg
  exact ⟨PEqualNP.Outside.L_meta_25464_aux.part_a n m n0 m0 s Q f g hf hg,
    PEqualNP.Outside.L_meta_25464_aux.part_b n m n0 m0 t Q f g hf hg⟩
