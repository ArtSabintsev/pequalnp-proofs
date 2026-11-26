import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22514 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1899769 : ℕ).testBit (6 * u.val + v.val)) 13 := by
  refine ⟨({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [12, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [10, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [11, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 18] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [17, 19] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [16, 20] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 21] }], output := 22 } : PEqualNP.CircuitLowerBounds.Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
