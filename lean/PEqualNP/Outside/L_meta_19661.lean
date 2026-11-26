import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_19661 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (16236582 : ℕ).testBit (5 * u.val + v.val)) C := by
  refine ⟨({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [5, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [13, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [16] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [15, 18] }], output := 19 } : PEqualNP.CircuitLowerBounds.Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
