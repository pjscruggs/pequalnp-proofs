import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.Upper23799 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (283359 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  let C : Circuit := ⟨[
    ⟨.or, [1, 2]⟩, ⟨.or, [0, 5]⟩, ⟨.not, [6]⟩, ⟨.and, [4, 7]⟩,
    ⟨.and, [3, 5]⟩, ⟨.or, [8, 9]⟩, ⟨.not, [10]⟩], 11⟩
  refine ⟨C, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
