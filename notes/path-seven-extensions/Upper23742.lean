import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.Upper23742 :
    PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (842943 : ℕ).testBit (6 * u.val + v.val)) 11 := by
  let C : Circuit := ⟨[
    ⟨.or, [1, 4]⟩,
    ⟨.or, [2, 5]⟩,
    ⟨.or, [3, 6]⟩,
    ⟨.or, [7, 10]⟩,
    ⟨.or, [8, 9]⟩,
    ⟨.or, [12, 13]⟩,
    ⟨.and, [11, 15]⟩,
    ⟨.or, [0, 16]⟩,
    ⟨.or, [3, 14]⟩,
    ⟨.and, [10, 18]⟩,
    ⟨.or, [17, 19]⟩], 20⟩
  refine ⟨C, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
