import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.Upper21076 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (106429 : ℕ).testBit (5 * u.val + v.val)) 10 := by
  let C : Circuit := ⟨[⟨.or, [0, 1]⟩, ⟨.or, [2, 3]⟩, ⟨.or, [5, 9]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [8, 10]⟩, ⟨.and, [2, 6]⟩, ⟨.or, [4, 14]⟩, ⟨.or, [12, 13]⟩, ⟨.and, [11, 16]⟩, ⟨.or, [15, 17]⟩], 18⟩
  refine ⟨C, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
