import PEqualNP.Defs

namespace PEqualNP.Outside.Upper23659
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [0, 4]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [3, 6]⟩, ⟨.or, [5, 10]⟩, ⟨.and, [7, 11]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [1, 10]⟩, ⟨.or, [12, 14]⟩, ⟨.or, [11, 15]⟩, ⟨.and, [13, 18]⟩, ⟨.and, [16, 17]⟩, ⟨.or, [19, 20]⟩], 21⟩

theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
end PEqualNP.Outside.Upper23659

theorem PEqualNP.Outside.Upper23659 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (275444 : ℕ).testBit (6 * u.val + v.val)) 12 := by
  exact ⟨PEqualNP.Outside.Upper23659.witness, PEqualNP.Outside.Upper23659.mono, by decide, by decide +kernel⟩
