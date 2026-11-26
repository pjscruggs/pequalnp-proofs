import PEqualNP.Defs

namespace Mask842943

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def adjacency (u : Fin 4) (v : Fin 6) : Bool := (842943 : ℕ).testBit (6 * u.val + v.val)

def signedCircuit : Circuit :=
  ⟨[⟨.or, [5, 8]⟩,
    ⟨.or, [10, 9]⟩,
    ⟨.not, [11]⟩,
    ⟨.or, [4, 5]⟩,
    ⟨.and, [1, 11]⟩,
    ⟨.and, [2, 12]⟩,
    ⟨.and, [3, 13]⟩,
    ⟨.or, [0, 14]⟩,
    ⟨.or, [17, 15]⟩,
    ⟨.or, [18, 16]⟩], 19⟩

theorem signedUpper : ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 10 ∧ Represents adjacency C := by
  refine ⟨signedCircuit, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [signedCircuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end Mask842943
