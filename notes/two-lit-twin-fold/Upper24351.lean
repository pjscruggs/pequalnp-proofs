import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

namespace PEqualNP.Outside.Upper24351

def witness : Circuit :=
  ⟨[⟨.not, [0]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [3, 4]⟩, ⟨.and, [5, 6]⟩,
    ⟨.and, [0, 7]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [10, 11]⟩, ⟨.not, [12]⟩], 13⟩

end PEqualNP.Outside.Upper24351

theorem PEqualNP.Outside.Upper24351 :
    ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 8 ∧
      ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
        (270649273 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.Upper24351.witness, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [PEqualNP.Outside.Upper24351.witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
