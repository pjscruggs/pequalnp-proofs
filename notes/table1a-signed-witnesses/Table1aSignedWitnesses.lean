import PEqualNP.Defs

namespace PEqualNP.Outside.Table1aSignedWitnesses

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def circuit20722 : Circuit :=
  ⟨[⟨.not, [9]⟩, ⟨.and, [3, 5]⟩, ⟨.and, [4, 10]⟩, ⟨.or, [11, 12]⟩], 13⟩

theorem signed20722 : ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 4 ∧
    Represents (fun u v : Fin 5 => (15761408 : ℕ).testBit (5 * u.val + v.val)) C := by
  refine ⟨circuit20722, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [circuit20722, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl <;> simp

def circuit20740 : Circuit :=
  ⟨[⟨.not, [2]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [5, 10]⟩, ⟨.or, [9, 11]⟩, ⟨.not, [13]⟩, ⟨.and, [12, 14]⟩], 15⟩

theorem signed20740 : ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 6 ∧
    Represents (fun u v : Fin 5 => (16221184 : ℕ).testBit (5 * u.val + v.val)) C := by
  refine ⟨circuit20740, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [circuit20740, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

def circuit20742 : Circuit :=
  ⟨[⟨.not, [0]⟩, ⟨.or, [1, 9]⟩, ⟨.and, [2, 8]⟩, ⟨.or, [11, 12]⟩, ⟨.not, [13]⟩, ⟨.and, [10, 14]⟩], 15⟩

theorem signed20742 : ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 6 ∧
    Represents (fun u v : Fin 5 => (16227328 : ℕ).testBit (5 * u.val + v.val)) C := by
  refine ⟨circuit20742, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [circuit20742, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

def circuit20777 : Circuit :=
  ⟨[⟨.and, [2, 5]⟩, ⟨.or, [3, 10]⟩, ⟨.or, [6, 5]⟩, ⟨.not, [12]⟩, ⟨.and, [4, 13]⟩, ⟨.and, [11, 12]⟩, ⟨.or, [14, 15]⟩], 16⟩

theorem signed20777 : ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 7 ∧
    Represents (fun u v : Fin 5 => (29459456 : ℕ).testBit (5 * u.val + v.val)) C := by
  refine ⟨circuit20777, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [circuit20777, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

def circuit20781 : Circuit :=
  ⟨[⟨.not, [5]⟩, ⟨.or, [2, 6]⟩, ⟨.or, [3, 5]⟩, ⟨.and, [4, 10]⟩, ⟨.or, [7, 11]⟩, ⟨.and, [12, 14]⟩, ⟨.or, [13, 15]⟩], 16⟩

theorem signed20781 : ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 7 ∧
    Represents (fun u v : Fin 5 => (31654912 : ℕ).testBit (5 * u.val + v.val)) C := by
  refine ⟨circuit20781, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [circuit20781, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.Table1aSignedWitnesses
