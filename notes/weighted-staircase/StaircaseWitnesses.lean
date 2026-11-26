import PEqualNP.Defs


namespace PEqualNP.Outside.Staircase20718Uppersigned

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.and, [2, 5]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [5, 12]⟩, ⟨.and, [13, 14]⟩], 15⟩

theorem upper : FanInTwo witness ∧ witness.size ≤ 6 ∧
    Represents (fun u v : Fin 5 => (7570432 : ℕ).testBit (5 * u.val + v.val)) witness := by
  refine ⟨?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.Staircase20718Uppersigned


namespace PEqualNP.Outside.Staircase20719Uppersigned

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [3, 4]⟩, ⟨.or, [2, 10]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [7, 10]⟩, ⟨.and, [11, 12]⟩, ⟨.or, [13, 14]⟩], 15⟩

theorem upper : FanInTwo witness ∧ witness.size ≤ 6 ∧
    Represents (fun u v : Fin 5 => (7572480 : ℕ).testBit (5 * u.val + v.val)) witness := by
  refine ⟨?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.Staircase20719Uppersigned


namespace PEqualNP.Outside.Staircase20723Uppersigned

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.not, [9]⟩, ⟨.and, [4, 10]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [3, 12]⟩, ⟨.or, [11, 13]⟩], 14⟩

theorem upper : FanInTwo witness ∧ witness.size ≤ 5 ∧
    Represents (fun u v : Fin 5 => (15826944 : ℕ).testBit (5 * u.val + v.val)) witness := by
  refine ⟨?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.Staircase20723Uppersigned


namespace PEqualNP.Outside.Staircase20724Uppersigned

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.not, [8]⟩, ⟨.not, [9]⟩, ⟨.and, [3, 10]⟩, ⟨.or, [4, 12]⟩, ⟨.and, [11, 13]⟩], 14⟩

theorem upper : FanInTwo witness ∧ witness.size ≤ 5 ∧
    Represents (fun u v : Fin 5 => (15958016 : ℕ).testBit (5 * u.val + v.val)) witness := by
  refine ⟨?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.Staircase20724Uppersigned


namespace PEqualNP.Outside.Staircase20735Uppersigned

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [0, 1]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [9, 10]⟩, ⟨.not, [12]⟩, ⟨.and, [11, 13]⟩], 14⟩

theorem upper : FanInTwo witness ∧ witness.size ≤ 5 ∧
    Represents (fun u v : Fin 5 => (15762432 : ℕ).testBit (5 * u.val + v.val)) witness := by
  refine ⟨?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.Staircase20735Uppersigned


namespace PEqualNP.Outside.Staircase20736Uppersigned

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [0, 1]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [6, 11]⟩, ⟨.or, [9, 10]⟩, ⟨.not, [13]⟩, ⟨.and, [12, 14]⟩], 15⟩

theorem upper : FanInTwo witness ∧ witness.size ≤ 6 ∧
    Represents (fun u v : Fin 5 => (15830016 : ℕ).testBit (5 * u.val + v.val)) witness := by
  refine ⟨?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.Staircase20736Uppersigned


namespace PEqualNP.Outside.Staircase20737Uppersigned

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [0, 1]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [8, 11]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [12, 13]⟩, ⟨.not, [14]⟩], 15⟩

theorem upper : FanInTwo witness ∧ witness.size ≤ 6 ∧
    Represents (fun u v : Fin 5 => (15965184 : ℕ).testBit (5 * u.val + v.val)) witness := by
  refine ⟨?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.Staircase20737Uppersigned


namespace PEqualNP.Outside.Staircase20740Uppersigned

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.not, [9]⟩, ⟨.and, [2, 5]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [10, 12]⟩, ⟨.or, [11, 13]⟩], 14⟩

theorem upper : FanInTwo witness ∧ witness.size ≤ 5 ∧
    Represents (fun u v : Fin 5 => (16221184 : ℕ).testBit (5 * u.val + v.val)) witness := by
  refine ⟨?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.Staircase20740Uppersigned


namespace PEqualNP.Outside.Staircase20741Uppersigned

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.not, [9]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [2, 12]⟩, ⟨.and, [10, 11]⟩, ⟨.or, [13, 14]⟩], 15⟩

theorem upper : FanInTwo witness ∧ witness.size ≤ 6 ∧
    Represents (fun u v : Fin 5 => (16223232 : ℕ).testBit (5 * u.val + v.val)) witness := by
  refine ⟨?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.Staircase20741Uppersigned


namespace PEqualNP.Outside.Staircase20742Uppersigned

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [0, 1]⟩, ⟨.and, [2, 8]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [11, 12]⟩, ⟨.not, [13]⟩], 14⟩

theorem upper : FanInTwo witness ∧ witness.size ≤ 5 ∧
    Represents (fun u v : Fin 5 => (16227328 : ℕ).testBit (5 * u.val + v.val)) witness := by
  refine ⟨?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.Staircase20742Uppersigned


namespace PEqualNP.Outside.Staircase20764Uppersigned

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [0, 9]⟩, ⟨.not, [10]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [11, 12]⟩], 13⟩

theorem upper : FanInTwo witness ∧ witness.size ≤ 4 ∧
    Represents (fun u v : Fin 5 => (15762464 : ℕ).testBit (5 * u.val + v.val)) witness := by
  refine ⟨?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.Staircase20764Uppersigned


namespace PEqualNP.Outside.Staircase20770Uppersigned

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [0, 9]⟩, ⟨.not, [10]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [5, 12]⟩, ⟨.and, [11, 13]⟩], 14⟩

theorem upper : FanInTwo witness ∧ witness.size ≤ 5 ∧
    Represents (fun u v : Fin 5 => (16221216 : ℕ).testBit (5 * u.val + v.val)) witness := by
  refine ⟨?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.Staircase20770Uppersigned


namespace PEqualNP.Outside.Staircase20771Uppersigned

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.not, [0]⟩, ⟨.or, [1, 9]⟩, ⟨.not, [11]⟩, ⟨.or, [5, 12]⟩, ⟨.and, [10, 13]⟩], 14⟩

theorem upper : FanInTwo witness ∧ witness.size ≤ 5 ∧
    Represents (fun u v : Fin 5 => (16235552 : ℕ).testBit (5 * u.val + v.val)) witness := by
  refine ⟨?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.Staircase20771Uppersigned
