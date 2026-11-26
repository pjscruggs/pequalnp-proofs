import PEqualNP.Defs


namespace PEqualNP.Outside.Core20743Uppersigned

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.not, [8]⟩, ⟨.not, [9]⟩, ⟨.and, [3, 11]⟩, ⟨.and, [4, 10]⟩, ⟨.or, [12, 13]⟩], 14⟩

theorem upper : FanInTwo witness ∧ witness.size ≤ 5 ∧
    Represents (fun u v : Fin 5 => (24608768 : ℕ).testBit (5 * u.val + v.val)) witness := by
  refine ⟨?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.Core20743Uppersigned


namespace PEqualNP.Outside.Core20744Uppersigned

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [6, 7]⟩, ⟨.not, [10]⟩, ⟨.and, [4, 11]⟩, ⟨.or, [5, 10]⟩, ⟨.and, [3, 13]⟩, ⟨.or, [12, 14]⟩], 15⟩

theorem upper : FanInTwo witness ∧ witness.size ≤ 6 ∧
    Represents (fun u v : Fin 5 => (26443776 : ℕ).testBit (5 * u.val + v.val)) witness := by
  refine ⟨?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.Core20744Uppersigned


namespace PEqualNP.Outside.Core20745Uppersigned

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.not, [7]⟩, ⟨.and, [4, 10]⟩, ⟨.or, [5, 6]⟩, ⟨.or, [7, 12]⟩, ⟨.and, [3, 13]⟩, ⟨.or, [11, 14]⟩], 15⟩

theorem upper : FanInTwo witness ∧ witness.size ≤ 6 ∧
    Represents (fun u v : Fin 5 => (28540928 : ℕ).testBit (5 * u.val + v.val)) witness := by
  refine ⟨?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.Core20745Uppersigned


namespace PEqualNP.Outside.Core20746Uppersigned

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.not, [6]⟩, ⟨.and, [4, 10]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [3, 12]⟩, ⟨.or, [11, 13]⟩], 14⟩

theorem upper : FanInTwo witness ∧ witness.size ≤ 5 ∧
    Represents (fun u v : Fin 5 => (30507008 : ℕ).testBit (5 * u.val + v.val)) witness := by
  refine ⟨?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.Core20746Uppersigned


namespace PEqualNP.Outside.Core20775Uppersigned

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [2, 3]⟩, ⟨.or, [6, 7]⟩, ⟨.not, [11]⟩, ⟨.and, [4, 12]⟩, ⟨.or, [5, 11]⟩, ⟨.and, [10, 14]⟩, ⟨.or, [13, 15]⟩], 16⟩

theorem upper : FanInTwo witness ∧ witness.size ≤ 7 ∧
    Represents (fun u v : Fin 5 => (26450944 : ℕ).testBit (5 * u.val + v.val)) witness := by
  refine ⟨?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.Core20775Uppersigned


namespace PEqualNP.Outside.Core20779Uppersigned

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.not, [6]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [4, 10]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [11, 13]⟩, ⟨.or, [12, 14]⟩], 15⟩

theorem upper : FanInTwo witness ∧ witness.size ≤ 6 ∧
    Represents (fun u v : Fin 5 => (30510080 : ℕ).testBit (5 * u.val + v.val)) witness := by
  refine ⟨?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.Core20779Uppersigned


namespace PEqualNP.Outside.Core20780Uppersigned

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.not, [6]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [2, 12]⟩, ⟨.and, [10, 11]⟩, ⟨.or, [13, 14]⟩], 15⟩

theorem upper : FanInTwo witness ∧ witness.size ≤ 6 ∧
    Represents (fun u v : Fin 5 => (31362048 : ℕ).testBit (5 * u.val + v.val)) witness := by
  refine ⟨?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.Core20780Uppersigned


namespace PEqualNP.Outside.Core21237Uppersigned

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [4, 5]⟩, ⟨.or, [6, 7]⟩, ⟨.and, [3, 11]⟩, ⟨.or, [3, 11]⟩, ⟨.not, [13]⟩, ⟨.and, [10, 14]⟩, ⟨.or, [12, 15]⟩], 16⟩

theorem upper : FanInTwo witness ∧ witness.size ≤ 7 ∧
    Represents (fun u v : Fin 5 => (26412065 : ℕ).testBit (5 * u.val + v.val)) witness := by
  refine ⟨?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.Core21237Uppersigned


namespace PEqualNP.Outside.Core21238Uppersigned

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [2, 3]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [6, 7]⟩, ⟨.and, [10, 12]⟩, ⟨.or, [10, 12]⟩, ⟨.not, [14]⟩, ⟨.and, [11, 15]⟩, ⟨.or, [13, 16]⟩], 17⟩

theorem upper : FanInTwo witness ∧ witness.size ≤ 8 ∧
    Represents (fun u v : Fin 5 => (26417185 : ℕ).testBit (5 * u.val + v.val)) witness := by
  refine ⟨?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.Core21238Uppersigned


namespace PEqualNP.Outside.Core21242Uppersigned

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [0, 6]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [5, 11]⟩, ⟨.or, [7, 10]⟩, ⟨.and, [12, 13]⟩, ⟨.or, [11, 13]⟩, ⟨.not, [15]⟩, ⟨.or, [14, 16]⟩], 17⟩

theorem upper : FanInTwo witness ∧ witness.size ≤ 8 ∧
    Represents (fun u v : Fin 5 => (27039937 : ℕ).testBit (5 * u.val + v.val)) witness := by
  refine ⟨?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.Core21242Uppersigned


namespace PEqualNP.Outside.Core21248Uppersigned

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [2, 5]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [6, 5]⟩, ⟨.and, [10, 12]⟩, ⟨.or, [11, 13]⟩, ⟨.and, [12, 11]⟩, ⟨.not, [15]⟩, ⟨.and, [14, 16]⟩], 17⟩

theorem upper : FanInTwo witness ∧ witness.size ≤ 8 ∧
    Represents (fun u v : Fin 5 => (30280737 : ℕ).testBit (5 * u.val + v.val)) witness := by
  refine ⟨?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.Core21248Uppersigned


namespace PEqualNP.Outside.Core21250Uppersigned

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.not, [0]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [6, 10]⟩, ⟨.or, [5, 12]⟩, ⟨.and, [11, 13]⟩, ⟨.not, [14]⟩, ⟨.or, [11, 13]⟩, ⟨.and, [15, 16]⟩], 17⟩

theorem upper : FanInTwo witness ∧ witness.size ≤ 8 ∧
    Represents (fun u v : Fin 5 => (30280801 : ℕ).testBit (5 * u.val + v.val)) witness := by
  refine ⟨?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.Core21250Uppersigned


namespace PEqualNP.Outside.Core21251Uppersigned

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.not, [0]⟩, ⟨.or, [1, 0]⟩, ⟨.and, [6, 10]⟩, ⟨.or, [5, 12]⟩, ⟨.and, [11, 13]⟩, ⟨.or, [11, 13]⟩, ⟨.not, [15]⟩, ⟨.or, [14, 16]⟩], 17⟩

theorem upper : FanInTwo witness ∧ witness.size ≤ 8 ∧
    Represents (fun u v : Fin 5 => (30306401 : ℕ).testBit (5 * u.val + v.val)) witness := by
  refine ⟨?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.Core21251Uppersigned


namespace PEqualNP.Outside.Core21262Uppersigned

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.and, [3, 6]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [3, 6]⟩, ⟨.not, [12]⟩, ⟨.and, [11, 13]⟩, ⟨.or, [10, 14]⟩], 15⟩

theorem upper : FanInTwo witness ∧ witness.size ≤ 6 ∧
    Represents (fun u v : Fin 5 => (30475297 : ℕ).testBit (5 * u.val + v.val)) witness := by
  refine ⟨?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.Core21262Uppersigned


namespace PEqualNP.Outside.Core21265Uppersigned

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [0, 1]⟩, ⟨.or, [2, 5]⟩, ⟨.or, [6, 10]⟩, ⟨.and, [11, 12]⟩, ⟨.or, [2, 12]⟩, ⟨.not, [14]⟩, ⟨.or, [13, 15]⟩], 16⟩

theorem upper : FanInTwo witness ∧ witness.size ≤ 7 ∧
    Represents (fun u v : Fin 5 => (31361057 : ℕ).testBit (5 * u.val + v.val)) witness := by
  refine ⟨?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.Core21265Uppersigned


namespace PEqualNP.Outside.Core21266Uppersigned

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [0, 6]⟩, ⟨.or, [1, 5]⟩, ⟨.and, [10, 11]⟩, ⟨.or, [1, 10]⟩, ⟨.not, [13]⟩, ⟨.or, [12, 14]⟩], 15⟩

theorem upper : FanInTwo witness ∧ witness.size ≤ 6 ∧
    Represents (fun u v : Fin 5 => (31388737 : ℕ).testBit (5 * u.val + v.val)) witness := by
  refine ⟨?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.Core21266Uppersigned


namespace PEqualNP.Outside.Core21267Uppersigned

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [3, 4]⟩, ⟨.and, [5, 10]⟩, ⟨.or, [3, 11]⟩, ⟨.not, [12]⟩, ⟨.or, [6, 13]⟩, ⟨.or, [5, 10]⟩, ⟨.and, [14, 15]⟩], 16⟩

theorem upper : FanInTwo witness ∧ witness.size ≤ 7 ∧
    Represents (fun u v : Fin 5 => (31523873 : ℕ).testBit (5 * u.val + v.val)) witness := by
  refine ⟨?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.Core21267Uppersigned


namespace PEqualNP.Outside.Core21268Uppersigned

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [3, 4]⟩, ⟨.and, [5, 10]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [3, 11]⟩, ⟨.not, [13]⟩, ⟨.or, [5, 10]⟩, ⟨.or, [12, 14]⟩, ⟨.and, [15, 16]⟩], 17⟩

theorem upper : FanInTwo witness ∧ witness.size ≤ 8 ∧
    Represents (fun u v : Fin 5 => (31654945 : ℕ).testBit (5 * u.val + v.val)) witness := by
  refine ⟨?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.Core21268Uppersigned


namespace PEqualNP.Outside.Core21269Uppersigned

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [0, 1]⟩, ⟨.or, [4, 6]⟩, ⟨.and, [5, 10]⟩, ⟨.or, [7, 11]⟩, ⟨.or, [5, 10]⟩, ⟨.not, [14]⟩, ⟨.and, [13, 15]⟩, ⟨.or, [12, 16]⟩], 17⟩

theorem upper : FanInTwo witness ∧ witness.size ≤ 8 ∧
    Represents (fun u v : Fin 5 => (31660065 : ℕ).testBit (5 * u.val + v.val)) witness := by
  refine ⟨?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.Core21269Uppersigned


namespace PEqualNP.Outside.Core21270Uppersigned

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.not, [9]⟩, ⟨.and, [3, 10]⟩, ⟨.or, [4, 11]⟩, ⟨.and, [5, 12]⟩, ⟨.not, [13]⟩, ⟨.or, [5, 12]⟩, ⟨.and, [14, 15]⟩], 16⟩

theorem upper : FanInTwo witness ∧ witness.size ≤ 7 ∧
    Represents (fun u v : Fin 5 => (31917089 : ℕ).testBit (5 * u.val + v.val)) witness := by
  refine ⟨?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.Core21270Uppersigned


namespace PEqualNP.Outside.Core21271Uppersigned

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [0, 1]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [9, 10]⟩, ⟨.and, [11, 12]⟩, ⟨.or, [5, 12]⟩, ⟨.not, [14]⟩, ⟨.or, [13, 15]⟩], 16⟩

theorem upper : FanInTwo witness ∧ witness.size ≤ 7 ∧
    Represents (fun u v : Fin 5 => (31930401 : ℕ).testBit (5 * u.val + v.val)) witness := by
  refine ⟨?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.Core21271Uppersigned


namespace PEqualNP.Outside.Core21285Uppersigned

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [0, 1]⟩, ⟨.or, [2, 5]⟩, ⟨.or, [6, 10]⟩, ⟨.and, [11, 12]⟩, ⟨.or, [10, 11]⟩, ⟨.not, [14]⟩, ⟨.or, [13, 15]⟩], 16⟩

theorem upper : FanInTwo witness ∧ witness.size ≤ 7 ∧
    Represents (fun u v : Fin 5 => (32442401 : ℕ).testBit (5 * u.val + v.val)) witness := by
  refine ⟨?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.Core21285Uppersigned
