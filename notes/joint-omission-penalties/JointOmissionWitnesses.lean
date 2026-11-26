import PEqualNP.Defs


namespace PEqualNP.Outside.Omission21240Uppersigned

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [0, 6]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [5, 11]⟩, ⟨.or, [7, 10]⟩, ⟨.or, [4, 13]⟩, ⟨.and, [12, 14]⟩, ⟨.or, [13, 12]⟩, ⟨.not, [16]⟩, ⟨.or, [15, 17]⟩], 18⟩

theorem upper : FanInTwo witness ∧ witness.size ≤ 9 ∧
    Represents (fun u v : Fin 5 => (27007169 : ℕ).testBit (5 * u.val + v.val)) witness := by
  refine ⟨?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.Omission21240Uppersigned


namespace PEqualNP.Outside.Omission21249Uppersigned

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [0, 2]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [6, 10]⟩, ⟨.and, [2, 6]⟩, ⟨.and, [11, 12]⟩, ⟨.or, [13, 14]⟩, ⟨.or, [11, 12]⟩, ⟨.not, [16]⟩, ⟨.or, [15, 17]⟩], 18⟩

theorem upper : FanInTwo witness ∧ witness.size ≤ 9 ∧
    Represents (fun u v : Fin 5 => (30280769 : ℕ).testBit (5 * u.val + v.val)) witness := by
  refine ⟨?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.Omission21249Uppersigned


namespace PEqualNP.Outside.Omission21263Uppersigned

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [0, 1]⟩, ⟨.or, [2, 5]⟩, ⟨.or, [6, 10]⟩, ⟨.or, [4, 12]⟩, ⟨.and, [11, 13]⟩, ⟨.or, [12, 11]⟩, ⟨.not, [15]⟩, ⟨.or, [14, 16]⟩], 17⟩

theorem upper : FanInTwo witness ∧ witness.size ≤ 8 ∧
    Represents (fun u v : Fin 5 => (31328289 : ℕ).testBit (5 * u.val + v.val)) witness := by
  refine ⟨?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.Omission21263Uppersigned


namespace PEqualNP.Outside.Omission21264Uppersigned

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [0, 6]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [4, 10]⟩, ⟨.and, [11, 12]⟩, ⟨.or, [10, 11]⟩, ⟨.not, [14]⟩, ⟨.or, [13, 15]⟩], 16⟩

theorem upper : FanInTwo witness ∧ witness.size ≤ 7 ∧
    Represents (fun u v : Fin 5 => (31354945 : ℕ).testBit (5 * u.val + v.val)) witness := by
  refine ⟨?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.Omission21264Uppersigned


namespace PEqualNP.Outside.Omission21282Uppersigned

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [0, 1]⟩, ⟨.or, [2, 5]⟩, ⟨.or, [4, 11]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [10, 13]⟩, ⟨.and, [12, 14]⟩, ⟨.or, [11, 14]⟩, ⟨.not, [16]⟩, ⟨.or, [15, 17]⟩], 18⟩

theorem upper : FanInTwo witness ∧ witness.size ≤ 9 ∧
    Represents (fun u v : Fin 5 => (32249889 : ℕ).testBit (5 * u.val + v.val)) witness := by
  refine ⟨?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.Omission21282Uppersigned


namespace PEqualNP.Outside.Omission21283Uppersigned

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [0, 8]⟩, ⟨.or, [3, 5]⟩, ⟨.or, [4, 11]⟩, ⟨.or, [9, 10]⟩, ⟨.and, [12, 13]⟩, ⟨.or, [11, 13]⟩, ⟨.not, [15]⟩, ⟨.or, [14, 16]⟩], 17⟩

theorem upper : FanInTwo witness ∧ witness.size ≤ 8 ∧
    Represents (fun u v : Fin 5 => (32250049 : ℕ).testBit (5 * u.val + v.val)) witness := by
  refine ⟨?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.Omission21283Uppersigned


namespace PEqualNP.Outside.Omission21284Uppersigned

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [0, 1]⟩, ⟨.or, [2, 5]⟩, ⟨.or, [4, 11]⟩, ⟨.or, [6, 10]⟩, ⟨.and, [12, 13]⟩, ⟨.or, [11, 13]⟩, ⟨.not, [15]⟩, ⟨.or, [14, 16]⟩], 17⟩

theorem upper : FanInTwo witness ∧ witness.size ≤ 8 ∧
    Represents (fun u v : Fin 5 => (32376865 : ℕ).testBit (5 * u.val + v.val)) witness := by
  refine ⟨?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.Omission21284Uppersigned
