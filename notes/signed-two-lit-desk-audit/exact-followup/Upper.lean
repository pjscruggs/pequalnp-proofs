import PEqualNP.Defs

namespace SignedTwoLitFollowup

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit22742 : Circuit := ⟨[⟨.and, [2, 1]⟩, ⟨.or, [6, 0]⟩, ⟨.or, [4, 3]⟩, ⟨.or, [5, 8]⟩, ⟨.not, [9]⟩, ⟨.and, [10, 7]⟩], 11⟩

theorem upper22742 : FanInTwo circuit22742 ∧ circuit22742.size ≤ 6 ∧
    ∀ i j : Fin 6, circuit22742.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
      (263 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [circuit22742, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

def circuit22745 : Circuit := ⟨[⟨.or, [1, 0]⟩, ⟨.and, [2, 6]⟩, ⟨.or, [3, 1]⟩, ⟨.or, [4, 8]⟩, ⟨.and, [9, 0]⟩, ⟨.or, [7, 10]⟩], 11⟩

theorem upper22745 : FanInTwo circuit22745 ∧ circuit22745.size ≤ 6 ∧
    ∀ i j : Fin 6, circuit22745.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
      (286 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [circuit22745, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

def circuit22748 : Circuit := ⟨[⟨.or, [4, 3]⟩, ⟨.and, [6, 0]⟩, ⟨.or, [5, 6]⟩, ⟨.not, [8]⟩, ⟨.and, [9, 1]⟩, ⟨.or, [10, 7]⟩], 11⟩

theorem upper22748 : FanInTwo circuit22748 ∧ circuit22748.size ≤ 6 ∧
    ∀ i j : Fin 6, circuit22748.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
      (410 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [circuit22748, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

def circuit22761 : Circuit := ⟨[⟨.or, [3, 2]⟩, ⟨.and, [6, 1]⟩, ⟨.or, [7, 0]⟩, ⟨.or, [5, 4]⟩, ⟨.not, [9]⟩, ⟨.and, [10, 8]⟩], 11⟩

theorem upper22761 : FanInTwo circuit22761 ∧ circuit22761.size ≤ 6 ∧
    ∀ i j : Fin 6, circuit22761.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
      (783 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [circuit22761, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

def circuit22763 : Circuit := ⟨[⟨.or, [3, 2]⟩, ⟨.and, [6, 1]⟩, ⟨.or, [5, 3]⟩, ⟨.not, [8]⟩, ⟨.and, [9, 0]⟩, ⟨.or, [7, 10]⟩], 11⟩

theorem upper22763 : FanInTwo circuit22763 ∧ circuit22763.size ≤ 6 ∧
    ∀ i j : Fin 6, circuit22763.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
      (791 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [circuit22763, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

def circuit22767 : Circuit := ⟨[⟨.or, [1, 3]⟩, ⟨.not, [6]⟩, ⟨.and, [0, 7]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [1, 9]⟩, ⟨.or, [8, 10]⟩], 11⟩

theorem upper22767 : FanInTwo circuit22767 ∧ circuit22767.size ≤ 6 ∧
    ∀ i j : Fin 6, circuit22767.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
      (821 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [circuit22767, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

def circuit22781 : Circuit := ⟨[⟨.or, [3, 2]⟩, ⟨.or, [4, 6]⟩, ⟨.and, [7, 1]⟩, ⟨.or, [8, 0]⟩, ⟨.not, [5]⟩, ⟨.and, [10, 9]⟩], 11⟩

theorem upper22781 : FanInTwo circuit22781 ∧ circuit22781.size ≤ 6 ∧
    ∀ i j : Fin 6, circuit22781.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
      (1823 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [circuit22781, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

def circuit22783 : Circuit := ⟨[⟨.or, [3, 2]⟩, ⟨.or, [4, 6]⟩, ⟨.and, [7, 1]⟩, ⟨.not, [4]⟩, ⟨.and, [9, 0]⟩, ⟨.or, [8, 10]⟩], 11⟩

theorem upper22783 : FanInTwo circuit22783 ∧ circuit22783.size ≤ 6 ∧
    ∀ i j : Fin 6, circuit22783.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
      (1839 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [circuit22783, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

def circuit22785 : Circuit := ⟨[⟨.or, [1, 0]⟩, ⟨.or, [3, 2]⟩, ⟨.or, [4, 7]⟩, ⟨.not, [1]⟩, ⟨.or, [9, 8]⟩, ⟨.and, [10, 6]⟩], 11⟩

theorem upper22785 : FanInTwo circuit22785 ∧ circuit22785.size ≤ 6 ∧
    ∀ i j : Fin 6, circuit22785.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
      (1853 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [circuit22785, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

def circuit22787 : Circuit := ⟨[⟨.or, [1, 0]⟩, ⟨.and, [2, 6]⟩, ⟨.or, [3, 7]⟩, ⟨.or, [4, 8]⟩, ⟨.or, [5, 9]⟩, ⟨.not, [10]⟩], 11⟩

theorem upper22787 : FanInTwo circuit22787 ∧ circuit22787.size ≤ 6 ∧
    ∀ i j : Fin 6, circuit22787.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
      (16515 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [circuit22787, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

def circuit22799 : Circuit := ⟨[⟨.or, [1, 0]⟩, ⟨.and, [3, 6]⟩, ⟨.or, [4, 3]⟩, ⟨.or, [5, 8]⟩, ⟨.not, [9]⟩, ⟨.or, [10, 7]⟩], 11⟩

theorem upper22799 : FanInTwo circuit22799 ∧ circuit22799.size ≤ 6 ∧
    ∀ i j : Fin 6, circuit22799.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
      (17295 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [circuit22799, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

def circuit22801 : Circuit := ⟨[⟨.and, [2, 1]⟩, ⟨.or, [2, 1]⟩, ⟨.or, [3, 6]⟩, ⟨.and, [8, 7]⟩, ⟨.and, [4, 0]⟩, ⟨.or, [9, 10]⟩], 11⟩

theorem upper22801 : FanInTwo circuit22801 ∧ circuit22801.size ≤ 6 ∧
    ∀ i j : Fin 6, circuit22801.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
      (33552 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [circuit22801, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

def circuit22803 : Circuit := ⟨[⟨.and, [3, 2]⟩, ⟨.or, [6, 0]⟩, ⟨.and, [4, 1]⟩, ⟨.or, [7, 8]⟩, ⟨.not, [5]⟩, ⟨.and, [10, 9]⟩], 11⟩

theorem upper22803 : FanInTwo circuit22803 ∧ circuit22803.size ≤ 6 ∧
    ∀ i j : Fin 6, circuit22803.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
      (33823 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [circuit22803, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

def circuit22806 : Circuit := ⟨[⟨.or, [3, 5]⟩, ⟨.not, [6]⟩, ⟨.and, [1, 7]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [0, 8]⟩, ⟨.or, [9, 10]⟩], 11⟩

theorem upper22806 : FanInTwo circuit22806 ∧ circuit22806.size ≤ 6 ∧
    ∀ i j : Fin 6, circuit22806.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
      (34239 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [circuit22806, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

def circuit22810 : Circuit := ⟨[⟨.and, [3, 2]⟩, ⟨.or, [6, 0]⟩, ⟨.or, [3, 2]⟩, ⟨.not, [8]⟩, ⟨.and, [9, 1]⟩, ⟨.or, [7, 10]⟩], 11⟩

theorem upper22810 : FanInTwo circuit22810 ∧ circuit22810.size ≤ 6 ∧
    ∀ i j : Fin 6, circuit22810.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
      (36031 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [circuit22810, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

def circuit22815 : Circuit := ⟨[⟨.or, [4, 3]⟩, ⟨.and, [6, 2]⟩, ⟨.or, [7, 0]⟩, ⟨.not, [5]⟩, ⟨.and, [9, 1]⟩, ⟨.or, [8, 10]⟩], 11⟩

theorem upper22815 : FanInTwo circuit22815 ∧ circuit22815.size ≤ 6 ∧
    ∀ i j : Fin 6, circuit22815.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
      (100287 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [circuit22815, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

def circuit22819 : Circuit := ⟨[⟨.or, [2, 1]⟩, ⟨.or, [4, 3]⟩, ⟨.not, [2]⟩, ⟨.or, [8, 7]⟩, ⟨.and, [9, 6]⟩, ⟨.or, [10, 0]⟩], 11⟩

theorem upper22819 : FanInTwo circuit22819 ∧ circuit22819.size ≤ 6 ∧
    ∀ i j : Fin 6, circuit22819.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
      (102079 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [circuit22819, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

def circuit22821 : Circuit := ⟨[⟨.not, [4]⟩, ⟨.and, [6, 1]⟩, ⟨.or, [7, 0]⟩, ⟨.not, [5]⟩, ⟨.and, [9, 2]⟩, ⟨.or, [10, 8]⟩], 11⟩

theorem upper22821 : FanInTwo circuit22821 ∧ circuit22821.size ≤ 6 ∧
    ∀ i j : Fin 6, circuit22821.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
      (117695 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [circuit22821, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

def circuit22824 : Circuit := ⟨[⟨.or, [1, 0]⟩, ⟨.or, [2, 6]⟩, ⟨.and, [3, 7]⟩, ⟨.or, [4, 8]⟩, ⟨.or, [5, 9]⟩, ⟨.not, [10]⟩], 11⟩

theorem upper22824 : FanInTwo circuit22824 ∧ circuit22824.size ≤ 6 ∧
    ∀ i j : Fin 6, circuit22824.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
      (2113927 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [circuit22824, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

def circuit22826 : Circuit := ⟨[⟨.and, [3, 2]⟩, ⟨.and, [4, 0]⟩, ⟨.or, [4, 6]⟩, ⟨.or, [5, 8]⟩, ⟨.not, [9]⟩, ⟨.or, [10, 7]⟩], 11⟩

theorem upper22826 : FanInTwo circuit22826 ∧ circuit22826.size ≤ 6 ∧
    ∀ i j : Fin 6, circuit22826.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
      (2114463 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [circuit22826, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

def circuit22827 : Circuit := ⟨[⟨.and, [3, 0]⟩, ⟨.or, [4, 6]⟩, ⟨.and, [4, 0]⟩, ⟨.or, [5, 7]⟩, ⟨.not, [9]⟩, ⟨.or, [10, 8]⟩], 11⟩

theorem upper22827 : FanInTwo circuit22827 ∧ circuit22827.size ≤ 6 ∧
    ∀ i j : Fin 6, circuit22827.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
      (2147223 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [circuit22827, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

def circuit22840 : Circuit := ⟨[⟨.or, [1, 0]⟩, ⟨.or, [2, 6]⟩, ⟨.and, [4, 7]⟩, ⟨.or, [5, 4]⟩, ⟨.not, [9]⟩, ⟨.or, [10, 8]⟩], 11⟩

theorem upper22840 : FanInTwo circuit22840 ∧ circuit22840.size ≤ 6 ∧
    ∀ i j : Fin 6, circuit22840.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
      (2213791 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [circuit22840, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

def circuit22843 : Circuit := ⟨[⟨.or, [1, 0]⟩, ⟨.and, [4, 3]⟩, ⟨.or, [7, 6]⟩, ⟨.not, [5]⟩, ⟨.and, [9, 2]⟩, ⟨.or, [8, 10]⟩], 11⟩

theorem upper22843 : FanInTwo circuit22843 ∧ circuit22843.size ≤ 6 ∧
    ∀ i j : Fin 6, circuit22843.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
      (4313023 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [circuit22843, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

def circuit22845 : Circuit := ⟨[⟨.or, [1, 0]⟩, ⟨.or, [4, 2]⟩, ⟨.not, [4]⟩, ⟨.or, [8, 3]⟩, ⟨.and, [9, 7]⟩, ⟨.or, [10, 6]⟩], 11⟩

theorem upper22845 : FanInTwo circuit22845 ∧ circuit22845.size ≤ 6 ∧
    ∀ i j : Fin 6, circuit22845.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
      (4378559 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [circuit22845, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

def circuit22863 : Circuit := ⟨[⟨.or, [3, 0]⟩, ⟨.and, [4, 6]⟩, ⟨.and, [5, 0]⟩, ⟨.or, [5, 7]⟩, ⟨.not, [9]⟩, ⟨.or, [10, 8]⟩], 11⟩

theorem upper22863 : FanInTwo circuit22863 ∧ circuit22863.size ≤ 6 ∧
    ∀ i j : Fin 6, circuit22863.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
      (270649263 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [circuit22863, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

def circuit22867 : Circuit := ⟨[⟨.or, [1, 0]⟩, ⟨.and, [4, 6]⟩, ⟨.or, [5, 7]⟩, ⟨.and, [5, 6]⟩, ⟨.not, [8]⟩, ⟨.or, [10, 9]⟩], 11⟩

theorem upper22867 : FanInTwo circuit22867 ∧ circuit22867.size ≤ 6 ∧
    ∀ i j : Fin 6, circuit22867.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
      (274844591 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [circuit22867, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

def circuit22868 : Circuit := ⟨[⟨.or, [1, 0]⟩, ⟨.and, [4, 1]⟩, ⟨.or, [5, 7]⟩, ⟨.and, [5, 6]⟩, ⟨.not, [8]⟩, ⟨.or, [10, 9]⟩], 11⟩

theorem upper22868 : FanInTwo circuit22868 ∧ circuit22868.size ≤ 6 ∧
    ∀ i j : Fin 6, circuit22868.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
      (274844607 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [circuit22868, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

def circuit22880 : Circuit := ⟨[⟨.and, [1, 0]⟩, ⟨.or, [1, 0]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [5, 7]⟩, ⟨.not, [8]⟩, ⟨.or, [10, 9]⟩], 11⟩

theorem upper22880 : FanInTwo circuit22880 ∧ circuit22880.size ≤ 6 ∧
    ∀ i j : Fin 6, circuit22880.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
      (274845629 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [circuit22880, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

def circuit22882 : Circuit := ⟨[⟨.or, [3, 2]⟩, ⟨.and, [4, 6]⟩, ⟨.or, [4, 6]⟩, ⟨.or, [5, 7]⟩, ⟨.and, [9, 8]⟩, ⟨.not, [10]⟩], 11⟩

theorem upper22882 : FanInTwo circuit22882 ∧ circuit22882.size ≤ 6 ∧
    ∀ i j : Fin 6, circuit22882.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
      (34630324159 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [circuit22882, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

def circuit22884 : Circuit := ⟨[⟨.or, [1, 0]⟩, ⟨.or, [2, 6]⟩, ⟨.or, [3, 7]⟩, ⟨.or, [4, 8]⟩, ⟨.and, [5, 9]⟩, ⟨.not, [10]⟩], 11⟩

theorem upper22884 : FanInTwo circuit22884 ∧ circuit22884.size ≤ 6 ∧
    ∀ i j : Fin 6, circuit22884.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
      (34634581919 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [circuit22884, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

def circuit22887 : Circuit := ⟨[⟨.or, [2, 3]⟩, ⟨.or, [4, 6]⟩, ⟨.and, [5, 7]⟩, ⟨.and, [0, 1]⟩, ⟨.or, [8, 9]⟩, ⟨.not, [10]⟩], 11⟩

theorem upper22887 : FanInTwo circuit22887 ∧ circuit22887.size ≤ 6 ∧
    ∀ i j : Fin 6, circuit22887.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
      (34634583997 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [circuit22887, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

def circuit22888 : Circuit := ⟨[⟨.or, [5, 1]⟩, ⟨.or, [5, 2]⟩, ⟨.and, [6, 3]⟩, ⟨.and, [7, 4]⟩, ⟨.or, [9, 8]⟩, ⟨.not, [10]⟩], 11⟩

theorem upper22888 : FanInTwo circuit22888 ∧ circuit22888.size ≤ 6 ∧
    ∀ i j : Fin 6, circuit22888.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
      (34634649023 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [circuit22888, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

def circuit22889 : Circuit := ⟨[⟨.or, [1, 0]⟩, ⟨.and, [2, 6]⟩, ⟨.or, [4, 3]⟩, ⟨.and, [5, 8]⟩, ⟨.or, [9, 7]⟩, ⟨.not, [10]⟩], 11⟩

theorem upper22889 : FanInTwo circuit22889 ∧ circuit22889.size ≤ 6 ∧
    ∀ i j : Fin 6, circuit22889.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
      (34634714811 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [circuit22889, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end SignedTwoLitFollowup
