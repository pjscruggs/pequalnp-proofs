import CofactorTransfer
import PEqualNP.Outside.L_meta_8664

namespace NineGates

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def table {n : ℕ} (bits : ℕ) (x : Fin n → Bool) : Bool :=
  bits.testBit (∑ i : Fin n, if x i then 2 ^ (i : ℕ) else 0)

def child : (Fin 6 → Bool) → Bool := table 0xfeeefaeafeaaeaaa

def witness : Circuit :=
  ⟨[⟨.or, [4,5]⟩, ⟨.and, [2,6]⟩, ⟨.and, [3,7]⟩, ⟨.or, [2,4]⟩,
    ⟨.or, [3,5]⟩, ⟨.and, [9,10]⟩, ⟨.and, [1,11]⟩, ⟨.or, [8,12]⟩,
    ⟨.or, [0,13]⟩], 14⟩

theorem upper : Monotone2 witness ∧ witness.size = 9 ∧
    ∀ x : Fin 6 → Bool, witness.eval (List.ofFn x) = child x := by
  refine ⟨?_, rfl, by decide +kernel⟩
  intro gate member
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

open PEqualNP.Outside.L_meta_8664 in
theorem parentLower (s : ℕ) (h : HasCircuitSize 5 (table 0xeac8e080) s) : 8 ≤ s := by
  let raw : List (BitVec 32) := [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000]
  let goal : BitVec 32 := 0xeac8e080
  have root : Lower (fullMask 32) (raw.map BitVec.toNat) goal.toNat 8 :=
    hcsLowerEq (by decide +kernel) (by decide +kernel) (by decide +kernel) s2Stock
  exact hcsLower (n := 5) raw goal 8 _ (by decide +kernel) (by decide +kernel) root s h

theorem lower (s : ℕ) (h : HasCircuitSize 6 child s) : 9 ≤ s := by
  by_contra! small
  obtain ⟨C, valid, sz, computes⟩ := h
  have h8 : HasCircuitSize 6 child 8 := ⟨C, valid, by omega, computes⟩
  let π : Fin 6 → Fin 6 := Fin.cases (Fin.last 5) Fin.castSucc
  let f : (Fin 6 → Bool) → Bool := fun x => child (x ∘ π)
  have rotated : HasCircuitSize 6 f 8 := Helpers.PermInputs.relabel_size π child 8 h8
  have depends : ∃ x, f (Function.update x (Fin.last 5) (!x (Fin.last 5))) ≠ f x :=
    ⟨fun _ => false, by decide +kernel⟩
  have varies : ∃ x y : Fin 5 → Bool, f (Fin.snoc x false) ≠ f (Fin.snoc y false) :=
    ⟨fun _ => false, fun _ => true, by decide +kernel⟩
  have cut := CofactorTransfer.dropLast (s := 7) f false depends varies rotated
  have same : ∀ x : Fin 5 → Bool, f (Fin.snoc x false) = table 0xeac8e080 x := by decide +kernel
  simp only [same] at cut
  exact (by decide : ¬ 8 ≤ 7) (parentLower 7 cut)

end NineGates
