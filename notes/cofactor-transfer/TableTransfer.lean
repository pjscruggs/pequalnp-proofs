import InputPair

namespace CofactorTransfer

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Helpers.PermInputs

abbrev NoSaving {n : ℕ} (g : (Fin n → Bool) → Bool) : Prop :=
  ∀ s, HasCircuitSize n g s → ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧
    ∀ x, C.eval (List.ofFn x) = g x

theorem monoRename {n m : ℕ} (π : Fin n → Fin m) (C : Circuit) (hC : Monotone2 C)
    (g : (Fin n → Bool) → Bool) (computes : ∀ x, C.eval (List.ofFn x) = g x) :
    ∃ D : Circuit, Monotone2 D ∧ D.size = C.size ∧ ∀ x, D.eval (List.ofFn x) = g (x ∘ π) := by
  refine ⟨relabel n m π C, ?_, by simp [relabel, Circuit.size], ?_⟩
  · intro gate member
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp member
    exact ⟨(hC q hq).1, by simpa [relGate] using (hC q hq).2⟩
  · intro x
    rw [← computes]
    exact (rel_fold n m π C.gates _ _ (rel_init n m π x)).2.2 C.output

/-- Permute the input wires in both the hypothesis and the monotone witness. -/
theorem renamedInherits {n : ℕ} (π : Equiv.Perm (Fin n)) (g : (Fin n → Bool) → Bool)
    (parent : NoSaving g) : NoSaving (fun x => g (x ∘ π)) := by
  intro s h
  have small := relabel_size (⇑π.symm) _ s h
  have back (x : Fin n → Bool) : (x ∘ π.symm) ∘ π = x := by funext i; simp [Function.comp]
  simp only [back] at small
  obtain ⟨C, mono, size, ev⟩ := parent s small
  obtain ⟨D, hd, eqn, he⟩ := monoRename (⇑π) C mono g ev
  exact ⟨D, hd, eqn.le.trans size, he⟩

/-- Add an input that is never read. -/
theorem unusedInherits {n : ℕ} [NeZero n] (g : (Fin n → Bool) → Bool)
    (parent : NoSaving g) : NoSaving (fun x : Fin (n+1) → Bool => g (x ∘ Fin.castSucc)) := by
  intro s h
  let π : Fin (n + 1) → Fin n := Fin.lastCases 0 id
  have small := relabel_size π _ s h
  have back (x : Fin n → Bool) : (x ∘ π) ∘ Fin.castSucc = x := by funext i; simp [π, Function.comp]
  simp only [back] at small
  obtain ⟨C, mono, size, ev⟩ := parent s small
  obtain ⟨D, hd, eqn, he⟩ := monoRename Fin.castSucc C mono g ev
  exact ⟨D, hd, eqn.le.trans size, he⟩

#print axioms renamedInherits
#print axioms unusedInherits
end CofactorTransfer
