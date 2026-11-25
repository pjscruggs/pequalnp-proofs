import CofactorTransfer

namespace CofactorTransfer

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Helpers.PermInputs

/-- Replace input v by its AND (a = true) or OR (a = false) with a fresh input. -/
def splitInputs {n : ℕ} (v : Fin n) (a : Bool) (x : Fin (n + 1) → Bool) : Fin n → Bool :=
  fun i => if i = v then
      (if a then x v.castSucc && x (Fin.last n) else x v.castSucc || x (Fin.last n))
    else x i.castSucc

private theorem splitNeutral {n : ℕ} (v : Fin n) (a : Bool) (z : Fin n → Bool) :
    splitInputs v a (Fin.snoc z a) = z := by
  funext i
  by_cases h : i = v <;> cases a <;> simp_all [splitInputs]

/-- Insert a single input gate ahead of a parent's monotone circuit. -/
theorem prependMono {n : ℕ} (v : Fin n) (a : Bool) (C : Circuit) (hC : Monotone2 C) :
    ∃ D : Circuit, Monotone2 D ∧ D.size = C.size + 1 ∧ ∀ x : Fin (n + 1) → Bool,
      D.eval (List.ofFn x) = C.eval (List.ofFn (splitInputs v a x)) := by
  let op : GateOp := if a then .and else .or
  let gate : Gate := ⟨op, [v.val, n]⟩
  let π : Fin n → Fin (n + 2) := fun i => if i = v then Fin.last (n+1) else i.castSucc.castSucc
  let R := relabel n (n+2) π C
  let D : Circuit := ⟨gate :: R.gates, R.output⟩
  refine ⟨D, ?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_cons.mp hg with h | h
    · subst g
      cases a <;> simp [gate, op]
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp h
      exact ⟨(hC q hq).1, by simpa [relGate] using (hC q hq).2⟩
  · simp [D, R, relabel, Circuit.size]
  · intro x
    let y : Fin (n+2) → Bool := Fin.snoc x (if a then x v.castSucc && x (Fin.last n) else x v.castSucc || x (Fin.last n))
    have agrees : y ∘ π = splitInputs v a x := by
      funext i
      by_cases h : i = v <;> simp [Function.comp, π, y, splitInputs, h]
    have step_eq : step (List.ofFn x) gate = List.ofFn y := by
      have vlt : v.val < (List.ofFn x).length := by simp
      have nlt : n < (List.ofFn x).length := by simp
      simp only [step, gate, List.map_cons, List.map_nil, List.getD_eq_getElem _ _ vlt,
        List.getD_eq_getElem _ _ nlt, List.getElem_ofFn]
      rw [List.ofFn_succ_last (f := y)]
      cases a <;> simp [y, op, GateOp.eval] <;> rfl
    have eqn := (rel_fold n (n+2) π C.gates _ _ (rel_init n (n+2) π y)).2.2 C.output
    change ((R.gates.foldl step (step (List.ofFn x) gate)).getD R.output false) = _
    rw [step_eq, ← agrees]
    exact eqn

/-- A nontrivial input-pair split inherits a no-saving table row. -/
theorem pairInherits {n : ℕ} [NeZero n] (g : (Fin n → Bool) → Bool) (v : Fin n)
    (depends : ∃ z, g (Function.update z v (!z v)) ≠ g z) (a : Bool)
    (parent : ∀ s, HasCircuitSize n g s → ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧
      ∀ x, C.eval (List.ofFn x) = g x) :
    ∀ s, HasCircuitSize (n + 1) (fun x => g (splitInputs v a x)) s →
      ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x, C.eval (List.ofFn x) = g (splitInputs v a x) := by
  obtain ⟨z, hz⟩ := depends
  let w := Function.update z v a
  have changes : g (Function.update z v (!a)) ≠ g w := by
    have same := Function.update_eq_self v z
    cases hv : z v <;> cases a <;> simp [w, hv] at hz ⊢ <;> rw [hv] at same <;>
      rw [same] <;> first | exact hz | exact Ne.symm hz
  apply fromParent (fun x => g (splitInputs v a x)) a
  · refine ⟨Fin.snoc w a, ?_⟩
    rw [splitNeutral]
    convert changes using 2
    funext i
    by_cases h : i = v <;> cases a <;> simp_all [splitInputs, w, Function.update]
  · exact ⟨Function.update z v (!z v), z, by simpa only [splitNeutral] using hz⟩
  · simpa only [splitNeutral] using parent
  · intro C hC computes
    obtain ⟨D, hD, sz, ev⟩ := prependMono v a C hC
    refine ⟨D, hD, sz.le, fun x => ?_⟩
    rw [ev, computes, splitNeutral]

#print axioms pairInherits
end CofactorTransfer
