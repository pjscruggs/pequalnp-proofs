import PEqualNP.MetaComplexity.Helpers.ForestElim
import PEqualNP.Defs.MetaComplexityLgpMono

namespace CofactorTransfer

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- A nonconstant cofactor of an essential last input saves at least one gate,
    with the fixed input removed from the arity of the resulting circuit. -/
theorem dropLast {n s : ℕ} [NeZero n] (f : (Fin (n + 1) → Bool) → Bool) (b : Bool)
    (depends : ∃ x, f (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ f x)
    (varies : ∃ x y : Fin n → Bool, f (Fin.snoc x b) ≠ f (Fin.snoc y b))
    (small : HasCircuitSize (n + 1) f (s + 1)) :
    HasCircuitSize n (fun x => f (Fin.snoc x b)) s := by
  have lift (x : Fin n → Bool) :
      Function.update (Fin.snoc x b : Fin (n + 1) → Bool) (Fin.last n) b = Fin.snoc x b := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · simp
  obtain ⟨x, y, hxy⟩ := varies
  have cut := Helpers.Forest.one_gate_at n f (Fin.last n) b s depends
    ⟨Fin.snoc x b, Fin.snoc y b, by simpa only [lift] using hxy⟩ small
  let π : Fin (n + 1) → Fin n := Fin.lastCases 0 id
  have project := Helpers.PermInputs.relabel_size π _ s cut
  have eqn (z : Fin n → Bool) :
      Function.update (z ∘ π) (Fin.last n) b = Fin.snoc z b := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · simp [Function.comp, π]
  simpa only [eqn] using project

/-- A monotone witness within one gate of any such cofactor's proved lower
    bound suffices to discharge the corresponding no-saving row. -/
theorem noSaving {n k : ℕ} [NeZero n] (f : (Fin (n + 1) → Bool) → Bool) (b : Bool)
    (depends : ∃ x, f (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ f x)
    (varies : ∃ x y : Fin n → Bool, f (Fin.snoc x b) ≠ f (Fin.snoc y b))
    (lower : ∀ s, HasCircuitSize n (fun x => f (Fin.snoc x b)) s → k ≤ s)
    (upper : ∃ C : Circuit, Monotone2 C ∧ C.size ≤ k + 1 ∧
      ∀ x, C.eval (List.ofFn x) = f x) :
    ∀ s, HasCircuitSize (n + 1) f s → ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧
      ∀ x, C.eval (List.ofFn x) = f x := by
  intro s hs
  cases s with
  | zero =>
    obtain ⟨C, _, sz, hC⟩ := hs
    have empty : C.gates = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero sz)
    exact ⟨C, by simp [Monotone2, empty], sz, hC⟩
  | succ s =>
    obtain ⟨C, mono, size, computes⟩ := upper
    exact ⟨C, mono, size.trans (Nat.succ_le_succ (lower s (dropLast f b depends varies hs))), computes⟩

/-- Also usable with a parent table row that only compares the two bases and
    does not publish its optimum. The rebuild hypothesis is the upper bound. -/
theorem fromParent {n : ℕ} [NeZero n] (f : (Fin (n + 1) → Bool) → Bool) (b : Bool)
    (depends : ∃ x, f (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ f x)
    (varies : ∃ x y : Fin n → Bool, f (Fin.snoc x b) ≠ f (Fin.snoc y b))
    (parent : ∀ s, HasCircuitSize n (fun x => f (Fin.snoc x b)) s →
      ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x, C.eval (List.ofFn x) = f (Fin.snoc x b))
    (rebuild : ∀ C : Circuit, Monotone2 C → (∀ x, C.eval (List.ofFn x) = f (Fin.snoc x b)) →
      ∃ D : Circuit, Monotone2 D ∧ D.size ≤ C.size + 1 ∧ ∀ x, D.eval (List.ofFn x) = f x) :
    ∀ s, HasCircuitSize (n + 1) f s → ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧
      ∀ x, C.eval (List.ofFn x) = f x := by
  intro s hs
  cases s with
  | zero =>
    obtain ⟨C, _, sz, hC⟩ := hs
    have empty : C.gates = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero sz)
    exact ⟨C, by simp [Monotone2, empty], sz, hC⟩
  | succ s =>
    obtain ⟨C, hm, hc, he⟩ := parent s (dropLast f b depends varies hs)
    obtain ⟨D, hd, hsiz, hcomp⟩ := rebuild C hm he
    exact ⟨D, hd, hsiz.trans (Nat.succ_le_succ hc), hcomp⟩

private theorem wirePrefix (gs : List Gate) (w : List Bool) :
    ∃ t, gs.foldl Helpers.PermInputs.step w = w ++ t ∧ t.length = gs.length := by
  induction gs generalizing w with
  | nil => exact ⟨[], by simp, rfl⟩
  | cons g gs ih =>
    obtain ⟨t, e, len⟩ := ih (Helpers.PermInputs.step w g)
    exact ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t,
      by simpa [Helpers.PermInputs.step, List.append_assoc] using e, by simp [len]⟩

/-- Attach a fresh last input to a monotone circuit's output with one counted gate.
    The Boolean flag selects AND (true) or OR (false). -/
theorem appendMono {n : ℕ} (C : Circuit) (mono : Monotone2 C) (a : Bool) :
    ∃ D : Circuit, Monotone2 D ∧ D.size ≤ C.size + 1 ∧ ∀ x : Fin (n + 1) → Bool,
      D.eval (List.ofFn x) =
        (if a then x (Fin.last n) && C.eval (List.ofFn (fun i => x (Fin.castSucc i)))
         else x (Fin.last n) || C.eval (List.ofFn (fun i => x (Fin.castSucc i)))) := by
  let R := Helpers.PermInputs.relabel n (n+1) Fin.castSucc C
  let op : GateOp := if a then .and else .or
  let gate : Gate := ⟨op, [n, R.output]⟩
  let D : Circuit := ⟨R.gates ++ [gate], n + 1 + R.gates.length⟩
  refine ⟨D, ?_, ?_, ?_⟩
  · intro g hg
    change g ∈ R.gates ++ [gate] at hg
    rcases List.mem_append.mp hg with hg | hg
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hg
      exact ⟨(mono p hp).1, by simpa [Helpers.PermInputs.relGate] using (mono p hp).2⟩
    · have eq : g = gate := by simpa using hg
      subst g
      cases a <;> simp [gate, op]
  · simp [D, R, Helpers.PermInputs.relabel, Circuit.size]
  · intro x
    let w := List.ofFn x
    obtain ⟨t, ht, lt⟩ := wirePrefix R.gates w
    change R.wires w = w ++ t at ht
    have wlen : w.length = n + 1 := List.length_ofFn
    have hn : n < w.length := by omega
    have len : (R.wires w).length = n + 1 + R.gates.length := by rw [ht, List.length_append, wlen, lt]
    have inp : (R.wires w).getD n false = x (Fin.last n) := by
      rw [ht, List.getD_append (n := n) _ _ _ hn, List.getD_eq_getElem _ _ hn, List.getElem_ofFn]
      rfl
    have base : R.eval w = C.eval (List.ofFn (fun i => x (Fin.castSucc i))) :=
      (Helpers.PermInputs.rel_fold n (n+1) Fin.castSucc C.gates _ _
        (Helpers.PermInputs.rel_init n (n+1) Fin.castSucc x)).2.2 C.output
    change (D.wires w).getD (n + 1 + R.gates.length) false = _
    have endWire : D.wires w = R.wires w ++ [op.eval
        [(R.wires w).getD n false, R.eval w]] := by
      simp [D, Circuit.wires, List.foldl_append, gate, Circuit.eval]
    rw [endWire, ← len, List.getD_append_right (n := _) _ _ _ (le_refl _), Nat.sub_self, inp, base]
    cases a <;> simp [op, GateOp.eval]

/-- Either monotone output padding operation preserves a no-saving table row. -/
theorem padInherits {n : ℕ} [NeZero n] (g : (Fin n → Bool) → Bool)
    (varies : ∃ x y, g x ≠ g y) (a : Bool)
    (parent : ∀ s, HasCircuitSize n g s → ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧
      ∀ x, C.eval (List.ofFn x) = g x) :
    let f := fun x : Fin (n + 1) → Bool =>
      if a then x (Fin.last n) && g (fun i => x (Fin.castSucc i))
      else x (Fin.last n) || g (fun i => x (Fin.castSucc i))
    ∀ s, HasCircuitSize (n + 1) f s → ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧
      ∀ x, C.eval (List.ofFn x) = f x := by
  intro f
  have neutral (z : Fin n → Bool) : f (Fin.snoc z a) = g z := by
    cases a <;> simp [f]
  obtain ⟨u, v, huv⟩ := varies
  have hit : ∃ z, g z = a := by
    cases hu : g u <;> cases hv : g v <;> cases a <;> first
      | exact ⟨u, hu⟩ | exact ⟨v, hv⟩ | simp [hu, hv] at huv
  obtain ⟨z, hz⟩ := hit
  apply fromParent f a
  · refine ⟨Fin.snoc z a, ?_⟩
    rw [neutral, hz]
    cases a <;> simp [f, hz]
  · exact ⟨u, v, by simpa only [neutral] using huv⟩
  · simpa only [neutral] using parent
  · intro C hm he
    obtain ⟨D, hd, sz, hdEval⟩ := appendMono (n := n) C hm a
    refine ⟨D, hd, sz, fun x => ?_⟩
    rw [hdEval, he, neutral]

end CofactorTransfer
