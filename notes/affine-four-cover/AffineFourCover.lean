import Mathlib.Data.Fintype.Basic
import Mathlib.Order.Bounds.Defs

namespace AffineFourCover

def rows : List Nat :=
  [69905, 74274, 83012, 100488, 164897, 149522, 139652, 135752,
   272449, 267394, 295444, 278824, 541313, 557378, 530468, 533528]

abbrev Point := Fin 16
abbrev Line := Fin 20
abbrev Rect := Finset Point × Finset Line

def incident (p : Point) (l : Line) : Bool := (rows.getD p.val 0).testBit l.val

-- Point 4 is the center. Every other label has two set bits, the endpoints
-- of an edge of the complete graph on six vertices.
def labels : List Nat := [34, 5, 6, 33, 63, 24, 36, 3, 17, 9, 10, 18, 12, 20, 40, 48]

def hyperoval (v : Fin 6) : Finset Point :=
  Finset.univ.filter (fun p => (labels.getD p.val 0).testBit v.val = true)

def puncturedLine (l : Line) : Finset Point :=
  Finset.univ.filter (fun p => p ≠ 4 ∧ incident p l = true)

def rectangle (s : Finset Point) : Rect :=
  (s, Finset.univ.filter (fun l => ∀ p ∈ s, incident p l = false))

def witness : List Rect :=
  (([0, 5, 10, 15, 17] : List Line).map (fun l => rectangle (puncturedLine l))) ++
    (List.finRange 6).map (fun v => rectangle (hyperoval v))

-- Same matrix, bit order and cover predicate as the public desk row.
def AtMost (k : Nat) : Prop :=
  ∃ L : List Rect, L.length ≤ k ∧
    (∀ r ∈ L, ∀ p ∈ r.1, ∀ l ∈ r.2, incident p l = false) ∧
    ∀ (p : Point) (l : Line), incident p l = false → ∃ r ∈ L, p ∈ r.1 ∧ l ∈ r.2

set_option maxRecDepth 100000 in
theorem eleven : AtMost 11 := by
  refine ⟨witness, ?_, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem least_of_lower (lower : ¬ AtMost 10) : IsLeast {k | AtMost k} 11 := by
  refine ⟨eleven, ?_⟩
  rintro k ⟨L, hlen, h⟩
  by_contra! small
  exact lower ⟨L, by omega, h⟩

#print axioms eleven
end AffineFourCover
