import PEqualNP.Defs

namespace LMeta9829Upper

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- One AND per line, three ORs within each line, and ten ORs across lines. -/
def circuit : Circuit :=
  ⟨[⟨.or, [2, 3]⟩,
    ⟨.or, [24, 5]⟩,
    ⟨.or, [25, 11]⟩,
    ⟨.and, [13, 26]⟩,
    ⟨.or, [3, 4]⟩,
    ⟨.or, [28, 6]⟩,
    ⟨.or, [29, 12]⟩,
    ⟨.and, [14, 30]⟩,
    ⟨.or, [0, 4]⟩,
    ⟨.or, [32, 5]⟩,
    ⟨.or, [33, 7]⟩,
    ⟨.and, [15, 34]⟩,
    ⟨.or, [1, 5]⟩,
    ⟨.or, [36, 6]⟩,
    ⟨.or, [37, 8]⟩,
    ⟨.and, [16, 38]⟩,
    ⟨.or, [2, 6]⟩,
    ⟨.or, [40, 7]⟩,
    ⟨.or, [41, 9]⟩,
    ⟨.and, [17, 42]⟩,
    ⟨.or, [3, 7]⟩,
    ⟨.or, [44, 8]⟩,
    ⟨.or, [45, 10]⟩,
    ⟨.and, [18, 46]⟩,
    ⟨.or, [4, 8]⟩,
    ⟨.or, [48, 9]⟩,
    ⟨.or, [49, 11]⟩,
    ⟨.and, [19, 50]⟩,
    ⟨.or, [5, 9]⟩,
    ⟨.or, [52, 10]⟩,
    ⟨.or, [53, 12]⟩,
    ⟨.and, [20, 54]⟩,
    ⟨.or, [0, 6]⟩,
    ⟨.or, [56, 10]⟩,
    ⟨.or, [57, 11]⟩,
    ⟨.and, [21, 58]⟩,
    ⟨.or, [1, 7]⟩,
    ⟨.or, [60, 11]⟩,
    ⟨.or, [61, 12]⟩,
    ⟨.and, [22, 62]⟩,
    ⟨.or, [0, 2]⟩,
    ⟨.or, [64, 8]⟩,
    ⟨.or, [65, 12]⟩,
    ⟨.and, [23, 66]⟩,
    ⟨.or, [27, 31]⟩,
    ⟨.or, [68, 35]⟩,
    ⟨.or, [69, 39]⟩,
    ⟨.or, [70, 43]⟩,
    ⟨.or, [71, 47]⟩,
    ⟨.or, [72, 51]⟩,
    ⟨.or, [73, 55]⟩,
    ⟨.or, [74, 59]⟩,
    ⟨.or, [75, 63]⟩,
    ⟨.or, [76, 67]⟩], 77⟩

theorem gate_count : circuit.size = 54 := rfl

theorem fan_in : FanInTwo circuit := by
  simp [circuit, FanInTwo]

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def start (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23]
def w24 (x : Fin 24 → Bool) : Bool := GateOp.eval .or [x 2, x 3]
def state24 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, w24 x]
theorem step24 (x : Fin 24 → Bool) : step (start x) ⟨.or, [2, 3]⟩ = state24 x := rfl
def w25 (x : Fin 24 → Bool) : Bool := GateOp.eval .or [w24 x, x 5]
def state25 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, w24 x, w25 x]
theorem step25 (x : Fin 24 → Bool) : step (state24 x) ⟨.or, [24, 5]⟩ = state25 x := rfl
def w26 (x : Fin 24 → Bool) : Bool := GateOp.eval .or [w25 x, x 11]
def state26 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, w24 x, w25 x, w26 x]
theorem step26 (x : Fin 24 → Bool) : step (state25 x) ⟨.or, [25, 11]⟩ = state26 x := rfl
def w27 (x : Fin 24 → Bool) : Bool := GateOp.eval .and [x 13, w26 x]
def state27 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, w24 x, w25 x, w26 x, w27 x]
theorem step27 (x : Fin 24 → Bool) : step (state26 x) ⟨.and, [13, 26]⟩ = state27 x := rfl
def w28 (x : Fin 24 → Bool) : Bool := GateOp.eval .or [x 3, x 4]
def state28 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, w24 x, w25 x, w26 x, w27 x, w28 x]
theorem step28 (x : Fin 24 → Bool) : step (state27 x) ⟨.or, [3, 4]⟩ = state28 x := rfl
def w29 (x : Fin 24 → Bool) : Bool := GateOp.eval .or [w28 x, x 6]
def state29 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, w24 x, w25 x, w26 x, w27 x, w28 x, w29 x]
theorem step29 (x : Fin 24 → Bool) : step (state28 x) ⟨.or, [28, 6]⟩ = state29 x := rfl
def w30 (x : Fin 24 → Bool) : Bool := GateOp.eval .or [w29 x, x 12]
def state30 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, w24 x, w25 x, w26 x, w27 x, w28 x, w29 x, w30 x]
theorem step30 (x : Fin 24 → Bool) : step (state29 x) ⟨.or, [29, 12]⟩ = state30 x := rfl
def w31 (x : Fin 24 → Bool) : Bool := GateOp.eval .and [x 14, w30 x]
def state31 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, w24 x, w25 x, w26 x, w27 x, w28 x, w29 x, w30 x, w31 x]
theorem step31 (x : Fin 24 → Bool) : step (state30 x) ⟨.and, [14, 30]⟩ = state31 x := rfl
def w32 (x : Fin 24 → Bool) : Bool := GateOp.eval .or [x 0, x 4]
def state32 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, w24 x, w25 x, w26 x, w27 x, w28 x, w29 x, w30 x, w31 x, w32 x]
theorem step32 (x : Fin 24 → Bool) : step (state31 x) ⟨.or, [0, 4]⟩ = state32 x := rfl
def w33 (x : Fin 24 → Bool) : Bool := GateOp.eval .or [w32 x, x 5]
def state33 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, w24 x, w25 x, w26 x, w27 x, w28 x, w29 x, w30 x, w31 x, w32 x, w33 x]
theorem step33 (x : Fin 24 → Bool) : step (state32 x) ⟨.or, [32, 5]⟩ = state33 x := rfl
def w34 (x : Fin 24 → Bool) : Bool := GateOp.eval .or [w33 x, x 7]
def state34 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, w24 x, w25 x, w26 x, w27 x, w28 x, w29 x, w30 x, w31 x, w32 x, w33 x, w34 x]
theorem step34 (x : Fin 24 → Bool) : step (state33 x) ⟨.or, [33, 7]⟩ = state34 x := rfl
def w35 (x : Fin 24 → Bool) : Bool := GateOp.eval .and [x 15, w34 x]
def state35 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, w24 x, w25 x, w26 x, w27 x, w28 x, w29 x, w30 x, w31 x, w32 x, w33 x, w34 x, w35 x]
theorem step35 (x : Fin 24 → Bool) : step (state34 x) ⟨.and, [15, 34]⟩ = state35 x := rfl
def w36 (x : Fin 24 → Bool) : Bool := GateOp.eval .or [x 1, x 5]
def state36 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, w24 x, w25 x, w26 x, w27 x, w28 x, w29 x, w30 x, w31 x, w32 x, w33 x, w34 x, w35 x, w36 x]
theorem step36 (x : Fin 24 → Bool) : step (state35 x) ⟨.or, [1, 5]⟩ = state36 x := rfl
def w37 (x : Fin 24 → Bool) : Bool := GateOp.eval .or [w36 x, x 6]
def state37 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, w24 x, w25 x, w26 x, w27 x, w28 x, w29 x, w30 x, w31 x, w32 x, w33 x, w34 x, w35 x, w36 x, w37 x]
theorem step37 (x : Fin 24 → Bool) : step (state36 x) ⟨.or, [36, 6]⟩ = state37 x := rfl
def w38 (x : Fin 24 → Bool) : Bool := GateOp.eval .or [w37 x, x 8]
def state38 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, w24 x, w25 x, w26 x, w27 x, w28 x, w29 x, w30 x, w31 x, w32 x, w33 x, w34 x, w35 x, w36 x, w37 x, w38 x]
theorem step38 (x : Fin 24 → Bool) : step (state37 x) ⟨.or, [37, 8]⟩ = state38 x := rfl
def w39 (x : Fin 24 → Bool) : Bool := GateOp.eval .and [x 16, w38 x]
def state39 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, w24 x, w25 x, w26 x, w27 x, w28 x, w29 x, w30 x, w31 x, w32 x, w33 x, w34 x, w35 x, w36 x, w37 x, w38 x, w39 x]
theorem step39 (x : Fin 24 → Bool) : step (state38 x) ⟨.and, [16, 38]⟩ = state39 x := rfl
def w40 (x : Fin 24 → Bool) : Bool := GateOp.eval .or [x 2, x 6]
def state40 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, w24 x, w25 x, w26 x, w27 x, w28 x, w29 x, w30 x, w31 x, w32 x, w33 x, w34 x, w35 x, w36 x, w37 x, w38 x, w39 x, w40 x]
theorem step40 (x : Fin 24 → Bool) : step (state39 x) ⟨.or, [2, 6]⟩ = state40 x := rfl
def w41 (x : Fin 24 → Bool) : Bool := GateOp.eval .or [w40 x, x 7]
def state41 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, w24 x, w25 x, w26 x, w27 x, w28 x, w29 x, w30 x, w31 x, w32 x, w33 x, w34 x, w35 x, w36 x, w37 x, w38 x, w39 x, w40 x, w41 x]
theorem step41 (x : Fin 24 → Bool) : step (state40 x) ⟨.or, [40, 7]⟩ = state41 x := rfl
def w42 (x : Fin 24 → Bool) : Bool := GateOp.eval .or [w41 x, x 9]
def state42 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, w24 x, w25 x, w26 x, w27 x, w28 x, w29 x, w30 x, w31 x, w32 x, w33 x, w34 x, w35 x, w36 x, w37 x, w38 x, w39 x, w40 x, w41 x, w42 x]
theorem step42 (x : Fin 24 → Bool) : step (state41 x) ⟨.or, [41, 9]⟩ = state42 x := rfl
def w43 (x : Fin 24 → Bool) : Bool := GateOp.eval .and [x 17, w42 x]
def state43 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, w24 x, w25 x, w26 x, w27 x, w28 x, w29 x, w30 x, w31 x, w32 x, w33 x, w34 x, w35 x, w36 x, w37 x, w38 x, w39 x, w40 x, w41 x, w42 x, w43 x]
theorem step43 (x : Fin 24 → Bool) : step (state42 x) ⟨.and, [17, 42]⟩ = state43 x := rfl
def w44 (x : Fin 24 → Bool) : Bool := GateOp.eval .or [x 3, x 7]
def state44 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, w24 x, w25 x, w26 x, w27 x, w28 x, w29 x, w30 x, w31 x, w32 x, w33 x, w34 x, w35 x, w36 x, w37 x, w38 x, w39 x, w40 x, w41 x, w42 x, w43 x, w44 x]
theorem step44 (x : Fin 24 → Bool) : step (state43 x) ⟨.or, [3, 7]⟩ = state44 x := rfl
def w45 (x : Fin 24 → Bool) : Bool := GateOp.eval .or [w44 x, x 8]
def state45 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, w24 x, w25 x, w26 x, w27 x, w28 x, w29 x, w30 x, w31 x, w32 x, w33 x, w34 x, w35 x, w36 x, w37 x, w38 x, w39 x, w40 x, w41 x, w42 x, w43 x, w44 x, w45 x]
theorem step45 (x : Fin 24 → Bool) : step (state44 x) ⟨.or, [44, 8]⟩ = state45 x := rfl
def w46 (x : Fin 24 → Bool) : Bool := GateOp.eval .or [w45 x, x 10]
def state46 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, w24 x, w25 x, w26 x, w27 x, w28 x, w29 x, w30 x, w31 x, w32 x, w33 x, w34 x, w35 x, w36 x, w37 x, w38 x, w39 x, w40 x, w41 x, w42 x, w43 x, w44 x, w45 x, w46 x]
theorem step46 (x : Fin 24 → Bool) : step (state45 x) ⟨.or, [45, 10]⟩ = state46 x := rfl
def w47 (x : Fin 24 → Bool) : Bool := GateOp.eval .and [x 18, w46 x]
def state47 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, w24 x, w25 x, w26 x, w27 x, w28 x, w29 x, w30 x, w31 x, w32 x, w33 x, w34 x, w35 x, w36 x, w37 x, w38 x, w39 x, w40 x, w41 x, w42 x, w43 x, w44 x, w45 x, w46 x, w47 x]
theorem step47 (x : Fin 24 → Bool) : step (state46 x) ⟨.and, [18, 46]⟩ = state47 x := rfl
def w48 (x : Fin 24 → Bool) : Bool := GateOp.eval .or [x 4, x 8]
def state48 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, w24 x, w25 x, w26 x, w27 x, w28 x, w29 x, w30 x, w31 x, w32 x, w33 x, w34 x, w35 x, w36 x, w37 x, w38 x, w39 x, w40 x, w41 x, w42 x, w43 x, w44 x, w45 x, w46 x, w47 x, w48 x]
theorem step48 (x : Fin 24 → Bool) : step (state47 x) ⟨.or, [4, 8]⟩ = state48 x := rfl
def w49 (x : Fin 24 → Bool) : Bool := GateOp.eval .or [w48 x, x 9]
def state49 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, w24 x, w25 x, w26 x, w27 x, w28 x, w29 x, w30 x, w31 x, w32 x, w33 x, w34 x, w35 x, w36 x, w37 x, w38 x, w39 x, w40 x, w41 x, w42 x, w43 x, w44 x, w45 x, w46 x, w47 x, w48 x, w49 x]
theorem step49 (x : Fin 24 → Bool) : step (state48 x) ⟨.or, [48, 9]⟩ = state49 x := rfl
def w50 (x : Fin 24 → Bool) : Bool := GateOp.eval .or [w49 x, x 11]
def state50 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, w24 x, w25 x, w26 x, w27 x, w28 x, w29 x, w30 x, w31 x, w32 x, w33 x, w34 x, w35 x, w36 x, w37 x, w38 x, w39 x, w40 x, w41 x, w42 x, w43 x, w44 x, w45 x, w46 x, w47 x, w48 x, w49 x, w50 x]
theorem step50 (x : Fin 24 → Bool) : step (state49 x) ⟨.or, [49, 11]⟩ = state50 x := rfl
def w51 (x : Fin 24 → Bool) : Bool := GateOp.eval .and [x 19, w50 x]
def state51 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, w24 x, w25 x, w26 x, w27 x, w28 x, w29 x, w30 x, w31 x, w32 x, w33 x, w34 x, w35 x, w36 x, w37 x, w38 x, w39 x, w40 x, w41 x, w42 x, w43 x, w44 x, w45 x, w46 x, w47 x, w48 x, w49 x, w50 x, w51 x]
theorem step51 (x : Fin 24 → Bool) : step (state50 x) ⟨.and, [19, 50]⟩ = state51 x := rfl
def w52 (x : Fin 24 → Bool) : Bool := GateOp.eval .or [x 5, x 9]
def state52 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, w24 x, w25 x, w26 x, w27 x, w28 x, w29 x, w30 x, w31 x, w32 x, w33 x, w34 x, w35 x, w36 x, w37 x, w38 x, w39 x, w40 x, w41 x, w42 x, w43 x, w44 x, w45 x, w46 x, w47 x, w48 x, w49 x, w50 x, w51 x, w52 x]
theorem step52 (x : Fin 24 → Bool) : step (state51 x) ⟨.or, [5, 9]⟩ = state52 x := rfl
def w53 (x : Fin 24 → Bool) : Bool := GateOp.eval .or [w52 x, x 10]
def state53 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, w24 x, w25 x, w26 x, w27 x, w28 x, w29 x, w30 x, w31 x, w32 x, w33 x, w34 x, w35 x, w36 x, w37 x, w38 x, w39 x, w40 x, w41 x, w42 x, w43 x, w44 x, w45 x, w46 x, w47 x, w48 x, w49 x, w50 x, w51 x, w52 x, w53 x]
theorem step53 (x : Fin 24 → Bool) : step (state52 x) ⟨.or, [52, 10]⟩ = state53 x := rfl
def w54 (x : Fin 24 → Bool) : Bool := GateOp.eval .or [w53 x, x 12]
def state54 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, w24 x, w25 x, w26 x, w27 x, w28 x, w29 x, w30 x, w31 x, w32 x, w33 x, w34 x, w35 x, w36 x, w37 x, w38 x, w39 x, w40 x, w41 x, w42 x, w43 x, w44 x, w45 x, w46 x, w47 x, w48 x, w49 x, w50 x, w51 x, w52 x, w53 x, w54 x]
theorem step54 (x : Fin 24 → Bool) : step (state53 x) ⟨.or, [53, 12]⟩ = state54 x := rfl
def w55 (x : Fin 24 → Bool) : Bool := GateOp.eval .and [x 20, w54 x]
def state55 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, w24 x, w25 x, w26 x, w27 x, w28 x, w29 x, w30 x, w31 x, w32 x, w33 x, w34 x, w35 x, w36 x, w37 x, w38 x, w39 x, w40 x, w41 x, w42 x, w43 x, w44 x, w45 x, w46 x, w47 x, w48 x, w49 x, w50 x, w51 x, w52 x, w53 x, w54 x, w55 x]
theorem step55 (x : Fin 24 → Bool) : step (state54 x) ⟨.and, [20, 54]⟩ = state55 x := rfl
def w56 (x : Fin 24 → Bool) : Bool := GateOp.eval .or [x 0, x 6]
def state56 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, w24 x, w25 x, w26 x, w27 x, w28 x, w29 x, w30 x, w31 x, w32 x, w33 x, w34 x, w35 x, w36 x, w37 x, w38 x, w39 x, w40 x, w41 x, w42 x, w43 x, w44 x, w45 x, w46 x, w47 x, w48 x, w49 x, w50 x, w51 x, w52 x, w53 x, w54 x, w55 x, w56 x]
theorem step56 (x : Fin 24 → Bool) : step (state55 x) ⟨.or, [0, 6]⟩ = state56 x := rfl
def w57 (x : Fin 24 → Bool) : Bool := GateOp.eval .or [w56 x, x 10]
def state57 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, w24 x, w25 x, w26 x, w27 x, w28 x, w29 x, w30 x, w31 x, w32 x, w33 x, w34 x, w35 x, w36 x, w37 x, w38 x, w39 x, w40 x, w41 x, w42 x, w43 x, w44 x, w45 x, w46 x, w47 x, w48 x, w49 x, w50 x, w51 x, w52 x, w53 x, w54 x, w55 x, w56 x, w57 x]
theorem step57 (x : Fin 24 → Bool) : step (state56 x) ⟨.or, [56, 10]⟩ = state57 x := rfl
def w58 (x : Fin 24 → Bool) : Bool := GateOp.eval .or [w57 x, x 11]
def state58 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, w24 x, w25 x, w26 x, w27 x, w28 x, w29 x, w30 x, w31 x, w32 x, w33 x, w34 x, w35 x, w36 x, w37 x, w38 x, w39 x, w40 x, w41 x, w42 x, w43 x, w44 x, w45 x, w46 x, w47 x, w48 x, w49 x, w50 x, w51 x, w52 x, w53 x, w54 x, w55 x, w56 x, w57 x, w58 x]
theorem step58 (x : Fin 24 → Bool) : step (state57 x) ⟨.or, [57, 11]⟩ = state58 x := rfl
def w59 (x : Fin 24 → Bool) : Bool := GateOp.eval .and [x 21, w58 x]
def state59 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, w24 x, w25 x, w26 x, w27 x, w28 x, w29 x, w30 x, w31 x, w32 x, w33 x, w34 x, w35 x, w36 x, w37 x, w38 x, w39 x, w40 x, w41 x, w42 x, w43 x, w44 x, w45 x, w46 x, w47 x, w48 x, w49 x, w50 x, w51 x, w52 x, w53 x, w54 x, w55 x, w56 x, w57 x, w58 x, w59 x]
theorem step59 (x : Fin 24 → Bool) : step (state58 x) ⟨.and, [21, 58]⟩ = state59 x := rfl
def w60 (x : Fin 24 → Bool) : Bool := GateOp.eval .or [x 1, x 7]
def state60 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, w24 x, w25 x, w26 x, w27 x, w28 x, w29 x, w30 x, w31 x, w32 x, w33 x, w34 x, w35 x, w36 x, w37 x, w38 x, w39 x, w40 x, w41 x, w42 x, w43 x, w44 x, w45 x, w46 x, w47 x, w48 x, w49 x, w50 x, w51 x, w52 x, w53 x, w54 x, w55 x, w56 x, w57 x, w58 x, w59 x, w60 x]
theorem step60 (x : Fin 24 → Bool) : step (state59 x) ⟨.or, [1, 7]⟩ = state60 x := rfl
def w61 (x : Fin 24 → Bool) : Bool := GateOp.eval .or [w60 x, x 11]
def state61 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, w24 x, w25 x, w26 x, w27 x, w28 x, w29 x, w30 x, w31 x, w32 x, w33 x, w34 x, w35 x, w36 x, w37 x, w38 x, w39 x, w40 x, w41 x, w42 x, w43 x, w44 x, w45 x, w46 x, w47 x, w48 x, w49 x, w50 x, w51 x, w52 x, w53 x, w54 x, w55 x, w56 x, w57 x, w58 x, w59 x, w60 x, w61 x]
theorem step61 (x : Fin 24 → Bool) : step (state60 x) ⟨.or, [60, 11]⟩ = state61 x := rfl
def w62 (x : Fin 24 → Bool) : Bool := GateOp.eval .or [w61 x, x 12]
def state62 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, w24 x, w25 x, w26 x, w27 x, w28 x, w29 x, w30 x, w31 x, w32 x, w33 x, w34 x, w35 x, w36 x, w37 x, w38 x, w39 x, w40 x, w41 x, w42 x, w43 x, w44 x, w45 x, w46 x, w47 x, w48 x, w49 x, w50 x, w51 x, w52 x, w53 x, w54 x, w55 x, w56 x, w57 x, w58 x, w59 x, w60 x, w61 x, w62 x]
theorem step62 (x : Fin 24 → Bool) : step (state61 x) ⟨.or, [61, 12]⟩ = state62 x := rfl
def w63 (x : Fin 24 → Bool) : Bool := GateOp.eval .and [x 22, w62 x]
def state63 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, w24 x, w25 x, w26 x, w27 x, w28 x, w29 x, w30 x, w31 x, w32 x, w33 x, w34 x, w35 x, w36 x, w37 x, w38 x, w39 x, w40 x, w41 x, w42 x, w43 x, w44 x, w45 x, w46 x, w47 x, w48 x, w49 x, w50 x, w51 x, w52 x, w53 x, w54 x, w55 x, w56 x, w57 x, w58 x, w59 x, w60 x, w61 x, w62 x, w63 x]
theorem step63 (x : Fin 24 → Bool) : step (state62 x) ⟨.and, [22, 62]⟩ = state63 x := rfl
def w64 (x : Fin 24 → Bool) : Bool := GateOp.eval .or [x 0, x 2]
def state64 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, w24 x, w25 x, w26 x, w27 x, w28 x, w29 x, w30 x, w31 x, w32 x, w33 x, w34 x, w35 x, w36 x, w37 x, w38 x, w39 x, w40 x, w41 x, w42 x, w43 x, w44 x, w45 x, w46 x, w47 x, w48 x, w49 x, w50 x, w51 x, w52 x, w53 x, w54 x, w55 x, w56 x, w57 x, w58 x, w59 x, w60 x, w61 x, w62 x, w63 x, w64 x]
theorem step64 (x : Fin 24 → Bool) : step (state63 x) ⟨.or, [0, 2]⟩ = state64 x := rfl
def w65 (x : Fin 24 → Bool) : Bool := GateOp.eval .or [w64 x, x 8]
def state65 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, w24 x, w25 x, w26 x, w27 x, w28 x, w29 x, w30 x, w31 x, w32 x, w33 x, w34 x, w35 x, w36 x, w37 x, w38 x, w39 x, w40 x, w41 x, w42 x, w43 x, w44 x, w45 x, w46 x, w47 x, w48 x, w49 x, w50 x, w51 x, w52 x, w53 x, w54 x, w55 x, w56 x, w57 x, w58 x, w59 x, w60 x, w61 x, w62 x, w63 x, w64 x, w65 x]
theorem step65 (x : Fin 24 → Bool) : step (state64 x) ⟨.or, [64, 8]⟩ = state65 x := rfl
def w66 (x : Fin 24 → Bool) : Bool := GateOp.eval .or [w65 x, x 12]
def state66 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, w24 x, w25 x, w26 x, w27 x, w28 x, w29 x, w30 x, w31 x, w32 x, w33 x, w34 x, w35 x, w36 x, w37 x, w38 x, w39 x, w40 x, w41 x, w42 x, w43 x, w44 x, w45 x, w46 x, w47 x, w48 x, w49 x, w50 x, w51 x, w52 x, w53 x, w54 x, w55 x, w56 x, w57 x, w58 x, w59 x, w60 x, w61 x, w62 x, w63 x, w64 x, w65 x, w66 x]
theorem step66 (x : Fin 24 → Bool) : step (state65 x) ⟨.or, [65, 12]⟩ = state66 x := rfl
def w67 (x : Fin 24 → Bool) : Bool := GateOp.eval .and [x 23, w66 x]
def state67 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, w24 x, w25 x, w26 x, w27 x, w28 x, w29 x, w30 x, w31 x, w32 x, w33 x, w34 x, w35 x, w36 x, w37 x, w38 x, w39 x, w40 x, w41 x, w42 x, w43 x, w44 x, w45 x, w46 x, w47 x, w48 x, w49 x, w50 x, w51 x, w52 x, w53 x, w54 x, w55 x, w56 x, w57 x, w58 x, w59 x, w60 x, w61 x, w62 x, w63 x, w64 x, w65 x, w66 x, w67 x]
theorem step67 (x : Fin 24 → Bool) : step (state66 x) ⟨.and, [23, 66]⟩ = state67 x := rfl
def w68 (x : Fin 24 → Bool) : Bool := GateOp.eval .or [w27 x, w31 x]
def state68 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, w24 x, w25 x, w26 x, w27 x, w28 x, w29 x, w30 x, w31 x, w32 x, w33 x, w34 x, w35 x, w36 x, w37 x, w38 x, w39 x, w40 x, w41 x, w42 x, w43 x, w44 x, w45 x, w46 x, w47 x, w48 x, w49 x, w50 x, w51 x, w52 x, w53 x, w54 x, w55 x, w56 x, w57 x, w58 x, w59 x, w60 x, w61 x, w62 x, w63 x, w64 x, w65 x, w66 x, w67 x, w68 x]
theorem step68 (x : Fin 24 → Bool) : step (state67 x) ⟨.or, [27, 31]⟩ = state68 x := rfl
def w69 (x : Fin 24 → Bool) : Bool := GateOp.eval .or [w68 x, w35 x]
def state69 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, w24 x, w25 x, w26 x, w27 x, w28 x, w29 x, w30 x, w31 x, w32 x, w33 x, w34 x, w35 x, w36 x, w37 x, w38 x, w39 x, w40 x, w41 x, w42 x, w43 x, w44 x, w45 x, w46 x, w47 x, w48 x, w49 x, w50 x, w51 x, w52 x, w53 x, w54 x, w55 x, w56 x, w57 x, w58 x, w59 x, w60 x, w61 x, w62 x, w63 x, w64 x, w65 x, w66 x, w67 x, w68 x, w69 x]
theorem step69 (x : Fin 24 → Bool) : step (state68 x) ⟨.or, [68, 35]⟩ = state69 x := rfl
def w70 (x : Fin 24 → Bool) : Bool := GateOp.eval .or [w69 x, w39 x]
def state70 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, w24 x, w25 x, w26 x, w27 x, w28 x, w29 x, w30 x, w31 x, w32 x, w33 x, w34 x, w35 x, w36 x, w37 x, w38 x, w39 x, w40 x, w41 x, w42 x, w43 x, w44 x, w45 x, w46 x, w47 x, w48 x, w49 x, w50 x, w51 x, w52 x, w53 x, w54 x, w55 x, w56 x, w57 x, w58 x, w59 x, w60 x, w61 x, w62 x, w63 x, w64 x, w65 x, w66 x, w67 x, w68 x, w69 x, w70 x]
theorem step70 (x : Fin 24 → Bool) : step (state69 x) ⟨.or, [69, 39]⟩ = state70 x := rfl
def w71 (x : Fin 24 → Bool) : Bool := GateOp.eval .or [w70 x, w43 x]
def state71 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, w24 x, w25 x, w26 x, w27 x, w28 x, w29 x, w30 x, w31 x, w32 x, w33 x, w34 x, w35 x, w36 x, w37 x, w38 x, w39 x, w40 x, w41 x, w42 x, w43 x, w44 x, w45 x, w46 x, w47 x, w48 x, w49 x, w50 x, w51 x, w52 x, w53 x, w54 x, w55 x, w56 x, w57 x, w58 x, w59 x, w60 x, w61 x, w62 x, w63 x, w64 x, w65 x, w66 x, w67 x, w68 x, w69 x, w70 x, w71 x]
theorem step71 (x : Fin 24 → Bool) : step (state70 x) ⟨.or, [70, 43]⟩ = state71 x := rfl
def w72 (x : Fin 24 → Bool) : Bool := GateOp.eval .or [w71 x, w47 x]
def state72 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, w24 x, w25 x, w26 x, w27 x, w28 x, w29 x, w30 x, w31 x, w32 x, w33 x, w34 x, w35 x, w36 x, w37 x, w38 x, w39 x, w40 x, w41 x, w42 x, w43 x, w44 x, w45 x, w46 x, w47 x, w48 x, w49 x, w50 x, w51 x, w52 x, w53 x, w54 x, w55 x, w56 x, w57 x, w58 x, w59 x, w60 x, w61 x, w62 x, w63 x, w64 x, w65 x, w66 x, w67 x, w68 x, w69 x, w70 x, w71 x, w72 x]
theorem step72 (x : Fin 24 → Bool) : step (state71 x) ⟨.or, [71, 47]⟩ = state72 x := rfl
def w73 (x : Fin 24 → Bool) : Bool := GateOp.eval .or [w72 x, w51 x]
def state73 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, w24 x, w25 x, w26 x, w27 x, w28 x, w29 x, w30 x, w31 x, w32 x, w33 x, w34 x, w35 x, w36 x, w37 x, w38 x, w39 x, w40 x, w41 x, w42 x, w43 x, w44 x, w45 x, w46 x, w47 x, w48 x, w49 x, w50 x, w51 x, w52 x, w53 x, w54 x, w55 x, w56 x, w57 x, w58 x, w59 x, w60 x, w61 x, w62 x, w63 x, w64 x, w65 x, w66 x, w67 x, w68 x, w69 x, w70 x, w71 x, w72 x, w73 x]
theorem step73 (x : Fin 24 → Bool) : step (state72 x) ⟨.or, [72, 51]⟩ = state73 x := rfl
def w74 (x : Fin 24 → Bool) : Bool := GateOp.eval .or [w73 x, w55 x]
def state74 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, w24 x, w25 x, w26 x, w27 x, w28 x, w29 x, w30 x, w31 x, w32 x, w33 x, w34 x, w35 x, w36 x, w37 x, w38 x, w39 x, w40 x, w41 x, w42 x, w43 x, w44 x, w45 x, w46 x, w47 x, w48 x, w49 x, w50 x, w51 x, w52 x, w53 x, w54 x, w55 x, w56 x, w57 x, w58 x, w59 x, w60 x, w61 x, w62 x, w63 x, w64 x, w65 x, w66 x, w67 x, w68 x, w69 x, w70 x, w71 x, w72 x, w73 x, w74 x]
theorem step74 (x : Fin 24 → Bool) : step (state73 x) ⟨.or, [73, 55]⟩ = state74 x := rfl
def w75 (x : Fin 24 → Bool) : Bool := GateOp.eval .or [w74 x, w59 x]
def state75 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, w24 x, w25 x, w26 x, w27 x, w28 x, w29 x, w30 x, w31 x, w32 x, w33 x, w34 x, w35 x, w36 x, w37 x, w38 x, w39 x, w40 x, w41 x, w42 x, w43 x, w44 x, w45 x, w46 x, w47 x, w48 x, w49 x, w50 x, w51 x, w52 x, w53 x, w54 x, w55 x, w56 x, w57 x, w58 x, w59 x, w60 x, w61 x, w62 x, w63 x, w64 x, w65 x, w66 x, w67 x, w68 x, w69 x, w70 x, w71 x, w72 x, w73 x, w74 x, w75 x]
theorem step75 (x : Fin 24 → Bool) : step (state74 x) ⟨.or, [74, 59]⟩ = state75 x := rfl
def w76 (x : Fin 24 → Bool) : Bool := GateOp.eval .or [w75 x, w63 x]
def state76 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, w24 x, w25 x, w26 x, w27 x, w28 x, w29 x, w30 x, w31 x, w32 x, w33 x, w34 x, w35 x, w36 x, w37 x, w38 x, w39 x, w40 x, w41 x, w42 x, w43 x, w44 x, w45 x, w46 x, w47 x, w48 x, w49 x, w50 x, w51 x, w52 x, w53 x, w54 x, w55 x, w56 x, w57 x, w58 x, w59 x, w60 x, w61 x, w62 x, w63 x, w64 x, w65 x, w66 x, w67 x, w68 x, w69 x, w70 x, w71 x, w72 x, w73 x, w74 x, w75 x, w76 x]
theorem step76 (x : Fin 24 → Bool) : step (state75 x) ⟨.or, [75, 63]⟩ = state76 x := rfl
def w77 (x : Fin 24 → Bool) : Bool := GateOp.eval .or [w76 x, w67 x]
def state77 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, w24 x, w25 x, w26 x, w27 x, w28 x, w29 x, w30 x, w31 x, w32 x, w33 x, w34 x, w35 x, w36 x, w37 x, w38 x, w39 x, w40 x, w41 x, w42 x, w43 x, w44 x, w45 x, w46 x, w47 x, w48 x, w49 x, w50 x, w51 x, w52 x, w53 x, w54 x, w55 x, w56 x, w57 x, w58 x, w59 x, w60 x, w61 x, w62 x, w63 x, w64 x, w65 x, w66 x, w67 x, w68 x, w69 x, w70 x, w71 x, w72 x, w73 x, w74 x, w75 x, w76 x, w77 x]
theorem step77 (x : Fin 24 → Bool) : step (state76 x) ⟨.or, [76, 67]⟩ = state77 x := rfl

set_option maxRecDepth 32000 in
set_option maxHeartbeats 16000000 in
theorem computed (x : Fin 24 → Bool) : circuit.eval (List.ofFn x) = w77 x := by
  change (circuit.gates.foldl step (List.ofFn x)).getD circuit.output false = _
  have initial : List.ofFn x = start x := rfl
  rw [initial]
  simp only [circuit, List.foldl_cons, List.foldl_nil, step24, step25, step26, step27, step28, step29, step30, step31, step32, step33, step34, step35, step36, step37, step38, step39, step40, step41, step42, step43, step44, step45, step46, step47, step48, step49, step50, step51, step52, step53, step54, step55, step56, step57, step58, step59, step60, step61, step62, step63, step64, step65, step66, step67, step68, step69, step70, step71, step72, step73, step74, step75, step76, step77]
  rfl

set_option maxRecDepth 32000 in
set_option maxHeartbeats 16000000 in
theorem eval_exact (x : Fin 24 → Bool) :
    circuit.eval (List.ofFn x) = ((x 0 && x 15) || (x 0 && x 21) || (x 0 && x 23) || (x 1 && x 16) || (x 1 && x 22) || (x 2 && x 13) || (x 2 && x 17) || (x 2 && x 23) || (x 3 && x 13) || (x 3 && x 14) || (x 3 && x 18) || (x 4 && x 14) || (x 4 && x 15) || (x 4 && x 19) || (x 5 && x 13) || (x 5 && x 15) || (x 5 && x 16) || (x 5 && x 20) || (x 6 && x 14) || (x 6 && x 16) || (x 6 && x 17) || (x 6 && x 21) || (x 7 && x 15) || (x 7 && x 17) || (x 7 && x 18) || (x 7 && x 22) || (x 8 && x 16) || (x 8 && x 18) || (x 8 && x 19) || (x 8 && x 23) || (x 9 && x 17) || (x 9 && x 19) || (x 9 && x 20) || (x 10 && x 18) || (x 10 && x 20) || (x 10 && x 21) || (x 11 && x 13) || (x 11 && x 19) || (x 11 && x 21) || (x 11 && x 22) || (x 12 && x 14) || (x 12 && x 20) || (x 12 && x 22) || (x 12 && x 23)) := by
  rw [computed]
  simp only [w77, w76, w75, w74, w73, w72, w71, w70, w69, w68, w67, w66, w65, w64, w63, w62, w61, w60, w59, w58, w57, w56, w55, w54, w53, w52, w51, w50, w49, w48, w47, w46, w45, w44, w43, w42, w41, w40, w39, w38, w37, w36, w35, w34, w33, w32, w31, w30, w29, w28, w27, w26, w25, w24, GateOp.eval, List.any_cons, List.any_nil, List.all_cons,
    List.all_nil, id_eq, Bool.and_true, Bool.or_false,
    Bool.and_or_distrib_left]
  ac_rfl

theorem upper54 : HasCircuitSize 24 (fun x : Fin 24 → Bool => (x 0 && x 15) || (x 0 && x 21) || (x 0 && x 23) || (x 1 && x 16) || (x 1 && x 22) || (x 2 && x 13) || (x 2 && x 17) || (x 2 && x 23) || (x 3 && x 13) || (x 3 && x 14) || (x 3 && x 18) || (x 4 && x 14) || (x 4 && x 15) || (x 4 && x 19) || (x 5 && x 13) || (x 5 && x 15) || (x 5 && x 16) || (x 5 && x 20) || (x 6 && x 14) || (x 6 && x 16) || (x 6 && x 17) || (x 6 && x 21) || (x 7 && x 15) || (x 7 && x 17) || (x 7 && x 18) || (x 7 && x 22) || (x 8 && x 16) || (x 8 && x 18) || (x 8 && x 19) || (x 8 && x 23) || (x 9 && x 17) || (x 9 && x 19) || (x 9 && x 20) || (x 10 && x 18) || (x 10 && x 20) || (x 10 && x 21) || (x 11 && x 13) || (x 11 && x 19) || (x 11 && x 21) || (x 11 && x 22) || (x 12 && x 14) || (x 12 && x 20) || (x 12 && x 22) || (x 12 && x 23)) 54 :=
  ⟨circuit, fan_in, by rw [gate_count], eval_exact⟩

end LMeta9829Upper
