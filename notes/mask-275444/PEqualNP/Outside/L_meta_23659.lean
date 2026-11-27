import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23659

-- Adapted from L_meta_20636 by Julius Lehtinen for the 4 by 6 mask 275444.
-- The lower-bound engine (build, live, compress, cuts, dispatch, optimized, the front / chunk replay and
-- no_small) is the checked file lean/PEqualNP/Outside/L_meta_6343.lean of this repository, by Bastian Milan
-- (PR 12547, Apache-2.0); the widths, sample lists and bound are regenerated for this graph.

section Live

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

theorem compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero =>
    exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ available := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s, hs, Or.inr ⟨a, by simp [s], b, by simp [s], hab, z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

theorem live_card {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal k s) : s.card ≤ k + 1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

theorem live_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live ops goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩

theorem first_live {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal (k + 1) s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, tail⟩
      · exact .inl done
      · exact .inr ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, Or.inl tail⟩
    · exact .inr step

end Live

abbrev W := BitVec 280

def ops (x y : W) : List W := [x &&& y, x ||| y]

def sep (x : W) : BitVec 140 := ((x >>> 140) &&& ~~~x).setWidth 140

def cuts (ws : List W) : BitVec 140 := ws.foldr (fun w v => sep w ||| v) 0

def goal : W := (-1 : BitVec 140) ++ (0 : BitVec 140)

def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

def rawInputs : List W :=
  [0x3ffffffffff001c007001c007001c007001c007001c007, 0x3fffffffffffffc000000000000600180060018006001800600180060018, 0x3ffffffc00000000000000000000000007801e007801e007801e007801e007801e0, 0xfffc0000000000000000000000000000000f803e00f803e00f803e00f803e00f803e00, 0xfffc000fffc0000000000fffc000000000000040010004001000400100040010004001, 0x3fff00000000003fff0000000000000008082020808202080820208082020808202, 0xfffc00000000000003fff10804201080420108042010804201080420, 0x3fff00000000000000000000021108442110844211084421108442110844, 0xfffc00042210884221088422108842210884221088, 0x3fff000000084421108442110844211084421108442110]

def inputs : List W := rawInputs

theorem pick_one {α : Type} {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a, rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, rest), hm, rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

theorem pick_two {α : Type} {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b, r), hm, rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) (by assumption)
        exact ⟨r, .inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a, r), hm, rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_,
          (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a, b, r), hm, rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b, a, r), hm, rfl⟩))

abbrev basicOps (a b : W) : Finset W := (ops a b).toFinset

def differs (i : Fin 140) (w : W) : Prop :=
  w.getLsbD (140 + i.val) = true ∧ w.getLsbD i.val = false

theorem ops_differs (i : Fin 140) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  unfold differs at hd ⊢
  rcases hz with rfl | rfl <;> revert hd <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or] <;>
    cases a.getLsbD (140 + i.val) <;> cases a.getLsbD i.val <;>
    cases b.getLsbD (140 + i.val) <;> cases b.getLsbD i.val <;> simp

theorem goal_differs : ∀ i : Fin 140, differs i goal := by
  unfold differs
  decide +kernel

theorem cuts_spec (ws : List W) (i : Fin 140) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have hi : i.val < 280 := by omega
    simp [sep, i.isLt, differs, hi, Nat.add_comm]

theorem cuts_full {k : ℕ} {ws : List W} (h : live basicOps goal k ws.toFinset) :
    cuts ws = -1 := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (goal_differs ⟨j, hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 140)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp [basicOps, ops, BitVec.and_comm, BitVec.or_comm]

def keepChoices (a b : W) (r : List W) : List (List W) := [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept {ws r : List W} {a b : W} {needed : Finset W}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

theorem singleton_list {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def possible (w : List W) (z : W) : Bool :=
  z == 0 || z == BitVec.allOnes 280 || w.any (fun u => z == u ||
    w.any (fun v => z == (u &&& v) || z == (u ||| v)))

private def bit (k : Fin 280) (z : W) : Bool := z[k.val]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 280) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

private theorem read_wire (w : List W) (i : ℕ) : w.getD i 0 = 0 ∨ w.getD i 0 ∈ w := by
  by_cases h : i < w.length
  · exact Or.inr (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_gt h)]

private theorem atom {ws : List W} {x : W} (hx : x = 0 ∨ x ∈ ws) : possible ws x := by
  rcases hx with rfl | hx
  · simp [possible]
  · simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    exact .inr ⟨x, hx, .inl rfl⟩

private theorem pair {ws : List W} {x y : W} (hx : x = 0 ∨ x ∈ ws) (hy : y = 0 ∨ y ∈ ws) :
    possible ws (x &&& y) ∧ possible ws (x ||| y) := by
  rcases hx with rfl | hx
  · simpa [possible] using atom hy
  rcases hy with rfl | hy
  · simpa [possible] using atom (.inr hx)
  · simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    constructor
    · exact .inr ⟨x, hx, .inr ⟨y, hy, .inl rfl⟩⟩
    · exact .inr ⟨x, hx, .inr ⟨y, hy, .inr rfl⟩⟩

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def legal (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2

set_option maxRecDepth 2000 in
private theorem gate_table (w ws : List W) (hw : w ⊆ ws) (g : Gate) (hg : legal g) :
    ∃ z, possible ws z ∧ ∀ k, step (w.map (bit k)) g = (w ++ [z]).map (bit k) := by
  have mem (i : ℕ) : w.getD i 0 = 0 ∨ w.getD i 0 ∈ ws :=
    (read_wire w i).imp_right (fun h => hw h)
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  change op = .and ∨ op = .or at hop
  change args.length ≤ 2 at hlen
  cases args with
  | nil =>
    rcases hop with rfl | rfl
    · exact ⟨BitVec.allOnes 280, by simp [possible], by simp [step, GateOp.eval, bit]; decide⟩
    · exact ⟨0, by simp [possible], by simp [step, GateOp.eval, bit]⟩
  | cons i tail =>
    cases tail with
    | nil =>
      rcases hop with rfl | rfl
      · exact ⟨_, atom (mem i),
          by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval]⟩
      · exact ⟨_, atom (mem i),
          by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval]⟩
    | cons j tail =>
      cases tail with
      | cons => simp at hlen
      | nil =>
        rcases hop with rfl | rfl
        · exact ⟨_, (pair (mem i) (mem j)).1,
            by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit]⟩
        · exact ⟨_, (pair (mem i) (mem j)).2,
            by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit]⟩

def represents (available : Finset W) (w : List W) : Prop :=
  ∀ u ∈ w, u = 0 ∨ u = BitVec.allOnes 280 ∨ u ∈ available

theorem classify {available : Finset W} {ws : List W} (hw : represents available ws)
    {z : W} (hz : possible ws z) :
    z = 0 ∨ z = BitVec.allOnes 280 ∨ z ∈ available ∨
      ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧ z ∈ basicOps a b := by
  have lift {t : W} (h : t = 0 ∨ t = BitVec.allOnes 280 ∨ t ∈ available) :
      t = 0 ∨ t = BitVec.allOnes 280 ∨ t ∈ available ∨
        ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧ t ∈ basicOps a b :=
    h.imp_right (Or.imp_right Or.inl)
  simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at hz
  rcases hz with ((h | h) | ⟨x, hx, h | ⟨y, hy, h | h⟩⟩)
  · exact .inl h
  · exact .inr (.inl h)
  · subst z; exact lift (hw _ hx)
  · subst z
    rcases hw _ hx with rfl | rfl | hu
    · left; simp
    · rw [BitVec.allOnes_and]; exact lift (hw _ hy)
    rcases hw _ hy with rfl | rfl | hv
    · left; simp
    · rw [BitVec.and_allOnes]; exact .inr (.inr (.inl hu))
    by_cases h : x = y
    · subst h; rw [BitVec.and_self]; exact .inr (.inr (.inl hu))
    · exact .inr (.inr (.inr ⟨x, hu, y, hv, h, by simp [basicOps, ops]⟩))
  · subst z
    rcases hw _ hx with rfl | rfl | hu
    · rw [show (0 : W) ||| y = y by ext i hi; simp]; exact lift (hw _ hy)
    · right; left; exact BitVec.allOnes_or
    rcases hw _ hy with rfl | rfl | hv
    · rw [show x ||| (0 : W) = x by ext i hi; simp]; exact .inr (.inr (.inl hu))
    · right; left; exact BitVec.or_allOnes
    by_cases h : x = y
    · subst h; rw [BitVec.or_self]; exact .inr (.inr (.inl hu))
    · exact .inr (.inr (.inr ⟨x, hu, y, hv, h, by simp [basicOps, ops]⟩))

private theorem compile (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W) (av : Finset W) (hw : represents av w)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false = bit k goal) :
    build basicOps goal gs.length av := by
  induction gs generalizing w av with
  | nil =>
    have hval : w.getD out 0 = goal := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i, hi⟩
    have hr := read_wire w out
    rw [hval] at hr
    rcases hr with hz | hm
    · exact False.elim ((by decide : goal ≠ (0 : W)) hz)
    · rcases hw _ hm with h | h | h
      · exact False.elim ((by decide : goal ≠ (0 : W)) h)
      · exact False.elim ((by decide : goal ≠ BitVec.allOnes 280) h)
      · exact h
  | cons g gs ih =>
    obtain ⟨z, hz, hstep⟩ := gate_table w w (fun _ h => h) g (hg g (by simp))
    have fn := ih (fun g' h => hg g' (by simp [h])) (w ++ [z])
    have he' : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k goal := by
      intro k; simpa only [List.foldl_cons, hstep] using he k
    have appendOK (h : z = 0 ∨ z = BitVec.allOnes 280 ∨ z ∈ av) : represents av (w ++ [z]) := by
      intro u hu
      rcases List.mem_append.mp hu with old | fresh
      · exact hw _ old
      · have eq : u = z := List.mem_singleton.mp fresh
        exact eq ▸ h
    rcases classify hw hz with h | h | h | ⟨a, ha, b, hb, hab, hop⟩
    · exact Or.inl (fn av (appendOK (.inl h)) he')
    · exact Or.inl (fn av (appendOK (.inr (.inl h))) he')
    · exact Or.inl (fn av (appendOK (.inr (.inr h))) he')
    · refine Or.inr ⟨a, ha, b, hb, hab, z, hop, fn (insert z av) ?_ he'⟩
      intro u hu
      rcases List.mem_append.mp hu with hu | hu
      · exact (hw _ hu).imp_right (Or.imp_right (Finset.mem_insert_of_mem ·))
      · simp_all

def dispatch (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) : Bool :=
  let base := cuts r
  (ops a b).any fun w =>
    let v := sep w ||| base
    ((v == -1) && next extra (w :: r)) ||
    ((extra != 0) && (((v ||| sep a == -1) && next (extra - 1) (w :: a :: r)) ||
                       ((v ||| sep b == -1) && next (extra - 1) (w :: b :: r)))) ||
    ((extra ≥ 2) && (v ||| sep a ||| sep b == -1) && next (extra - 2) (w :: a :: b :: r))

def optimized : ℕ → ℕ → List W → Bool
  | 0, _, ws => ws == [goal]
  | k + 1, extra, ws => ws == [goal] ||
    (pairs ws).any (fun (a, b, r) => dispatch extra (optimized k) a b r)

theorem dispatch_complete {k extra : ℕ} {a b z : W} {r kept : List W}
    (next : ℕ → List W → Bool)
    (hz : z ∈ basicOps a b) (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cuts (z :: kept) = -1) (ht : next (k - kept.length) (z :: kept) = true) :
    dispatch extra next a b r = true := by
  apply List.any_eq_true.mpr
  refine ⟨z, List.mem_toFinset.mp hz, ?_⟩
  simp [keepChoices] at hk
  rcases hk with rfl | rfl | rfl | rfl <;>
    simp only [cuts, List.foldr_cons] at hc ⊢ <;>
    (try simp only [List.length_cons] at *) <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne]
  · left; left; exact ⟨hc, by convert ht using 2; omega⟩
  · left; right; exact ⟨by omega, .inl ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · left; right; exact ⟨by omega, .inr ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · right; exact ⟨⟨by omega, by convert hc using 1; ac_rfl⟩, by convert ht using 2; omega⟩

theorem optimized_complete (n : ℕ) (ws : List W) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n + 1) (h : live basicOps goal n ws.toFinset) :
    optimized n extra ws = true := by
  induction n generalizing ws extra with
  | zero => simp [optimized, singleton_list hn h]
  | succ k ih =>
    rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
    · simp [optimized, singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : W} (perm : ws.Perm (a :: b :: r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          dispatch extra (optimized k) a b r = true := by
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live basicOps goal k (z :: kept).toFinset := by
          simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        apply dispatch_complete (k := k) (extra := extra) (optimized k) hop hk (by omega) (by omega) (cuts_full hl)
        apply ih _ _ hnd _ hl
        simp; omega
      simp only [optimized, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, go hp hs hz⟩
      · exact ⟨(b, a, r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩


def A : Fin 4 → Fin 6 → Bool := fun u v => (275444 : ℕ).testBit (6 * u.val + v.val)

def posL : List (Fin 4 × Fin 6) :=
  [(0, 2), (0, 4), (0, 5), (1, 0), (1, 1), (1, 2), (1, 3), (2, 0), (2, 1), (3, 0)]

def negL : List (Fin 4 × Fin 6) :=
  [(0, 0), (0, 1), (0, 3), (1, 4), (1, 5), (2, 2), (2, 3), (2, 4), (2, 5), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5)]

def samp (k : Fin 280) : Fin 4 × Fin 6 :=
  if k.val < 140 then negL.getD (k.val % 14) (0, 0) else posL.getD ((k.val - 140) / 14) (0, 0)

theorem input_rows : ∀ k : Fin 280,
    rawInputs.map (bit k) = PEqualNP.Represents.oneEach (samp k).1 (samp k).2 := by
  decide +kernel

theorem goal_rows : ∀ k : Fin 280, bit k goal = A (samp k).1 (samp k).2 := by
  decide +kernel

theorem rows_eval (C : Circuit) (hr : PEqualNP.Represents.Represents A C) (k : Fin 280) :
    (C.gates.foldl step (rawInputs.map (bit k))).getD C.output false = bit k goal := by
  rw [input_rows k, goal_rows k]
  exact hr (samp k).1 (samp k).2

theorem initial_rep : represents inputs.toFinset rawInputs := by
  intro u hu
  exact .inr (.inr (List.mem_toFinset.mpr hu))

theorem get_build (C : Circuit) (hg : Monotone2 C) (hr : PEqualNP.Represents.Represents A C) :
    build basicOps goal C.gates.length inputs.toFinset :=
  compile C.gates C.output hg rawInputs inputs.toFinset initial_rep (rows_eval C hr)

theorem extend_live {m n : ℕ} {s : Finset W} (le : m ≤ n) (h : live basicOps goal m s) :
    live basicOps goal n s := by
  induction le with
  | refl => exact h
  | step _ ih => exact Or.inl ih

theorem inputs_nodup : inputs.Nodup := by decide +kernel

def localLayer (oracle : Nat → List W → Bool) (extra : Nat) (ws : List W) : Bool :=
  ws == [goal] || (pairs ws).any fun (a,b,r) => dispatch extra oracle a b r
theorem layer_closed (k : Nat) (ws : List W) (extra : Nat) (oracle : Nat → List W → Bool)
    (hn : ws.Nodup) (room : extra + ws.length = k + 2)
    (sound : ∀ (l : List W) (e : Nat), l.Nodup → e + l.length = k+1 → live basicOps goal k l.toFinset → oracle e l = true)
    (closed : localLayer oracle extra ws = false) : ¬ live basicOps goal (k+1) ws.toFinset := by
  intro h
  suffices success : localLayer oracle extra ws = true by simp [closed] at success
  rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
  · simp [localLayer, singleton_list hn done]
  · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
    have go {a b : W} (perm : ws.Perm (a :: b :: r))
        (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
        dispatch extra oracle a b r = true := by
      obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
      have hznew : z ∉ kept := by
        intro hu
        apply hout
        rw [hset]
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
      have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
      have hl : live basicOps goal k (z :: kept).toFinset := by simpa [hfin] using tail
      have hc := live_card hl
      rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
      have len := perm.length_eq
      simp only [List.length_cons] at len
      apply dispatch_complete (k := k) (extra := extra) oracle hop hk (by omega) (by omega) (cuts_full hl)
      apply sound _ _ hnd _ hl
      simp; omega
    simp only [localLayer, Bool.or_eq_true, List.any_eq_true]
    right
    rcases hm with direct | swap
    · exact ⟨(a, b, r), direct, go hp hs hz⟩
    · exact ⟨(b, a, r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩


section RectanglePartition
variable {α : Type} [DecidableEq α] {P N : Type}

structure KWChoice (s : Finset α) (D : α → P → N → Prop) where
  lbl : P → N → α
  usable : ∀ i j, lbl i j ∈ s
  correct : ∀ i j, D (lbl i j) i j
  rect : ∀ i j i' j', lbl i j = lbl i' j' → lbl i j' = lbl i j

private theorem sameFibre {a b z x y : α} {dx dy : Bool}
    (ha : x = z ∨ x ≠ a ∧ x ≠ b) (hb : y = z ∨ y ≠ a ∧ y ≠ b)
    (h : (if x = z then (if dx then a else b) else x) =
         (if y = z then (if dy then a else b) else y)) : x = y := by
  by_cases hx : x = z
  · by_cases hy : y = z
    · exact hx.trans hy.symm
    · obtain ⟨hya,hyb⟩ := hb.resolve_left hy
      cases dx <;> simp [hx,hy] at h
      · exact False.elim (hyb h.symm)
      · exact False.elim (hya h.symm)
  · by_cases hy : y = z
    · obtain ⟨hxa,hxb⟩ := ha.resolve_left hx
      cases dy <;> simp [hx,hy] at h
      · exact False.elim (hxb h)
      · exact False.elim (hxa h)
    · simpa [hx,hy] using h

noncomputable def kwChoiceExpand {s : Finset α} {a b z : α} {D : α → P → N → Prop}
    (ha : a ∉ s) (hb : b ∉ s) (hab : a ≠ b) (h : KWChoice (insert z s) D)
    (side : P → N → Bool)
    (cs : (∀ i j j', side i j = side i j') ∨ (∀ i i' j, side i j = side i' j))
    (split : ∀ i j, D z i j → D (if side i j then a else b) i j) :
    KWChoice (insert a (insert b s)) D := by
  classical
  let lab := fun i j => if h.lbl i j = z then (if side i j then a else b) else h.lbl i j
  refine ⟨lab, ?_, ?_, ?_⟩
  · intro i j
    by_cases hz : h.lbl i j = z
    · cases hs : side i j <;> simp [lab,hz,hs]
    · have hm := h.usable i j
      simp [hz] at hm
      simp [lab,hz,hm]
  · intro i j
    by_cases hz : h.lbl i j = z
    · simpa [lab,hz] using (split i j (hz ▸ h.correct i j))
    · simpa [lab,hz] using h.correct i j
  · intro i j i' j' he
    have classify (i : P) (j : N) : h.lbl i j = z ∨ h.lbl i j ≠ a ∧ h.lbl i j ≠ b := by
      rcases Finset.mem_insert.mp (h.usable i j) with hz | hm
      · exact .inl hz
      · exact .inr ⟨fun eq => ha (eq ▸ hm), fun eq => hb (eq ▸ hm)⟩
    have eq := sameFibre (classify i j) (classify i' j') he
    have cross := h.rect i j i' j' eq
    by_cases hz : h.lbl i j = z
    · have hz' := eq.symm.trans hz
      have hzCross := cross.trans hz
      have hs : side i j = side i' j' := by
        cases h1 : side i j <;> cases h2 : side i' j'
        · rfl
        · exact False.elim (hab (by simpa [lab,hz,hz',h1,h2] using he.symm))
        · exact False.elim (hab (by simpa [lab,hz,hz',h1,h2] using he))
        · rfl
      rcases cs with left | right
      · simp [lab,hz,hzCross,left i j' j]
      · simp [lab,hz,hzCross,right i i' j',hs]
    · simp [lab,cross,hz]

theorem zeroSlackKW {op : α → α → Finset α} {g : α} {D : α → P → N → Prop}
    (hg : ∀ i j, D g i j)
    (hops : ∀ a b z, z ∈ op a b →
      ∃ side : P → N → Bool,
        ((∀ i j j', side i j = side i j') ∨ (∀ i i' j, side i j = side i' j)) ∧
        (∀ i j, D z i j → D (if side i j then a else b) i j)) :
    ∀ {k : ℕ} {s : Finset α}, s.card = k+1 → live op g k s → Nonempty (KWChoice s D) := by
  intro k
  induction k with
  | zero =>
    intro s _ H
    change s = {g} at H
    subst s
    exact ⟨⟨fun _ _ => g, by simp, hg, by simp⟩⟩
  | succ k ih =>
    intro s hs run
    rcases run with less | ⟨a,ha,b,hb,hab,z,hz,hout,r,he,tail⟩
    · have := live_card less; omega
    · subst s
      have hz' : z ∉ r := fun hh => hout (by simp [hh])
      have small := live_card tail
      rw [Finset.card_insert_of_notMem hz'] at small
      have hbcard := Finset.card_insert_le b r
      have h1 := Finset.card_insert_le a (insert b r)
      have rsize : r.card = k := by omega
      have hrb : b ∉ r := by
        intro hm
        rw [Finset.insert_eq_of_mem hm] at hs
        have := Finset.card_insert_le a r
        omega
      have hra : a ∉ r := by
        intro hm
        have ha' : a ∈ insert b r := by simp [hm]
        rw [Finset.insert_eq_of_mem ha'] at hs
        omega
      obtain ⟨ch⟩ := ih (s := insert z r) (by rw [Finset.card_insert_of_notMem hz',rsize]) tail
      obtain ⟨f,hf,hc⟩ := hops a b z hz
      exact ⟨kwChoiceExpand hra hrb hab ch f hf hc⟩


omit [DecidableEq α] in
theorem kwQuadImpossible {s : Finset α} {D : α → P → N → Prop} (ch : KWChoice s D)
    (p p₁ p₂ : P) (n n₁ n₂ : N) (a b : α) (hab : a ≠ b)
    (a₁ : ∀ w ∈ s, D w p n₁ → w = a)
    (a₂ : ∀ w ∈ s, D w p₁ n → w = a)
    (b₁ : ∀ w ∈ s, D w p n₂ → w = b)
    (b₂ : ∀ w ∈ s, D w p₂ n → w = b) : False := by
  have x₁ := a₁ _ (ch.usable p n₁) (ch.correct p n₁)
  have x₂ := a₂ _ (ch.usable p₁ n) (ch.correct p₁ n)
  have y₁ := b₁ _ (ch.usable p n₂) (ch.correct p n₂)
  have y₂ := b₂ _ (ch.usable p₂ n) (ch.correct p₂ n)
  have ac := (ch.rect p n₁ p₁ n (x₁.trans x₂.symm)).trans x₁
  have bc := (ch.rect p n₂ p₂ n (y₁.trans y₂.symm)).trans y₁
  exact hab (ac.symm.trans bc)

end RectanglePartition

def kwSep (w : W) (p : Fin 10) (n : Fin 14) : Prop :=
  w.getLsbD (140 + 14*p.val) = true ∧ w.getLsbD n.val = false

instance (w : W) (p : Fin 10) (n : Fin 14) : Decidable (kwSep w p n) := by
  unfold kwSep
  infer_instance

theorem kwOfBasic {s : Finset W} {k : ℕ}
    (hc : s.card = k+1) (hl : live basicOps goal k s) : Nonempty (KWChoice s kwSep) := by
  apply zeroSlackKW (g := goal) (op := basicOps) _ _ hc hl
  · decide +kernel
  · intro a b z hz
    simp only [basicOps,ops,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl
    · refine ⟨fun _ n => !a.getLsbD n.val, .inr (by simp), ?_⟩
      intro p n hd
      simp only [kwSep,BitVec.getLsbD_and,Bool.and_eq_true] at hd
      rcases hd with ⟨⟨ha,hb⟩,h⟩
      cases hn : a.getLsbD n.val <;> simp_all [kwSep]
    · refine ⟨fun p _ => a.getLsbD (140 + 14*p.val), .inl (by simp), ?_⟩
      intro p n hd
      simp only [kwSep,BitVec.getLsbD_or,Bool.or_eq_false_iff] at hd
      rcases hd with ⟨h,ha,hb⟩
      cases hp : a.getLsbD (140+14*p.val) <;> simp_all [kwSep]

def kwOnly (l : List W) (w : W) (p : Fin 10) (n : Fin 14) : Bool :=
  l.all fun x => !decide (kwSep x p n) || x == w

theorem kwOnlySound {l : List W} {w : W} {p : Fin 10} {n : Fin 14}
    (h : kwOnly l w p n = true) : ∀ x ∈ l.toFinset, kwSep x p n → x = w := by
  intro x hx hD
  have h' := List.all_eq_true.mp h x (List.mem_toFinset.mp hx)
  simpa [hD] using h'

theorem kwPrune {l : List W} {k : ℕ} (hc : l.toFinset.card = k + 1)
    (p p₁ p₂ : Fin 10) (n n₁ n₂ : Fin 14) (a b : W)
    (h : a != b && kwOnly l a p n₁ && kwOnly l a p₁ n &&
          kwOnly l b p n₂ && kwOnly l b p₂ n) : ¬ live basicOps goal k l.toFinset := by
  intro hl
  obtain ⟨ch⟩ := kwOfBasic hc hl
  simp only [Bool.and_eq_true,bne_iff_ne] at h
  exact kwQuadImpossible ch p p₁ p₂ n n₁ n₂ a b h.1.1.1.1
    (kwOnlySound h.1.1.1.2) (kwOnlySound h.1.1.2)
    (kwOnlySound h.1.2) (kwOnlySound h.2)


-- Each 14-bit block is one positive input against all 14 negative inputs.
-- The bit scan supplies guesses. Only the four direct separation checks
-- below certify a successful guess, including on arbitrary wire lists.
structure KWFeatures where
  wire : W
  unique : Nat
  rows : Nat
  cols : Nat

structure KWGuess where
  p : Fin 10
  p₁ : Fin 10
  p₂ : Fin 10
  n : Fin 14
  n₁ : Fin 14
  n₂ : Fin 14
  a : W
  b : W

def kwStride : Nat := 0x40010004001000400100040010004001
def kwLow : Nat := 0x7ffdfff7ffdfff7ffdfff7ffdfff7ffdfff

def kwFeatures (l : List W) : List KWFeatures :=
  let dup := (l.foldl (fun (s : BitVec 140 × BitVec 140) w =>
    let c := sep w
    (s.1 ||| c, s.2 ||| (s.1 &&& c))) (0,0)).2
  l.map fun w =>
    let u := ((sep w) &&& ~~~dup).toNat
    let rows := (((u &&& kwLow) + kwLow) ||| u) &&& (kwStride <<< 13)
    let c := u ||| (u >>> 14)
    let c := c ||| (c >>> 28)
    let c := c ||| (c >>> 56)
    let c := c ||| (c >>> 112)
    ⟨w, u, rows, c &&& 16383⟩

def kwFindPair (a b : KWFeatures) : Option KWGuess := do
  let rows := a.rows &&& b.rows
  let cols := a.cols &&& b.cols
  if rows == 0 || cols == 0 then none else
    let p := rows.log2 / 14
    let n := cols.log2
    let row (u : Nat) := (u &&& (kwStride <<< n)).log2 / 14
    let col (u : Nat) := ((u >>> (14*p)) &&& 16383).log2
    some ⟨Fin.ofNat 10 p, Fin.ofNat 10 (row a.unique), Fin.ofNat 10 (row b.unique),
      Fin.ofNat 14 n, Fin.ofNat 14 (col a.unique), Fin.ofNat 14 (col b.unique),
      a.wire, b.wire⟩

def kwFind : List KWFeatures → Option KWGuess
  | [] => none
  | a :: xs => match xs.findSome? (kwFindPair a) with
    | some g => some g
    | none => kwFind xs

def kwImpossible (l : List W) : Bool :=
  match kwFind (kwFeatures l) with
  | none => false
  | some g =>
    (g.a != g.b) && kwOnly l g.a g.p g.n₁ && kwOnly l g.a g.p₁ g.n &&
      kwOnly l g.b g.p g.n₂ && kwOnly l g.b g.p₂ g.n

theorem kwImpossible_sound {l : List W} {k : ℕ}
    (card : l.toFinset.card = k+1) (h : kwImpossible l = true) :
    ¬ live basicOps goal k l.toFinset := by
  unfold kwImpossible at h
  split at h
  · contradiction
  · rename_i g hg
    exact kwPrune card g.p g.p₁ g.p₂ g.n g.n₁ g.n₂ g.a g.b h

def wireTag (w : W) : Nat :=
  let a := w.toNat % 65521
  a * a % 65521

def stateTag (ws : List W) : Nat :=
  (ws.foldl (fun acc w => acc + wireTag w) 0) % 65521

structure Chart (k : Nat) where
  wires : List W
  tag : Nat
  closed : ¬ live basicOps goal k wires.toFinset

def chartOpen {k : Nat} (known : List (Chart k)) (e : Nat) (l : List W) : Bool :=
  let t := stateTag l
  !((e == 0) && kwImpossible l) &&
    decide l.Nodup && !(known.any fun c => (c.tag == t) && c.wires.toFinset == l.toFinset)

theorem chartOpen_sound {k : Nat} (known : List (Chart k))
    (l : List W) (e : Nat) (hN : l.Nodup) (room : e + l.length = k+1)
    (h : live basicOps goal k l.toFinset) : chartOpen known e l = true := by
  have avoid : ((e == 0) && kwImpossible l) = false := by
    by_cases he : e = 0
    · have card : l.toFinset.card = k+1 := by
        rw [List.toFinset_card_of_nodup hN]
        omega
      have no := Bool.eq_false_iff.mpr (fun bad => kwImpossible_sound card bad h)
      simp [no]
    · simp [he]
  simp only [chartOpen, avoid, Bool.not_false, hN, decide_true, Bool.true_and, Bool.not_eq_true', List.any_eq_false]
  intro c _ hin
  simp only [Bool.and_eq_true, beq_iff_eq] at hin
  exact c.closed (hin.2.symm ▸ h)

def make {k : Nat} (t : Nat) (ws : List W) (next : List (Chart k))
    (test : ws.Nodup ∧ (k+2-ws.length) + ws.length = k+2 ∧
      localLayer (chartOpen next) (k+2-ws.length) ws = false) : Chart (k+1) := by
  refine ⟨ws, t, layer_closed k ws (k+2-ws.length) (chartOpen next) test.1 test.2.1 ?_ test.2.2⟩
  exact chartOpen_sound next
def causalMark : List (Fin 140) := [5, 42, 98, 126, 45, 59, 0, 87, 14, 28]
theorem source_indispensable {k : Nat} {s : Finset W} (hs : s ⊆ inputs.toFinset) (h : live basicOps goal k s) : s = inputs.toFinset := by
  apply Finset.Subset.antisymm hs
  intro w hw
  have markers : ∀ w ∈ inputs, ∃ i ∈ causalMark, ∀ u ∈ inputs, differs i u → u = w := by
    intro w hw
    simp only [inputs, rawInputs, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨5, by decide +kernel, ?_⟩
      intro u hu
      simp only [inputs, rawInputs, List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> unfold differs <;> decide +kernel
    · refine ⟨42, by decide +kernel, ?_⟩
      intro u hu
      simp only [inputs, rawInputs, List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> unfold differs <;> decide +kernel
    · refine ⟨98, by decide +kernel, ?_⟩
      intro u hu
      simp only [inputs, rawInputs, List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> unfold differs <;> decide +kernel
    · refine ⟨126, by decide +kernel, ?_⟩
      intro u hu
      simp only [inputs, rawInputs, List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> unfold differs <;> decide +kernel
    · refine ⟨45, by decide +kernel, ?_⟩
      intro u hu
      simp only [inputs, rawInputs, List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> unfold differs <;> decide +kernel
    · refine ⟨59, by decide +kernel, ?_⟩
      intro u hu
      simp only [inputs, rawInputs, List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> unfold differs <;> decide +kernel
    · refine ⟨0, by decide +kernel, ?_⟩
      intro u hu
      simp only [inputs, rawInputs, List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> unfold differs <;> decide +kernel
    · refine ⟨87, by decide +kernel, ?_⟩
      intro u hu
      simp only [inputs, rawInputs, List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> unfold differs <;> decide +kernel
    · refine ⟨14, by decide +kernel, ?_⟩
      intro u hu
      simp only [inputs, rawInputs, List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> unfold differs <;> decide +kernel
    · refine ⟨28, by decide +kernel, ?_⟩
      intro u hu
      simp only [inputs, rawInputs, List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> unfold differs <;> decide +kernel
  obtain ⟨i, _, hi⟩ := markers w (List.mem_toFinset.mp hw)
  obtain ⟨z, hz, hsep⟩ := live_separates (differs i) (goal_differs i) (ops_differs i) h
  exact hi z (List.mem_toFinset.mp (hs hz)) hsep ▸ hz

section Project
variable {α β : Type} [DecidableEq α] [DecidableEq β]

theorem weakenBuild {op : β → β → Finset β} {goal : β}
    {n : Nat} {a b : Finset β} (inc : a ⊆ b) (h : build op goal n a) : build op goal n b := by
  induction n generalizing a b with
  | zero => exact inc h
  | succ n ih =>
    rcases h with skip | ⟨x,hx,y,hy,ne,z,hz,rest⟩
    · exact Or.inl (ih inc skip)
    · exact Or.inr ⟨x,inc hx,y,inc hy,ne,z,hz,ih (Finset.insert_subset_insert z inc) rest⟩

def projAvail (f : α → β) (off : β) (s : Finset α) := (s.image f).erase off
def projCharge (f : α → β) (off : β) (s : Finset α) : Nat := if off ∈ s.image f then 1 else 0

theorem projectLive {op : α → α → Finset α} {op' : β → β → Finset β}
    (f : α → β) (off : β) (goal : α) (nontriv : f goal ≠ off)
    (gate : ∀ a b z, z ∈ op a b → f z = off ∨ f z = f a ∨ f z = f b ∨
      (f a ≠ off ∧ f b ≠ off ∧ f a ≠ f b ∧ f z ∈ op' (f a) (f b)))
    {n : Nat} {s : Finset α} (h : live op goal n s) :
    ∃ m, build op' (f goal) m (projAvail f off s) ∧ m + projCharge f off s ≤ n := by
  induction n generalizing s with
  | zero =>
    change s = {goal} at h
    subst s
    refine ⟨0, ?_, ?_⟩
    · change f goal ∈ (Finset.image f {goal}).erase off
      simp [nontriv]
    · simp [projCharge, Ne.symm nontriv]
  | succ k ih =>
    rcases h with skip | ⟨a,ha,b,hb,hab,z,hz,hout,r,hs,tail⟩
    · obtain ⟨m,hm,hle⟩ := ih skip
      exact ⟨m,hm,by omega⟩
    · obtain ⟨m,hm,hle⟩ := ih tail
      have inc : r ⊆ s := fun x hx => by rw [hs]; simp [hx]
      have useful {x : α} (hx : x ∈ s) (ho : f x ≠ off) : f x ∈ projAvail f off s :=
        Finset.mem_erase.mpr ⟨ho,Finset.mem_image_of_mem _ hx⟩
      have tailInc : projAvail f off (insert z r) ⊆ insert (f z) (projAvail f off s) := by
        intro u hu
        obtain ⟨hue,hi⟩ := Finset.mem_erase.mp hu
        rcases Finset.mem_image.mp hi with ⟨x,hx,rfl⟩
        rcases Finset.mem_insert.mp hx with rfl | hxr
        · simp
        · exact Finset.mem_insert_of_mem (useful (inc hxr) hue)
      by_cases ign : f z = off ∨ f z ∈ projAvail f off s
      · refine ⟨m, weakenBuild ?_ hm, ?_⟩
        · intro x hx
          rcases Finset.mem_insert.mp (tailInc hx) with eq | already
          · rcases ign with hz0 | present
            · exact False.elim ((Finset.mem_erase.mp hx).1 (eq.trans hz0))
            · exact eq ▸ present
          · exact already
        · have c : projCharge f off s ≤ 1 := by
            unfold projCharge; split <;> omega
          omega
      · have nz : f z ≠ off := fun eq => ign (.inl eq)
        have un : f z ∉ projAvail f off s := fun mem => ign (.inr mem)
        rcases gate a b z hz with hz0 | az | bz | ⟨na,nb,ne,hop⟩
        · exact (nz hz0).elim
        · exact (un (az ▸ useful ha (az ▸ nz))).elim
        · exact (un (bz ▸ useful hb (bz ▸ nz))).elim
        · refine ⟨m+1, Or.inr ⟨f a,useful ha na,f b,useful hb nb,ne,f z,hop,weakenBuild tailInc hm⟩, ?_⟩
          have c : projCharge f off s ≤ projCharge f off (insert z r) := by
            unfold projCharge
            by_cases present : off ∈ s.image f
            · obtain ⟨x,hx,eq⟩ := Finset.mem_image.mp present
              rw [hs] at hx
              rcases Finset.mem_insert.mp hx with rfl | hx
              · exact (na eq).elim
              · rcases Finset.mem_insert.mp hx with rfl | hxr
                · exact (nb eq).elim
                · have mem := Finset.mem_image_of_mem f (Finset.mem_insert_of_mem hxr : x ∈ insert z r)
                  have hmem : off ∈ (insert z r).image f := eq ▸ mem
                  rw [ite_eq_left present, ite_eq_left hmem]
            · simp [present]
          omega
end Project
def qPos : List Nat := [0, 1, 1, 3, 4, 5, 6, 7, 8, 9]
def qNeg : List Nat := [0, 1, 2, 3, 3, 5, 6, 7, 7, 9, 10, 11, 12, 12]

def qIndex (i : Nat) : Nat :=
  if i < 140 then qNeg.getD (i % 14) 0 else 140 + 14 * qPos.getD ((i-140)/14) 0

def qBits (bit : Nat → Bool) : (n : Nat) → BitVec n
  | 0 => 0
  | n+1 => BitVec.cons (bit n) (qBits bit n)

theorem qBits_get {f : Nat → Bool} {n i : Nat} (h : i < n) : (qBits f n).getLsbD i = f i := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [qBits, BitVec.getLsbD_cons]
    split
    · next he => rw [he]
    · exact ih (by omega)

def qProject (w : W) : W := qBits (fun i => w.getLsbD (qIndex i)) 280

theorem qProject_and (a b : W) : qProject (a &&& b) = qProject a &&& qProject b := by
  apply BitVec.eq_of_getLsbD_eq
  intro n hn
  simp [qProject, BitVec.getLsbD_and, qBits_get hn]

theorem qProject_or (a b : W) : qProject (a ||| b) = qProject a ||| qProject b := by
  apply BitVec.eq_of_getLsbD_eq
  intro n hn
  simp [qProject, BitVec.getLsbD_or, qBits_get hn]

theorem qGate (a b z : W) (hz : z ∈ basicOps a b) :
    qProject z = 0 ∨ qProject z = qProject a ∨ qProject z = qProject b ∨
      (qProject a ≠ 0 ∧ qProject b ≠ 0 ∧ qProject a ≠ qProject b ∧ qProject z ∈ basicOps (qProject a) (qProject b)) := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
  rcases hz with rfl | rfl <;>
    by_cases ha : qProject a = 0 <;> by_cases hb : qProject b = 0 <;>
    by_cases hab : qProject a = qProject b <;> simp_all [qProject_and, qProject_or]

def projectedPins := rawInputs.take 8 ++ [rawInputs[8]! ||| rawInputs[9]!]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2500000 in
theorem qConstant : qProject goal = goal ∧
    projCharge qProject 0 inputs.toFinset = 1 ∧
    projAvail qProject 0 inputs.toFinset = projectedPins.toFinset := by decide +kernel

theorem quotientTransfer (full : ∀ {k : Nat} {s : Finset W}, s ⊆ inputs.toFinset →
      live basicOps goal k s → s = inputs.toFinset)
    (noSmall : ¬ build basicOps goal 10 projectedPins.toFinset) :
      ¬ PEqualNP.Represents.RepSizeAtMost A 11 := by
  rintro ⟨C,hm,hs,hr⟩
  obtain ⟨s,inc,run⟩ := compress (get_build C hm hr)
  have equ := full inc run
  rw [equ] at run
  have ng : qProject goal ≠ 0 := by rw [qConstant.1]; decide
  obtain ⟨cost,small,limit⟩ := projectLive qProject 0 goal ng qGate run
  rw [qConstant.1, qConstant.2.2] at small
  rw [qConstant.2.1] at limit
  have extend {a b : Nat} (h : a ≤ b) {s : Finset W} (hb : build basicOps goal a s) : build basicOps goal b s := by
    induction h with
    | refl => exact hb
    | step _ ih => exact Or.inl ih
  apply noSmall (extend (by change C.gates.length ≤ 11 at hs; omega) small)

namespace Quotient
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def w0 : W := 0x3ffffffc00000000000000000000000000000000000000
def w1 : W := 0x3ffffffffff00000000000000000000000000000000000
def w2 : W := 0x3ffffffffff001c007001c007001c007001c007001c007
def w3 : W := 0x3fff00000000000000000000000000000000000000000000000000000000
def w4 : W := 0x3fff00000000003ffffffffff001c007001c007001c007001c007001c007
def w5 : W := 0x3fffffffffffffc000000000000600180060018006001800600180060018
def w6 : W := 0x3ffffffffffffffffffffc00000600180060018006001800600180060018
def w7 : W := 0x3ffffffc00000000000000000000000007801e007801e007801e007801e007801e0
def w8 : W := 0x3ffffffc00000000000003ffffffc00007801e007801e007801e007801e007801e0
def w9 : W := 0x3ffffffffff00000000000000000000007801e007801e007801e007801e007801e0
def w10 : W := 0x3ffffffffffffffffffffc000000000007e01f807e01f807e01f807e01f807e01f8
def w11 : W := 0xfffc000000000000000000000000000000000000000000000000000000000000000000
def w12 : W := 0xfffc000000000000000000003ffffffc00000000000000000000000000000000000000
def w13 : W := 0xfffc0000003fffffffffffffc000000000000600180060018006001800600180060018
def w14 : W := 0xfffc0000003ffffffffffffffffffffc00000600180060018006001800600180060018
def w15 : W := 0xfffc000fffc0000000000fffc000000000000040010004001000400100040010004001
def w16 : W := 0xfffc000fffc0000000000ffffffffffffff001c007001c007001c007001c007001c007
def w17 : W := 0xfffc000fffffff0000000fffc000000000000040010004001000400100040010004001
def w18 : W := 0xfffc000fffffff0000000ffffffffffffff001c007001c007001c007001c007001c007
def w19 : W := 0xfffc000ffffffffffffffffffffffffffff007c01f007c01f007c01f007c01f007c01f
def w20 : W := 0xffffffffffc00000000000000000000000007801e007801e007801e007801e007801e0
def w21 : W := 0xffffffffffc00000000000003ffffffc00007801e007801e007801e007801e007801e0
def w22 : W := 0x3fff00000000003fff0000000000000008082020808202080820208082020808202
def w23 : W := 0x3fff00000000003fff0003ffffffffff081c207081c207081c207081c207081c207
def w24 : W := 0x3fff0003fff0003fff0000000000000008082020808202080820208082020808202
def w25 : W := 0x3fff0003fff0003fff0003ffffffffff081c207081c207081c207081c207081c207
def w26 : W := 0xfffffff00000000003fff0000000000000008082020808202080820208082020808202
def w27 : W := 0xffffffffffc0000003ffffffc0000000000080c203080c203080c203080c203080c203
def w28 : W := 0xffffffffffc0000003fffffffffffffffff081c207081c207081c207081c207081c207
def w29 : W := 0xfffc00000000000003fff10804201080420108042010804201080420
def w30 : W := 0xfffc0000003ffffffffff10804201080420108042010804201080420
def w31 : W := 0x3ffffffc00000000000003fff10804201080420108042010804201080420
def w32 : W := 0x3ffffffc000fffc00000000000003fff17805e017805e017805e017805e017805e0
def w33 : W := 0x3ffffffc000fffc0000003ffffffffff17805e017805e017805e017805e017805e0
def w34 : W := 0x3fffffffffffffc00000000000003fff17805e017805e017805e017805e017805e0
def w35 : W := 0x3ffffffffffffffffffffc0000003fff17e05f817e05f817e05f817e05f817e05f8
def w36 : W := 0xfffc0000000000fffc00000000000003fff10804201080420108042010804201080420
def w37 : W := 0xfffc0000000000fffc0000003ffffffffff10804201080420108042010804201080420
def w38 : W := 0xffffffffffc000fffc00000000000003fff17805e017805e017805e017805e017805e0
def w39 : W := 0xffffffffffc000fffc0000003ffffffffff17805e017805e017805e017805e017805e0
def w40 : W := 0x3fff00000000000000000000021108442110844211084421108442110844
def w41 : W := 0x3fff00000000003ffffffffff211c847211c847211c847211c847211c847
def w42 : W := 0x3ffffffffff00000000000000000000027909e427909e427909e427909e427909e4
def w43 : W := 0xfffc0000003fff00000000000000000000021108442110844211084421108442110844
def w44 : W := 0xfffc000fffffff0000000fffc000000000021148452114845211484521148452114845
def w45 : W := 0xfffc000fffffff0000000ffffffffffffff211c847211c847211c847211c847211c847
def w46 : W := 0xffffffffffffff00000000000000000000027909e427909e427909e427909e427909e4
def w47 : W := 0x3fff0003fff0003fff000000000000002918a462918a462918a462918a462918a46
def w48 : W := 0x3fff0003fff0003fff0003ffffffffff291ca47291ca47291ca47291ca47291ca47
def w49 : W := 0x3ffffffc00000000000003fff3190c643190c643190c643190c643190c64
def w50 : W := 0x3fffffffffffffc00000000000003fff3790de43790de43790de43790de43790de4
def w51 : W := 0x3ffffffc000c663198c663198c663198c663198c663198
def w52 : W := 0x3ffffffffffffffffffffc000c663198c663198c663198c663198c663198
def w53 : W := 0x3ffffffc00000000000003ffffffc000c7e31f8c7e31f8c7e31f8c7e31f8c7e31f8
def w54 : W := 0x3fffffffffffffffffffffffffffc000c7e31f8c7e31f8c7e31f8c7e31f8c7e31f8
def w55 : W := 0xfffc000000000000000000003ffffffc000c663198c663198c663198c663198c663198
def w56 : W := 0xfffc0000003ffffffffffffffffffffc000c663198c663198c663198c663198c663198
def w57 : W := 0xfffc000ffffffffffffffffffffffffffffc67f19fc67f19fc67f19fc67f19fc67f19f
def w58 : W := 0xffffffffffc00000000000003ffffffc000c7e31f8c7e31f8c7e31f8c7e31f8c7e31f8
def w59 : W := 0xfffc0000003ffffffffffd6e35b8d6e35b8d6e35b8d6e35b8d6e35b8
def w60 : W := 0x3ffffffc000fffc0000003ffffffffffd7e35f8d7e35f8d7e35f8d7e35f8d7e35f8
def w61 : W := 0x3fffffffffffffffffffffffffffffffd7e35f8d7e35f8d7e35f8d7e35f8d7e35f8
def w62 : W := 0xfffc0000000000000000000000000000000f803e00f803e00f803e00f803e00f803e00
def w63 : W := 0xfffc000000000000000000003ffffffc000f803e00f803e00f803e00f803e00f803e00
def w64 : W := 0xfffc0000003fff000000000000000000000f803e00f803e00f803e00f803e00f803e00
def w65 : W := 0xfffc0000003fffffffffffffc0000000000f863e18f863e18f863e18f863e18f863e18
def w66 : W := 0xfffffff00000000003fff00000000000000f80be02f80be02f80be02f80be02f80be02
def w67 : W := 0xfffffff0003fff0003fff00000000000000f80be02f80be02f80be02f80be02f80be02
def w68 : W := 0xfffc0000000000fffc00000000000003ffff883e20f883e20f883e20f883e20f883e20
def w69 : W := 0xfffc0000000000fffc0000003fffffffffff883e20f883e20f883e20f883e20f883e20
def w70 : W := 0xfffc0000003ffffffc00000000000003ffff883e20f883e20f883e20f883e20f883e20
def w71 : W := 0xfffc0000003fff000000000000000000000f913e44f913e44f913e44f913e44f913e44
def w72 : W := 0xfffffff0003fff0003fff00000000000000f91be46f91be46f91be46f91be46f91be46
def w73 : W := 0xfffc0000003ffffffc00000000000003ffff993e64f993e64f993e64f993e64f993e64
def w74 : W := 0xfffc000000000000000000003ffffffc000fe63f98fe63f98fe63f98fe63f98fe63f98
def w75 : W := 0xfffc0000003ffffffffffffffffffffc000fe63f98fe63f98fe63f98fe63f98fe63f98
def w76 : W := 0xfffc0000000000fffc0000003fffffffffffee3fb8fee3fb8fee3fb8fee3fb8fee3fb8
def w77 : W := 0xffffffffffc000000000000000000000000ff83fe0ff83fe0ff83fe0ff83fe0ff83fe0
def w78 : W := 0xffffffffffc000fffc00000000000003fffff83fe0ff83fe0ff83fe0ff83fe0ff83fe0
def w79 : W := 0xffffffffffffff000000000000000000000ff93fe4ff93fe4ff93fe4ff93fe4ff93fe4
def w80 : W := 0xfffffffffffffffffc00000000000003fffff93fe4ff93fe4ff93fe4ff93fe4ff93fe4
def w81 : W := 0xffffffffffc00000000000003ffffffc000ffe3ff8ffe3ff8ffe3ff8ffe3ff8ffe3ff8
def w82 : W := 0xffffffffffc000fffc0000003ffffffffffffe3ff8ffe3ff8ffe3ff8ffe3ff8ffe3ff8
def s0 : Chart 4 := make 32972 [w19,w22,w45,w54,w68] [] (by decide +kernel)
def s1 : Chart 4 := make 12915 [w5,w28,w39,w40] [] (by decide +kernel)
def s2 : Chart 4 := make 29585 [w14,w28,w32,w40] [] (by decide +kernel)
def s3 : Chart 5 := make 48852 [w5,w15,w23,w33,w71] [] (by decide +kernel)
def s4 : Chart 5 := make 54195 [w6,w15,w23,w32,w71] [] (by decide +kernel)
def s5 : Chart 5 := make 3044 [w5,w16,w22,w34,w74] [] (by decide +kernel)
def s6 : Chart 5 := make 52385 [w5,w16,w24,w32,w74] [] (by decide +kernel)
def s7 : Chart 5 := make 11445 [w5,w18,w22,w32,w74] [] (by decide +kernel)
def s8 : Chart 5 := make 2221 [w5,w16,w22,w53,w70] [] (by decide +kernel)
def s9 : Chart 5 := make 59512 [w5,w16,w24,w53,w68] [] (by decide +kernel)
def s10 : Chart 5 := make 18572 [w5,w18,w22,w53,w68] [] (by decide +kernel)
def s11 : Chart 5 := make 48140 [w5,w28,w29,w40,w58] [] (by decide +kernel)
def s12 : Chart 5 := make 10853 [w5,w28,w32,w40,w55] [] (by decide +kernel)
def s13 : Chart 5 := make 10381 [w7,w27,w29,w41,w56] [] (by decide +kernel)
def s14 : Chart 5 := make 2158 [w7,w28,w29,w40,w56] [] (by decide +kernel)
def s15 : Chart 5 := make 29820 [w5,w28,w36,w40,w53] [] (by decide +kernel)
def s16 : Chart 5 := make 20867 [w5,w28,w38,w40,w51] [] (by decide +kernel)
def s17 : Chart 5 := make 7478 [w7,w27,w36,w41,w52] [] (by decide +kernel)
def s18 : Chart 5 := make 64776 [w7,w28,w36,w40,w52] [] (by decide +kernel)
def s19 : Chart 5 := make 4292 [w13,w28,w29,w40,w53] [] (by decide +kernel)
def s20 : Chart 5 := make 32194 [w13,w28,w32,w40,w51] [] (by decide +kernel)
def s21 : Chart 5 := make 220 [w20,w27,w29,w41,w52] [] (by decide +kernel)
def s22 : Chart 5 := make 57518 [w20,w28,w29,w40,w52] [] (by decide +kernel)
def s23 : Chart 5 := make 48960 [w7,w19,w28,w29,w40,w75] [] (by decide +kernel)
def s24 : Chart 5 := make 14626 [w19,w28,w29,w40,w53,w65] [] (by decide +kernel)
def s25 : Chart 5 := make 52089 [w5,w15,w23,w60,w73] [] (by decide +kernel)
def s26 : Chart 5 := make 34732 [w5,w16,w22,w45,w54,w68] [s0] (by decide +kernel)
def s27 : Chart 5 := make 46690 [w5,w16,w28,w40,w54,w68] [] (by decide +kernel)
def s28 : Chart 5 := make 48520 [w16,w19,w22,w40,w54,w68] [s0] (by decide +kernel)
def s29 : Chart 5 := make 20233 [w7,w19,w22,w45,w52,w68] [s0] (by decide +kernel)
def s30 : Chart 5 := make 32191 [w7,w19,w28,w40,w52,w68] [] (by decide +kernel)
def s31 : Chart 5 := make 20471 [w19,w22,w29,w45,w54,w62] [s0] (by decide +kernel)
def s32 : Chart 5 := make 64441 [w5,w15,w23,w50,w61,w62] [] (by decide +kernel)
def s33 : Chart 5 := make 11408 [w5,w16,w22,w50,w61,w62] [] (by decide +kernel)
def s34 : Chart 5 := make 27836 [w10,w19,w22,w29,w45,w74] [] (by decide +kernel)
def s35 : Chart 5 := make 59753 [w5,w16,w22,w35,w50,w74] [] (by decide +kernel)
def s36 : Chart 5 := make 60195 [w5,w16,w22,w50,w82] [] (by decide +kernel)
def s37 : Chart 5 := make 16648 [w5,w12,w28,w32,w40] [s1,s2] (by decide +kernel)
def s38 : Chart 5 := make 16505 [w5,w16,w22,w39,w40] [s1] (by decide +kernel)
def s39 : Chart 5 := make 33175 [w14,w16,w22,w32,w40] [s2] (by decide +kernel)
def s40 : Chart 5 := make 3218 [w5,w28,w32,w45,w74] [] (by decide +kernel)
def s41 : Chart 5 := make 33207 [w5,w7,w28,w37,w40] [s1] (by decide +kernel)
def s42 : Chart 5 := make 34453 [w5,w21,w28,w29,w40] [s1] (by decide +kernel)
def s43 : Chart 5 := make 22622 [w7,w14,w28,w29,w40] [s2] (by decide +kernel)
def s44 : Chart 5 := make 56729 [w5,w15,w23,w60,w80] [] (by decide +kernel)
def s45 : Chart 5 := make 62865 [w10,w19,w22,w45,w51,w68] [s0] (by decide +kernel)
def s46 : Chart 5 := make 50798 [w5,w19,w22,w45,w53,w68] [s0] (by decide +kernel)
def s47 : Chart 5 := make 62756 [w5,w19,w28,w40,w53,w68] [] (by decide +kernel)
def s48 : Chart 5 := make 10345 [w5,w28,w45,w53,w68] [] (by decide +kernel)
def s49 : Chart 5 := make 10311 [w7,w28,w29,w40,w57,w75] [] (by decide +kernel)
def s50 : Chart 5 := make 47343 [w22,w29,w45,w54,w57,w62] [] (by decide +kernel)
def s51 : Chart 6 := make 12595 [w0,w5,w15,w23,w32,w71] [s3,s4] (by decide +kernel)
def s52 : Chart 6 := make 40551 [w2,w5,w15,w22,w33,w71] [s3] (by decide +kernel)
def s53 : Chart 6 := make 45894 [w2,w6,w15,w22,w32,w71] [s4] (by decide +kernel)
def s54 : Chart 6 := make 32289 [w5,w7,w15,w23,w30,w71] [s3] (by decide +kernel)
def s55 : Chart 6 := make 40793 [w5,w8,w15,w23,w29,w71] [s3] (by decide +kernel)
def s56 : Chart 6 := make 47232 [w6,w7,w15,w23,w29,w71] [s4] (by decide +kernel)
def s57 : Chart 6 := make 25116 [w2,w5,w15,w22,w42,w69] [] (by decide +kernel)
def s58 : Chart 6 := make 6217 [w2,w6,w15,w22,w42,w68] [] (by decide +kernel)
def s59 : Chart 6 := make 33328 [w5,w7,w16,w22,w40,w69] [] (by decide +kernel)
def s60 : Chart 6 := make 7990 [w5,w8,w16,w22,w40,w68] [] (by decide +kernel)
def s61 : Chart 6 := make 14429 [w6,w7,w16,w22,w40,w68] [] (by decide +kernel)
def s62 : Chart 6 := make 56565 [w5,w7,w15,w30,w41,w66] [] (by decide +kernel)
def s63 : Chart 6 := make 5987 [w6,w7,w15,w29,w41,w66] [] (by decide +kernel)
def s64 : Chart 6 := make 56581 [w5,w15,w23,w33,w40,w62] [s3] (by decide +kernel)
def s65 : Chart 6 := make 61924 [w6,w15,w23,w32,w40,w62] [s4] (by decide +kernel)
def s66 : Chart 6 := make 32833 [w5,w16,w22,w32,w40,w63] [] (by decide +kernel)
def s67 : Chart 6 := make 3548 [w5,w16,w22,w33,w40,w62] [] (by decide +kernel)
def s68 : Chart 6 := make 8891 [w6,w16,w22,w32,w40,w62] [] (by decide +kernel)
def s69 : Chart 6 := make 47776 [w2,w5,w15,w22,w34,w74] [s5] (by decide +kernel)
def s70 : Chart 6 := make 31596 [w2,w5,w15,w24,w32,w74] [s6] (by decide +kernel)
def s71 : Chart 6 := make 24012 [w2,w5,w17,w22,w32,w74] [s7] (by decide +kernel)
def s72 : Chart 6 := make 34670 [w3,w5,w16,w22,w32,w74] [s5,s6,s7] (by decide +kernel)
def s73 : Chart 6 := make 57341 [w4,w5,w15,w22,w32,w74] [s7] (by decide +kernel)
def s74 : Chart 6 := make 43955 [w5,w7,w16,w22,w31,w74] [s5] (by decide +kernel)
def s75 : Chart 6 := make 45422 [w5,w7,w16,w24,w29,w74] [s6] (by decide +kernel)
def s76 : Chart 6 := make 4482 [w5,w7,w18,w22,w29,w74] [s7] (by decide +kernel)
def s77 : Chart 6 := make 13668 [w5,w9,w16,w22,w29,w74] [s5] (by decide +kernel)
def s78 : Chart 6 := make 46953 [w2,w5,w15,w22,w53,w70] [s8] (by decide +kernel)
def s79 : Chart 6 := make 38723 [w2,w5,w15,w24,w53,w68] [s9] (by decide +kernel)
def s80 : Chart 6 := make 31139 [w2,w5,w17,w22,w53,w68] [s10] (by decide +kernel)
def s81 : Chart 6 := make 41797 [w3,w5,w16,w22,w53,w68] [s8,s9,s10] (by decide +kernel)
def s82 : Chart 6 := make 64468 [w4,w5,w15,w22,w53,w68] [s10] (by decide +kernel)
def s83 : Chart 6 := make 23160 [w5,w7,w16,w22,w51,w70] [s8] (by decide +kernel)
def s84 : Chart 6 := make 14930 [w5,w7,w16,w24,w51,w68] [s9] (by decide +kernel)
def s85 : Chart 6 := make 39511 [w5,w7,w18,w22,w51,w68] [s10] (by decide +kernel)
def s86 : Chart 6 := make 48697 [w5,w9,w16,w22,w51,w68] [] (by decide +kernel)
def s87 : Chart 6 := make 60889 [w5,w15,w23,w29,w53,w64] [] (by decide +kernel)
def s88 : Chart 6 := make 7856 [w5,w16,w22,w29,w53,w64] [s8] (by decide +kernel)
def s89 : Chart 6 := make 33056 [w5,w15,w23,w31,w53,w62] [] (by decide +kernel)
def s90 : Chart 6 := make 45544 [w5,w16,w22,w31,w53,w62] [s8] (by decide +kernel)
def s91 : Chart 6 := make 55393 [w5,w15,w25,w29,w53,w62] [] (by decide +kernel)
def s92 : Chart 6 := make 47011 [w5,w16,w24,w29,w53,w62] [s9] (by decide +kernel)
def s93 : Chart 6 := make 26939 [w5,w17,w23,w29,w53,w62] [] (by decide +kernel)
def s94 : Chart 6 := make 6071 [w5,w18,w22,w29,w53,w62] [s10] (by decide +kernel)
def s95 : Chart 6 := make 23270 [w5,w15,w23,w32,w51,w64] [] (by decide +kernel)
def s96 : Chart 6 := make 35758 [w5,w16,w22,w32,w51,w64] [] (by decide +kernel)
def s97 : Chart 6 := make 13084 [w5,w15,w23,w34,w51,w62] [] (by decide +kernel)
def s98 : Chart 6 := make 25572 [w5,w16,w22,w34,w51,w62] [s5] (by decide +kernel)
def s99 : Chart 6 := make 17774 [w5,w15,w25,w32,w51,w62] [] (by decide +kernel)
def s100 : Chart 6 := make 9392 [w5,w16,w24,w32,w51,w62] [s6] (by decide +kernel)
def s101 : Chart 6 := make 54841 [w5,w17,w23,w32,w51,w62] [] (by decide +kernel)
def s102 : Chart 6 := make 33973 [w5,w18,w22,w32,w51,w62] [s7] (by decide +kernel)
def s103 : Chart 6 := make 2491 [w7,w15,w23,w31,w52,w62] [] (by decide +kernel)
def s104 : Chart 6 := make 14979 [w7,w16,w22,w31,w52,w62] [] (by decide +kernel)
def s105 : Chart 6 := make 24828 [w7,w15,w25,w29,w52,w62] [] (by decide +kernel)
def s106 : Chart 6 := make 16446 [w7,w16,w24,w29,w52,w62] [] (by decide +kernel)
def s107 : Chart 6 := make 61895 [w7,w17,w23,w29,w52,w62] [] (by decide +kernel)
def s108 : Chart 6 := make 41027 [w7,w18,w22,w29,w52,w62] [] (by decide +kernel)
def s109 : Chart 6 := make 33293 [w2,w5,w27,w29,w40,w58] [s11] (by decide +kernel)
def s110 : Chart 6 := make 1620 [w2,w5,w27,w29,w42,w55] [] (by decide +kernel)
def s111 : Chart 6 := make 61527 [w2,w5,w27,w32,w40,w55] [s12] (by decide +kernel)
def s112 : Chart 6 := make 52832 [w2,w7,w27,w29,w40,w56] [s13,s14] (by decide +kernel)
def s113 : Chart 6 := make 12113 [w5,w7,w27,w29,w41,w55] [s13] (by decide +kernel)
def s114 : Chart 6 := make 3890 [w5,w7,w28,w29,w40,w55] [s11,s12,s14] (by decide +kernel)
def s115 : Chart 6 := make 50518 [w2,w5,w27,w29,w43,w53] [] (by decide +kernel)
def s116 : Chart 6 := make 20717 [w2,w5,w27,w29,w46,w51] [] (by decide +kernel)
def s117 : Chart 6 := make 12899 [w2,w5,w27,w32,w43,w51] [] (by decide +kernel)
def s118 : Chart 6 := make 19953 [w2,w7,w27,w29,w43,w52] [] (by decide +kernel)
def s119 : Chart 6 := make 14973 [w2,w5,w27,w36,w40,w53] [s15] (by decide +kernel)
def s120 : Chart 6 := make 48489 [w2,w5,w27,w36,w42,w51] [] (by decide +kernel)
def s121 : Chart 6 := make 6020 [w2,w5,w27,w38,w40,w51] [s16] (by decide +kernel)
def s122 : Chart 6 := make 49929 [w2,w7,w27,w36,w40,w52] [s17,s18] (by decide +kernel)
def s123 : Chart 6 := make 58982 [w5,w7,w27,w36,w41,w51] [s17] (by decide +kernel)
def s124 : Chart 6 := make 50759 [w5,w7,w28,w36,w40,w51] [s15,s16,s18] (by decide +kernel)
def s125 : Chart 6 := make 54966 [w2,w13,w27,w29,w40,w53] [s19] (by decide +kernel)
def s126 : Chart 6 := make 32955 [w5,w11,w28,w29,w40,w53] [s11,s15,s19] (by decide +kernel)
def s127 : Chart 6 := make 22961 [w2,w13,w27,w29,w42,w51] [] (by decide +kernel)
def s128 : Chart 6 := make 17347 [w2,w13,w27,w32,w40,w51] [s20] (by decide +kernel)
def s129 : Chart 6 := make 60857 [w5,w11,w28,w32,w40,w51] [s12,s16,s20] (by decide +kernel)
def s130 : Chart 6 := make 42671 [w2,w20,w27,w29,w40,w52] [s21,s22] (by decide +kernel)
def s131 : Chart 6 := make 51724 [w5,w20,w27,w29,w41,w51] [s21] (by decide +kernel)
def s132 : Chart 6 := make 43501 [w5,w20,w28,w29,w40,w51] [s11,s16,s22] (by decide +kernel)
def s133 : Chart 6 := make 10613 [w7,w11,w27,w29,w41,w52] [s13,s17,s21] (by decide +kernel)
def s134 : Chart 6 := make 2390 [w7,w11,w28,w29,w40,w52] [s14,s18,s22] (by decide +kernel)
def s135 : Chart 6 := make 33454 [w7,w13,w27,w29,w41,w51] [s13] (by decide +kernel)
def s136 : Chart 6 := make 25231 [w7,w13,w28,w29,w40,w51] [s14,s19,s20] (by decide +kernel)
def s137 : Chart 6 := make 39242 [w5,w15,w23,w29,w40,w58] [s11] (by decide +kernel)
def s138 : Chart 6 := make 51730 [w5,w16,w22,w29,w40,w58] [s11] (by decide +kernel)
def s139 : Chart 6 := make 1955 [w5,w15,w23,w32,w40,w55] [s12] (by decide +kernel)
def s140 : Chart 6 := make 14443 [w5,w16,w22,w32,w40,w55] [s12] (by decide +kernel)
def s141 : Chart 6 := make 8029 [w7,w15,w22,w29,w41,w56] [s13] (by decide +kernel)
def s142 : Chart 6 := make 58781 [w7,w15,w23,w29,w40,w56] [s14] (by decide +kernel)
def s143 : Chart 6 := make 5748 [w7,w16,w22,w29,w40,w56] [s14] (by decide +kernel)
def s144 : Chart 6 := make 56467 [w5,w15,w23,w29,w43,w53] [] (by decide +kernel)
def s145 : Chart 6 := make 18848 [w5,w15,w23,w32,w43,w51] [] (by decide +kernel)
def s146 : Chart 6 := make 25902 [w7,w15,w23,w29,w43,w52] [] (by decide +kernel)
def s147 : Chart 6 := make 20922 [w5,w15,w23,w36,w40,w53] [s15] (by decide +kernel)
def s148 : Chart 6 := make 33410 [w5,w16,w22,w36,w40,w53] [s15] (by decide +kernel)
def s149 : Chart 6 := make 11969 [w5,w15,w23,w38,w40,w51] [s16] (by decide +kernel)
def s150 : Chart 6 := make 24457 [w5,w16,w22,w38,w40,w51] [s16] (by decide +kernel)
def s151 : Chart 6 := make 5126 [w7,w15,w22,w36,w41,w52] [s17] (by decide +kernel)
def s152 : Chart 6 := make 55878 [w7,w15,w23,w36,w40,w52] [s18] (by decide +kernel)
def s153 : Chart 6 := make 2845 [w7,w16,w22,w36,w40,w52] [s18] (by decide +kernel)
def s154 : Chart 6 := make 44608 [w7,w15,w26,w29,w41,w52] [] (by decide +kernel)
def s155 : Chart 6 := make 60915 [w13,w15,w23,w29,w40,w53] [s19] (by decide +kernel)
def s156 : Chart 6 := make 7882 [w13,w16,w22,w29,w40,w53] [s19] (by decide +kernel)
def s157 : Chart 6 := make 23296 [w13,w15,w23,w32,w40,w51] [s20] (by decide +kernel)
def s158 : Chart 6 := make 35784 [w13,w16,w22,w32,w40,w51] [s20] (by decide +kernel)
def s159 : Chart 6 := make 63389 [w15,w20,w22,w29,w41,w52] [s21] (by decide +kernel)
def s160 : Chart 6 := make 48620 [w15,w20,w23,w29,w40,w52] [s22] (by decide +kernel)
def s161 : Chart 6 := make 61108 [w16,w20,w22,w29,w40,w52] [s22] (by decide +kernel)
def s162 : Chart 6 := make 60728 [w5,w16,w22,w32,w40,w75] [] (by decide +kernel)
def s163 : Chart 6 := make 44893 [w10,w16,w22,w29,w40,w75] [] (by decide +kernel)
def s164 : Chart 6 := make 38762 [w5,w7,w16,w22,w29,w45,w75] [] (by decide +kernel)
def s165 : Chart 6 := make 50720 [w5,w7,w16,w28,w29,w40,w75] [s23] (by decide +kernel)
def s166 : Chart 6 := make 52550 [w7,w16,w19,w22,w29,w40,w75] [s23] (by decide +kernel)
def s167 : Chart 6 := make 54638 [w15,w23,w29,w40,w54,w65] [] (by decide +kernel)
def s168 : Chart 6 := make 1605 [w16,w22,w29,w40,w54,w65] [] (by decide +kernel)
def s169 : Chart 6 := make 4428 [w5,w16,w22,w29,w45,w53,w65] [] (by decide +kernel)
def s170 : Chart 6 := make 16386 [w5,w16,w28,w29,w40,w53,w65] [s24] (by decide +kernel)
def s171 : Chart 6 := make 18216 [w16,w19,w22,w29,w40,w53,w65] [s24] (by decide +kernel)
def s172 : Chart 6 := make 48862 [w15,w23,w32,w40,w52,w65] [] (by decide +kernel)
def s173 : Chart 6 := make 61350 [w16,w22,w32,w40,w52,w65] [] (by decide +kernel)
def s174 : Chart 6 := make 35565 [w7,w19,w28,w29,w40,w51,w65] [s23,s24] (by decide +kernel)
def s175 : Chart 6 := make 23944 [w5,w15,w23,w29,w53,w72] [] (by decide +kernel)
def s176 : Chart 6 := make 51846 [w5,w15,w23,w32,w51,w72] [] (by decide +kernel)
def s177 : Chart 6 := make 65252 [w7,w15,w29,w48,w52,w66] [] (by decide +kernel)
def s178 : Chart 6 := make 39798 [w2,w5,w15,w22,w50,w76] [] (by decide +kernel)
def s179 : Chart 6 := make 18968 [w5,w7,w16,w22,w49,w76] [] (by decide +kernel)
def s180 : Chart 6 := make 11825 [w5,w16,w22,w32,w40,w76] [] (by decide +kernel)
def s181 : Chart 6 := make 34384 [w1,w5,w7,w15,w22,w73] [] (by decide +kernel)
def s182 : Chart 6 := make 43788 [w2,w5,w15,w22,w60,w73] [s25] (by decide +kernel)
def s183 : Chart 6 := make 18226 [w5,w7,w15,w23,w59,w73] [s25] (by decide +kernel)
def s184 : Chart 6 := make 49003 [w5,w15,w23,w29,w53,w73] [s25] (by decide +kernel)
def s185 : Chart 6 := make 11384 [w5,w15,w23,w32,w51,w73] [s25] (by decide +kernel)
def s186 : Chart 6 := make 28938 [w5,w16,w22,w40,w53,w68] [] (by decide +kernel)
def s187 : Chart 6 := make 61790 [w1,w5,w15,w22,w42,w68] [] (by decide +kernel)
def s188 : Chart 6 := make 1397 [w5,w15,w23,w40,w60,w68] [s25] (by decide +kernel)
def s189 : Chart 6 := make 13885 [w5,w16,w22,w40,w60,w68] [] (by decide +kernel)
def s190 : Chart 6 := make 12417 [w5,w15,w23,w49,w53,w68] [] (by decide +kernel)
def s191 : Chart 6 := make 24905 [w5,w16,w22,w49,w53,w68] [] (by decide +kernel)
def s192 : Chart 6 := make 47373 [w7,w15,w23,w49,w52,w68] [] (by decide +kernel)
def s193 : Chart 6 := make 59861 [w7,w16,w22,w49,w52,w68] [] (by decide +kernel)
def s194 : Chart 6 := make 54999 [w15,w22,w32,w41,w52,w68] [] (by decide +kernel)
def s195 : Chart 6 := make 40230 [w15,w23,w32,w40,w52,w68] [] (by decide +kernel)
def s196 : Chart 6 := make 52718 [w16,w22,w32,w40,w52,w68] [] (by decide +kernel)
def s197 : Chart 6 := make 61741 [w5,w15,w23,w29,w53,w71] [] (by decide +kernel)
def s198 : Chart 6 := make 24122 [w5,w15,w23,w32,w51,w71] [] (by decide +kernel)
def s199 : Chart 6 := make 21811 [w5,w16,w22,w32,w40,w74] [] (by decide +kernel)
def s200 : Chart 6 := make 17149 [w5,w16,w22,w29,w42,w81] [] (by decide +kernel)
def s201 : Chart 6 := make 11535 [w5,w16,w22,w32,w40,w81] [] (by decide +kernel)
def s202 : Chart 6 := make 54635 [w5,w15,w23,w29,w53,w79] [] (by decide +kernel)
def s203 : Chart 6 := make 17016 [w5,w15,w23,w32,w51,w79] [] (by decide +kernel)
def s204 : Chart 6 := make 43856 [w5,w16,w22,w40,w53,w78] [] (by decide +kernel)
def s205 : Chart 6 := make 11851 [w5,w16,w22,w42,w51,w78] [] (by decide +kernel)
def s206 : Chart 6 := make 17017 [w5,w15,w23,w29,w54,w71] [] (by decide +kernel)
def s207 : Chart 6 := make 11241 [w5,w15,w23,w32,w52,w71] [] (by decide +kernel)
def s208 : Chart 6 := make 60927 [w10,w15,w23,w29,w52,w71] [] (by decide +kernel)
def s209 : Chart 6 := make 49735 [w5,w16,w22,w40,w54,w68] [s26,s27,s28] (by decide +kernel)
def s210 : Chart 6 := make 28124 [w10,w16,w22,w40,w52,w68] [] (by decide +kernel)
def s211 : Chart 6 := make 21993 [w5,w7,w16,w22,w45,w52,w68] [s26,s29] (by decide +kernel)
def s212 : Chart 6 := make 33951 [w5,w7,w16,w28,w40,w52,w68] [s27,s30] (by decide +kernel)
def s213 : Chart 6 := make 35781 [w7,w16,w19,w22,w40,w52,w68] [s29,s30,s28] (by decide +kernel)
def s214 : Chart 6 := make 19682 [w10,w15,w29,w41,w52,w66] [] (by decide +kernel)
def s215 : Chart 6 := make 22231 [w5,w16,w22,w29,w45,w54,w62] [s26,s31] (by decide +kernel)
def s216 : Chart 6 := make 34189 [w5,w16,w28,w29,w40,w54,w62] [s27] (by decide +kernel)
def s217 : Chart 6 := make 36019 [w16,w19,w22,w29,w40,w54,w62] [s28,s31] (by decide +kernel)
def s218 : Chart 6 := make 28250 [w5,w15,w23,w32,w40,w52,w78] [] (by decide +kernel)
def s219 : Chart 6 := make 40738 [w5,w16,w22,w32,w40,w52,w78] [] (by decide +kernel)
def s220 : Chart 6 := make 56140 [w2,w5,w15,w22,w50,w61,w62] [s32,s33] (by decide +kernel)
def s221 : Chart 6 := make 15679 [w5,w15,w23,w32,w40,w61,w62] [s32] (by decide +kernel)
def s222 : Chart 6 := make 28167 [w5,w16,w22,w32,w40,w61,w62] [s33] (by decide +kernel)
def s223 : Chart 6 := make 31821 [w5,w15,w23,w32,w50,w52,w62] [s32] (by decide +kernel)
def s224 : Chart 6 := make 44309 [w5,w16,w22,w32,w50,w52,w62] [s33] (by decide +kernel)
def s225 : Chart 6 := make 7732 [w7,w19,w22,w29,w45,w52,w62] [s29,s31] (by decide +kernel)
def s226 : Chart 6 := make 19690 [w7,w19,w28,w29,w40,w52,w62] [s23,s30] (by decide +kernel)
def s227 : Chart 6 := make 43969 [w5,w15,w23,w32,w53,w71] [] (by decide +kernel)
def s228 : Chart 6 := make 16780 [w5,w16,w22,w42,w53,w68] [] (by decide +kernel)
def s229 : Chart 6 := make 35946 [w1,w5,w15,w22,w32,w71] [] (by decide +kernel)
def s230 : Chart 6 := make 52596 [w1,w5,w7,w15,w49,w66] [] (by decide +kernel)
def s231 : Chart 6 := make 26916 [w1,w5,w15,w22,w50,w62] [] (by decide +kernel)
def s232 : Chart 6 := make 46688 [w5,w15,w23,w29,w60,w71] [s25] (by decide +kernel)
def s233 : Chart 6 := make 19788 [w5,w15,w23,w32,w59,w71] [] (by decide +kernel)
def s234 : Chart 6 := make 3002 [w5,w15,w23,w49,w60,w62] [s25] (by decide +kernel)
def s235 : Chart 6 := make 15490 [w5,w16,w22,w49,w60,w62] [] (by decide +kernel)
def s236 : Chart 6 := make 40635 [w5,w16,w22,w32,w71,w74] [] (by decide +kernel)
def s237 : Chart 6 := make 21263 [w5,w15,w23,w32,w41,w74] [] (by decide +kernel)
def s238 : Chart 6 := make 33751 [w5,w16,w22,w32,w41,w74] [] (by decide +kernel)
def s239 : Chart 6 := make 9653 [w5,w16,w22,w32,w42,w74] [] (by decide +kernel)
def s240 : Chart 6 := make 3128 [w2,w5,w27,w32,w44,w74] [] (by decide +kernel)
def s241 : Chart 6 := make 21565 [w5,w16,w22,w32,w44,w74] [] (by decide +kernel)
def s242 : Chart 6 := make 20515 [w5,w16,w22,w32,w47,w74] [] (by decide +kernel)
def s243 : Chart 6 := make 17778 [w5,w16,w22,w32,w49,w74] [] (by decide +kernel)
def s244 : Chart 6 := make 18982 [w5,w16,w23,w32,w40,w74] [] (by decide +kernel)
def s245 : Chart 6 := make 20663 [w5,w16,w27,w29,w42,w74] [] (by decide +kernel)
def s246 : Chart 6 := make 15049 [w5,w16,w27,w32,w40,w74] [] (by decide +kernel)
def s247 : Chart 6 := make 29596 [w5,w10,w16,w22,w29,w45,w74] [s34] (by decide +kernel)
def s248 : Chart 6 := make 41554 [w5,w10,w16,w28,w29,w40,w74] [] (by decide +kernel)
def s249 : Chart 6 := make 43384 [w10,w16,w19,w22,w29,w40,w74] [s34] (by decide +kernel)
def s250 : Chart 6 := make 38964 [w2,w5,w15,w22,w35,w50,w74] [s35] (by decide +kernel)
def s251 : Chart 6 := make 10991 [w5,w16,w22,w32,w35,w40,w74] [s35] (by decide +kernel)
def s252 : Chart 6 := make 39406 [w2,w5,w15,w22,w50,w82] [s36] (by decide +kernel)
def s253 : Chart 6 := make 11433 [w5,w16,w22,w32,w40,w82] [s36] (by decide +kernel)
def s254 : Chart 6 := make 34662 [w5,w16,w22,w32,w50,w74] [s35,s36] (by decide +kernel)
def s255 : Chart 6 := make 20238 [w5,w12,w16,w22,w32,w40] [s37,s38,s39] (by decide +kernel)
def s256 : Chart 6 := make 6808 [w5,w16,w22,w32,w45,w74] [s40] (by decide +kernel)
def s257 : Chart 6 := make 18766 [w5,w16,w28,w32,w40,w74] [s37,s40] (by decide +kernel)
def s258 : Chart 6 := make 9685 [w5,w7,w12,w28,w29,w40] [s41,s37,s42,s43] (by decide +kernel)
def s259 : Chart 6 := make 36797 [w5,w7,w16,w22,w37,w40] [s41,s38] (by decide +kernel)
def s260 : Chart 6 := make 38043 [w5,w16,w21,w22,w29,w40] [s38,s42] (by decide +kernel)
def s261 : Chart 6 := make 26212 [w7,w14,w16,w22,w29,w40] [s43,s39] (by decide +kernel)
def s262 : Chart 6 := make 36708 [w5,w7,w19,w22,w29,w45,w74] [s34] (by decide +kernel)
def s263 : Chart 6 := make 48666 [w5,w7,w19,w28,w29,w40,w74] [s23] (by decide +kernel)
def s264 : Chart 6 := make 61776 [w5,w7,w28,w29,w45,w74] [s40] (by decide +kernel)
def s265 : Chart 6 := make 28390 [w5,w15,w23,w41,w53,w68] [] (by decide +kernel)
def s266 : Chart 6 := make 40878 [w5,w16,w22,w41,w53,w68] [] (by decide +kernel)
def s267 : Chart 6 := make 10255 [w2,w5,w27,w44,w53,w68] [] (by decide +kernel)
def s268 : Chart 6 := make 28692 [w5,w16,w22,w44,w53,w68] [] (by decide +kernel)
def s269 : Chart 6 := make 12601 [w5,w28,w29,w44,w53,w62] [] (by decide +kernel)
def s270 : Chart 6 := make 40503 [w5,w28,w32,w44,w51,w62] [] (by decide +kernel)
def s271 : Chart 6 := make 29083 [w7,w27,w29,w45,w52,w62] [] (by decide +kernel)
def s272 : Chart 6 := make 47557 [w7,w28,w29,w44,w52,w62] [] (by decide +kernel)
def s273 : Chart 6 := make 27642 [w5,w16,w22,w47,w53,w68] [] (by decide +kernel)
def s274 : Chart 6 := make 41835 [w15,w23,w32,w49,w52,w62] [] (by decide +kernel)
def s275 : Chart 6 := make 54323 [w16,w22,w32,w49,w52,w62] [] (by decide +kernel)
def s276 : Chart 6 := make 47762 [w5,w16,w22,w53,w68,w71] [] (by decide +kernel)
def s277 : Chart 6 := make 61525 [w5,w15,w28,w29,w53,w71] [] (by decide +kernel)
def s278 : Chart 6 := make 1946 [w5,w16,w27,w29,w53,w71] [] (by decide +kernel)
def s279 : Chart 6 := make 23906 [w5,w15,w28,w32,w51,w71] [] (by decide +kernel)
def s280 : Chart 6 := make 29848 [w5,w16,w27,w32,w51,w71] [] (by decide +kernel)
def s281 : Chart 6 := make 48428 [w2,w5,w15,w22,w60,w80] [s44] (by decide +kernel)
def s282 : Chart 6 := make 16024 [w5,w15,w23,w32,w51,w80] [s44] (by decide +kernel)
def s283 : Chart 6 := make 28916 [w5,w15,w23,w32,w60,w71] [s44] (by decide +kernel)
def s284 : Chart 6 := make 29087 [w5,w7,w16,w22,w73,w76] [] (by decide +kernel)
def s285 : Chart 6 := make 35024 [w5,w16,w22,w53,w68,w73] [] (by decide +kernel)
def s286 : Chart 6 := make 26109 [w5,w16,w23,w40,w53,w68] [] (by decide +kernel)
def s287 : Chart 6 := make 22176 [w5,w16,w27,w40,w53,w68] [] (by decide +kernel)
def s288 : Chart 6 := make 55692 [w5,w16,w27,w42,w51,w68] [] (by decide +kernel)
def s289 : Chart 6 := make 64625 [w5,w10,w16,w22,w45,w51,w68] [s26,s45] (by decide +kernel)
def s290 : Chart 6 := make 11062 [w5,w10,w16,w28,w40,w51,w68] [s27] (by decide +kernel)
def s291 : Chart 6 := make 12892 [w10,w16,w19,w22,w40,w51,w68] [s45,s28] (by decide +kernel)
def s292 : Chart 6 := make 825 [w5,w16,w19,w22,w40,w53,w68] [s46,s47,s28] (by decide +kernel)
def s293 : Chart 6 := make 13935 [w5,w16,w22,w45,w53,w68] [s26,s46,s48] (by decide +kernel)
def s294 : Chart 6 := make 25893 [w5,w16,w28,w40,w53,w68] [s27,s47,s48] (by decide +kernel)
def s295 : Chart 6 := make 6216 [w5,w7,w19,w22,w45,w51,w68] [s46,s29,s45] (by decide +kernel)
def s296 : Chart 6 := make 18174 [w5,w7,w19,w28,w40,w51,w68] [s47,s30] (by decide +kernel)
def s297 : Chart 6 := make 31284 [w5,w7,w28,w45,w51,w68] [s48] (by decide +kernel)
def s298 : Chart 6 := make 50364 [w10,w19,w22,w29,w45,w51,w62] [s34,s45,s31] (by decide +kernel)
def s299 : Chart 6 := make 38297 [w5,w19,w22,w29,w45,w53,w62] [s46,s31] (by decide +kernel)
def s300 : Chart 6 := make 50255 [w5,w19,w28,w29,w40,w53,w62] [s47,s24] (by decide +kernel)
def s301 : Chart 6 := make 63365 [w5,w28,w29,w45,w53,w62] [s48] (by decide +kernel)
def s302 : Chart 6 := make 4272 [w5,w15,w23,w35,w50,w51,w62] [s32] (by decide +kernel)
def s303 : Chart 6 := make 16760 [w5,w16,w22,w35,w50,w51,w62] [s35,s33] (by decide +kernel)
def s304 : Chart 6 := make 16315 [w5,w15,w23,w40,w60,w78] [s44] (by decide +kernel)
def s305 : Chart 6 := make 28803 [w5,w16,w22,w40,w60,w78] [] (by decide +kernel)
def s306 : Chart 6 := make 24372 [w5,w15,w23,w50,w51,w78] [] (by decide +kernel)
def s307 : Chart 6 := make 36860 [w5,w16,w22,w50,w51,w78] [s36] (by decide +kernel)
def s308 : Chart 6 := make 19886 [w5,w15,w23,w50,w60,w62] [s32,s44] (by decide +kernel)
def s309 : Chart 6 := make 32374 [w5,w16,w22,w50,w60,w62] [s33,s36] (by decide +kernel)
def s310 : Chart 6 := make 25746 [w5,w28,w32,w45,w51,w62] [s40] (by decide +kernel)
def s311 : Chart 6 := make 65305 [w15,w22,w29,w41,w54,w75] [] (by decide +kernel)
def s312 : Chart 6 := make 50536 [w15,w23,w29,w40,w54,w75] [] (by decide +kernel)
def s313 : Chart 6 := make 63024 [w16,w22,w29,w40,w54,w75] [] (by decide +kernel)
def s314 : Chart 6 := make 13901 [w7,w16,w22,w29,w40,w57,w75] [s49] (by decide +kernel)
def s315 : Chart 6 := make 35282 [w7,w16,w22,w29,w45,w52,w75] [] (by decide +kernel)
def s316 : Chart 6 := make 47240 [w7,w16,w28,w29,w40,w52,w75] [s49] (by decide +kernel)
def s317 : Chart 6 := make 62891 [w16,w22,w29,w40,w54,w57,w62] [s50] (by decide +kernel)
def s318 : Chart 6 := make 18751 [w16,w22,w29,w45,w52,w54,w62] [s50] (by decide +kernel)
def s319 : Chart 6 := make 30709 [w16,w28,w29,w40,w52,w54,w62] [] (by decide +kernel)
def s320 : Chart 6 := make 34604 [w7,w22,w29,w45,w52,w57,w62] [s50] (by decide +kernel)
def s321 : Chart 6 := make 46562 [w7,w28,w29,w40,w52,w57,w62] [s49] (by decide +kernel)
def s322 : Chart 6 := make 32800 [w7,w28,w29,w45,w52,w62] [] (by decide +kernel)
def s323 : Chart 7 := make 4294 [w0,w2,w5,w15,w22,w32,w71] [s51,s52,s53] (by decide +kernel)
def s324 : Chart 7 := make 5632 [w0,w5,w7,w15,w23,w29,w71] [s51,s54,s55,s56] (by decide +kernel)
def s325 : Chart 7 := make 23988 [w2,w5,w7,w15,w22,w30,w71] [s52,s54] (by decide +kernel)
def s326 : Chart 7 := make 32492 [w2,w5,w8,w15,w22,w29,w71] [s52,s55] (by decide +kernel)
def s327 : Chart 7 := make 38931 [w2,w6,w7,w15,w22,w29,w71] [s53,s56] (by decide +kernel)
def s328 : Chart 7 := make 30138 [w0,w2,w5,w15,w22,w42,w68] [s57,s58] (by decide +kernel)
def s329 : Chart 7 := make 38350 [w0,w5,w7,w16,w22,w40,w68] [s59,s60,s61] (by decide +kernel)
def s330 : Chart 7 := make 12539 [w2,w5,w7,w15,w22,w40,w69] [s57,s59] (by decide +kernel)
def s331 : Chart 7 := make 52722 [w2,w5,w8,w15,w22,w40,w68] [s60] (by decide +kernel)
def s332 : Chart 7 := make 59161 [w2,w6,w7,w15,w22,w40,w68] [s58,s61] (by decide +kernel)
def s333 : Chart 7 := make 29908 [w0,w5,w7,w15,w29,w41,w66] [s62,s63] (by decide +kernel)
def s334 : Chart 7 := make 33495 [w2,w5,w7,w15,w30,w40,w66] [s62] (by decide +kernel)
def s335 : Chart 7 := make 41999 [w2,w5,w8,w15,w29,w40,w66] [] (by decide +kernel)
def s336 : Chart 7 := make 48438 [w2,w6,w7,w15,w29,w40,w66] [s63] (by decide +kernel)
def s337 : Chart 7 := make 17658 [w2,w5,w15,w22,w29,w42,w63] [s57] (by decide +kernel)
def s338 : Chart 7 := make 44294 [w2,w5,w15,w22,w30,w42,w62] [s57] (by decide +kernel)
def s339 : Chart 7 := make 59237 [w2,w6,w15,w22,w29,w42,w62] [s58] (by decide +kernel)
def s340 : Chart 7 := make 20324 [w0,w5,w15,w23,w32,w40,w62] [s51,s64,s65] (by decide +kernel)
def s341 : Chart 7 := make 32812 [w0,w5,w16,w22,w32,w40,w62] [s66,s67,s68] (by decide +kernel)
def s342 : Chart 7 := make 12044 [w2,w5,w15,w22,w32,w40,w63] [s66] (by decide +kernel)
def s343 : Chart 7 := make 48280 [w2,w5,w15,w22,w33,w40,w62] [s52,s64,s67] (by decide +kernel)
def s344 : Chart 7 := make 53623 [w2,w6,w15,w22,w32,w40,w62] [s53,s65,s68] (by decide +kernel)
def s345 : Chart 7 := make 54787 [w5,w7,w15,w22,w30,w41,w62] [s62] (by decide +kernel)
def s346 : Chart 7 := make 4209 [w6,w7,w15,w22,w29,w41,w62] [s63] (by decide +kernel)
def s347 : Chart 7 := make 40018 [w5,w7,w15,w23,w30,w40,w62] [s54,s64] (by decide +kernel)
def s348 : Chart 7 := make 48522 [w5,w8,w15,w23,w29,w40,w62] [s55,s64] (by decide +kernel)
def s349 : Chart 7 := make 54961 [w6,w7,w15,w23,w29,w40,w62] [s56,s65] (by decide +kernel)
def s350 : Chart 7 := make 25870 [w5,w7,w16,w22,w29,w40,w63] [s59,s66] (by decide +kernel)
def s351 : Chart 7 := make 52506 [w5,w7,w16,w22,w30,w40,w62] [s59,s67] (by decide +kernel)
def s352 : Chart 7 := make 61010 [w5,w8,w16,w22,w29,w40,w62] [s60,s67] (by decide +kernel)
def s353 : Chart 7 := make 1928 [w6,w7,w16,w22,w29,w40,w62] [s61,s68] (by decide +kernel)
def s354 : Chart 7 := make 13881 [w2,w3,w5,w15,w22,w32,w74] [s69,s70,s71,s72,s73] (by decide +kernel)
def s355 : Chart 7 := make 23166 [w2,w5,w7,w15,w22,w31,w74] [s69,s74] (by decide +kernel)
def s356 : Chart 7 := make 24633 [w2,w5,w7,w15,w24,w29,w74] [s70,s75] (by decide +kernel)
def s357 : Chart 7 := make 17049 [w2,w5,w7,w17,w22,w29,w74] [s71,s76] (by decide +kernel)
def s358 : Chart 7 := make 58400 [w2,w5,w9,w15,w22,w29,w74] [s69,s77] (by decide +kernel)
def s359 : Chart 7 := make 27707 [w3,w5,w7,w16,w22,w29,w74] [s72,s74,s75,s76,s77] (by decide +kernel)
def s360 : Chart 7 := make 50378 [w4,w5,w7,w15,w22,w29,w74] [s73,s76] (by decide +kernel)
def s361 : Chart 7 := make 21008 [w2,w3,w5,w15,w22,w53,w68] [s78,s79,s80,s81,s82] (by decide +kernel)
def s362 : Chart 7 := make 2371 [w2,w5,w7,w15,w22,w51,w70] [s78,s83] (by decide +kernel)
def s363 : Chart 7 := make 59662 [w2,w5,w7,w15,w24,w51,w68] [s79,s84] (by decide +kernel)
def s364 : Chart 7 := make 52078 [w2,w5,w7,w17,w22,w51,w68] [s80,s85] (by decide +kernel)
def s365 : Chart 7 := make 27908 [w2,w5,w9,w15,w22,w51,w68] [s86] (by decide +kernel)
def s366 : Chart 7 := make 62736 [w3,w5,w7,w16,w22,w51,w68] [s81,s83,s84,s85,s86] (by decide +kernel)
def s367 : Chart 7 := make 19886 [w4,w5,w7,w15,w22,w51,w68] [s82,s85] (by decide +kernel)
def s368 : Chart 7 := make 10307 [w2,w5,w7,w15,w29,w51,w67] [] (by decide +kernel)
def s369 : Chart 7 := make 47472 [w2,w5,w7,w15,w31,w51,w66] [] (by decide +kernel)
def s370 : Chart 7 := make 41355 [w2,w5,w7,w17,w29,w51,w66] [] (by decide +kernel)
def s371 : Chart 7 := make 17185 [w2,w5,w9,w15,w29,w51,w66] [] (by decide +kernel)
def s372 : Chart 7 := make 9163 [w4,w5,w7,w15,w29,w51,w66] [] (by decide +kernel)
def s373 : Chart 7 := make 52588 [w2,w5,w15,w22,w29,w53,w64] [s78,s87,s88] (by decide +kernel)
def s374 : Chart 7 := make 24755 [w2,w5,w15,w22,w31,w53,w62] [s78,s89,s90] (by decide +kernel)
def s375 : Chart 7 := make 26222 [w2,w5,w15,w24,w29,w53,w62] [s79,s91,s92] (by decide +kernel)
def s376 : Chart 7 := make 18638 [w2,w5,w17,w22,w29,w53,w62] [s80,s93,s94] (by decide +kernel)
def s377 : Chart 7 := make 16808 [w3,w5,w15,w23,w29,w53,w62] [s87,s89,s91,s93] (by decide +kernel)
def s378 : Chart 7 := make 29296 [w3,w5,w16,w22,w29,w53,w62] [s81,s88,s90,s92,s94] (by decide +kernel)
def s379 : Chart 7 := make 51967 [w4,w5,w15,w22,w29,w53,w62] [s82,s91,s94] (by decide +kernel)
def s380 : Chart 7 := make 14969 [w2,w5,w15,w22,w32,w51,w64] [s95,s96] (by decide +kernel)
def s381 : Chart 7 := make 4783 [w2,w5,w15,w22,w34,w51,w62] [s69,s97,s98] (by decide +kernel)
def s382 : Chart 7 := make 54124 [w2,w5,w15,w24,w32,w51,w62] [s70,s99,s100] (by decide +kernel)
def s383 : Chart 7 := make 46540 [w2,w5,w17,w22,w32,w51,w62] [s71,s101,s102] (by decide +kernel)
def s384 : Chart 7 := make 44710 [w3,w5,w15,w23,w32,w51,w62] [s95,s97,s99,s101] (by decide +kernel)
def s385 : Chart 7 := make 57198 [w3,w5,w16,w22,w32,w51,w62] [s72,s96,s98,s100,s102] (by decide +kernel)
def s386 : Chart 7 := make 14348 [w4,w5,w15,w22,w32,w51,w62] [s73,s99,s102] (by decide +kernel)
def s387 : Chart 7 := make 59711 [w2,w7,w15,w22,w31,w52,w62] [s103,s104] (by decide +kernel)
def s388 : Chart 7 := make 61178 [w2,w7,w15,w24,w29,w52,w62] [s105,s106] (by decide +kernel)
def s389 : Chart 7 := make 53594 [w2,w7,w17,w22,w29,w52,w62] [s107,s108] (by decide +kernel)
def s390 : Chart 7 := make 51764 [w3,w7,w15,w23,w29,w52,w62] [s103,s105,s107] (by decide +kernel)
def s391 : Chart 7 := make 64252 [w3,w7,w16,w22,w29,w52,w62] [s104,s106,s108] (by decide +kernel)
def s392 : Chart 7 := make 21402 [w4,w7,w15,w22,w29,w52,w62] [s105,s108] (by decide +kernel)
def s393 : Chart 7 := make 16307 [w5,w7,w15,w23,w29,w51,w64] [s87,s95] (by decide +kernel)
def s394 : Chart 7 := make 28795 [w5,w7,w16,w22,w29,w51,w64] [s83,s88,s96] (by decide +kernel)
def s395 : Chart 7 := make 53995 [w5,w7,w15,w23,w31,w51,w62] [s89,s97,s103] (by decide +kernel)
def s396 : Chart 7 := make 962 [w5,w7,w16,w22,w31,w51,w62] [s74,s83,s90,s98,s104] (by decide +kernel)
def s397 : Chart 7 := make 10811 [w5,w7,w15,w25,w29,w51,w62] [s91,s99,s105] (by decide +kernel)
def s398 : Chart 7 := make 2429 [w5,w7,w16,w24,w29,w51,w62] [s75,s84,s92,s100,s106] (by decide +kernel)
def s399 : Chart 7 := make 47878 [w5,w7,w17,w23,w29,w51,w62] [s93,s101,s107] (by decide +kernel)
def s400 : Chart 7 := make 27010 [w5,w7,w18,w22,w29,w51,w62] [s76,s85,s94,s102,s108] (by decide +kernel)
def s401 : Chart 7 := make 23708 [w5,w9,w15,w23,w29,w51,w62] [s97] (by decide +kernel)
def s402 : Chart 7 := make 36196 [w5,w9,w16,w22,w29,w51,w62] [s77,s86,s98] (by decide +kernel)
def s403 : Chart 7 := make 54564 [w2,w5,w7,w27,w29,w40,w55] [s109,s110,s111,s112,s113,s114] (by decide +kernel)
def s404 : Chart 7 := make 5936 [w2,w5,w7,w27,w29,w43,w51] [s115,s116,s117,s118] (by decide +kernel)
def s405 : Chart 7 := make 35912 [w2,w5,w7,w27,w36,w40,w51] [s119,s120,s121,s122,s123,s124] (by decide +kernel)
def s406 : Chart 7 := make 18108 [w2,w5,w11,w27,w29,w40,w53] [s109,s115,s119,s125,s126] (by decide +kernel)
def s407 : Chart 7 := make 51624 [w2,w5,w11,w27,w29,w42,w51] [s110,s116,s120,s127] (by decide +kernel)
def s408 : Chart 7 := make 46010 [w2,w5,w11,w27,w32,w40,w51] [s111,s117,s121,s128,s129] (by decide +kernel)
def s409 : Chart 7 := make 28654 [w2,w5,w20,w27,w29,w40,w51] [s109,s116,s121,s130,s131,s132] (by decide +kernel)
def s410 : Chart 7 := make 53064 [w2,w7,w11,w27,w29,w40,w52] [s112,s118,s122,s130,s133,s134] (by decide +kernel)
def s411 : Chart 7 := make 10384 [w2,w7,w13,w27,w29,w40,w51] [s112,s125,s127,s128,s135,s136] (by decide +kernel)
def s412 : Chart 7 := make 62117 [w5,w7,w11,w27,w29,w41,w51] [s113,s123,s131,s133,s135] (by decide +kernel)
def s413 : Chart 7 := make 53894 [w5,w7,w11,w28,w29,w40,w51] [s114,s124,s126,s129,s132,s134,s136] (by decide +kernel)
def s414 : Chart 7 := make 30941 [w2,w5,w15,w22,w29,w40,w58] [s109,s137,s138] (by decide +kernel)
def s415 : Chart 7 := make 64789 [w2,w5,w15,w22,w29,w42,w55] [s110] (by decide +kernel)
def s416 : Chart 7 := make 59175 [w2,w5,w15,w22,w32,w40,w55] [s111,s139,s140] (by decide +kernel)
def s417 : Chart 7 := make 50480 [w2,w7,w15,w22,w29,w40,w56] [s112,s141,s142,s143] (by decide +kernel)
def s418 : Chart 7 := make 9761 [w5,w7,w15,w22,w29,w41,w55] [s113,s141] (by decide +kernel)
def s419 : Chart 7 := make 60513 [w5,w7,w15,w23,w29,w40,w55] [s114,s137,s139,s142] (by decide +kernel)
def s420 : Chart 7 := make 7480 [w5,w7,w16,w22,w29,w40,w55] [s114,s138,s140,s143] (by decide +kernel)
def s421 : Chart 7 := make 48166 [w2,w5,w15,w22,w29,w43,w53] [s115,s144] (by decide +kernel)
def s422 : Chart 7 := make 18365 [w2,w5,w15,w22,w29,w46,w51] [s116] (by decide +kernel)
def s423 : Chart 7 := make 10547 [w2,w5,w15,w22,w32,w43,w51] [s117,s145] (by decide +kernel)
def s424 : Chart 7 := make 17601 [w2,w7,w15,w22,w29,w43,w52] [s118,s146] (by decide +kernel)
def s425 : Chart 7 := make 11885 [w5,w7,w15,w23,w29,w43,w51] [s144,s145,s146] (by decide +kernel)
def s426 : Chart 7 := make 12621 [w2,w5,w15,w22,w36,w40,w53] [s119,s147,s148] (by decide +kernel)
def s427 : Chart 7 := make 46137 [w2,w5,w15,w22,w36,w42,w51] [s120] (by decide +kernel)
def s428 : Chart 7 := make 3668 [w2,w5,w15,w22,w38,w40,w51] [s121,s149,s150] (by decide +kernel)
def s429 : Chart 7 := make 47577 [w2,w7,w15,w22,w36,w40,w52] [s122,s151,s152,s153] (by decide +kernel)
def s430 : Chart 7 := make 56630 [w5,w7,w15,w22,w36,w41,w51] [s123,s151] (by decide +kernel)
def s431 : Chart 7 := make 41861 [w5,w7,w15,w23,w36,w40,w51] [s124,s147,s149,s152] (by decide +kernel)
def s432 : Chart 7 := make 54349 [w5,w7,w16,w22,w36,w40,w51] [s124,s148,s150,s153] (by decide +kernel)
def s433 : Chart 7 := make 52103 [w2,w5,w15,w26,w29,w40,w53] [] (by decide +kernel)
def s434 : Chart 7 := make 20098 [w2,w5,w15,w26,w29,w42,w51] [] (by decide +kernel)
def s435 : Chart 7 := make 14484 [w2,w5,w15,w26,w32,w40,w51] [] (by decide +kernel)
def s436 : Chart 7 := make 21538 [w2,w7,w15,w26,w29,w40,w52] [s154] (by decide +kernel)
def s437 : Chart 7 := make 30591 [w5,w7,w15,w26,w29,w41,w51] [s154] (by decide +kernel)
def s438 : Chart 7 := make 52614 [w2,w13,w15,w22,w29,w40,w53] [s125,s155,s156] (by decide +kernel)
def s439 : Chart 7 := make 24057 [w5,w11,w15,w23,w29,w40,w53] [s126,s137,s144,s147,s155] (by decide +kernel)
def s440 : Chart 7 := make 36545 [w5,w11,w16,w22,w29,w40,w53] [s126,s138,s148,s156] (by decide +kernel)
def s441 : Chart 7 := make 20609 [w2,w13,w15,w22,w29,w42,w51] [s127] (by decide +kernel)
def s442 : Chart 7 := make 14995 [w2,w13,w15,w22,w32,w40,w51] [s128,s157,s158] (by decide +kernel)
def s443 : Chart 7 := make 51959 [w5,w11,w15,w23,w32,w40,w51] [s129,s139,s145,s149,s157] (by decide +kernel)
def s444 : Chart 7 := make 64447 [w5,w11,w16,w22,w32,w40,w51] [s129,s140,s150,s158] (by decide +kernel)
def s445 : Chart 7 := make 40319 [w2,w15,w20,w22,w29,w40,w52] [s130,s159,s160,s161] (by decide +kernel)
def s446 : Chart 7 := make 49372 [w5,w15,w20,w22,w29,w41,w51] [s131,s159] (by decide +kernel)
def s447 : Chart 7 := make 34603 [w5,w15,w20,w23,w29,w40,w51] [s137,s149,s132,s160] (by decide +kernel)
def s448 : Chart 7 := make 47091 [w5,w16,w20,w22,w29,w40,w51] [s138,s150,s132,s161] (by decide +kernel)
def s449 : Chart 7 := make 8261 [w7,w11,w15,w22,w29,w41,w52] [s133,s141,s151,s154,s159] (by decide +kernel)
def s450 : Chart 7 := make 59013 [w7,w11,w15,w23,w29,w40,w52] [s134,s142,s146,s152,s160] (by decide +kernel)
def s451 : Chart 7 := make 5980 [w7,w11,w16,w22,w29,w40,w52] [s134,s143,s153,s161] (by decide +kernel)
def s452 : Chart 7 := make 31102 [w7,w13,w15,w22,w29,w41,w51] [s135,s141] (by decide +kernel)
def s453 : Chart 7 := make 16333 [w7,w13,w15,w23,w29,w40,w51] [s136,s142,s155,s157] (by decide +kernel)
def s454 : Chart 7 := make 28821 [w7,w13,w16,w22,w29,w40,w51] [s136,s143,s156,s158] (by decide +kernel)
def s455 : Chart 7 := make 45553 [w2,w5,w15,w22,w29,w42,w75] [] (by decide +kernel)
def s456 : Chart 7 := make 39939 [w2,w5,w15,w22,w32,w40,w75] [s162] (by decide +kernel)
def s457 : Chart 7 := make 24104 [w2,w10,w15,w22,w29,w40,w75] [s163] (by decide +kernel)
def s458 : Chart 7 := make 53765 [w5,w7,w16,w22,w29,w40,w75] [s164,s165,s162,s166,s163] (by decide +kernel)
def s459 : Chart 7 := make 46337 [w2,w15,w22,w29,w40,w54,w65] [s167,s168] (by decide +kernel)
def s460 : Chart 7 := make 6943 [w5,w15,w23,w29,w40,w53,w65] [s167] (by decide +kernel)
def s461 : Chart 7 := make 19431 [w5,w16,w22,w29,w40,w53,w65] [s169,s170,s171,s168] (by decide +kernel)
def s462 : Chart 7 := make 46175 [w2,w15,w22,w29,w42,w52,w65] [] (by decide +kernel)
def s463 : Chart 7 := make 40561 [w2,w15,w22,w32,w40,w52,w65] [s172,s173] (by decide +kernel)
def s464 : Chart 7 := make 34845 [w5,w15,w23,w32,w40,w51,w65] [s172] (by decide +kernel)
def s465 : Chart 7 := make 47333 [w5,w16,w22,w32,w40,w51,w65] [s162,s173] (by decide +kernel)
def s466 : Chart 7 := make 56668 [w7,w15,w22,w29,w41,w52,w65] [] (by decide +kernel)
def s467 : Chart 7 := make 41899 [w7,w15,w23,w29,w40,w52,w65] [s167,s172] (by decide +kernel)
def s468 : Chart 7 := make 54387 [w7,w16,w22,w29,w40,w52,w65] [s168,s173] (by decide +kernel)
def s469 : Chart 7 := make 33779 [w10,w15,w22,w29,w41,w51,w65] [] (by decide +kernel)
def s470 : Chart 7 := make 19010 [w10,w15,w23,w29,w40,w51,w65] [s167] (by decide +kernel)
def s471 : Chart 7 := make 31498 [w10,w16,w22,w29,w40,w51,w65] [s163,s168] (by decide +kernel)
def s472 : Chart 7 := make 25367 [w5,w7,w16,w22,w29,w45,w51,w65] [s164,s169] (by decide +kernel)
def s473 : Chart 7 := make 37325 [w5,w7,w16,w28,w29,w40,w51,w65] [s165,s170,s174] (by decide +kernel)
def s474 : Chart 7 := make 39155 [w7,w16,w19,w22,w29,w40,w51,w65] [s166,s174,s171] (by decide +kernel)
def s475 : Chart 7 := make 15643 [w2,w5,w15,w22,w29,w53,w72] [s175] (by decide +kernel)
def s476 : Chart 7 := make 43545 [w2,w5,w15,w22,w32,w51,w72] [s176] (by decide +kernel)
def s477 : Chart 7 := make 44883 [w5,w7,w15,w23,w29,w51,w72] [s175,s176] (by decide +kernel)
def s478 : Chart 7 := make 41435 [w5,w7,w15,w29,w41,w51,w66] [] (by decide +kernel)
def s479 : Chart 7 := make 61651 [w2,w5,w15,w29,w47,w53,w66] [] (by decide +kernel)
def s480 : Chart 7 := make 24032 [w2,w5,w15,w32,w47,w51,w66] [] (by decide +kernel)
def s481 : Chart 7 := make 31086 [w2,w7,w15,w29,w47,w52,w66] [s177] (by decide +kernel)
def s482 : Chart 7 := make 51235 [w5,w7,w15,w29,w48,w51,w66] [s177] (by decide +kernel)
def s483 : Chart 7 := make 11916 [w5,w15,w23,w29,w40,w53,w66] [s175] (by decide +kernel)
def s484 : Chart 7 := make 45432 [w5,w15,w23,w29,w42,w51,w66] [] (by decide +kernel)
def s485 : Chart 7 := make 39818 [w5,w15,w23,w32,w40,w51,w66] [s176] (by decide +kernel)
def s486 : Chart 7 := make 61641 [w7,w15,w22,w29,w41,w52,w66] [s177] (by decide +kernel)
def s487 : Chart 7 := make 46872 [w7,w15,w23,w29,w40,w52,w66] [s177] (by decide +kernel)
def s488 : Chart 7 := make 63700 [w2,w5,w7,w15,w22,w49,w76] [s178,s179] (by decide +kernel)
def s489 : Chart 7 := make 62171 [w2,w5,w15,w22,w29,w42,w76] [s178] (by decide +kernel)
def s490 : Chart 7 := make 56557 [w2,w5,w15,w22,w32,w40,w76] [s178,s180] (by decide +kernel)
def s491 : Chart 7 := make 4862 [w5,w7,w16,w22,w29,w40,w76] [s179,s180] (by decide +kernel)
def s492 : Chart 7 := make 9925 [w2,w5,w7,w15,w22,w59,w73] [s181,s182,s183] (by decide +kernel)
def s493 : Chart 7 := make 40702 [w2,w5,w15,w22,w29,w53,w73] [s182,s184] (by decide +kernel)
def s494 : Chart 7 := make 3083 [w2,w5,w15,w22,w32,w51,w73] [s182,s185] (by decide +kernel)
def s495 : Chart 7 := make 4421 [w5,w7,w15,w23,w29,w51,w73] [s183,s184,s185] (by decide +kernel)
def s496 : Chart 7 := make 8149 [w2,w5,w15,w22,w40,w53,w68] [s186] (by decide +kernel)
def s497 : Chart 7 := make 41665 [w2,w5,w15,w22,w42,w51,w68] [] (by decide +kernel)
def s498 : Chart 7 := make 49877 [w5,w7,w16,w22,w40,w51,w68] [s186] (by decide +kernel)
def s499 : Chart 7 := make 49213 [w1,w5,w7,w15,w22,w40,w68] [s181,s187] (by decide +kernel)
def s500 : Chart 7 := make 58617 [w2,w5,w15,w22,w40,w60,w68] [s182,s188,s189] (by decide +kernel)
def s501 : Chart 7 := make 37331 [w2,w5,w15,w22,w42,w59,w68] [s187] (by decide +kernel)
def s502 : Chart 7 := make 47824 [w5,w7,w15,w22,w41,w59,w68] [] (by decide +kernel)
def s503 : Chart 7 := make 33055 [w5,w7,w15,w23,w40,w59,w68] [s183,s188] (by decide +kernel)
def s504 : Chart 7 := make 45543 [w5,w7,w16,w22,w40,w59,w68] [s189] (by decide +kernel)
def s505 : Chart 7 := make 4116 [w2,w5,w15,w22,w49,w53,w68] [s190,s191] (by decide +kernel)
def s506 : Chart 7 := make 1153 [w2,w5,w15,w22,w50,w51,w68] [s178] (by decide +kernel)
def s507 : Chart 7 := make 39072 [w2,w7,w15,w22,w49,w52,w68] [s192,s193] (by decide +kernel)
def s508 : Chart 7 := make 33356 [w5,w7,w15,w23,w49,w51,w68] [s190,s192] (by decide +kernel)
def s509 : Chart 7 := make 45844 [w5,w7,w16,w22,w49,w51,w68] [s179,s191,s193] (by decide +kernel)
def s510 : Chart 7 := make 63832 [w5,w15,w23,w29,w40,w53,w68] [s184,s188,s190] (by decide +kernel)
def s511 : Chart 7 := make 10799 [w5,w16,w22,w29,w40,w53,w68] [s186,s189,s191] (by decide +kernel)
def s512 : Chart 7 := make 31929 [w2,w15,w22,w32,w40,w52,w68] [s194,s195,s196] (by decide +kernel)
def s513 : Chart 7 := make 40982 [w5,w15,w22,w32,w41,w51,w68] [s194] (by decide +kernel)
def s514 : Chart 7 := make 26213 [w5,w15,w23,w32,w40,w51,w68] [s185,s188,s195] (by decide +kernel)
def s515 : Chart 7 := make 38701 [w5,w16,w22,w32,w40,w51,w68] [s180,s189,s196] (by decide +kernel)
def s516 : Chart 7 := make 48036 [w7,w15,w22,w29,w41,w52,w68] [s194] (by decide +kernel)
def s517 : Chart 7 := make 33267 [w7,w15,w23,w29,w40,w52,w68] [s192,s195] (by decide +kernel)
def s518 : Chart 7 := make 45755 [w7,w16,w22,w29,w40,w52,w68] [s193,s196] (by decide +kernel)
def s519 : Chart 7 := make 53440 [w2,w5,w15,w22,w29,w53,w71] [s197] (by decide +kernel)
def s520 : Chart 7 := make 15821 [w2,w5,w15,w22,w32,w51,w71] [s198] (by decide +kernel)
def s521 : Chart 7 := make 17159 [w5,w7,w15,w23,w29,w51,w71] [s197,s198] (by decide +kernel)
def s522 : Chart 7 := make 22057 [w5,w15,w23,w29,w40,w53,w71] [s197] (by decide +kernel)
def s523 : Chart 7 := make 61289 [w2,w15,w22,w29,w42,w52,w71] [] (by decide +kernel)
def s524 : Chart 7 := make 49959 [w5,w15,w23,w32,w40,w51,w71] [s198] (by decide +kernel)
def s525 : Chart 7 := make 6261 [w7,w15,w22,w29,w41,w52,w71] [] (by decide +kernel)
def s526 : Chart 7 := make 57013 [w7,w15,w23,w29,w40,w52,w71] [] (by decide +kernel)
def s527 : Chart 7 := make 6636 [w2,w5,w15,w22,w29,w42,w74] [] (by decide +kernel)
def s528 : Chart 7 := make 1022 [w2,w5,w15,w22,w32,w40,w74] [s199] (by decide +kernel)
def s529 : Chart 7 := make 14848 [w5,w7,w16,w22,w29,w40,w74] [s199] (by decide +kernel)
def s530 : Chart 7 := make 44214 [w5,w15,w22,w29,w41,w53,w74] [] (by decide +kernel)
def s531 : Chart 7 := make 29445 [w5,w15,w23,w29,w40,w53,w74] [] (by decide +kernel)
def s532 : Chart 7 := make 41933 [w5,w16,w22,w29,w40,w53,w74] [] (by decide +kernel)
def s533 : Chart 7 := make 57347 [w5,w15,w23,w32,w40,w51,w74] [] (by decide +kernel)
def s534 : Chart 7 := make 4314 [w5,w16,w22,w32,w40,w51,w74] [s199] (by decide +kernel)
def s535 : Chart 7 := make 13649 [w7,w15,w22,w29,w41,w52,w74] [] (by decide +kernel)
def s536 : Chart 7 := make 64401 [w7,w15,w23,w29,w40,w52,w74] [] (by decide +kernel)
def s537 : Chart 7 := make 11368 [w7,w16,w22,w29,w40,w52,w74] [] (by decide +kernel)
def s538 : Chart 7 := make 61881 [w2,w5,w15,w22,w29,w42,w81] [s200] (by decide +kernel)
def s539 : Chart 7 := make 56267 [w2,w5,w15,w22,w32,w40,w81] [s201] (by decide +kernel)
def s540 : Chart 7 := make 4572 [w5,w7,w16,w22,w29,w40,w81] [s200,s201] (by decide +kernel)
def s541 : Chart 7 := make 46334 [w2,w5,w15,w22,w29,w53,w79] [s202] (by decide +kernel)
def s542 : Chart 7 := make 8715 [w2,w5,w15,w22,w32,w51,w79] [s203] (by decide +kernel)
def s543 : Chart 7 := make 10053 [w5,w7,w15,w23,w29,w51,w79] [s202,s203] (by decide +kernel)
def s544 : Chart 7 := make 23067 [w2,w5,w15,w22,w40,w53,w78] [s204] (by decide +kernel)
def s545 : Chart 7 := make 56583 [w2,w5,w15,w22,w42,w51,w78] [s205] (by decide +kernel)
def s546 : Chart 7 := make 64795 [w5,w7,w16,w22,w40,w51,w78] [s204,s205] (by decide +kernel)
def s547 : Chart 7 := make 49884 [w5,w15,w23,w29,w40,w53,w77] [s202] (by decide +kernel)
def s548 : Chart 7 := make 62372 [w5,w16,w22,w29,w40,w53,w77] [s204] (by decide +kernel)
def s549 : Chart 7 := make 17879 [w5,w15,w23,w29,w42,w51,w77] [] (by decide +kernel)
def s550 : Chart 7 := make 30367 [w5,w16,w22,w29,w42,w51,w77] [s200,s205] (by decide +kernel)
def s551 : Chart 7 := make 12265 [w5,w15,w23,w32,w40,w51,w77] [s203] (by decide +kernel)
def s552 : Chart 7 := make 24753 [w5,w16,w22,w32,w40,w51,w77] [s201] (by decide +kernel)
def s553 : Chart 7 := make 34088 [w7,w15,w22,w29,w41,w52,w77] [] (by decide +kernel)
def s554 : Chart 7 := make 19319 [w7,w15,w23,w29,w40,w52,w77] [] (by decide +kernel)
def s555 : Chart 7 := make 31807 [w7,w16,w22,w29,w40,w52,w77] [] (by decide +kernel)
def s556 : Chart 7 := make 8716 [w2,w5,w15,w22,w29,w54,w71] [s206] (by decide +kernel)
def s557 : Chart 7 := make 2940 [w2,w5,w15,w22,w32,w52,w71] [s207] (by decide +kernel)
def s558 : Chart 7 := make 52626 [w2,w10,w15,w22,w29,w52,w71] [s208] (by decide +kernel)
def s559 : Chart 7 := make 4278 [w5,w7,w15,w23,w29,w52,w71] [s206,s207,s208] (by decide +kernel)
def s560 : Chart 7 := make 28946 [w2,w5,w15,w22,w40,w54,w68] [s209] (by decide +kernel)
def s561 : Chart 7 := make 28784 [w2,w5,w15,w22,w42,w52,w68] [] (by decide +kernel)
def s562 : Chart 7 := make 7335 [w2,w10,w15,w22,w40,w52,w68] [s210] (by decide +kernel)
def s563 : Chart 7 := make 36996 [w5,w7,w16,w22,w40,w52,w68] [s211,s212,s209,s213,s210] (by decide +kernel)
def s564 : Chart 7 := make 62133 [w2,w10,w15,w29,w40,w52,w66] [s214] (by decide +kernel)
def s565 : Chart 7 := make 28554 [w5,w7,w15,w29,w41,w52,w66] [s214] (by decide +kernel)
def s566 : Chart 7 := make 24746 [w5,w15,w23,w29,w40,w54,w62] [s206,s167] (by decide +kernel)
def s567 : Chart 7 := make 37234 [w5,w16,w22,w29,w40,w54,w62] [s215,s209,s216,s217,s168] (by decide +kernel)
def s568 : Chart 7 := make 19949 [w2,w5,w15,w22,w32,w40,w52,w78] [s218,s219] (by decide +kernel)
def s569 : Chart 7 := make 7378 [w2,w5,w15,w22,w32,w40,w61,w62] [s220,s221,s222] (by decide +kernel)
def s570 : Chart 7 := make 23520 [w2,w5,w15,w22,w32,w50,w52,w62] [s220,s223,s224] (by decide +kernel)
def s571 : Chart 7 := make 18970 [w5,w15,w23,w32,w40,w52,w62] [s218,s221,s223,s207,s172] (by decide +kernel)
def s572 : Chart 7 := make 31458 [w5,w16,w22,w32,w40,w52,w62] [s219,s222,s162,s224,s173] (by decide +kernel)
def s573 : Chart 7 := make 53674 [w7,w15,w22,w29,w41,w52,w62] [] (by decide +kernel)
def s574 : Chart 7 := make 38905 [w7,w15,w23,w29,w40,w52,w62] [] (by decide +kernel)
def s575 : Chart 7 := make 51393 [w7,w16,w22,w29,w40,w52,w62] [] (by decide +kernel)
def s576 : Chart 7 := make 17904 [w10,w15,w22,w29,w41,w52,w62] [s214] (by decide +kernel)
def s577 : Chart 7 := make 3135 [w10,w15,w23,w29,w40,w52,w62] [s208] (by decide +kernel)
def s578 : Chart 7 := make 15623 [w10,w16,w22,w29,w40,w52,w62] [s163,s210] (by decide +kernel)
def s579 : Chart 7 := make 9492 [w5,w7,w16,w22,w29,w45,w52,w62] [s164,s211,s215,s225] (by decide +kernel)
def s580 : Chart 7 := make 21450 [w5,w7,w16,w28,w29,w40,w52,w62] [s165,s212,s216,s226] (by decide +kernel)
def s581 : Chart 7 := make 23280 [w7,w16,w19,w22,w29,w40,w52,w62] [s166,s213,s225,s226,s217] (by decide +kernel)
def s582 : Chart 7 := make 35668 [w2,w5,w15,w22,w32,w53,w71] [s227] (by decide +kernel)
def s583 : Chart 7 := make 37006 [w5,w7,w15,w23,w29,w53,w71] [s197,s202,s227] (by decide +kernel)
def s584 : Chart 7 := make 61512 [w2,w5,w15,w22,w42,w53,w68] [s228] (by decide +kernel)
def s585 : Chart 7 := make 4203 [w5,w7,w16,w22,w40,w53,w68] [s186,s204,s228] (by decide +kernel)
def s586 : Chart 7 := make 50789 [w2,w5,w15,w29,w42,w53,w66] [] (by decide +kernel)
def s587 : Chart 7 := make 45175 [w2,w5,w15,w32,w40,w53,w66] [] (by decide +kernel)
def s588 : Chart 7 := make 3949 [w5,w15,w23,w29,w40,w53,w62] [s197] (by decide +kernel)
def s589 : Chart 7 := make 16437 [w5,w16,w22,w29,w40,w53,w62] [s186] (by decide +kernel)
def s590 : Chart 7 := make 57312 [w5,w15,w23,w29,w42,w53,w62] [s202] (by decide +kernel)
def s591 : Chart 7 := make 4279 [w5,w16,w22,w29,w42,w53,w62] [s200,s228] (by decide +kernel)
def s592 : Chart 7 := make 51698 [w5,w15,w23,w32,w40,w53,w62] [s227] (by decide +kernel)
def s593 : Chart 7 := make 64186 [w5,w16,w22,w32,w40,w53,w62] [s201,s204] (by decide +kernel)
def s594 : Chart 7 := make 28983 [w1,w5,w7,w15,w22,w29,w71] [s181,s229] (by decide +kernel)
def s595 : Chart 7 := make 50818 [w1,w5,w7,w15,w22,w49,w62] [s181,s230,s231] (by decide +kernel)
def s596 : Chart 7 := make 38490 [w1,w5,w7,w15,w29,w40,w66] [s230] (by decide +kernel)
def s597 : Chart 7 := make 49289 [w1,w5,w15,w22,w29,w42,w62] [s187,s231] (by decide +kernel)
def s598 : Chart 7 := make 43675 [w1,w5,w15,w22,w32,w40,w62] [s229,s231] (by decide +kernel)
def s599 : Chart 7 := make 38387 [w2,w5,w15,w22,w29,w60,w71] [s182,s232] (by decide +kernel)
def s600 : Chart 7 := make 11487 [w2,w5,w15,w22,w32,w59,w71] [s229,s233] (by decide +kernel)
def s601 : Chart 7 := make 12825 [w5,w7,w15,w23,w29,w59,w71] [s183,s232,s233] (by decide +kernel)
def s602 : Chart 7 := make 28137 [w2,w5,w7,w15,w49,w59,w66] [s230] (by decide +kernel)
def s603 : Chart 7 := make 60222 [w2,w5,w15,w22,w49,w60,w62] [s182,s234,s235] (by decide +kernel)
def s604 : Chart 7 := make 2457 [w2,w5,w15,w22,w50,w59,w62] [s231,s178] (by decide +kernel)
def s605 : Chart 7 := make 34660 [w5,w7,w15,w23,w49,w59,w62] [s183,s234] (by decide +kernel)
def s606 : Chart 7 := make 47148 [w5,w7,w16,w22,w49,w59,w62] [s179,s235] (by decide +kernel)
def s607 : Chart 7 := make 37101 [w5,w7,w15,w29,w41,w59,w66] [] (by decide +kernel)
def s608 : Chart 7 := make 54417 [w5,w15,w23,w29,w40,w60,w62] [s232,s188,s234] (by decide +kernel)
def s609 : Chart 7 := make 1384 [w5,w16,w22,w29,w40,w60,w62] [s189,s235] (by decide +kernel)
def s610 : Chart 7 := make 42286 [w5,w15,w22,w32,w41,w59,w62] [] (by decide +kernel)
def s611 : Chart 7 := make 27517 [w5,w15,w23,w32,w40,w59,w62] [s233] (by decide +kernel)
def s612 : Chart 7 := make 40005 [w5,w16,w22,w32,w40,w59,w62] [s180] (by decide +kernel)
def s613 : Chart 7 := make 19846 [w2,w5,w15,w22,w32,w71,w74] [s236] (by decide +kernel)
def s614 : Chart 7 := make 33672 [w5,w7,w16,w22,w29,w71,w74] [s236] (by decide +kernel)
def s615 : Chart 7 := make 45690 [w2,w5,w15,w22,w42,w68,w74] [] (by decide +kernel)
def s616 : Chart 7 := make 53902 [w5,w7,w16,w22,w40,w68,w74] [] (by decide +kernel)
def s617 : Chart 7 := make 43179 [w5,w7,w16,w29,w40,w66,w74] [] (by decide +kernel)
def s618 : Chart 7 := make 48364 [w5,w16,w22,w32,w40,w62,w74] [s199,s236] (by decide +kernel)
def s619 : Chart 7 := make 12962 [w2,w5,w15,w22,w32,w41,w74] [s237,s238] (by decide +kernel)
def s620 : Chart 7 := make 14300 [w5,w7,w15,w23,w29,w41,w74] [s237] (by decide +kernel)
def s621 : Chart 7 := make 26788 [w5,w7,w16,w22,w29,w41,w74] [s238] (by decide +kernel)
def s622 : Chart 7 := make 54385 [w2,w5,w15,w22,w32,w42,w74] [s239] (by decide +kernel)
def s623 : Chart 7 := make 2690 [w5,w7,w16,w22,w29,w42,w74] [s200,s239] (by decide +kernel)
def s624 : Chart 7 := make 61686 [w2,w5,w7,w27,w29,w44,w74] [s240] (by decide +kernel)
def s625 : Chart 7 := make 776 [w2,w5,w15,w22,w32,w44,w74] [s240,s241] (by decide +kernel)
def s626 : Chart 7 := make 14602 [w5,w7,w16,w22,w29,w44,w74] [s241] (by decide +kernel)
def s627 : Chart 7 := make 65247 [w2,w5,w15,w22,w32,w47,w74] [s242] (by decide +kernel)
def s628 : Chart 7 := make 13552 [w5,w7,w16,w22,w29,w47,w74] [s242] (by decide +kernel)
def s629 : Chart 7 := make 31645 [w2,w5,w15,w22,w29,w50,w74] [s178] (by decide +kernel)
def s630 : Chart 7 := make 62510 [w2,w5,w15,w22,w32,w49,w74] [s243] (by decide +kernel)
def s631 : Chart 7 := make 10815 [w5,w7,w16,w22,w29,w49,w74] [s179,s243] (by decide +kernel)
def s632 : Chart 7 := make 62597 [w5,w7,w16,w22,w32,w40,w74] [s199,s201,s239] (by decide +kernel)
def s633 : Chart 7 := make 63714 [w2,w5,w15,w23,w32,w40,w74] [s237,s244] (by decide +kernel)
def s634 : Chart 7 := make 12019 [w5,w7,w16,w23,w29,w40,w74] [s244] (by decide +kernel)
def s635 : Chart 7 := make 65395 [w2,w5,w15,w27,w29,w42,w74] [s245] (by decide +kernel)
def s636 : Chart 7 := make 59781 [w2,w5,w15,w27,w32,w40,w74] [s240,s246] (by decide +kernel)
def s637 : Chart 7 := make 8086 [w5,w7,w16,w27,w29,w40,w74] [s245,s246] (by decide +kernel)
def s638 : Chart 7 := make 10681 [w2,w5,w16,w22,w32,w40,w74] [s199,s238,s244] (by decide +kernel)
def s639 : Chart 7 := make 44599 [w5,w10,w16,w22,w29,w40,w74] [s247,s248,s249,s163] (by decide +kernel)
def s640 : Chart 7 := make 3672 [w5,w16,w22,w29,w32,w40,w74] [s199,s180,s243] (by decide +kernel)
def s641 : Chart 7 := make 18311 [w5,w15,w16,w22,w29,w42,w74] [s245] (by decide +kernel)
def s642 : Chart 7 := make 55723 [w2,w5,w15,w22,w32,w35,w40,w74] [s250,s251] (by decide +kernel)
def s643 : Chart 7 := make 56165 [w2,w5,w15,w22,w32,w40,w82] [s252,s253] (by decide +kernel)
def s644 : Chart 7 := make 13873 [w2,w5,w15,w22,w32,w50,w74] [s250,s252,s254] (by decide +kernel)
def s645 : Chart 7 := make 12697 [w5,w15,w16,w22,w32,w40,w74] [s199,s241,s246] (by decide +kernel)
def s646 : Chart 7 := make 21811 [w5,w16,w22,w32,w40,w74] [s72,s255,s251,s162,s253,s256,s242,s254,s257] (by decide +kernel)
def s647 : Chart 7 := make 13275 [w5,w7,w12,w16,w22,w29,w40] [s258,s259,s255,s260,s261] (by decide +kernel)
def s648 : Chart 7 := make 52256 [w5,w7,w16,w19,w22,w29,w40,w74] [s262,s263,s166,s249] (by decide +kernel)
def s649 : Chart 7 := make 65366 [w5,w7,w16,w22,w29,w45,w74] [s164,s262,s264,s247,s256] (by decide +kernel)
def s650 : Chart 7 := make 11803 [w5,w7,w16,w28,w29,w40,w74] [s258,s165,s263,s264,s248,s257] (by decide +kernel)
def s651 : Chart 7 := make 20089 [w2,w5,w15,w22,w41,w53,w68] [s265,s266] (by decide +kernel)
def s652 : Chart 7 := make 49329 [w5,w7,w15,w23,w41,w51,w68] [s265] (by decide +kernel)
def s653 : Chart 7 := make 61817 [w5,w7,w16,w22,w41,w51,w68] [s266] (by decide +kernel)
def s654 : Chart 7 := make 15889 [w5,w15,w23,w29,w41,w53,w62] [s265] (by decide +kernel)
def s655 : Chart 7 := make 28377 [w5,w16,w22,w29,w41,w53,w62] [s266] (by decide +kernel)
def s656 : Chart 7 := make 43791 [w5,w15,w23,w32,w41,w51,w62] [s237] (by decide +kernel)
def s657 : Chart 7 := make 56279 [w5,w16,w22,w32,w41,w51,w62] [s238] (by decide +kernel)
def s658 : Chart 7 := make 50845 [w7,w15,w23,w29,w41,w52,w62] [] (by decide +kernel)
def s659 : Chart 7 := make 63333 [w7,w16,w22,w29,w41,w52,w62] [] (by decide +kernel)
def s660 : Chart 7 := make 37719 [w5,w7,w16,w22,w42,w51,w68] [s205,s228] (by decide +kernel)
def s661 : Chart 7 := make 13170 [w2,w5,w15,w32,w42,w51,w66] [] (by decide +kernel)
def s662 : Chart 7 := make 19693 [w5,w15,w23,w32,w42,w51,w62] [s203] (by decide +kernel)
def s663 : Chart 7 := make 32181 [w5,w16,w22,w32,w42,w51,w62] [s239,s205] (by decide +kernel)
def s664 : Chart 7 := make 31194 [w2,w5,w7,w27,w44,w51,w68] [s267] (by decide +kernel)
def s665 : Chart 7 := make 7903 [w2,w5,w15,w22,w44,w53,w68] [s267,s268] (by decide +kernel)
def s666 : Chart 7 := make 49631 [w5,w7,w16,w22,w44,w51,w68] [s268] (by decide +kernel)
def s667 : Chart 7 := make 14492 [w5,w7,w15,w29,w45,w51,w66] [] (by decide +kernel)
def s668 : Chart 7 := make 38908 [w5,w7,w16,w29,w44,w51,w66] [] (by decide +kernel)
def s669 : Chart 7 := make 63275 [w2,w5,w27,w29,w44,w53,w62] [s267,s269] (by decide +kernel)
def s670 : Chart 7 := make 25656 [w2,w5,w27,w32,w44,w51,w62] [s240,s270] (by decide +kernel)
def s671 : Chart 7 := make 32710 [w2,w7,w27,w29,w44,w52,w62] [s271,s272] (by decide +kernel)
def s672 : Chart 7 := make 15066 [w5,w7,w27,w29,w45,w51,w62] [s271] (by decide +kernel)
def s673 : Chart 7 := make 33540 [w5,w7,w28,w29,w44,w51,w62] [s269,s270,s272] (by decide +kernel)
def s674 : Chart 7 := make 3703 [w5,w15,w23,w29,w44,w53,w62] [s269] (by decide +kernel)
def s675 : Chart 7 := make 16191 [w5,w16,w22,w29,w44,w53,w62] [s268,s269] (by decide +kernel)
def s676 : Chart 7 := make 31605 [w5,w15,w23,w32,w44,w51,w62] [s270] (by decide +kernel)
def s677 : Chart 7 := make 44093 [w5,w16,w22,w32,w44,w51,w62] [s241,s270] (by decide +kernel)
def s678 : Chart 7 := make 26731 [w7,w15,w22,w29,w45,w52,w62] [s271] (by decide +kernel)
def s679 : Chart 7 := make 38659 [w7,w15,w23,w29,w44,w52,w62] [s272] (by decide +kernel)
def s680 : Chart 7 := make 51147 [w7,w16,w22,w29,w44,w52,w62] [s272] (by decide +kernel)
def s681 : Chart 7 := make 6853 [w2,w5,w15,w22,w47,w53,w68] [s273] (by decide +kernel)
def s682 : Chart 7 := make 48581 [w5,w7,w16,w22,w47,w51,w68] [s273] (by decide +kernel)
def s683 : Chart 7 := make 2653 [w5,w15,w23,w29,w47,w53,w62] [s175] (by decide +kernel)
def s684 : Chart 7 := make 15141 [w5,w16,w22,w29,w47,w53,w62] [s273] (by decide +kernel)
def s685 : Chart 7 := make 30555 [w5,w15,w23,w32,w47,w51,w62] [s176] (by decide +kernel)
def s686 : Chart 7 := make 43043 [w5,w16,w22,w32,w47,w51,w62] [s242] (by decide +kernel)
def s687 : Chart 7 := make 63474 [w7,w15,w22,w29,w48,w52,w62] [s177] (by decide +kernel)
def s688 : Chart 7 := make 37609 [w7,w15,w23,w29,w47,w52,w62] [] (by decide +kernel)
def s689 : Chart 7 := make 50097 [w7,w16,w22,w29,w47,w52,w62] [] (by decide +kernel)
def s690 : Chart 7 := make 65437 [w5,w15,w23,w29,w49,w53,w62] [s184,s190,s234] (by decide +kernel)
def s691 : Chart 7 := make 12404 [w5,w16,w22,w29,w49,w53,w62] [s191,s235] (by decide +kernel)
def s692 : Chart 7 := make 33534 [w2,w15,w22,w32,w49,w52,w62] [s274,s275] (by decide +kernel)
def s693 : Chart 7 := make 27818 [w5,w15,w23,w32,w49,w51,w62] [s185,s234,s274] (by decide +kernel)
def s694 : Chart 7 := make 40306 [w5,w16,w22,w32,w49,w51,w62] [s243,s235,s275] (by decide +kernel)
def s695 : Chart 7 := make 34872 [w7,w15,w23,w29,w49,w52,w62] [s192,s274] (by decide +kernel)
def s696 : Chart 7 := make 47360 [w7,w16,w22,w29,w49,w52,w62] [s193,s275] (by decide +kernel)
def s697 : Chart 7 := make 26973 [w2,w5,w15,w22,w53,w68,w71] [s276] (by decide +kernel)
def s698 : Chart 7 := make 3180 [w5,w7,w16,w22,w51,w68,w71] [s276] (by decide +kernel)
def s699 : Chart 7 := make 57978 [w5,w7,w16,w29,w51,w66,w71] [] (by decide +kernel)
def s700 : Chart 7 := make 22773 [w5,w15,w23,w29,w53,w62,w71] [s197] (by decide +kernel)
def s701 : Chart 7 := make 35261 [w5,w16,w22,w29,w53,w62,w71] [s276] (by decide +kernel)
def s702 : Chart 7 := make 50675 [w5,w15,w23,w32,w51,w62,w71] [s198] (by decide +kernel)
def s703 : Chart 7 := make 63163 [w5,w16,w22,w32,w51,w62,w71] [s236] (by decide +kernel)
def s704 : Chart 7 := make 64908 [w5,w7,w15,w23,w32,w51,w71] [s198,s203,s227] (by decide +kernel)
def s705 : Chart 7 := make 50611 [w2,w5,w15,w23,w29,w53,w71] [s197] (by decide +kernel)
def s706 : Chart 7 := make 12992 [w2,w5,w15,w23,w32,w51,w71] [s51,s198] (by decide +kernel)
def s707 : Chart 7 := make 46678 [w2,w5,w15,w27,w29,w53,w71] [s277,s278] (by decide +kernel)
def s708 : Chart 7 := make 9059 [w2,w5,w15,w27,w32,w51,w71] [s279,s280] (by decide +kernel)
def s709 : Chart 7 := make 16943 [w5,w7,w15,w28,w29,w51,w71] [s277,s279] (by decide +kernel)
def s710 : Chart 7 := make 22885 [w5,w7,w16,w27,w29,w51,w71] [s278,s280] (by decide +kernel)
def s711 : Chart 7 := make 46910 [w5,w10,w15,w23,w29,w51,w71] [s206,s208] (by decide +kernel)
def s712 : Chart 7 := make 5983 [w5,w15,w23,w29,w32,w51,w71] [s232,s198,s185,s233] (by decide +kernel)
def s713 : Chart 7 := make 44244 [w5,w15,w23,w29,w51,w53,w71] [s197] (by decide +kernel)
def s714 : Chart 7 := make 65115 [w5,w15,w16,w22,w29,w53,w71] [s277,s278] (by decide +kernel)
def s715 : Chart 7 := make 2409 [w5,w15,w22,w23,w29,w53,w71] [s197,s175] (by decide +kernel)
def s716 : Chart 7 := make 61741 [w5,w15,w23,w29,w53,w71] [s184,s206,s232,s277] (by decide +kernel)
def s717 : Chart 7 := make 7723 [w2,w5,w15,w22,w32,w51,w80] [s281,s282] (by decide +kernel)
def s718 : Chart 7 := make 20615 [w2,w5,w15,w22,w32,w60,w71] [s229,s281,s283] (by decide +kernel)
def s719 : Chart 7 := make 27496 [w5,w15,w16,w22,w32,w51,w71] [s279,s280] (by decide +kernel)
def s720 : Chart 7 := make 30311 [w5,w15,w22,w23,w32,w51,w71] [s198,s176] (by decide +kernel)
def s721 : Chart 7 := make 24122 [w5,w15,w23,w32,w51,w71] [s51,s282,s207,s283,s279] (by decide +kernel)
def s722 : Chart 7 := make 31851 [w5,w15,w23,w32,w40,w51,w62] [s198] (by decide +kernel)
def s723 : Chart 7 := make 44339 [w5,w16,w22,w32,w40,w51,w62] [s199] (by decide +kernel)
def s724 : Chart 7 := make 12687 [w5,w7,w16,w40,w51,w66,w68] [] (by decide +kernel)
def s725 : Chart 7 := make 55491 [w5,w16,w22,w40,w53,w62,w68] [s186,s276] (by decide +kernel)
def s726 : Chart 7 := make 8298 [w2,w5,w7,w15,w22,w73,w76] [s181,s284] (by decide +kernel)
def s727 : Chart 7 := make 35704 [w2,w5,w15,w22,w42,w68,w76] [s187] (by decide +kernel)
def s728 : Chart 7 := make 43916 [w5,w7,w16,w22,w40,w68,w76] [s284] (by decide +kernel)
def s729 : Chart 7 := make 14235 [w2,w5,w15,w22,w53,w68,w73] [s285] (by decide +kernel)
def s730 : Chart 7 := make 55963 [w5,w7,w16,w22,w51,w68,w73] [s284,s285] (by decide +kernel)
def s731 : Chart 7 := make 5320 [w2,w5,w15,w23,w40,w53,w68] [s265,s286] (by decide +kernel)
def s732 : Chart 7 := make 47048 [w5,w7,w16,w23,w40,w51,w68] [s286] (by decide +kernel)
def s733 : Chart 7 := make 1387 [w2,w5,w15,w27,w40,w53,w68] [s267,s287] (by decide +kernel)
def s734 : Chart 7 := make 34903 [w2,w5,w15,w27,w42,w51,w68] [s288] (by decide +kernel)
def s735 : Chart 7 := make 43115 [w5,w7,w16,w27,w40,w51,w68] [s287,s288] (by decide +kernel)
def s736 : Chart 7 := make 17808 [w2,w5,w16,w22,w40,w53,w68] [s186,s266,s286] (by decide +kernel)
def s737 : Chart 7 := make 14107 [w5,w10,w16,w22,w40,w51,w68] [s289,s290,s209,s291,s210] (by decide +kernel)
def s738 : Chart 7 := make 11441 [w5,w16,w22,w40,w51,w53,w68] [s186] (by decide +kernel)
def s739 : Chart 7 := make 19824 [w5,w15,w16,w22,w40,w53,w68] [s186,s268,s287] (by decide +kernel)
def s740 : Chart 7 := make 28938 [w5,w16,w22,w40,w53,w68] [s81,s292,s209,s293,s273,s285,s294] (by decide +kernel)
def s741 : Chart 7 := make 53340 [w5,w15,w16,w22,w42,w51,w68] [s288] (by decide +kernel)
def s742 : Chart 7 := make 21764 [w5,w7,w16,w19,w22,w40,w51,w68] [s295,s296,s292,s213,s291] (by decide +kernel)
def s743 : Chart 7 := make 34874 [w5,w7,w16,w22,w45,w51,w68] [s211,s295,s297,s289,s293] (by decide +kernel)
def s744 : Chart 7 := make 46832 [w5,w7,w16,w28,w40,w51,w68] [s212,s296,s297,s290,s294] (by decide +kernel)
def s745 : Chart 7 := make 13608 [w5,w16,w23,w29,w40,w53,w62] [s286] (by decide +kernel)
def s746 : Chart 7 := make 41510 [w5,w16,w23,w32,w40,w51,w62] [s244] (by decide +kernel)
def s747 : Chart 7 := make 48564 [w7,w16,w23,w29,w40,w52,w62] [] (by decide +kernel)
def s748 : Chart 7 := make 3733 [w5,w15,w28,w29,w40,w53,w62] [s126,s277,s269] (by decide +kernel)
def s749 : Chart 7 := make 9675 [w5,w16,w27,w29,w40,w53,w62] [s278,s287] (by decide +kernel)
def s750 : Chart 7 := make 43191 [w5,w16,w27,w29,w42,w51,w62] [s245,s288] (by decide +kernel)
def s751 : Chart 7 := make 31635 [w5,w15,w28,w32,w40,w51,w62] [s129,s279,s270] (by decide +kernel)
def s752 : Chart 7 := make 37577 [w5,w16,w27,w32,w40,w51,w62] [s246,s280] (by decide +kernel)
def s753 : Chart 7 := make 46912 [w7,w15,w27,w29,w41,w52,w62] [s133,s271] (by decide +kernel)
def s754 : Chart 7 := make 38689 [w7,w15,w28,w29,w40,w52,w62] [s134,s272] (by decide +kernel)
def s755 : Chart 7 := make 44631 [w7,w16,w27,w29,w40,w52,w62] [s271] (by decide +kernel)
def s756 : Chart 7 := make 5665 [w5,w10,w15,w29,w41,w51,w66] [s214] (by decide +kernel)
def s757 : Chart 7 := make 52124 [w5,w10,w16,w22,w29,w45,w51,w62] [s247,s289,s215,s298] (by decide +kernel)
def s758 : Chart 7 := make 64082 [w5,w10,w16,w28,w29,w40,w51,w62] [s248,s290,s216] (by decide +kernel)
def s759 : Chart 7 := make 391 [w10,w16,w19,w22,w29,w40,w51,w62] [s249,s291,s298,s217] (by decide +kernel)
def s760 : Chart 7 := make 42498 [w15,w22,w29,w32,w41,w52,w62] [s194] (by decide +kernel)
def s761 : Chart 7 := make 27729 [w15,w23,w29,w32,w40,w52,w62] [s195,s274] (by decide +kernel)
def s762 : Chart 7 := make 40217 [w16,w22,w29,w32,w40,w52,w62] [s196,s275] (by decide +kernel)
def s763 : Chart 7 := make 26567 [w15,w22,w29,w41,w42,w52,w62] [] (by decide +kernel)
def s764 : Chart 7 := make 15238 [w15,w22,w29,w41,w52,w53,w62] [] (by decide +kernel)
def s765 : Chart 7 := make 469 [w15,w23,w29,w40,w52,w53,w62] [] (by decide +kernel)
def s766 : Chart 7 := make 12957 [w16,w22,w29,w40,w52,w53,w62] [] (by decide +kernel)
def s767 : Chart 7 := make 19169 [w5,w15,w23,w29,w40,w53,w81] [] (by decide +kernel)
def s768 : Chart 7 := make 31657 [w5,w16,w22,w29,w40,w53,w81] [] (by decide +kernel)
def s769 : Chart 7 := make 25689 [w5,w15,w23,w29,w48,w53,w62] [] (by decide +kernel)
def s770 : Chart 7 := make 53845 [w5,w16,w19,w22,w29,w40,w53,w62] [s292,s299,s300,s171,s217] (by decide +kernel)
def s771 : Chart 7 := make 1434 [w5,w16,w22,w29,w45,w53,w62] [s169,s215,s293,s299,s301] (by decide +kernel)
def s772 : Chart 7 := make 13392 [w5,w16,w28,w29,w40,w53,w62] [s126,s170,s216,s294,s300,s301] (by decide +kernel)
def s773 : Chart 7 := make 61492 [w2,w5,w15,w22,w35,w50,w51,w62] [s250,s220,s302,s303] (by decide +kernel)
def s774 : Chart 7 := make 21031 [w5,w15,w23,w32,w35,w40,w51,w62] [s221,s302] (by decide +kernel)
def s775 : Chart 7 := make 33519 [w5,w16,w22,w32,w35,w40,w51,w62] [s251,s222,s303] (by decide +kernel)
def s776 : Chart 7 := make 8014 [w2,w5,w15,w22,w40,w60,w78] [s281,s304,s305] (by decide +kernel)
def s777 : Chart 7 := make 16071 [w2,w5,w15,w22,w50,w51,w78] [s252,s306,s307] (by decide +kernel)
def s778 : Chart 7 := make 41131 [w5,w15,w23,w32,w40,w51,w78] [s218,s282,s304,s306] (by decide +kernel)
def s779 : Chart 7 := make 53619 [w5,w16,w22,w32,w40,w51,w78] [s219,s253,s305,s307] (by decide +kernel)
def s780 : Chart 7 := make 11585 [w2,w5,w15,w22,w50,w60,w62] [s231,s220,s252,s281,s308,s309] (by decide +kernel)
def s781 : Chart 7 := make 36645 [w5,w15,w23,w32,w40,w60,w62] [s221,s283,s304,s308] (by decide +kernel)
def s782 : Chart 7 := make 49133 [w5,w16,w22,w32,w40,w60,w62] [s222,s253,s305,s309] (by decide +kernel)
def s783 : Chart 7 := make 44702 [w5,w15,w23,w32,w50,w51,w62] [s223,s282,s302,s306,s308] (by decide +kernel)
def s784 : Chart 7 := make 57190 [w5,w16,w22,w32,w50,w51,w62] [s224,s254,s303,s307,s309] (by decide +kernel)
def s785 : Chart 7 := make 53591 [w5,w15,w23,w32,w48,w51,w62] [] (by decide +kernel)
def s786 : Chart 7 := make 29336 [w5,w16,w22,w32,w45,w51,w62] [s256,s310] (by decide +kernel)
def s787 : Chart 7 := make 41294 [w5,w16,w28,w32,w40,w51,w62] [s129,s257,s310] (by decide +kernel)
def s788 : Chart 7 := make 42235 [w2,w15,w22,w29,w40,w54,w75] [s311,s312,s313] (by decide +kernel)
def s789 : Chart 7 := make 52566 [w7,w15,w22,w29,w41,w52,w75] [s311] (by decide +kernel)
def s790 : Chart 7 := make 37797 [w7,w15,w23,w29,w40,w52,w75] [s312] (by decide +kernel)
def s791 : Chart 7 := make 50285 [w7,w16,w22,w29,w40,w52,w75] [s314,s315,s316,s313] (by decide +kernel)
def s792 : Chart 7 := make 36035 [w15,w22,w29,w41,w52,w54,w62] [s311] (by decide +kernel)
def s793 : Chart 7 := make 21266 [w15,w23,w29,w40,w52,w54,w62] [s312] (by decide +kernel)
def s794 : Chart 7 := make 33754 [w16,w22,w29,w40,w52,w54,w62] [s317,s313,s318,s319] (by decide +kernel)
def s795 : Chart 7 := make 60645 [w7,w15,w23,w29,w48,w52,w62] [] (by decide +kernel)
def s796 : Chart 7 := make 50152 [w7,w16,w22,w29,w40,w52,w57,w62] [s314,s320,s321,s317] (by decide +kernel)
def s797 : Chart 7 := make 36390 [w7,w16,w22,w29,w45,w52,w62] [s315,s320,s322,s318] (by decide +kernel)
def s798 : Chart 7 := make 48348 [w7,w16,w28,w29,w40,w52,w62] [s134,s316,s321,s322,s319] (by decide +kernel)
def s799 : Chart 7 := make 59236 [w5,w7,w19,w22,w29,w45,w51,w62] [s262,s295,s299,s225,s298] (by decide +kernel)
def s800 : Chart 7 := make 5673 [w5,w7,w19,w28,w29,w40,w51,w62] [s263,s296,s300,s174,s226] (by decide +kernel)
def s801 : Chart 7 := make 18783 [w5,w7,w28,w29,w45,w51,w62] [s264,s297,s301,s310,s322] (by decide +kernel)
def s802 : Chart 8 := make 62852 [w0,w2,w5,w7,w15,w22,w29,w71] [s323,s324,s325,s326,s327] (by decide +kernel)
def s803 : Chart 8 := make 17561 [w0,w2,w5,w7,w15,w22,w40,w68] [s328,s329,s330,s331,s332] (by decide +kernel)
def s804 : Chart 8 := make 6838 [w0,w2,w5,w7,w15,w29,w40,w66] [s333,s334,s335,s336] (by decide +kernel)
def s805 : Chart 8 := make 17637 [w0,w2,w5,w15,w22,w29,w42,w62] [s328,s337,s338,s339] (by decide +kernel)
def s806 : Chart 8 := make 12023 [w0,w2,w5,w15,w22,w32,w40,w62] [s323,s340,s341,s342,s343,s344] (by decide +kernel)
def s807 : Chart 8 := make 28130 [w0,w5,w7,w15,w22,w29,w41,w62] [s333,s345,s346] (by decide +kernel)
def s808 : Chart 8 := make 13361 [w0,w5,w7,w15,w23,w29,w40,w62] [s324,s340,s347,s348,s349] (by decide +kernel)
def s809 : Chart 8 := make 25849 [w0,w5,w7,w16,w22,w29,w40,w62] [s329,s341,s350,s351,s352,s353] (by decide +kernel)
def s810 : Chart 8 := make 5081 [w2,w5,w7,w15,w22,w29,w40,w63] [s330,s337,s342,s350] (by decide +kernel)
def s811 : Chart 8 := make 31717 [w2,w5,w7,w15,w22,w30,w40,w62] [s325,s330,s334,s338,s343,s345,s347,s351] (by decide +kernel)
def s812 : Chart 8 := make 40221 [w2,w5,w8,w15,w22,w29,w40,w62] [s326,s331,s335,s343,s348,s352] (by decide +kernel)
def s813 : Chart 8 := make 46660 [w2,w6,w7,w15,w22,w29,w40,w62] [s327,s332,s336,s339,s344,s346,s349,s353] (by decide +kernel)
def s814 : Chart 8 := make 6918 [w2,w3,w5,w7,w15,w22,w29,w74] [s354,s355,s356,s357,s358,s359,s360] (by decide +kernel)
def s815 : Chart 8 := make 41947 [w2,w3,w5,w7,w15,w22,w51,w68] [s361,s362,s363,s364,s365,s366,s367] (by decide +kernel)
def s816 : Chart 8 := make 31224 [w2,w3,w5,w7,w15,w29,w51,w66] [s368,s369,s370,s371,s372] (by decide +kernel)
def s817 : Chart 8 := make 8507 [w2,w3,w5,w15,w22,w29,w53,w62] [s361,s373,s374,s375,s376,s377,s378,s379] (by decide +kernel)
def s818 : Chart 8 := make 36409 [w2,w3,w5,w15,w22,w32,w51,w62] [s354,s380,s381,s382,s383,s384,s385,s386] (by decide +kernel)
def s819 : Chart 8 := make 43463 [w2,w3,w7,w15,w22,w29,w52,w62] [s387,s388,s389,s390,s391,s392] (by decide +kernel)
def s820 : Chart 8 := make 8006 [w2,w5,w7,w15,w22,w29,w51,w64] [s362,s368,s373,s380,s393,s394] (by decide +kernel)
def s821 : Chart 8 := make 45694 [w2,w5,w7,w15,w22,w31,w51,w62] [s355,s362,s369,s374,s381,s387,s395,s396] (by decide +kernel)
def s822 : Chart 8 := make 47161 [w2,w5,w7,w15,w24,w29,w51,w62] [s356,s363,s368,s375,s382,s388,s397,s398] (by decide +kernel)
def s823 : Chart 8 := make 39577 [w2,w5,w7,w17,w22,w29,w51,w62] [s357,s364,s370,s376,s383,s389,s399,s400] (by decide +kernel)
def s824 : Chart 8 := make 15407 [w2,w5,w9,w15,w22,w29,w51,w62] [s358,s365,s371,s381,s401,s402] (by decide +kernel)
def s825 : Chart 8 := make 37747 [w3,w5,w7,w15,w23,w29,w51,w62] [s377,s384,s390,s393,s395,s397,s399,s401] (by decide +kernel)
def s826 : Chart 8 := make 50235 [w3,w5,w7,w16,w22,w29,w51,w62] [s359,s366,s378,s385,s391,s394,s396,s398,s400,s402] (by decide +kernel)
def s827 : Chart 8 := make 7385 [w4,w5,w7,w15,w22,w29,w51,w62] [s360,s367,s372,s379,s386,s392,s397,s400] (by decide +kernel)
def s828 : Chart 8 := make 39047 [w2,w5,w7,w11,w27,w29,w40,w51] [s403,s404,s405,s406,s407,s408,s409,s410,s411,s412,s413] (by decide +kernel)
def s829 : Chart 8 := make 52212 [w2,w5,w7,w15,w22,w29,w40,w55] [s403,s414,s415,s416,s417,s418,s419,s420] (by decide +kernel)
def s830 : Chart 8 := make 3584 [w2,w5,w7,w15,w22,w29,w43,w51] [s404,s421,s422,s423,s424,s425] (by decide +kernel)
def s831 : Chart 8 := make 33560 [w2,w5,w7,w15,w22,w36,w40,w51] [s405,s426,s427,s428,s429,s430,s431,s432] (by decide +kernel)
def s832 : Chart 8 := make 7521 [w2,w5,w7,w15,w26,w29,w40,w51] [s433,s434,s435,s436,s437] (by decide +kernel)
def s833 : Chart 8 := make 15756 [w2,w5,w11,w15,w22,w29,w40,w53] [s406,s414,s421,s426,s433,s438,s439,s440] (by decide +kernel)
def s834 : Chart 8 := make 49272 [w2,w5,w11,w15,w22,w29,w42,w51] [s407,s415,s422,s427,s434,s441] (by decide +kernel)
def s835 : Chart 8 := make 43658 [w2,w5,w11,w15,w22,w32,w40,w51] [s408,s416,s423,s428,s435,s442,s443,s444] (by decide +kernel)
def s836 : Chart 8 := make 26302 [w2,w5,w15,w20,w22,w29,w40,w51] [s414,s422,s428,s409,s445,s446,s447,s448] (by decide +kernel)
def s837 : Chart 8 := make 50712 [w2,w7,w11,w15,w22,w29,w40,w52] [s410,s417,s424,s429,s436,s445,s449,s450,s451] (by decide +kernel)
def s838 : Chart 8 := make 8032 [w2,w7,w13,w15,w22,w29,w40,w51] [s411,s417,s438,s441,s442,s452,s453,s454] (by decide +kernel)
def s839 : Chart 8 := make 59765 [w5,w7,w11,w15,w22,w29,w41,w51] [s412,s418,s430,s437,s446,s449,s452] (by decide +kernel)
def s840 : Chart 8 := make 44996 [w5,w7,w11,w15,w23,w29,w40,w51] [s413,s419,s425,s431,s439,s443,s447,s450,s453] (by decide +kernel)
def s841 : Chart 8 := make 57484 [w5,w7,w11,w16,w22,w29,w40,w51] [s413,s420,s432,s440,s444,s448,s451,s454] (by decide +kernel)
def s842 : Chart 8 := make 32976 [w2,w5,w7,w15,w22,w29,w40,w75] [s455,s456,s457,s458] (by decide +kernel)
def s843 : Chart 8 := make 64163 [w2,w5,w15,w22,w29,w40,w53,w65] [s459,s460,s461] (by decide +kernel)
def s844 : Chart 8 := make 32158 [w2,w5,w15,w22,w29,w42,w51,w65] [s455,s462] (by decide +kernel)
def s845 : Chart 8 := make 26544 [w2,w5,w15,w22,w32,w40,w51,w65] [s456,s463,s464,s465] (by decide +kernel)
def s846 : Chart 8 := make 33598 [w2,w7,w15,w22,w29,w40,w52,w65] [s459,s462,s463,s466,s467,s468] (by decide +kernel)
def s847 : Chart 8 := make 10709 [w2,w10,w15,w22,w29,w40,w51,w65] [s457,s459,s469,s470,s471] (by decide +kernel)
def s848 : Chart 8 := make 42651 [w5,w7,w15,w22,w29,w41,w51,w65] [s466,s469] (by decide +kernel)
def s849 : Chart 8 := make 27882 [w5,w7,w15,w23,w29,w40,w51,w65] [s460,s464,s467,s470] (by decide +kernel)
def s850 : Chart 8 := make 40370 [w5,w7,w16,w22,w29,w40,w51,w65] [s458,s472,s473,s461,s465,s474,s468,s471] (by decide +kernel)
def s851 : Chart 8 := make 36582 [w2,w5,w7,w15,w22,w29,w51,w72] [s475,s476,s477] (by decide +kernel)
def s852 : Chart 8 := make 18365 [w2,w5,w7,w15,w29,w40,w51,w66] [s478] (by decide +kernel)
def s853 : Chart 8 := make 17069 [w2,w5,w7,w15,w29,w47,w51,w66] [s479,s480,s481,s482] (by decide +kernel)
def s854 : Chart 8 := make 3615 [w2,w5,w15,w22,w29,w40,w53,w66] [s475,s479,s483] (by decide +kernel)
def s855 : Chart 8 := make 37131 [w2,w5,w15,w22,w29,w42,w51,w66] [s484] (by decide +kernel)
def s856 : Chart 8 := make 31517 [w2,w5,w15,w22,w32,w40,w51,w66] [s476,s480,s485] (by decide +kernel)
def s857 : Chart 8 := make 38571 [w2,w7,w15,w22,w29,w40,w52,w66] [s481,s486,s487] (by decide +kernel)
def s858 : Chart 8 := make 47624 [w5,w7,w15,w22,w29,w41,w51,w66] [s478,s482,s486] (by decide +kernel)
def s859 : Chart 8 := make 32855 [w5,w7,w15,w23,w29,w40,w51,w66] [s477,s482,s483,s484,s485,s487] (by decide +kernel)
def s860 : Chart 8 := make 49594 [w2,w5,w7,w15,w22,w29,w40,w76] [s488,s489,s490,s491] (by decide +kernel)
def s861 : Chart 8 := make 61641 [w2,w5,w7,w15,w22,w29,w51,w73] [s492,s493,s494,s495] (by decide +kernel)
def s862 : Chart 8 := make 29088 [w2,w5,w7,w15,w22,w40,w51,w68] [s496,s497,s498] (by decide +kernel)
def s863 : Chart 8 := make 24754 [w2,w5,w7,w15,w22,w40,w59,w68] [s499,s492,s500,s501,s502,s503,s504] (by decide +kernel)
def s864 : Chart 8 := make 25055 [w2,w5,w7,w15,w22,w49,w51,w68] [s488,s505,s506,s507,s508,s509] (by decide +kernel)
def s865 : Chart 8 := make 55531 [w2,w5,w15,w22,w29,w40,w53,w68] [s493,s496,s500,s505,s510,s511] (by decide +kernel)
def s866 : Chart 8 := make 23526 [w2,w5,w15,w22,w29,w42,w51,w68] [s489,s497,s501,s506] (by decide +kernel)
def s867 : Chart 8 := make 17912 [w2,w5,w15,w22,w32,w40,w51,w68] [s490,s494,s500,s506,s512,s513,s514,s515] (by decide +kernel)
def s868 : Chart 8 := make 24966 [w2,w7,w15,w22,w29,w40,w52,w68] [s507,s512,s516,s517,s518] (by decide +kernel)
def s869 : Chart 8 := make 34019 [w5,w7,w15,w22,w29,w41,w51,w68] [s502,s513,s516] (by decide +kernel)
def s870 : Chart 8 := make 19250 [w5,w7,w15,w23,w29,w40,w51,w68] [s495,s503,s508,s510,s514,s517] (by decide +kernel)
def s871 : Chart 8 := make 31738 [w5,w7,w16,w22,w29,w40,w51,w68] [s491,s498,s504,s509,s511,s515,s518] (by decide +kernel)
def s872 : Chart 8 := make 8858 [w2,w5,w7,w15,w22,w29,w51,w71] [s519,s520,s521] (by decide +kernel)
def s873 : Chart 8 := make 13756 [w2,w5,w15,w22,w29,w40,w53,w71] [s519,s522] (by decide +kernel)
def s874 : Chart 8 := make 47272 [w2,w5,w15,w22,w29,w42,w51,w71] [s523] (by decide +kernel)
def s875 : Chart 8 := make 41658 [w2,w5,w15,w22,w32,w40,w51,w71] [s520,s524] (by decide +kernel)
def s876 : Chart 8 := make 48712 [w2,w7,w15,w22,w29,w40,w52,w71] [s523,s525,s526] (by decide +kernel)
def s877 : Chart 8 := make 57765 [w5,w7,w15,w22,w29,w41,w51,w71] [s525] (by decide +kernel)
def s878 : Chart 8 := make 42996 [w5,w7,w15,w23,w29,w40,w51,w71] [s521,s522,s524,s526] (by decide +kernel)
def s879 : Chart 8 := make 59580 [w2,w5,w7,w15,w22,w29,w40,w74] [s527,s528,s529] (by decide +kernel)
def s880 : Chart 8 := make 21144 [w2,w5,w15,w22,w29,w40,w53,w74] [s530,s531,s532] (by decide +kernel)
def s881 : Chart 8 := make 54660 [w2,w5,w15,w22,w29,w42,w51,w74] [s527] (by decide +kernel)
def s882 : Chart 8 := make 49046 [w2,w5,w15,w22,w32,w40,w51,w74] [s528,s533,s534] (by decide +kernel)
def s883 : Chart 8 := make 56100 [w2,w7,w15,w22,w29,w40,w52,w74] [s535,s536,s537] (by decide +kernel)
def s884 : Chart 8 := make 65153 [w5,w7,w15,w22,w29,w41,w51,w74] [s530,s535] (by decide +kernel)
def s885 : Chart 8 := make 50384 [w5,w7,w15,w23,w29,w40,w51,w74] [s531,s533,s536] (by decide +kernel)
def s886 : Chart 8 := make 62872 [w5,w7,w16,w22,w29,w40,w51,w74] [s529,s532,s534,s537] (by decide +kernel)
def s887 : Chart 8 := make 49304 [w2,w5,w7,w15,w22,w29,w40,w81] [s538,s539,s540] (by decide +kernel)
def s888 : Chart 8 := make 1752 [w2,w5,w7,w15,w22,w29,w51,w79] [s541,s542,s543] (by decide +kernel)
def s889 : Chart 8 := make 44006 [w2,w5,w7,w15,w22,w40,w51,w78] [s544,s545,s546] (by decide +kernel)
def s890 : Chart 8 := make 41583 [w2,w5,w15,w22,w29,w40,w53,w77] [s541,s544,s547,s548] (by decide +kernel)
def s891 : Chart 8 := make 9578 [w2,w5,w15,w22,w29,w42,w51,w77] [s538,s545,s549,s550] (by decide +kernel)
def s892 : Chart 8 := make 3964 [w2,w5,w15,w22,w32,w40,w51,w77] [s539,s542,s551,s552] (by decide +kernel)
def s893 : Chart 8 := make 11018 [w2,w7,w15,w22,w29,w40,w52,w77] [s553,s554,s555] (by decide +kernel)
def s894 : Chart 8 := make 20071 [w5,w7,w15,w22,w29,w41,w51,w77] [s553] (by decide +kernel)
def s895 : Chart 8 := make 5302 [w5,w7,w15,w23,w29,w40,w51,w77] [s543,s547,s549,s551,s554] (by decide +kernel)
def s896 : Chart 8 := make 17790 [w5,w7,w16,w22,w29,w40,w51,w77] [s540,s546,s548,s550,s552,s555] (by decide +kernel)
def s897 : Chart 8 := make 61498 [w2,w5,w7,w15,w22,w29,w52,w71] [s556,s557,s558,s559] (by decide +kernel)
def s898 : Chart 8 := make 16207 [w2,w5,w7,w15,w22,w40,w52,w68] [s560,s561,s562,s563] (by decide +kernel)
def s899 : Chart 8 := make 5484 [w2,w5,w7,w15,w29,w40,w52,w66] [s564,s565] (by decide +kernel)
def s900 : Chart 8 := make 16445 [w2,w5,w15,w22,w29,w40,w54,w62] [s556,s560,s459,s566,s567] (by decide +kernel)
def s901 : Chart 8 := make 16283 [w2,w5,w15,w22,w29,w42,w52,w62] [s455,s561,s462] (by decide +kernel)
def s902 : Chart 8 := make 10669 [w2,w5,w15,w22,w32,w40,w52,w62] [s568,s569,s456,s570,s557,s463,s571,s572] (by decide +kernel)
def s903 : Chart 8 := make 30604 [w2,w7,w15,w22,w29,w40,w52,w62] [s573,s574,s575] (by decide +kernel)
def s904 : Chart 8 := make 60355 [w2,w10,w15,w22,w29,w40,w52,w62] [s457,s558,s562,s564,s576,s577,s578] (by decide +kernel)
def s905 : Chart 8 := make 26776 [w5,w7,w15,w22,w29,w41,w52,w62] [s565,s573,s466,s576] (by decide +kernel)
def s906 : Chart 8 := make 12007 [w5,w7,w15,w23,w29,w40,w52,w62] [s390,s559,s566,s571,s574,s467,s577] (by decide +kernel)
def s907 : Chart 8 := make 24495 [w5,w7,w16,w22,w29,w40,w52,w62] [s391,s458,s579,s563,s580,s567,s572,s581,s575,s468,s578] (by decide +kernel)
def s908 : Chart 8 := make 28705 [w2,w5,w7,w15,w22,w29,w53,w71] [s519,s541,s582,s583] (by decide +kernel)
def s909 : Chart 8 := make 48935 [w2,w5,w7,w15,w22,w40,w53,w68] [s496,s544,s584,s585] (by decide +kernel)
def s910 : Chart 8 := make 38212 [w2,w5,w7,w15,w29,w40,w53,w66] [s586,s587] (by decide +kernel)
def s911 : Chart 8 := make 61169 [w2,w5,w15,w22,w29,w40,w53,w62] [s519,s496,s588,s589] (by decide +kernel)
def s912 : Chart 8 := make 49011 [w2,w5,w15,w22,w29,w42,w53,w62] [s538,s541,s584,s586,s590,s591] (by decide +kernel)
def s913 : Chart 8 := make 43397 [w2,w5,w15,w22,w32,w40,w53,w62] [s539,s582,s544,s587,s592,s593] (by decide +kernel)
def s914 : Chart 8 := make 44735 [w5,w7,w15,w23,w29,w40,w53,w62] [s583,s588,s547,s590,s592] (by decide +kernel)
def s915 : Chart 8 := make 57223 [w5,w7,w16,w22,w29,w40,w53,w62] [s540,s585,s589,s548,s591,s593] (by decide +kernel)
def s916 : Chart 8 := make 36712 [w1,w5,w7,w15,w22,w29,w40,w62] [s594,s499,s595,s596,s597,s598] (by decide +kernel)
def s917 : Chart 8 := make 4524 [w2,w5,w7,w15,w22,w29,w59,w71] [s594,s492,s599,s600,s601] (by decide +kernel)
def s918 : Chart 8 := make 26359 [w2,w5,w7,w15,w22,w49,w59,w62] [s595,s488,s492,s602,s603,s604,s605,s606] (by decide +kernel)
def s919 : Chart 8 := make 14031 [w2,w5,w7,w15,w29,w40,w59,w66] [s596,s602,s607] (by decide +kernel)
def s920 : Chart 8 := make 46116 [w2,w5,w15,w22,w29,w40,w60,w62] [s599,s500,s603,s608,s609] (by decide +kernel)
def s921 : Chart 8 := make 24830 [w2,w5,w15,w22,w29,w42,w59,w62] [s597,s489,s501,s604] (by decide +kernel)
def s922 : Chart 8 := make 19216 [w2,w5,w15,w22,w32,w40,w59,w62] [s598,s490,s600,s604,s610,s611,s612] (by decide +kernel)
def s923 : Chart 8 := make 35323 [w5,w7,w15,w22,w29,w41,w59,w62] [s502,s607,s610] (by decide +kernel)
def s924 : Chart 8 := make 20554 [w5,w7,w15,w23,w29,w40,w59,w62] [s601,s503,s605,s608,s611] (by decide +kernel)
def s925 : Chart 8 := make 33042 [w5,w7,w16,w22,w29,w40,w59,w62] [s491,s504,s606,s609,s612] (by decide +kernel)
def s926 : Chart 8 := make 12883 [w2,w5,w7,w15,w22,w29,w71,w74] [s613,s614] (by decide +kernel)
def s927 : Chart 8 := make 33113 [w2,w5,w7,w15,w22,w40,w68,w74] [s615,s616] (by decide +kernel)
def s928 : Chart 8 := make 22390 [w2,w5,w7,w15,w29,w40,w66,w74] [s617] (by decide +kernel)
def s929 : Chart 8 := make 33189 [w2,w5,w15,w22,w29,w42,w62,w74] [s527,s615] (by decide +kernel)
def s930 : Chart 8 := make 27575 [w2,w5,w15,w22,w32,w40,w62,w74] [s528,s613,s618] (by decide +kernel)
def s931 : Chart 8 := make 41401 [w5,w7,w16,w22,w29,w40,w62,w74] [s529,s614,s616,s617,s618] (by decide +kernel)
def s932 : Chart 8 := make 5999 [w2,w5,w7,w15,w22,w29,w41,w74] [s619,s620,s621] (by decide +kernel)
def s933 : Chart 8 := make 47422 [w2,w5,w7,w15,w22,w29,w42,w74] [s527,s538,s622,s623] (by decide +kernel)
def s934 : Chart 8 := make 59334 [w2,w5,w7,w15,w22,w29,w44,w74] [s624,s625,s626] (by decide +kernel)
def s935 : Chart 8 := make 58284 [w2,w5,w7,w15,w22,w29,w47,w74] [s627,s628] (by decide +kernel)
def s936 : Chart 8 := make 55547 [w2,w5,w7,w15,w22,w29,w49,w74] [s488,s629,s630,s631] (by decide +kernel)
def s937 : Chart 8 := make 41808 [w2,w5,w7,w15,w22,w32,w40,w74] [s528,s539,s622,s632] (by decide +kernel)
def s938 : Chart 8 := make 56751 [w2,w5,w7,w15,w23,w29,w40,w74] [s633,s620,s634] (by decide +kernel)
def s939 : Chart 8 := make 52818 [w2,w5,w7,w15,w27,w29,w40,w74] [s624,s635,s636,s637] (by decide +kernel)
def s940 : Chart 8 := make 3718 [w2,w5,w7,w16,w22,w29,w40,w74] [s638,s529,s621,s634] (by decide +kernel)
def s941 : Chart 8 := make 23810 [w2,w5,w10,w15,w22,w29,w40,w74] [s457,s639] (by decide +kernel)
def s942 : Chart 8 := make 48404 [w2,w5,w15,w22,w29,w32,w40,w74] [s629,s528,s490,s630,s640] (by decide +kernel)
def s943 : Chart 8 := make 32473 [w2,w5,w15,w22,w29,w40,w42,w74] [s527] (by decide +kernel)
def s944 : Chart 8 := make 6636 [w2,w5,w15,w22,w29,w42,w74] [s455,s489,s629,s635,s641] (by decide +kernel)
def s945 : Chart 8 := make 1022 [w2,w5,w15,w22,w32,w40,w74] [s354,s642,s456,s643,s619,s625,s627,s644,s633,s636,s638,s645,s646] (by decide +kernel)
def s946 : Chart 8 := make 5734 [w5,w7,w15,w16,w22,w29,w40,w74] [s529,s626,s637,s641,s645] (by decide +kernel)
def s947 : Chart 8 := make 14848 [w5,w7,w16,w22,w29,w40,w74] [s359,s647,s648,s458,s491,s540,s623,s649,s628,s631,s632,s650,s639,s640,s646] (by decide +kernel)
def s948 : Chart 8 := make 41028 [w2,w5,w7,w15,w22,w41,w51,w68] [s651,s652,s653] (by decide +kernel)
def s949 : Chart 8 := make 30305 [w2,w5,w7,w15,w29,w41,w51,w66] [s333,s478] (by decide +kernel)
def s950 : Chart 8 := make 7588 [w2,w5,w15,w22,w29,w41,w53,w62] [s651,s654,s655] (by decide +kernel)
def s951 : Chart 8 := make 35490 [w2,w5,w15,w22,w32,w41,w51,w62] [s619,s656,s657] (by decide +kernel)
def s952 : Chart 8 := make 42544 [w2,w7,w15,w22,w29,w41,w52,w62] [s573,s658,s659] (by decide +kernel)
def s953 : Chart 8 := make 39657 [w5,w7,w15,w22,w29,w41,w51,w62] [s478,s573] (by decide +kernel)
def s954 : Chart 8 := make 36828 [w5,w7,w15,w23,w29,w41,w51,w62] [s620,s652,s654,s656,s658] (by decide +kernel)
def s955 : Chart 8 := make 49316 [w5,w7,w16,w22,w29,w41,w51,w62] [s621,s653,s655,s657,s659] (by decide +kernel)
def s956 : Chart 8 := make 16930 [w2,w5,w7,w15,w22,w42,w51,w68] [s497,s545,s584,s660] (by decide +kernel)
def s957 : Chart 8 := make 6207 [w2,w5,w7,w15,w29,w42,w51,w66] [s586,s661] (by decide +kernel)
def s958 : Chart 8 := make 29164 [w2,w5,w15,w22,w29,w42,w51,w62] [s527,s497] (by decide +kernel)
def s959 : Chart 8 := make 11392 [w2,w5,w15,w22,w32,w42,w51,w62] [s622,s542,s545,s661,s662,s663] (by decide +kernel)
def s960 : Chart 8 := make 12730 [w5,w7,w15,w23,w29,w42,w51,w62] [s543,s549,s590,s662] (by decide +kernel)
def s961 : Chart 8 := make 25218 [w5,w7,w16,w22,w29,w42,w51,w62] [s623,s660,s550,s591,s663] (by decide +kernel)
def s962 : Chart 8 := make 28842 [w2,w5,w7,w15,w22,w44,w51,w68] [s664,s665,s666] (by decide +kernel)
def s963 : Chart 8 := make 18119 [w2,w5,w7,w15,w29,w44,w51,w66] [s667,s668] (by decide +kernel)
def s964 : Chart 8 := make 18693 [w2,w5,w7,w27,w29,w44,w51,w62] [s624,s664,s669,s670,s671,s672,s673] (by decide +kernel)
def s965 : Chart 8 := make 60923 [w2,w5,w15,w22,w29,w44,w53,w62] [s665,s669,s674,s675] (by decide +kernel)
def s966 : Chart 8 := make 23304 [w2,w5,w15,w22,w32,w44,w51,w62] [s625,s670,s676,s677] (by decide +kernel)
def s967 : Chart 8 := make 30358 [w2,w7,w15,w22,w29,w44,w52,w62] [s671,s678,s679,s680] (by decide +kernel)
def s968 : Chart 8 := make 12714 [w5,w7,w15,w22,w29,w45,w51,w62] [s667,s672,s678] (by decide +kernel)
def s969 : Chart 8 := make 24642 [w5,w7,w15,w23,w29,w44,w51,w62] [s673,s674,s676,s679] (by decide +kernel)
def s970 : Chart 8 := make 37130 [w5,w7,w16,w22,w29,w44,w51,w62] [s626,s666,s668,s673,s675,s677,s680] (by decide +kernel)
def s971 : Chart 8 := make 27792 [w2,w5,w7,w15,w22,w47,w51,w68] [s681,s682] (by decide +kernel)
def s972 : Chart 8 := make 59873 [w2,w5,w15,w22,w29,w47,w53,w62] [s475,s681,s479,s683,s684] (by decide +kernel)
def s973 : Chart 8 := make 22254 [w2,w5,w15,w22,w32,w47,w51,w62] [s627,s476,s480,s685,s686] (by decide +kernel)
def s974 : Chart 8 := make 29308 [w2,w7,w15,w22,w29,w47,w52,w62] [s481,s687,s688,s689] (by decide +kernel)
def s975 : Chart 8 := make 49457 [w5,w7,w15,w22,w29,w48,w51,w62] [s482,s687] (by decide +kernel)
def s976 : Chart 8 := make 23592 [w5,w7,w15,w23,w29,w47,w51,w62] [s477,s683,s685,s688] (by decide +kernel)
def s977 : Chart 8 := make 36080 [w5,w7,w16,w22,w29,w47,w51,w62] [s628,s682,s684,s686,s689] (by decide +kernel)
def s978 : Chart 8 := make 14332 [w2,w5,w7,w15,w29,w49,w51,w66] [s602] (by decide +kernel)
def s979 : Chart 8 := make 57136 [w2,w5,w15,w22,w29,w49,w53,w62] [s493,s505,s603,s690,s691] (by decide +kernel)
def s980 : Chart 8 := make 54173 [w2,w5,w15,w22,w29,w50,w51,w62] [s629,s506,s604] (by decide +kernel)
def s981 : Chart 8 := make 19517 [w2,w5,w15,w22,w32,w49,w51,w62] [s630,s494,s603,s692,s693,s694] (by decide +kernel)
def s982 : Chart 8 := make 26571 [w2,w7,w15,w22,w29,w49,w52,w62] [s507,s692,s695,s696] (by decide +kernel)
def s983 : Chart 8 := make 20855 [w5,w7,w15,w23,w29,w49,w51,w62] [s495,s508,s605,s690,s693,s695] (by decide +kernel)
def s984 : Chart 8 := make 33343 [w5,w7,w16,w22,w29,w49,w51,w62] [s631,s509,s606,s691,s694,s696] (by decide +kernel)
def s985 : Chart 8 := make 47912 [w2,w5,w7,w15,w22,w51,w68,w71] [s697,s698] (by decide +kernel)
def s986 : Chart 8 := make 37189 [w2,w5,w7,w15,w29,w51,w66,w71] [s699] (by decide +kernel)
def s987 : Chart 8 := make 14472 [w2,w5,w15,w22,w29,w53,w62,w71] [s519,s697,s700,s701] (by decide +kernel)
def s988 : Chart 8 := make 42374 [w2,w5,w15,w22,w32,w51,w62,w71] [s520,s613,s702,s703] (by decide +kernel)
def s989 : Chart 8 := make 43712 [w5,w7,w15,w23,w29,w51,w62,w71] [s521,s700,s702] (by decide +kernel)
def s990 : Chart 8 := make 56200 [w5,w7,w16,w22,w29,w51,w62,w71] [s614,s698,s699,s701,s703] (by decide +kernel)
def s991 : Chart 8 := make 56607 [w2,w5,w7,w15,w22,w32,w51,w71] [s520,s542,s582,s704] (by decide +kernel)
def s992 : Chart 8 := make 6029 [w2,w5,w7,w15,w23,w29,w51,w71] [s324,s705,s706,s521] (by decide +kernel)
def s993 : Chart 8 := make 2096 [w2,w5,w7,w15,w27,w29,w51,w71] [s707,s708,s709,s710] (by decide +kernel)
def s994 : Chart 8 := make 38609 [w2,w5,w10,w15,w22,w29,w51,w71] [s556,s558,s711] (by decide +kernel)
def s995 : Chart 8 := make 63203 [w2,w5,w15,w22,w29,w32,w51,w71] [s599,s520,s494,s600,s712] (by decide +kernel)
def s996 : Chart 8 := make 35943 [w2,w5,w15,w22,w29,w51,w53,w71] [s519,s713] (by decide +kernel)
def s997 : Chart 8 := make 53440 [w2,w5,w15,w22,w29,w53,w71] [s475,s493,s556,s599,s705,s707,s714,s715,s716] (by decide +kernel)
def s998 : Chart 8 := make 15821 [w2,w5,w15,w22,w32,w51,w71] [s323,s476,s717,s557,s718,s706,s708,s719,s720,s721] (by decide +kernel)
def s999 : Chart 8 := make 20533 [w5,w7,w15,w16,w22,w29,w51,w71] [s709,s710,s714,s719] (by decide +kernel)
def s1000 : Chart 8 := make 23348 [w5,w7,w15,w22,w23,w29,w51,w71] [s521,s477,s715,s720] (by decide +kernel)
def s1001 : Chart 8 := make 17159 [w5,w7,w15,w23,w29,w51,w71] [s324,s495,s543,s559,s583,s601,s704,s709,s711,s712,s713,s716,s721] (by decide +kernel)
def s1002 : Chart 8 := make 593 [w2,w5,w7,w15,w32,w40,w51,w66] [s587,s661] (by decide +kernel)
def s1003 : Chart 8 := make 23550 [w2,w5,w15,w22,w32,w40,w51,w62] [s528,s520,s722,s723] (by decide +kernel)
def s1004 : Chart 8 := make 7116 [w5,w7,w15,w23,w32,w40,w51,w62] [s704,s722,s551,s592,s662] (by decide +kernel)
def s1005 : Chart 8 := make 19604 [w5,w7,w16,w22,w32,w40,w51,w62] [s632,s546,s723,s552,s593,s663] (by decide +kernel)
def s1006 : Chart 8 := make 57419 [w2,w5,w7,w15,w40,w51,w66,w68] [s724] (by decide +kernel)
def s1007 : Chart 8 := make 34702 [w2,w5,w15,w22,w40,w53,w62,w68] [s496,s697,s725] (by decide +kernel)
def s1008 : Chart 8 := make 2697 [w2,w5,w15,w22,w42,w51,w62,w68] [s497,s615] (by decide +kernel)
def s1009 : Chart 8 := make 10909 [w5,w7,w16,w22,w40,w51,w62,w68] [s498,s616,s698,s724,s725] (by decide +kernel)
def s1010 : Chart 8 := make 23127 [w2,w5,w7,w15,w22,w40,w68,w76] [s499,s726,s727,s728] (by decide +kernel)
def s1011 : Chart 8 := make 35174 [w2,w5,w7,w15,w22,w51,w68,w73] [s726,s729,s730] (by decide +kernel)
def s1012 : Chart 8 := make 26259 [w2,w5,w7,w15,w23,w40,w51,w68] [s731,s652,s732] (by decide +kernel)
def s1013 : Chart 8 := make 22326 [w2,w5,w7,w15,w27,w40,w51,w68] [s664,s733,s734,s735] (by decide +kernel)
def s1014 : Chart 8 := make 38747 [w2,w5,w7,w16,w22,w40,w51,w68] [s329,s736,s498,s653,s732] (by decide +kernel)
def s1015 : Chart 8 := make 58839 [w2,w5,w10,w15,w22,w40,w51,w68] [s560,s562,s737] (by decide +kernel)
def s1016 : Chart 8 := make 1981 [w2,w5,w15,w22,w40,w42,w51,w68] [s497] (by decide +kernel)
def s1017 : Chart 8 := make 56173 [w2,w5,w15,w22,w40,w51,w53,w68] [s496,s738] (by decide +kernel)
def s1018 : Chart 8 := make 8149 [w2,w5,w15,w22,w40,w53,w68] [s361,s560,s651,s665,s681,s729,s731,s733,s736,s739,s740] (by decide +kernel)
def s1019 : Chart 8 := make 41665 [w2,w5,w15,w22,w42,w51,w68] [s328,s561,s727,s734,s741] (by decide +kernel)
def s1020 : Chart 8 := make 40763 [w5,w7,w15,w16,w22,w40,w51,w68] [s498,s666,s735,s739,s741] (by decide +kernel)
def s1021 : Chart 8 := make 49877 [w5,w7,w16,w22,w40,w51,w68] [s329,s366,s742,s546,s563,s585,s728,s660,s743,s682,s730,s744,s737,s738,s740] (by decide +kernel)
def s1022 : Chart 8 := make 58340 [w2,w5,w15,w23,w29,w40,w53,w62] [s705,s731,s588,s654,s745] (by decide +kernel)
def s1023 : Chart 8 := make 20721 [w2,w5,w15,w23,w32,w40,w51,w62] [s340,s633,s706,s722,s656,s746] (by decide +kernel)
def s1024 : Chart 8 := make 27775 [w2,w7,w15,w23,w29,w40,w52,w62] [s574,s658,s747] (by decide +kernel)
def s1025 : Chart 8 := make 24888 [w5,w7,w15,w23,w29,w40,w51,w62] [s521,s588,s722,s574] (by decide +kernel)
def s1026 : Chart 8 := make 34547 [w5,w7,w16,w23,w29,w40,w51,w62] [s634,s732,s745,s746,s747] (by decide +kernel)
def s1027 : Chart 8 := make 54407 [w2,w5,w15,w27,w29,w40,w53,w62] [s406,s707,s733,s669,s748,s749] (by decide +kernel)
def s1028 : Chart 8 := make 22402 [w2,w5,w15,w27,w29,w42,w51,w62] [s407,s635,s734,s750] (by decide +kernel)
def s1029 : Chart 8 := make 16788 [w2,w5,w15,w27,w32,w40,w51,w62] [s408,s636,s708,s670,s751,s752] (by decide +kernel)
def s1030 : Chart 8 := make 23842 [w2,w7,w15,w27,w29,w40,w52,w62] [s410,s671,s753,s754,s755] (by decide +kernel)
def s1031 : Chart 8 := make 32895 [w5,w7,w15,w27,w29,w41,w51,w62] [s412,s672,s753] (by decide +kernel)
def s1032 : Chart 8 := make 24672 [w5,w7,w15,w28,w29,w40,w51,w62] [s413,s709,s673,s748,s751,s754] (by decide +kernel)
def s1033 : Chart 8 := make 30614 [w5,w7,w16,w27,w29,w40,w51,w62] [s637,s710,s735,s672,s749,s750,s752,s755] (by decide +kernel)
def s1034 : Chart 8 := make 2467 [w5,w7,w15,w29,w41,w51,w62,w66] [s478] (by decide +kernel)
def s1035 : Chart 8 := make 186 [w5,w7,w16,w29,w40,w51,w62,w66] [s617,s699,s724] (by decide +kernel)
def s1036 : Chart 8 := make 64913 [w2,w5,w7,w15,w29,w51,w66,w72] [] (by decide +kernel)
def s1037 : Chart 8 := make 48116 [w2,w5,w10,w15,w29,w40,w51,w66] [s564,s756] (by decide +kernel)
def s1038 : Chart 8 := make 30040 [w5,w7,w15,w16,w29,w40,w51,w66] [s667,s668] (by decide +kernel)
def s1039 : Chart 8 := make 1751 [w5,w7,w15,w29,w40,w41,w51,w66] [s478] (by decide +kernel)
def s1040 : Chart 8 := make 41435 [w5,w7,w15,w29,w41,w51,w66] [s333,s565,s607,s667,s756] (by decide +kernel)
def s1041 : Chart 8 := make 5307 [w2,w5,w16,w22,w29,w40,w53,w62] [s736,s589,s655,s745] (by decide +kernel)
def s1042 : Chart 8 := make 33209 [w2,w5,w16,w22,w32,w40,w51,w62] [s341,s638,s723,s657,s746] (by decide +kernel)
def s1043 : Chart 8 := make 40263 [w2,w7,w16,w22,w29,w40,w52,w62] [s575,s659,s747] (by decide +kernel)
def s1044 : Chart 8 := make 37376 [w5,w7,w16,w22,w29,w40,w51,w62] [s529,s498,s589,s723,s575] (by decide +kernel)
def s1045 : Chart 8 := make 3887 [w5,w10,w15,w22,w29,w41,w51,w62] [s756,s469,s576] (by decide +kernel)
def s1046 : Chart 8 := make 54639 [w5,w10,w15,w23,w29,w40,w51,w62] [s711,s566,s470,s577] (by decide +kernel)
def s1047 : Chart 8 := make 1606 [w5,w10,w16,w22,w29,w40,w51,w62] [s639,s757,s737,s758,s567,s759,s471,s578] (by decide +kernel)
def s1048 : Chart 8 := make 19428 [w2,w15,w22,w29,w32,w40,w52,w62] [s512,s692,s760,s761,s762] (by decide +kernel)
def s1049 : Chart 8 := make 28481 [w5,w15,w22,w29,w32,w41,w51,w62] [s513,s610,s760] (by decide +kernel)
def s1050 : Chart 8 := make 13712 [w5,w15,w23,w29,w32,w40,w51,w62] [s712,s608,s722,s514,s611,s693,s761] (by decide +kernel)
def s1051 : Chart 8 := make 26200 [w5,w16,w22,w29,w32,w40,w51,w62] [s640,s609,s723,s515,s612,s694,s762] (by decide +kernel)
def s1052 : Chart 8 := make 3497 [w2,w15,w22,w29,w40,w42,w52,w62] [s523,s763] (by decide +kernel)
def s1053 : Chart 8 := make 12550 [w5,w15,w22,w29,w41,w42,w51,w62] [s763] (by decide +kernel)
def s1054 : Chart 8 := make 57689 [w2,w15,w22,w29,w40,w52,w53,w62] [s764,s765,s766] (by decide +kernel)
def s1055 : Chart 8 := make 1221 [w5,w15,w22,w29,w41,w51,w53,w62] [s530,s764] (by decide +kernel)
def s1056 : Chart 8 := make 51973 [w5,w15,w23,w29,w40,w51,w53,w62] [s588,s531,s713,s765] (by decide +kernel)
def s1057 : Chart 8 := make 64461 [w5,w16,w22,w29,w40,w51,w53,w62] [s589,s532,s738,s766] (by decide +kernel)
def s1058 : Chart 8 := make 10868 [w2,w5,w15,w22,w29,w40,w53,w81] [s767,s768] (by decide +kernel)
def s1059 : Chart 8 := make 7323 [w5,w15,w16,w22,w29,w40,w53,w62] [s440,s714,s739,s748,s589,s675,s749] (by decide +kernel)
def s1060 : Chart 8 := make 10138 [w5,w15,w22,w23,w29,w40,w53,w62] [s715,s588,s483,s683] (by decide +kernel)
def s1061 : Chart 8 := make 3949 [w5,w15,w23,w29,w40,w53,w62] [s377,s439,s460,s510,s522,s767,s566,s608,s674,s769,s690,s700,s716,s748] (by decide +kernel)
def s1062 : Chart 8 := make 16437 [w5,w16,w22,w29,w40,w53,w62] [s378,s440,s770,s461,s511,s768,s567,s609,s771,s684,s691,s701,s725,s740,s772] (by decide +kernel)
def s1063 : Chart 8 := make 40166 [w2,w5,w15,w22,w29,w42,w51,w79] [] (by decide +kernel)
def s1064 : Chart 8 := make 40839 [w5,w15,w16,w22,w29,w42,w51,w62] [s641,s741,s750] (by decide +kernel)
def s1065 : Chart 8 := make 43654 [w5,w15,w22,w23,w29,w42,w51,w62] [s484] (by decide +kernel)
def s1066 : Chart 8 := make 12730 [w2,w5,w15,w22,w32,w35,w40,w51,w62] [s642,s569,s773,s774,s775] (by decide +kernel)
def s1067 : Chart 8 := make 32830 [w2,w5,w15,w22,w32,w40,w51,w78] [s568,s643,s717,s776,s777,s778,s779] (by decide +kernel)
def s1068 : Chart 8 := make 28344 [w2,w5,w15,w22,w32,w40,w60,w62] [s598,s569,s643,s718,s776,s780,s781,s782] (by decide +kernel)
def s1069 : Chart 8 := make 36401 [w2,w5,w15,w22,w32,w50,w51,w62] [s570,s644,s717,s773,s777,s780,s783,s784] (by decide +kernel)
def s1070 : Chart 8 := make 35225 [w5,w15,w16,w22,w32,w40,w51,w62] [s444,s645,s719,s751,s723,s677,s752] (by decide +kernel)
def s1071 : Chart 8 := make 38040 [w5,w15,w22,w23,w32,w40,w51,w62] [s720,s722,s485,s685] (by decide +kernel)
def s1072 : Chart 8 := make 31851 [w5,w15,w23,w32,w40,w51,w62] [s340,s384,s443,s774,s464,s524,s533,s778,s571,s781,s676,s785,s783,s702,s721,s751] (by decide +kernel)
def s1073 : Chart 8 := make 44339 [w5,w16,w22,w32,w40,w51,w62] [s341,s385,s444,s775,s465,s534,s779,s572,s782,s618,s646,s786,s686,s784,s703,s787] (by decide +kernel)
def s1074 : Chart 8 := make 36177 [w7,w15,w22,w29,w41,w51,w52,w62] [s573,s535,s764] (by decide +kernel)
def s1075 : Chart 8 := make 21408 [w7,w15,w23,w29,w40,w51,w52,w62] [s574,s536,s765] (by decide +kernel)
def s1076 : Chart 8 := make 33896 [w7,w16,w22,w29,w40,w51,w52,w62] [s575,s537,s766] (by decide +kernel)
def s1077 : Chart 8 := make 29496 [w2,w7,w15,w22,w29,w40,w52,w75] [s788,s789,s790,s791] (by decide +kernel)
def s1078 : Chart 8 := make 12965 [w2,w15,w22,w29,w40,w52,w54,w62] [s788,s792,s793,s794] (by decide +kernel)
def s1079 : Chart 8 := make 42279 [w7,w15,w16,w22,w29,w40,w52,w62] [s451,s678,s754,s575,s680,s755] (by decide +kernel)
def s1080 : Chart 8 := make 45094 [w7,w15,w22,w23,w29,w40,w52,w62] [s687,s574,s487,s688] (by decide +kernel)
def s1081 : Chart 8 := make 13990 [w7,w15,w22,w29,w40,w41,w52,w62] [s573,s525,s763] (by decide +kernel)
def s1082 : Chart 8 := make 53674 [w7,w15,w22,w29,w41,w52,w62] [s449,s486,s516,s789,s553,s678,s687,s753,s760,s792] (by decide +kernel)
def s1083 : Chart 8 := make 38905 [w7,w15,w23,w29,w40,w52,w62] [s390,s450,s517,s526,s790,s554,s679,s795,s695,s754,s761,s793] (by decide +kernel)
def s1084 : Chart 8 := make 51393 [w7,w16,w22,w29,w40,w52,w62] [s391,s451,s796,s518,s791,s555,s797,s689,s696,s798,s762,s794] (by decide +kernel)
def s1085 : Chart 8 := make 46628 [w5,w7,w15,w23,w29,w48,w51,w62] [s769,s785,s795] (by decide +kernel)
def s1086 : Chart 8 := make 9263 [w5,w7,w16,w19,w22,w29,w40,w51,w62] [s648,s742,s799,s800,s770,s474,s581,s759] (by decide +kernel)
def s1087 : Chart 8 := make 22373 [w5,w7,w16,w22,w29,w45,w51,w62] [s472,s579,s649,s743,s799,s801,s757,s771,s786,s797] (by decide +kernel)
def s1088 : Chart 8 := make 34331 [w5,w7,w16,w28,w29,w40,w51,w62] [s413,s473,s580,s650,s744,s800,s801,s758,s772,s787,s798] (by decide +kernel)
def s1089 : Chart 9 := make 5060 [w0,w2,w5,w7,w15,w22,w29,w40,w62] [s802,s803,s804,s805,s806,s807,s808,s809,s810,s811,s812,s813] (by decide +kernel)
def s1090 : Chart 9 := make 29446 [w2,w3,w5,w7,w15,w22,w29,w51,w62] [s814,s815,s816,s817,s818,s819,s820,s821,s822,s823,s824,s825,s826,s827] (by decide +kernel)
def s1091 : Chart 9 := make 36695 [w2,w5,w7,w11,w15,w22,w29,w40,w51] [s828,s829,s830,s831,s832,s833,s834,s835,s836,s837,s838,s839,s840,s841] (by decide +kernel)
def s1092 : Chart 9 := make 19581 [w2,w5,w7,w15,w22,w29,w40,w51,w65] [s842,s843,s844,s845,s846,s847,s848,s849,s850] (by decide +kernel)
def s1093 : Chart 9 := make 24554 [w2,w5,w7,w15,w22,w29,w40,w51,w66] [s851,s852,s853,s854,s855,s856,s857,s858,s859] (by decide +kernel)
def s1094 : Chart 9 := make 10949 [w2,w5,w7,w15,w22,w29,w40,w51,w68] [s860,s861,s862,s863,s864,s865,s866,s867,s868,s869,s870,s871] (by decide +kernel)
def s1095 : Chart 9 := make 34695 [w2,w5,w7,w15,w22,w29,w40,w51,w71] [s872,s873,s874,s875,s876,s877,s878] (by decide +kernel)
def s1096 : Chart 9 := make 42083 [w2,w5,w7,w15,w22,w29,w40,w51,w74] [s879,s880,s881,s882,s883,s884,s885,s886] (by decide +kernel)
def s1097 : Chart 9 := make 62522 [w2,w5,w7,w15,w22,w29,w40,w51,w77] [s887,s888,s889,s890,s891,s892,s893,s894,s895,s896] (by decide +kernel)
def s1098 : Chart 9 := make 3706 [w2,w5,w7,w15,w22,w29,w40,w52,w62] [s819,s842,s897,s898,s899,s900,s901,s902,s903,s846,s904,s905,s906,s907] (by decide +kernel)
def s1099 : Chart 9 := make 36434 [w2,w5,w7,w15,w22,w29,w40,w53,w62] [s887,s908,s909,s910,s911,s890,s912,s913,s914,s915] (by decide +kernel)
def s1100 : Chart 9 := make 12253 [w2,w5,w7,w15,w22,w29,w40,w59,w62] [s916,s860,s917,s863,s918,s919,s920,s921,s922,s923,s924,s925] (by decide +kernel)
def s1101 : Chart 9 := make 20612 [w2,w5,w7,w15,w22,w29,w40,w62,w74] [s879,s926,s927,s928,s929,s930,s931] (by decide +kernel)
def s1102 : Chart 9 := make 59580 [w2,w5,w7,w15,w22,w29,w40,w74] [s814,s842,s860,s887,s932,s933,s934,s935,s936,s937,s938,s939,s940,s941,s942,s943,s944,s945,s946,s947] (by decide +kernel)
def s1103 : Chart 9 := make 28527 [w2,w5,w7,w15,w22,w29,w41,w51,w62] [s807,s932,s948,s949,s950,s951,s952,s953,s954,s955] (by decide +kernel)
def s1104 : Chart 9 := make 4429 [w2,w5,w7,w15,w22,w29,w42,w51,w62] [s933,s888,s956,s957,s958,s891,s912,s959,s960,s961] (by decide +kernel)
def s1105 : Chart 9 := make 16341 [w2,w5,w7,w15,w22,w29,w44,w51,w62] [s934,s962,s963,s964,s965,s966,s967,s968,s969,s970] (by decide +kernel)
def s1106 : Chart 9 := make 15291 [w2,w5,w7,w15,w22,w29,w47,w51,w62] [s935,s851,s971,s853,s972,s973,s974,s975,s976,s977] (by decide +kernel)
def s1107 : Chart 9 := make 12554 [w2,w5,w7,w15,w22,w29,w49,w51,w62] [s936,s861,s864,s918,s978,s979,s980,s981,s982,s983,s984] (by decide +kernel)
def s1108 : Chart 9 := make 35411 [w2,w5,w7,w15,w22,w29,w51,w62,w71] [s872,s926,s985,s986,s987,s988,s989,s990] (by decide +kernel)
def s1109 : Chart 9 := make 8858 [w2,w5,w7,w15,w22,w29,w51,w71] [s802,s851,s861,s888,s897,s908,s917,s991,s992,s993,s994,s995,s996,s997,s998,s999,s1000,s1001] (by decide +kernel)
def s1110 : Chart 9 := make 64336 [w2,w5,w7,w15,w22,w32,w40,w51,w62] [s937,s991,s889,s1002,s1003,s892,s913,s959,s1004,s1005] (by decide +kernel)
def s1111 : Chart 9 := make 55641 [w2,w5,w7,w15,w22,w40,w51,w62,w68] [s862,s927,s985,s1006,s1007,s1008,s1009] (by decide +kernel)
def s1112 : Chart 9 := make 29088 [w2,w5,w7,w15,w22,w40,w51,w68] [s803,s815,s889,s898,s909,s1010,s948,s956,s962,s971,s1011,s1012,s1013,s1014,s1015,s1016,s1017,s1018,s1019,s1020,s1021] (by decide +kernel)
def s1113 : Chart 9 := make 13758 [w2,w5,w7,w15,w23,w29,w40,w51,w62] [s808,s938,s992,s1012,s1022,s1023,s1024,s1025,s954,s1026] (by decide +kernel)
def s1114 : Chart 9 := make 9825 [w2,w5,w7,w15,w27,w29,w40,w51,w62] [s828,s939,s993,s1013,s964,s1027,s1028,s1029,s1030,s1031,s1032,s1033] (by decide +kernel)
def s1115 : Chart 9 := make 44918 [w2,w5,w7,w15,w29,w40,w51,w62,w66] [s852,s928,s986,s1006,s1034,s1035] (by decide +kernel)
def s1116 : Chart 9 := make 18365 [w2,w5,w7,w15,w29,w40,w51,w66] [s804,s816,s899,s910,s919,s949,s957,s963,s978,s1036,s1002,s1037,s1038,s1039,s1040] (by decide +kernel)
def s1117 : Chart 9 := make 26246 [w2,w5,w7,w16,w22,w29,w40,w51,w62] [s809,s940,s1014,s1041,s1042,s1043,s1044,s955,s1026] (by decide +kernel)
def s1118 : Chart 9 := make 46338 [w2,w5,w10,w15,w22,w29,w40,w51,w62] [s941,s994,s1015,s1037,s900,s847,s904,s1045,s1046,s1047] (by decide +kernel)
def s1119 : Chart 9 := make 5411 [w2,w5,w15,w22,w29,w32,w40,w51,w62] [s942,s995,s920,s980,s1003,s867,s922,s981,s1048,s1049,s1050,s1051] (by decide +kernel)
def s1120 : Chart 9 := make 55001 [w2,w5,w15,w22,w29,w40,w42,w51,w62] [s943,s958,s874,s1016,s1052,s1053] (by decide +kernel)
def s1121 : Chart 9 := make 43672 [w2,w5,w15,w22,w29,w40,w51,w53,w62] [s911,s880,s996,s1017,s1054,s1055,s1056,s1057] (by decide +kernel)
def s1122 : Chart 9 := make 61169 [w2,w5,w15,w22,w29,w40,w53,w62] [s817,s833,s843,s854,s865,s873,s1058,s900,s920,s950,s965,s972,s979,s987,s997,s1007,s1018,s1022,s1027,s1041,s1059,s1060,s1061,s1062] (by decide +kernel)
def s1123 : Chart 9 := make 29164 [w2,w5,w15,w22,w29,w42,w51,w62] [s805,s834,s844,s855,s866,s881,s1063,s901,s921,s929,s944,s980,s1008,s1019,s1028,s1064,s1065] (by decide +kernel)
def s1124 : Chart 9 := make 23550 [w2,w5,w15,w22,w32,w40,w51,w62] [s806,s818,s835,s1066,s845,s856,s875,s882,s1067,s902,s1068,s930,s945,s951,s966,s973,s1069,s988,s998,s1023,s1029,s1042,s1070,s1071,s1072,s1073] (by decide +kernel)
def s1125 : Chart 9 := make 13107 [w2,w7,w15,w22,w29,w40,w51,w52,w62] [s903,s883,s1054,s1074,s1075,s1076] (by decide +kernel)
def s1126 : Chart 9 := make 30604 [w2,w7,w15,w22,w29,w40,w52,w62] [s819,s837,s857,s868,s876,s1077,s893,s952,s967,s974,s982,s1024,s1030,s1043,s1048,s1052,s1078,s1079,s1080,s1081,s1082,s1083,s1084] (by decide +kernel)
def s1127 : Chart 9 := make 28262 [w5,w7,w15,w16,w22,w29,w40,w51,w62] [s841,s946,s999,s1020,s1038,s968,s1032,s1044,s970,s1033,s1059,s1064,s1070,s1079] (by decide +kernel)
def s1128 : Chart 9 := make 31077 [w5,w7,w15,w22,w23,w29,w40,w51,w62] [s1000,s975,s1025,s859,s976,s1060,s1065,s1071,s1080] (by decide +kernel)
def s1129 : Chart 9 := make 65494 [w5,w7,w15,w22,w29,w40,w41,w51,w62] [s953,s877,s1039,s1053,s1081] (by decide +kernel)
def s1130 : Chart 9 := make 39657 [w5,w7,w15,w22,w29,w41,w51,w62] [s807,s839,s848,s858,s869,s884,s894,s905,s923,s968,s975,s1031,s1034,s1040,s1045,s1049,s1055,s1074,s1082] (by decide +kernel)
def s1131 : Chart 9 := make 24888 [w5,w7,w15,w23,w29,w40,w51,w62] [s808,s825,s840,s849,s870,s878,s885,s895,s906,s914,s924,s960,s969,s1085,s983,s989,s1001,s1004,s1032,s1046,s1050,s1056,s1061,s1072,s1075,s1083] (by decide +kernel)
def s1132 : Chart 9 := make 37376 [w5,w7,w16,w22,w29,w40,w51,w62] [s809,s826,s841,s1086,s850,s871,s886,s896,s907,s915,s925,s931,s947,s961,s1087,s977,s984,s990,s1005,s1009,s1021,s1088,s1035,s1047,s1051,s1057,s1062,s1073,s1076,s1084] (by decide +kernel)
def s1133 : Chart 10 := make 16587 [w2,w5,w7,w15,w22,w29,w40,w51,w62] [s1089,s1090,s1091,s1092,s1093,s1094,s1095,s1096,s1097,s1098,s1099,s1100,s1101,s1102,s1103,s1104,s1105,s1106,s1107,s1108,s1109,s1110,s1111,s1112,s1113,s1114,s1115,s1116,s1117,s1118,s1119,s1120,s1121,s1122,s1123,s1124,s1125,s1126,s1127,s1128,s1129,s1130,s1131,s1132] (by decide +kernel)
def qInputs : List W := rawInputs.take 8 ++ [rawInputs[8]! ||| rawInputs[9]!]
theorem qvals : qInputs = [w2, w5, w7, w62, w15, w22, w29, w40, w51] := by decide +kernel
theorem q_indispensable {k : Nat} {s : Finset W} (hs : s ⊆ qInputs.toFinset) (h : live basicOps goal k s) : s = qInputs.toFinset := by
  apply Finset.Subset.antisymm hs
  intro w hw
  have hw := List.mem_toFinset.mp hw
  rw [qvals] at hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨u, hu, hd⟩ := live_separates (differs 5) (goal_differs 5) (ops_differs 5) h
    have mem := List.mem_toFinset.mp (hs hu)
    rw [qvals] at mem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    have eq : u = w2 := by
      rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> revert hd <;> unfold differs <;> decide +kernel
    exact eq ▸ hu
  · obtain ⟨u, hu, hd⟩ := live_separates (differs 42) (goal_differs 42) (ops_differs 42) h
    have mem := List.mem_toFinset.mp (hs hu)
    rw [qvals] at mem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    have eq : u = w5 := by
      rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> revert hd <;> unfold differs <;> decide +kernel
    exact eq ▸ hu
  · obtain ⟨u, hu, hd⟩ := live_separates (differs 98) (goal_differs 98) (ops_differs 98) h
    have mem := List.mem_toFinset.mp (hs hu)
    rw [qvals] at mem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    have eq : u = w7 := by
      rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> revert hd <;> unfold differs <;> decide +kernel
    exact eq ▸ hu
  · obtain ⟨u, hu, hd⟩ := live_separates (differs 126) (goal_differs 126) (ops_differs 126) h
    have mem := List.mem_toFinset.mp (hs hu)
    rw [qvals] at mem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    have eq : u = w62 := by
      rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> revert hd <;> unfold differs <;> decide +kernel
    exact eq ▸ hu
  · obtain ⟨u, hu, hd⟩ := live_separates (differs 45) (goal_differs 45) (ops_differs 45) h
    have mem := List.mem_toFinset.mp (hs hu)
    rw [qvals] at mem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    have eq : u = w15 := by
      rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> revert hd <;> unfold differs <;> decide +kernel
    exact eq ▸ hu
  · obtain ⟨u, hu, hd⟩ := live_separates (differs 59) (goal_differs 59) (ops_differs 59) h
    have mem := List.mem_toFinset.mp (hs hu)
    rw [qvals] at mem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    have eq : u = w22 := by
      rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> revert hd <;> unfold differs <;> decide +kernel
    exact eq ▸ hu
  · obtain ⟨u, hu, hd⟩ := live_separates (differs 0) (goal_differs 0) (ops_differs 0) h
    have mem := List.mem_toFinset.mp (hs hu)
    rw [qvals] at mem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    have eq : u = w29 := by
      rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> revert hd <;> unfold differs <;> decide +kernel
    exact eq ▸ hu
  · obtain ⟨u, hu, hd⟩ := live_separates (differs 87) (goal_differs 87) (ops_differs 87) h
    have mem := List.mem_toFinset.mp (hs hu)
    rw [qvals] at mem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    have eq : u = w40 := by
      rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> revert hd <;> unfold differs <;> decide +kernel
    exact eq ▸ hu
  · obtain ⟨u, hu, hd⟩ := live_separates (differs 14) (goal_differs 14) (ops_differs 14) h
    have mem := List.mem_toFinset.mp (hs hu)
    rw [qvals] at mem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    have eq : u = w51 := by
      rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> revert hd <;> unfold differs <;> decide +kernel
    exact eq ▸ hu
theorem no_q_live : ¬ live basicOps goal 10 qInputs.toFinset := by
  have eq : qInputs.toFinset = s1133.wires.toFinset := by decide +kernel
  rw [eq]
  exact s1133.closed
theorem no_q_build : ¬ build basicOps goal 10 qInputs.toFinset := by
  intro h
  obtain ⟨s, hs, hl⟩ := compress h
  exact no_q_live (q_indispensable hs hl ▸ hl)

end Quotient
end PEqualNP.Outside.L_meta_23659

theorem PEqualNP.Outside.L_meta_23659 : ¬ (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (275444 : ℕ).testBit (6 * u.val + v.val)) 11) :=
  PEqualNP.Outside.L_meta_23659.quotientTransfer PEqualNP.Outside.L_meta_23659.source_indispensable PEqualNP.Outside.L_meta_23659.Quotient.no_q_build
