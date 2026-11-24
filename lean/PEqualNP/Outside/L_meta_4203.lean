import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_4203

def pmWire (n m : ℕ) (π : Fin n → Fin m) (w : ℕ) : ℕ :=
  if h : w < n then (π ⟨w, h⟩ : ℕ) else w - n + m

def pmGate (n m : ℕ) (π : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (pmWire n m π)⟩

def pmCirc (n m : ℕ) (π : Fin n → Fin m) (C : Circuit) : Circuit :=
  ⟨C.gates.map (pmGate n m π), pmWire n m π C.output⟩

def pmStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def PmRel (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) : Prop :=
  n ≤ W.length ∧ W'.length + n = W.length + m ∧
    ∀ w : ℕ, W'.getD (pmWire n m π w) false = W.getD w false

theorem pm_getD_snoc (L : List Bool) (S d : Bool) : (L ++ [S]).getD L.length d = S := by
  simp

theorem pm_rel_step (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) (g : Gate)
    (h : PmRel n m π W W') : PmRel n m π (pmStep W g) (pmStep W' (pmGate n m π g)) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hv : (pmGate n m π g).op.eval
      ((pmGate n m π g).inputs.map fun i => W'.getD i false)
      = g.op.eval (g.inputs.map fun i => W.getD i false) := by
    simp only [pmGate, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a _
    exact h3 a
  refine ⟨by simp [pmStep]; omega, by simp [pmStep]; omega, ?_⟩
  intro w
  simp only [pmStep, hv]
  rcases Nat.lt_trichotomy w W.length with hw | hw | hw
  · have hlt : pmWire n m π w < W'.length := by
      unfold pmWire
      split
      · have := (π ⟨w, by assumption⟩).2; omega
      · omega
    rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hw]
    exact h3 w
  · have he : pmWire n m π w = W'.length := by
      unfold pmWire
      split
      · omega
      · omega
    rw [he, hw, pm_getD_snoc, pm_getD_snoc]
  · have hge : W'.length + 1 ≤ pmWire n m π w := by
      unfold pmWire
      split
      · omega
      · omega
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

theorem pm_rel_fold (n m : ℕ) (π : Fin n → Fin m) (gs : List Gate) :
    ∀ W W' : List Bool, PmRel n m π W W' →
      PmRel n m π (gs.foldl pmStep W) ((gs.map (pmGate n m π)).foldl pmStep W') := by
  induction gs with
  | nil => intro W W' h; exact h
  | cons g gs ih =>
    intro W W' h
    exact ih _ _ (pm_rel_step n m π W W' g h)

theorem pm_rel_init (n m : ℕ) (π : Fin n → Fin m) (x : Fin m → Bool) :
    PmRel n m π (List.ofFn (x ∘ π)) (List.ofFn x) := by
  refine ⟨by simp, by simp; omega, ?_⟩
  intro w
  unfold pmWire
  split
  · rename_i hw
    rw [List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simpa using hw)]
    simp
  · rename_i hw
    rw [List.getD_eq_default _ _ (by simp), List.getD_eq_default _ _ (by simp; omega)]

theorem pm_fun {n m : ℕ} (π : Fin n → Fin m) (C : Circuit) (x : Fin m → Bool) :
    circuitFun m (pmCirc n m π C) x = circuitFun n C (x ∘ π) := by
  have := (pm_rel_fold n m π C.gates _ _ (pm_rel_init n m π x)).2.2 C.output
  exact this

theorem pm_size {n m : ℕ} (π : Fin n → Fin m) (C : Circuit) :
    (pmCirc n m π C).size = C.size := by
  simp [pmCirc, Circuit.size]

theorem pm_fan {n m : ℕ} (π : Fin n → Fin m) (C : Circuit) (h : FanInTwo C) :
    FanInTwo (pmCirc n m π C) := by
  intro g hg
  obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
  exact ⟨(h g0 hg0).1, by simpa [pmGate] using (h g0 hg0).2⟩

theorem pm_get {n m : ℕ} (π : Fin n → Fin m) (C : Circuit) (k : Fin C.size)
    (k' : Fin (pmCirc n m π C).size) (hk : (k' : ℕ) = k) :
    (pmCirc n m π C).gates.get k' = pmGate n m π (C.gates.get k) := by
  have e : ∀ (l : List Gate) (j : ℕ) (h1 : j < (l.map (pmGate n m π)).length)
      (h2 : j < l.length),
      (l.map (pmGate n m π)).get ⟨j, h1⟩ = pmGate n m π (l.get ⟨j, h2⟩) := by
    intro l j h1 h2
    simp [List.get_eq_getElem]
  obtain ⟨i, hi⟩ := k
  obtain ⟨j, hj⟩ := k'
  simp only at hk
  subst hk
  exact e C.gates j hj hi

theorem pm_inj (n : ℕ) (σ : Equiv.Perm (Fin n)) : Function.Injective (pmWire n n ⇑σ) := by
  intro a b h
  unfold pmWire at h
  split at h <;> split at h
  · exact congrArg Fin.val (σ.injective (Fin.ext h))
  · rename_i ha hb
    have := (σ ⟨a, ha⟩).2
    omega
  · rename_i ha hb
    have := (σ ⟨b, hb⟩).2
    omega
  · omega

theorem pm_gate_props (n : ℕ) (σ : Equiv.Perm (Fin n)) (g : Gate) (k : ℕ) :
    (pmGate n n ⇑σ g).op = g.op ∧ (pmGate n n ⇑σ g).inputs.length = g.inputs.length ∧
    (g.inputs.Nodup → (pmGate n n ⇑σ g).inputs.Nodup) ∧
    ((∀ i ∈ g.inputs, i < n + k) → ∀ i ∈ (pmGate n n ⇑σ g).inputs, i < n + k) ∧
    ∀ j : Fin n, ((σ j : Fin n) : ℕ) ∈ (pmGate n n ⇑σ g).inputs ↔ (j : ℕ) ∈ g.inputs := by
  have hinj := pm_inj n σ
  refine ⟨rfl, by simp [pmGate], fun h => List.Nodup.map hinj h, ?_, ?_⟩
  · intro hb i hi
    simp only [pmGate, List.mem_map] at hi
    obtain ⟨a, ham, rfl⟩ := hi
    have hab := hb a ham
    unfold pmWire
    split
    · rename_i ha
      have := (σ ⟨a, ha⟩).2
      omega
    · omega
  · intro j
    have hj : pmWire n n ⇑σ (j : ℕ) = ((σ j : Fin n) : ℕ) := by
      simp [pmWire]
    rw [← hj]
    exact List.mem_map_of_injective hinj

end PEqualNP.Outside.L_meta_4203

theorem PEqualNP.Outside.L_meta_4203 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Equiv.Perm (Fin x1)),   ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : Fin x2.size ≃ Fin x4.size),     x4.size = x2.size ∧       (PEqualNP.MetaComplexity.IsMinimalCircuit x1 x2 → PEqualNP.MetaComplexity.IsMinimalCircuit x1 x4) ∧         (∀ (x6 : Fin x1 → Bool), PEqualNP.MetaComplexity.circuitFun x1 x4 x6 = PEqualNP.MetaComplexity.circuitFun x1 x2 (x6 ∘ ⇑x3)) ∧           ∀ (x6 : Fin x2.size),             have x7 : PEqualNP.CircuitLowerBounds.Gate := x2.gates.get x6;             have x8 : PEqualNP.CircuitLowerBounds.Gate := x4.gates.get (x5 x6);             x8.op = x7.op ∧ x8.inputs.length = x7.inputs.length ∧ (x7.inputs.Nodup → x8.inputs.Nodup) ∧ ((∀ x9 ∈ x7.inputs, x9 < x1 + ↑x6) → ∀ x10 ∈ x8.inputs, x10 < x1 + ↑(x5 x6)) ∧ ∀ (x9 : Fin x1), ↑(x3 x9) ∈ x8.inputs ↔ ↑x9 ∈ x7.inputs := by
  intro n C σ
  have hsz : C.size = (PEqualNP.Outside.L_meta_4203.pmCirc n n ⇑σ C).size :=
    (PEqualNP.Outside.L_meta_4203.pm_size (⇑σ) C).symm
  refine ⟨PEqualNP.Outside.L_meta_4203.pmCirc n n ⇑σ C, finCongr hsz, hsz.symm, ?_, ?_, ?_⟩
  · rintro ⟨hfan, hmin⟩
    refine ⟨PEqualNP.Outside.L_meta_4203.pm_fan (⇑σ) C hfan, ?_⟩
    intro D hD hDf
    have hD' := PEqualNP.Outside.L_meta_4203.pm_fan (⇑σ.symm) D hD
    have hf : circuitFun n (PEqualNP.Outside.L_meta_4203.pmCirc n n ⇑σ.symm D)
        = circuitFun n C := by
      funext x
      rw [PEqualNP.Outside.L_meta_4203.pm_fun, hDf, PEqualNP.Outside.L_meta_4203.pm_fun]
      congr 1
      funext j
      simp
    have h1 := hmin _ hD' hf
    have h2 := PEqualNP.Outside.L_meta_4203.pm_size (⇑σ.symm) D
    omega
  · intro x
    exact PEqualNP.Outside.L_meta_4203.pm_fun (⇑σ) C x
  · intro k
    dsimp only
    have hget := PEqualNP.Outside.L_meta_4203.pm_get (⇑σ) C k (finCongr hsz k) (by simp)
    have hv : ((finCongr hsz k : Fin _) : ℕ) = (k : ℕ) := by
      simp
    rw [hget, hv]
    exact PEqualNP.Outside.L_meta_4203.pm_gate_props n σ (C.gates.get k) k
