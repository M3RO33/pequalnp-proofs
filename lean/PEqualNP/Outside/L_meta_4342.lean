import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_4342

def aoRd (L : List (Option Bool)) (i : ℕ) : Option Bool := L.getD i (some false)

def aoAbs (g : Gate) : Bool :=
  match g.op with
  | GateOp.or => true
  | _ => false

def aoCls (L : List (Option Bool)) (g : Gate) : Option Bool :=
  if ∃ i ∈ g.inputs, aoRd L i = some (aoAbs g) then some (aoAbs g)
  else if ∀ i ∈ g.inputs, aoRd L i = some (!aoAbs g) then some (!aoAbs g)
  else none

def aoReal (L : List (Option Bool)) (g : Gate) : List ℕ :=
  g.inputs.filter fun i => decide (aoRd L i = none)

def aoNew (L : List (Option Bool)) (g : Gate) : Gate :=
  match aoCls L g with
  | none => ⟨g.op, (aoReal L g ++ aoReal L g).take 2⟩
  | some _ => ⟨GateOp.and, [0, 0]⟩

def aoBuild : List Gate → List (Option Bool) → List Gate
  | [], _ => []
  | g :: gs, L => aoNew L g :: aoBuild gs (L ++ [aoCls L g])

def aoFold : List Gate → List (Option Bool) → List (Option Bool)
  | [], L => L
  | g :: gs, L => aoFold gs (L ++ [aoCls L g])

def aoOut (Lf : List (Option Bool)) (n : ℕ) (C : Circuit) : ℕ :=
  match aoRd Lf C.output with
  | none => C.output
  | some _ => n + C.gates.length

def aoC (n : ℕ) (C : Circuit) : Circuit :=
  ⟨aoBuild C.gates (List.replicate n none),
    aoOut (aoFold C.gates (List.replicate n none)) n C⟩

def aoStp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def AoAgree (L : List (Option Bool)) (W W' : List Bool) : Prop :=
  ∀ i, (aoRd L i = none → W'.getD i false = W.getD i false) ∧
    (∀ b, aoRd L i = some b → W.getD i false = b)

theorem ao_getD_snoc {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

theorem ao_rd_lt (L : List (Option Bool)) (i : ℕ) (h : aoRd L i = none) : i < L.length := by
  by_contra hc
  unfold aoRd at h
  rw [List.getD_eq_default _ _ (by omega)] at h
  simp at h

theorem ao_opt {o : Option Bool} {a : Bool} (h1 : o ≠ some a) (h2 : o ≠ some (!a)) :
    o = none := by
  cases o with
  | none => rfl
  | some b => cases a <;> cases b <;> simp_all

theorem ao_real_ne (L : List (Option Bool)) (g : Gate) (h : aoCls L g = none) :
    aoReal L g ≠ [] := by
  unfold aoCls at h
  by_cases h1 : ∃ i ∈ g.inputs, aoRd L i = some (aoAbs g)
  · rw [if_pos h1] at h
    simp at h
  · rw [if_neg h1] at h
    by_cases h2 : ∀ i ∈ g.inputs, aoRd L i = some (!aoAbs g)
    · rw [if_pos h2] at h
      simp at h
    · push_neg at h1 h2
      obtain ⟨i, hi, hne⟩ := h2
      have hn := ao_opt (h1 i hi) hne
      intro he
      have hm : i ∈ aoReal L g := by
        unfold aoReal
        rw [List.mem_filter]
        exact ⟨hi, by simpa using hn⟩
      rw [he] at hm
      simp at hm

theorem ao_real_le (L : List (Option Bool)) (g : Gate) (h : g.inputs.length ≤ 2) :
    (aoReal L g).length ≤ 2 := by
  unfold aoReal
  exact le_trans (List.length_filter_le _ _) h

theorem ao_new_reads (L : List (Option Bool)) (g : Gate) (hL : 1 ≤ L.length) :
    ∀ i ∈ (aoNew L g).inputs, i < L.length := by
  intro i hi
  unfold aoNew at hi
  split at hi
  · have h1 := List.mem_of_mem_take hi
    rw [List.mem_append, or_self] at h1
    unfold aoReal at h1
    rw [List.mem_filter] at h1
    exact ao_rd_lt L i (by simpa using h1.2)
  · simp at hi
    omega

theorem ao_new_len (L : List (Option Bool)) (g : Gate) (h2 : g.inputs.length ≤ 2) :
    (aoNew L g).inputs.length = 2 := by
  unfold aoNew
  split
  · rename_i hc
    have hne := ao_real_ne L g hc
    have hle := ao_real_le L g h2
    have hpos : 0 < (aoReal L g).length := by
      cases hr : aoReal L g with
      | nil => exact absurd hr hne
      | cons a t => simp
    simp only [List.length_take, List.length_append]
    omega
  · rfl

theorem ao_new_op (L : List (Option Bool)) (g : Gate)
    (h : g.op = GateOp.and ∨ g.op = GateOp.or) :
    (aoNew L g).op = GateOp.and ∨ (aoNew L g).op = GateOp.or := by
  unfold aoNew
  split
  · exact h
  · exact Or.inl rfl

theorem ao_build_len : ∀ (gs : List Gate) (L : List (Option Bool)),
    (aoBuild gs L).length = gs.length
  | [], _ => rfl
  | g :: gs, L => by simp [aoBuild, ao_build_len gs]

theorem ao_build_mem : ∀ (gs : List Gate) (L : List (Option Bool)) (g' : Gate),
    g' ∈ aoBuild gs L → ∃ L' g, g ∈ gs ∧ g' = aoNew L' g
  | [], _, _, h => by simp [aoBuild] at h
  | g :: gs, L, g', h => by
    simp only [aoBuild, List.mem_cons] at h
    rcases h with h | h
    · exact ⟨L, g, List.mem_cons_self, h⟩
    · obtain ⟨L', g0, hg0, e⟩ := ao_build_mem gs _ g' h
      exact ⟨L', g0, List.mem_cons_of_mem _ hg0, e⟩

theorem ao_build_reads : ∀ (gs : List Gate) (L : List (Option Bool)) (j : ℕ), 1 ≤ L.length →
    j < (aoBuild gs L).length →
    ∀ i ∈ ((aoBuild gs L).getD j ⟨GateOp.or, []⟩).inputs, i < L.length + j
  | [], _, _, _, hj, _, _ => by simp [aoBuild] at hj
  | g :: gs, L, j, hL, hj, i, hi => by
    cases j with
    | zero =>
      simp only [aoBuild, List.getD_cons_zero] at hi
      have := ao_new_reads L g hL i hi
      omega
    | succ j =>
      simp only [aoBuild, List.getD_cons_succ] at hi
      simp only [aoBuild, List.length_cons] at hj
      have := ao_build_reads gs (L ++ [aoCls L g]) j (by simp) (by omega) i hi
      simp only [List.length_append, List.length_cons, List.length_nil] at this
      omega

theorem ao_all_filt (l : List ℕ) (p q : ℕ → Bool) (h : ∀ i ∈ l, q i = false → p i = true) :
    l.all p = (l.filter q).all p := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    have ht := ih (fun i hi => h i (List.mem_cons_of_mem _ hi))
    by_cases hq : q a = true
    · simp [hq, ht]
    · have hp := h a List.mem_cons_self (by simpa using hq)
      simp [hq, hp, ht]

theorem ao_any_filt (l : List ℕ) (p q : ℕ → Bool) (h : ∀ i ∈ l, q i = false → p i = false) :
    l.any p = (l.filter q).any p := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    have ht := ih (fun i hi => h i (List.mem_cons_of_mem _ hi))
    by_cases hq : q a = true
    · simp [hq, ht]
    · have hp := h a List.mem_cons_self (by simpa using hq)
      simp [hq, hp, ht]

theorem ao_all_congr (l : List ℕ) (f g : ℕ → Bool) (h : ∀ i ∈ l, f i = g i) :
    l.all f = l.all g := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.all_cons, h a List.mem_cons_self,
      ih (fun i hi => h i (List.mem_cons_of_mem _ hi))]

theorem ao_any_congr (l : List ℕ) (f g : ℕ → Bool) (h : ∀ i ∈ l, f i = g i) :
    l.any f = l.any g := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.any_cons, h a List.mem_cons_self,
      ih (fun i hi => h i (List.mem_cons_of_mem _ hi))]

theorem ao_pad (l : List ℕ) (p : ℕ → Bool) (h1 : l ≠ []) (h2 : l.length ≤ 2) :
    ((l ++ l).take 2).all p = l.all p ∧ ((l ++ l).take 2).any p = l.any p := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
  · exact absurd rfl h1
  · simp
  · simp
  · simp only [List.length_cons] at h2
    omega

theorem ao_ev_and (l : List ℕ) (f : ℕ → Bool) : GateOp.and.eval (l.map f) = l.all f := by
  simp [GateOp.eval, List.all_map]

theorem ao_ev_or (l : List ℕ) (f : ℕ → Bool) : GateOp.or.eval (l.map f) = l.any f := by
  simp [GateOp.eval, List.any_map]

theorem ao_all_false (l : List ℕ) (f : ℕ → Bool) (i : ℕ) (hi : i ∈ l) (hf : f i = false) :
    l.all f = false := by
  cases h : l.all f with
  | false => rfl
  | true =>
    have := List.all_eq_true.1 h i hi
    rw [hf] at this
    exact absurd this (by decide)

theorem ao_any_true (l : List ℕ) (f : ℕ → Bool) (i : ℕ) (hi : i ∈ l) (hf : f i = true) :
    l.any f = true :=
  List.any_eq_true.2 ⟨i, hi, hf⟩

theorem ao_all_true (l : List ℕ) (f : ℕ → Bool) (h : ∀ i ∈ l, f i = true) :
    l.all f = true :=
  List.all_eq_true.2 h

theorem ao_any_false (l : List ℕ) (f : ℕ → Bool) (h : ∀ i ∈ l, f i = false) :
    l.any f = false := by
  cases hh : l.any f with
  | false => rfl
  | true =>
    obtain ⟨i, hi, hti⟩ := List.any_eq_true.1 hh
    rw [h i hi] at hti
    exact absurd hti (by decide)

theorem ao_sem (L : List (Option Bool)) (W W' : List Bool) (g : Gate) (hA : AoAgree L W W')
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (hlen : g.inputs.length ≤ 2) :
    (∀ b, aoCls L g = some b → g.op.eval (g.inputs.map fun i => W.getD i false) = b) ∧
    (aoCls L g = none →
      (aoNew L g).op.eval ((aoNew L g).inputs.map fun i => W'.getD i false)
        = g.op.eval (g.inputs.map fun i => W.getD i false)) := by
  have hreal : ∀ i ∈ aoReal L g, W'.getD i false = W.getD i false := by
    intro i hi
    unfold aoReal at hi
    rw [List.mem_filter] at hi
    exact (hA i).1 (by simpa using hi.2)
  constructor
  · intro b hb
    unfold aoCls at hb
    by_cases h1 : ∃ i ∈ g.inputs, aoRd L i = some (aoAbs g)
    · rw [if_pos h1] at hb
      obtain ⟨i, hi, hri⟩ := h1
      have hw := (hA i).2 _ hri
      simp only [Option.some.injEq] at hb
      subst hb
      rcases hop with hop | hop
      · have hab : aoAbs g = false := by simp [aoAbs, hop]
        rw [hop, ao_ev_and]
        rw [hab] at hw ⊢
        exact ao_all_false _ _ i hi hw
      · have hab : aoAbs g = true := by simp [aoAbs, hop]
        rw [hop, ao_ev_or]
        rw [hab] at hw ⊢
        exact ao_any_true _ _ i hi hw
    · rw [if_neg h1] at hb
      by_cases h2 : ∀ i ∈ g.inputs, aoRd L i = some (!aoAbs g)
      · rw [if_pos h2] at hb
        simp only [Option.some.injEq] at hb
        subst hb
        have hw : ∀ i ∈ g.inputs, W.getD i false = !aoAbs g :=
          fun i hi => (hA i).2 _ (h2 i hi)
        rcases hop with hop | hop
        · have hab : aoAbs g = false := by simp [aoAbs, hop]
          rw [hop, ao_ev_and]
          rw [hab] at hw ⊢
          exact ao_all_true _ _ hw
        · have hab : aoAbs g = true := by simp [aoAbs, hop]
          rw [hop, ao_ev_or]
          rw [hab] at hw ⊢
          exact ao_any_false _ _ hw
      · rw [if_neg h2] at hb
        simp at hb
  · intro hc
    have hne := ao_real_ne L g hc
    have hle := ao_real_le L g hlen
    have hnew : aoNew L g = ⟨g.op, (aoReal L g ++ aoReal L g).take 2⟩ := by
      simp only [aoNew, hc]
    rw [hnew]
    dsimp only
    unfold aoCls at hc
    have h1 : ¬ ∃ i ∈ g.inputs, aoRd L i = some (aoAbs g) := by
      intro h
      rw [if_pos h] at hc
      simp at hc
    push_neg at h1
    have hnr : ∀ i ∈ g.inputs, decide (aoRd L i = none) = false →
        W.getD i false = !aoAbs g := by
      intro i hi hq
      have hq' : aoRd L i ≠ none := by simpa using hq
      have hs : aoRd L i = some (!aoAbs g) := by
        by_contra hne2
        exact hq' (ao_opt (h1 i hi) hne2)
      exact (hA i).2 _ hs
    rcases hop with hop | hop
    · have hab : aoAbs g = false := by simp [aoAbs, hop]
      rw [hop, ao_ev_and, ao_ev_and, (ao_pad _ _ hne hle).1, ao_all_congr _ _ _ hreal]
      refine (ao_all_filt g.inputs (fun i => W.getD i false)
        (fun i => decide (aoRd L i = none)) ?_).symm
      intro i hi hq
      have := hnr i hi hq
      rw [hab] at this
      exact this
    · have hab : aoAbs g = true := by simp [aoAbs, hop]
      rw [hop, ao_ev_or, ao_ev_or, (ao_pad _ _ hne hle).2, ao_any_congr _ _ _ hreal]
      refine (ao_any_filt g.inputs (fun i => W.getD i false)
        (fun i => decide (aoRd L i = none)) ?_).symm
      intro i hi hq
      have := hnr i hi hq
      rw [hab] at this
      exact this

theorem ao_step (L : List (Option Bool)) (W W' : List Bool) (g : Gate)
    (hl : L.length = W.length) (hl' : W'.length = W.length) (hA : AoAgree L W W')
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (hlen : g.inputs.length ≤ 2) :
    AoAgree (L ++ [aoCls L g]) (aoStp W g) (aoStp W' (aoNew L g)) := by
  obtain ⟨s1, s2⟩ := ao_sem L W W' g hA hop hlen
  intro i
  rcases Nat.lt_trichotomy i L.length with hi | hi | hi
  · have e1 : aoRd (L ++ [aoCls L g]) i = aoRd L i := by
      unfold aoRd
      exact List.getD_append _ _ _ _ hi
    have e2 : (aoStp W g).getD i false = W.getD i false := by
      unfold aoStp
      exact List.getD_append _ _ _ _ (by omega)
    have e3 : (aoStp W' (aoNew L g)).getD i false = W'.getD i false := by
      unfold aoStp
      exact List.getD_append _ _ _ _ (by omega)
    rw [e1, e2, e3]
    exact hA i
  · subst hi
    have e1 : aoRd (L ++ [aoCls L g]) L.length = aoCls L g := by
      unfold aoRd
      exact ao_getD_snoc _ _ _
    have e2 : (aoStp W g).getD L.length false
        = g.op.eval (g.inputs.map fun i => W.getD i false) := by
      unfold aoStp
      rw [hl]
      exact ao_getD_snoc _ _ _
    have e3 : (aoStp W' (aoNew L g)).getD L.length false
        = (aoNew L g).op.eval ((aoNew L g).inputs.map fun i => W'.getD i false) := by
      unfold aoStp
      rw [hl, ← hl']
      exact ao_getD_snoc _ _ _
    rw [e1, e2, e3]
    exact ⟨s2, s1⟩
  · have e1 : aoRd (L ++ [aoCls L g]) i = some false := by
      unfold aoRd
      exact List.getD_eq_default _ _ (by simp; omega)
    have e2 : (aoStp W g).getD i false = false := by
      unfold aoStp
      exact List.getD_eq_default _ _ (by simp; omega)
    rw [e1, e2]
    refine ⟨fun h => by simp at h, fun b hb => ?_⟩
    cases b <;> simp_all

theorem ao_fold : ∀ (gs : List Gate),
    (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) →
    ∀ (L : List (Option Bool)) (W W' : List Bool), L.length = W.length →
      W'.length = W.length → AoAgree L W W' →
      AoAgree (aoFold gs L) (gs.foldl aoStp W) ((aoBuild gs L).foldl aoStp W')
  | [], _, _, _, _, _, _, h => h
  | g :: gs, hok, L, W, W', hl, hl', h => by
    have hg := hok g List.mem_cons_self
    have := ao_fold gs (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg')) (L ++ [aoCls L g])
      (aoStp W g) (aoStp W' (aoNew L g)) (by simp [aoStp, hl]) (by simp [aoStp, hl'])
      (ao_step L W W' g hl hl' h hg.1 hg.2)
    exact this

theorem ao_fold_len : ∀ (gs : List Gate) (W : List Bool),
    (gs.foldl aoStp W).length = W.length + gs.length
  | [], W => by simp
  | g :: gs, W => by
    have h1 := ao_fold_len gs (aoStp W g)
    have h2 : (aoStp W g).length = W.length + 1 := by simp [aoStp]
    simp only [List.foldl_cons, List.length_cons]
    omega

theorem ao_init (n : ℕ) (x : Fin n → Bool) :
    AoAgree (List.replicate n none) (List.ofFn x) (List.ofFn x) := by
  intro i
  refine ⟨fun _ => rfl, fun b hb => ?_⟩
  unfold aoRd at hb
  by_cases hi : i < n
  · rw [List.getD_eq_getElem _ _ (by simpa using hi)] at hb
    simp at hb
  · rw [List.getD_eq_default _ _ (by simp; omega)] at hb
    rw [List.getD_eq_default _ _ (by simp; omega)]
    cases b <;> simp_all

end PEqualNP.Outside.L_meta_4342

theorem PEqualNP.Outside.L_meta_4342 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → (PEqualNP.MetaComplexity.circuitFun x1 x2 fun (x4 : Fin x1) => Bool.false) = Bool.false → ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x1 x5 ∧ x5.size ≤ x2.size ∧ PEqualNP.MetaComplexity.circuitFun x1 x5 = PEqualNP.MetaComplexity.circuitFun x1 x2 := by
  intro n C hmono h0
  have hok : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    have := hmono g hg
    simpa using this
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    refine ⟨⟨[], 0⟩, ?_, ?_, ?_⟩
    · unfold PEqualNP.TopForm.IsAO2
      refine ⟨?_, ?_, ?_⟩
      · intro g hg
        simp at hg
      · intro j hj
        simp at hj
      · intro g hg
        simp at hg
    · simp [Circuit.size]
    · funext x
      have hx : x = fun _ => false := funext fun i => i.elim0
      subst hx
      rw [h0]
      rfl
  · refine ⟨PEqualNP.Outside.L_meta_4342.aoC n C, ?_, ?_, ?_⟩
    · unfold PEqualNP.TopForm.IsAO2
      refine ⟨?_, ?_, ?_⟩
      · intro g' hg'
        obtain ⟨L', g, hg, rfl⟩ := PEqualNP.Outside.L_meta_4342.ao_build_mem C.gates
          (List.replicate n none) g' hg'
        exact PEqualNP.Outside.L_meta_4342.ao_new_op L' g (hok g hg).1
      · intro j hj i hi
        have := PEqualNP.Outside.L_meta_4342.ao_build_reads C.gates (List.replicate n none) j
          (by simp; omega) hj i hi
        simpa using this
      · intro g' hg'
        obtain ⟨L', g, hg, rfl⟩ := PEqualNP.Outside.L_meta_4342.ao_build_mem C.gates
          (List.replicate n none) g' hg'
        exact PEqualNP.Outside.L_meta_4342.ao_new_len L' g (hok g hg).2
    · exact le_of_eq (PEqualNP.Outside.L_meta_4342.ao_build_len _ _)
    · funext x
      have hA := PEqualNP.Outside.L_meta_4342.ao_fold C.gates hok (List.replicate n none)
        (List.ofFn x) (List.ofFn x) (by simp) rfl (PEqualNP.Outside.L_meta_4342.ao_init n x)
      have hA0 := PEqualNP.Outside.L_meta_4342.ao_fold C.gates hok (List.replicate n none)
        (List.ofFn fun _ : Fin n => false) (List.ofFn fun _ : Fin n => false) (by simp) rfl
        (PEqualNP.Outside.L_meta_4342.ao_init n _)
      have hlen := PEqualNP.Outside.L_meta_4342.ao_fold_len
        (PEqualNP.Outside.L_meta_4342.aoBuild C.gates (List.replicate n none)) (List.ofFn x)
      rw [PEqualNP.Outside.L_meta_4342.ao_build_len] at hlen
      simp only [List.length_ofFn] at hlen
      show ((PEqualNP.Outside.L_meta_4342.aoBuild C.gates (List.replicate n none)).foldl
          PEqualNP.Outside.L_meta_4342.aoStp (List.ofFn x)).getD
          (PEqualNP.Outside.L_meta_4342.aoOut
            (PEqualNP.Outside.L_meta_4342.aoFold C.gates (List.replicate n none)) n C) false
        = (C.gates.foldl PEqualNP.Outside.L_meta_4342.aoStp (List.ofFn x)).getD C.output false
      unfold PEqualNP.Outside.L_meta_4342.aoOut
      split
      · rename_i hc
        exact (hA C.output).1 hc
      · rename_i b hc
        have hb := (hA C.output).2 b hc
        cases b
        · have hle := le_of_eq hlen
          rw [List.getD_eq_default _ _ hle]
          exact hb.symm
        · exfalso
          have hb0 := (hA0 C.output).2 true hc
          have h0' : (C.gates.foldl PEqualNP.Outside.L_meta_4342.aoStp
              (List.ofFn fun _ : Fin n => false)).getD C.output false = false := h0
          rw [h0'] at hb0
          exact Bool.false_ne_true hb0
