/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.DeligneLaumon.Reduction.Weights
public import WeilConjectures.WeilSheaf.StalkExact
public import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule.Map

/-!
# Mixed Weil sheaves with weights in a prescribed set

A constructible Weil sheaf `F` is `ι`-*mixed with weights in* a set `S ⊆ ℝ`
(`AlgebraicGeometry.WeilSheaf.IsMixedOfWeightsIn`) if it admits a finite filtration whose
successive quotients are punctually `ι`-pure of weights belonging to `S`. For `S = Iic w` this is
being mixed of weights at most `w`.

The weights of the pure quotients of a mixed filtration are the weights of the eigenvalues of the
local Frobenius of `F` at closed points (`AlgebraicGeometry.WeilSheaf.HasWeightsIn`): a nonzero
punctually pure quotient has an eigenvalue at some closed point, which is an eigenvalue of `F`.
Hence a mixed sheaf is mixed with weights in `S` as soon as all its punctual weights lie in `S`
(`AlgebraicGeometry.WeilSheaf.isMixedOfWeightsIn_iff`); in particular a mixed sheaf with weights
at most `w` at every closed point is mixed of weights at most `w`
(`AlgebraicGeometry.WeilSheaf.IsMixed.isMixedOfWeightsAtMost`), without any separatedness or
quasi-compactness assumption on the base.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  {ι : PadicAlgCl l →+* ℂ} {F G : WeilSheaf k₀ l X} {S T : Set ℝ}

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] in
/-- The residue cardinality `q_x` at a closed point is larger than one. -/
lemma one_lt_residueCard (x : X.finitePoints) :
    1 < ((X ↘ Spec (CommRingCat.of k₀)).residueCard x.1 : ℝ) := by
  rw [Scheme.Hom.residueCard]
  exact_mod_cast Nat.one_lt_pow (Scheme.Hom.degreeOver_ne_zero _ x.2) Finite.one_lt_card

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] in
/-- A zero Weil sheaf has no local Frobenius eigenvalues. -/
theorem not_hasEigenvalue_stalk_of_isZero (hF : IsZero F) (x : X.finitePoints)
    (α : PadicAlgCl l) : ¬ (F.stalk x).frobeniusEnd.HasEigenvalue α := fun hα ↦ by
  have : x ∉ F.support := by
    rw [support_eq_empty_of_isZero hF]
    exact id
  have : Subsingleton (F.stalk x).carrier := not_nontrivial_iff_subsingleton.1 this
  obtain ⟨v, hv⟩ := hα.exists_hasEigenvector
  exact hv.2 (Subsingleton.elim _ _)

variable (ι) in
/-- `F` has *punctual weights in* `S`: at every closed point `x`, every eigenvalue `α` of the
local Frobenius `Fₓ` satisfies `|ι α| = q_x ^ (v / 2)` for some `v ∈ S`
(blueprint: `def-weil-punctual-weights`). -/
def HasWeightsIn (F : WeilSheaf k₀ l X) (S : Set ℝ) : Prop :=
  ∀ (x : X.finitePoints) (α : PadicAlgCl l), (F.stalk x).frobeniusEnd.HasEigenvalue α →
    ∃ v ∈ S, ‖ι α‖ = ((X ↘ Spec (CommRingCat.of k₀)).residueCard x.1 : ℝ) ^ (v / 2)

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] in
/-- Punctual weights in `S` are punctual weights in any larger set. -/
theorem HasWeightsIn.mono_set (h : F.HasWeightsIn ι S) (hST : S ⊆ T) : F.HasWeightsIn ι T :=
  fun x α hα ↦ (h x α hα).imp fun _ hv ↦ ⟨hST hv.1, hv.2⟩

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] in
/-- A punctually pure sheaf of weight `v ∈ S` has punctual weights in `S`. -/
theorem IsPunctuallyPureOfWeight.hasWeightsIn {v : ℝ} (h : F.IsPunctuallyPureOfWeight ι v)
    (hv : v ∈ S) : F.HasWeightsIn ι S :=
  fun x α hα ↦ ⟨v, hv, h x α hα⟩

/-- A subobject of a sheaf with punctual weights in `S` has punctual weights in `S`. -/
theorem HasWeightsIn.of_mono (f : F ⟶ G) [Mono f] (h : G.HasWeightsIn ι S) :
    F.HasWeightsIn ι S := fun x α hα ↦
  h x α (FrobeniusModule.hasEigenvalue_of_injective _ (stalkAtMap_frobenius _ _ _ f)
    (injective_stalkAtMap _ _ _ f) hα)

/-- A quotient of a sheaf with punctual weights in `S` has punctual weights in `S`. -/
theorem HasWeightsIn.of_epi (f : F ⟶ G) [Epi f] (h : F.HasWeightsIn ι S) :
    G.HasWeightsIn ι S := fun x α hα ↦
  h x α (FrobeniusModule.hasEigenvalue_of_surjective _ (stalkAtMap_frobenius _ _ _ f)
    (surjective_stalkAtMap _ _ _ f) hα)

/-- Punctual weights in `S` are invariant under isomorphism. -/
theorem HasWeightsIn.of_iso (e : F ≅ G) (h : F.HasWeightsIn ι S) : G.HasWeightsIn ι S :=
  h.of_epi e.hom

/-- An extension of sheaves with punctual weights in `S` has punctual weights in `S`: the stalks
form short exact sequences of Frobenius modules. -/
theorem HasWeightsIn.of_mono_cokernel (i : G ⟶ F) [Mono i] (hG : G.HasWeightsIn ι S)
    (hQ : (cokernel i).HasWeightsIn ι S) : F.HasWeightsIn ι S := fun x α hα ↦
  (FrobeniusModule.hasEigenvalue_or_of_exact _ (stalkAtMap_frobenius _ _ _ i) _
    (stalkAtMap_frobenius _ _ _ (cokernel.π i)) (injective_stalkAtMap _ _ _ i)
    (range_stalkAtMap_eq_ker (ShortComplex.exact_cokernel i) _ _ _) hα).elim
    (hG x α) (hQ x α)

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] in
/-- A sheaf with weights at most `w` at every closed point has punctual weights in `Iic w`: the
local Frobenius is invertible, so its eigenvalues are nonzero and have a weight. -/
theorem HasWeightsAtMost.hasWeightsIn_Iic {w : ℝ} (h : F.HasWeightsAtMost ι w) :
    F.HasWeightsIn ι (Set.Iic w) := fun x α hα ↦ by
  have hq := one_lt_residueCard (k₀ := k₀) x
  have hα0 : 0 < ‖ι α‖ := by
    refine norm_pos_iff.2 ((map_ne_zero ι).2 fun h0 ↦ ?_)
    obtain ⟨v, hv⟩ := hα.exists_hasEigenvector
    rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff, h0, zero_smul] at hv
    exact hv.2 ((F.stalk x).frobenius.map_eq_zero_iff.1 hv.1)
  refine ⟨2 * Real.logb ((X ↘ Spec (CommRingCat.of k₀)).residueCard x.1) ‖ι α‖, ?_, ?_⟩
  · rw [Set.mem_Iic, ← le_div_iff₀' two_pos, Real.logb_le_iff_le_rpow hq hα0]
    exact h x α hα
  · rw [mul_div_cancel_left₀ _ two_ne_zero, Real.rpow_logb (by linarith) hq.ne' hα0]

variable (ι S) in
/-- The property of a Weil sheaf of being punctually `ι`-pure of some weight in `S`. -/
def isPunctuallyPureOfWeightIn : ObjectProperty (WeilSheaf k₀ l X) :=
  fun F ↦ ∃ v ∈ S, F.IsPunctuallyPureOfWeight ι v

instance : (isPunctuallyPureOfWeightIn (k₀ := k₀) (l := l) (X := X) ι S).IsClosedUnderSubobjects
    where
  prop_of_mono f _ := fun ⟨v, hv, h⟩ ↦ ⟨v, hv, h.of_mono f⟩

instance : (isPunctuallyPureOfWeightIn (k₀ := k₀) (l := l) (X := X) ι S).IsClosedUnderQuotients
    where
  prop_of_epi f _ := fun ⟨v, hv, h⟩ ↦ ⟨v, hv, h.of_epi f⟩

instance :
    (isPunctuallyPureOfWeightIn (k₀ := k₀) (l := l) (X := X) ι S).IsClosedUnderIsomorphisms where
  of_iso e := fun ⟨v, hv, h⟩ ↦ ⟨v, hv, h.of_epi e.hom⟩

variable (ι) in
/-- `F` is `ι`-*mixed with weights in* `S` if it admits a finite filtration whose successive
quotients are punctually `ι`-pure of weights belonging to `S`
(blueprint: `sk-d-real-weights`, `def-weil-punctual-weights`). -/
def IsMixedOfWeightsIn (F : WeilSheaf k₀ l X) (S : Set ℝ) : Prop :=
  (isPunctuallyPureOfWeightIn ι S).filtrationClosure F

/-- Being mixed with weights in `Iic w` is being mixed of weights at most `w`. -/
theorem isMixedOfWeightsIn_Iic_iff {w : ℝ} :
    F.IsMixedOfWeightsIn ι (Set.Iic w) ↔ F.IsMixedOfWeightsAtMost ι w := by
  rw [isMixedOfWeightsAtMost_iff_filtrationClosure]
  rfl

/-- A punctually pure sheaf of weight `v ∈ S` is mixed with weights in `S`. -/
theorem IsPunctuallyPureOfWeight.isMixedOfWeightsIn {v : ℝ} (h : F.IsPunctuallyPureOfWeight ι v)
    (hv : v ∈ S) : F.IsMixedOfWeightsIn ι S :=
  ObjectProperty.le_filtrationClosure _ ⟨v, hv, h⟩

/-- Being mixed with weights in `S` is monotone in `S`. -/
theorem IsMixedOfWeightsIn.mono_set (h : F.IsMixedOfWeightsIn ι S) (hST : S ⊆ T) :
    F.IsMixedOfWeightsIn ι T := by
  induction h with
  | of_isZero hX => exact ObjectProperty.filtrationClosure.of_isZero hX
  | of_mono i hX hi ih =>
    obtain ⟨v, hv, h⟩ := hi
    exact ObjectProperty.filtrationClosure.of_mono i ih ⟨v, hST hv, h⟩

/-- Being mixed with weights in `S` is invariant under isomorphism. -/
theorem IsMixedOfWeightsIn.of_iso (e : F ≅ G) (h : F.IsMixedOfWeightsIn ι S) :
    G.IsMixedOfWeightsIn ι S :=
  (isPunctuallyPureOfWeightIn ι S).filtrationClosure.prop_of_iso e h

/-- A subobject of a sheaf mixed with weights in `S` is mixed with weights in `S`. -/
theorem IsMixedOfWeightsIn.of_mono (i : G ⟶ F) [Mono i] (h : F.IsMixedOfWeightsIn ι S) :
    G.IsMixedOfWeightsIn ι S :=
  (isPunctuallyPureOfWeightIn ι S).filtrationClosure.prop_of_mono i h

/-- A quotient of a sheaf mixed with weights in `S` is mixed with weights in `S`. -/
theorem IsMixedOfWeightsIn.of_epi (p : F ⟶ G) [Epi p] (h : F.IsMixedOfWeightsIn ι S) :
    G.IsMixedOfWeightsIn ι S :=
  (isPunctuallyPureOfWeightIn ι S).filtrationClosure.prop_of_epi p h

/-- An extension of sheaves mixed with weights in `S` is mixed with weights in `S`. -/
theorem IsMixedOfWeightsIn.of_mono_cokernel (i : G ⟶ F) [Mono i]
    (hG : G.IsMixedOfWeightsIn ι S) (hQ : (cokernel i).IsMixedOfWeightsIn ι S) :
    F.IsMixedOfWeightsIn ι S :=
  (isPunctuallyPureOfWeightIn ι S).filtrationClosure.prop_X₂_of_shortExact
    (ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel i) inferInstance inferInstance) hG hQ

/-- In an exact sequence `A ⟶ B ⟶ C` whose outer terms are mixed with weights in `S`, the middle
term is mixed with weights in `S`. -/
theorem IsMixedOfWeightsIn.of_exact {Sc : ShortComplex (WeilSheaf k₀ l X)} (hS : Sc.Exact)
    (h₁ : Sc.X₁.IsMixedOfWeightsIn ι S) (h₃ : Sc.X₃.IsMixedOfWeightsIn ι S) :
    Sc.X₂.IsMixedOfWeightsIn ι S :=
  have := hS.epi_kernelLift
  (h₁.of_epi (kernel.lift Sc.g Sc.f Sc.zero)).of_mono_cokernel (kernel.ι Sc.g)
    (h₃.of_mono (Abelian.factorThruCoimage Sc.g))

/-- A sheaf mixed with weights in `S` has punctual weights in `S`. -/
theorem IsMixedOfWeightsIn.hasWeightsIn (h : F.IsMixedOfWeightsIn ι S) : F.HasWeightsIn ι S := by
  induction h with
  | of_isZero hX => exact fun x α hα ↦ (not_hasEigenvalue_stalk_of_isZero hX x α hα).elim
  | of_mono i _ hi ih =>
    obtain ⟨v, hv, h⟩ := hi
    exact ih.of_mono_cokernel i (h.hasWeightsIn hv)

/-- A sheaf mixed with weights in `S` is mixed. -/
theorem IsMixedOfWeightsIn.isMixed (h : F.IsMixedOfWeightsIn ι S) : F.IsMixed ι := by
  induction h with
  | of_isZero hX => exact ⟨0, isMixedOfWeightsAtMost_of_isZero hX 0⟩
  | of_mono i _ hi ih =>
    obtain ⟨w, hw⟩ := ih
    obtain ⟨v, -, h⟩ := hi
    exact ⟨max w v, (hw.mono_weight (le_max_left _ _)).of_mono_cokernel i
      (isMixedOfWeightsIn_Iic_iff.1 (h.isMixedOfWeightsIn (le_max_right w v)))⟩

/-- A mixed sheaf whose punctual weights lie in `S` is mixed with weights in `S`: the weight of a
nonzero punctually pure quotient of a mixed filtration is the weight of an eigenvalue of the
local Frobenius of the sheaf at some closed point. -/
theorem IsMixed.isMixedOfWeightsIn (h : F.IsMixed ι) (hS : F.HasWeightsIn ι S) :
    F.IsMixedOfWeightsIn ι S := by
  obtain ⟨w, h⟩ := h
  rw [isMixedOfWeightsAtMost_iff_filtrationClosure] at h
  induction h generalizing S with
  | of_isZero hX => exact ObjectProperty.filtrationClosure.of_isZero hX
  | of_mono i _ hi ih =>
    by_cases hz : IsZero (cokernel i)
    · have : Epi i := Preadditive.epi_of_isZero_cokernel i hz
      have : IsIso i := isIso_of_mono_of_epi i
      exact (ih (hS.of_iso (asIso i).symm)).of_iso (asIso i)
    obtain ⟨v, -, hpure⟩ := hi
    obtain ⟨x, hx⟩ := exists_nontrivial_stalk_of_not_isZero _ hz
    have := ((cokernel i).stalk x).finiteDimensional
    obtain ⟨α, hα⟩ := Module.End.exists_eigenvalue ((cokernel i).stalk x).frobeniusEnd
    obtain ⟨v', hv', hα'⟩ := hS.of_epi (cokernel.π i) x α hα
    have hq := one_lt_residueCard (k₀ := k₀) x
    have h₁ := Real.logb_rpow (b := ((X ↘ Spec (CommRingCat.of k₀)).residueCard x.1 : ℝ))
      (x := v / 2) (by linarith) hq.ne'
    have h₂ := Real.logb_rpow (b := ((X ↘ Spec (CommRingCat.of k₀)).residueCard x.1 : ℝ))
      (x := v' / 2) (by linarith) hq.ne'
    rw [← hpure x α hα] at h₁
    rw [← hα'] at h₂
    have hvv : v = v' := by linarith
    exact ObjectProperty.filtrationClosure.of_mono i (ih (hS.of_mono i)) ⟨v, hvv ▸ hv', hpure⟩

/-- **Weights of a mixed sheaf.** A sheaf is mixed with weights in `S` if and only if it is mixed
and all its punctual weights lie in `S`. -/
theorem isMixedOfWeightsIn_iff : F.IsMixedOfWeightsIn ι S ↔ F.IsMixed ι ∧ F.HasWeightsIn ι S :=
  ⟨fun h ↦ ⟨h.isMixed, h.hasWeightsIn⟩, fun h ↦ h.1.isMixedOfWeightsIn h.2⟩

/-- **Punctual cutoff for a mixed sheaf.** A mixed sheaf with weights at most `w` at every closed
point is mixed of weights at most `w` (compare
`AlgebraicGeometry.WeilSheaf.IsMixedOfWeightsAtMost.of_hasWeightsAtMost`, which assumes the base
separated and quasi-compact). -/
theorem IsMixed.isMixedOfWeightsAtMost {w : ℝ} (h : F.IsMixed ι) (hw : F.HasWeightsAtMost ι w) :
    F.IsMixedOfWeightsAtMost ι w :=
  isMixedOfWeightsIn_Iic_iff.1 (h.isMixedOfWeightsIn hw.hasWeightsIn_Iic)

end AlgebraicGeometry.WeilSheaf
