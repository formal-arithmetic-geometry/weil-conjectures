/- Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H4 -/
module

public import Sheaf.SixFunctors.IntegralSystemOperations
public import Sheaf.Paper.AmbientPullbackTensorCoherence
import all Sheaf.Paper.CompletedPullbackTensorComparison

/-! # Identifying the two canonical presentations of system pullback

Source: Stacks 03D3, 03EL and 07A7. Both direct images use the same map on
constant sections; their inverse images and composition maps are fixed by adjunction.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E]
variable {X Y Z : Scheme.{u}}

private theorem chosen_left_eq {A B : Type*} [Category A] [Category B]
    (F G : A ⥤ B) [F.IsRightAdjoint] [G.IsRightAdjoint] (h : F = G) :
    F.leftAdjoint = G.leftAdjoint := by
  subst G
  rfl

private theorem sequence_ring_eq (f : X ⟶ Y) :
    pullbackTensorSequenceRing l E f = AmbientPullbackTensor.ringUnit l E f none := by
  apply (pullbackTensorSequenceRing_existsUnique l E f).unique
  · exact (pullbackTensorSequenceRing_existsUnique l E f).exists.choose_spec
  · intro n U
    rfl

/-- Both presentations of direct image use precisely the same ringed sequence-site map.
Source: Stacks 03D3 (blueprint: lem-sf-system-pullback-compositor-identification).
Proof: the unique coefficient map is the map on constant sections at every (n,U).
The displayed direct images are the same pushforward after replacing that map. -/
theorem sequence_direct_eq (f : X ⟶ Y) :
    pullbackTensorSequenceDirect l E f = AmbientPullbackTensor.push l E f none := by
  unfold pullbackTensorSequenceDirect
  rw [sequence_ring_eq]
  rfl

/-- The inverse-image presentations agree because leftAdjoint is applied to equal functors.
Source: Stacks 03D3 (blueprint: lem-sf-system-pullback-compositor-identification).
Proof: apply congruence to the established equality of the right adjoints. -/
theorem sequence_inverse_eq (f : X ⟶ Y) :
    pullbackTensorSequenceInverse l E f = AmbientPullbackTensor.pull l E f none := by
  unfold pullbackTensorSequenceInverse AmbientPullbackTensor.pull
  let : (AmbientPullbackTensor.push l E f none).IsRightAdjoint :=
    AmbientPullbackTensor.pushRightAdjoint l E f none
  exact chosen_left_eq _ _ (sequence_direct_eq l E f)

/-- Exact localization preserves the equality of these inverse-image presentations.
Source: Stacks 015F (blueprint: lem-sf-system-pullback-compositor-identification).
Proof: apply congruence to mapDerivedCategory. -/
theorem sequence_derived_eq (f : X ⟶ Y) :
    pullbackTensorSequenceDerived l E f = AmbientPullbackTensor.derivedPull l E f none := by
  unfold pullbackTensorSequenceDerived AmbientPullbackTensor.derivedPull
  congr 1
  exact sequence_inverse_eq l E f

/-- Direct-image compositors agree when their prescribed section formulas agree.
Source: Stacks 03CB (blueprint: lem-sf-system-pullback-compositor-identification).
Proof: module-sheaf morphisms are determined by their maps on each (n,U) section.
The section certificate in Compositors is independent of its presentation. -/
theorem sequence_direct_compositor_unique
    (o o' : IntegralSystemRealization.Operations l E)
    (c : IntegralSystemRealization.Compositors l E o)
    (c' : IntegralSystemRealization.Compositors l E o') (f : X ⟶ Y) (g : Y ⟶ Z) :
    c.ordinaryDirect f g = c'.ordinaryDirect f g := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext x
  exact (c.sections f g M U.unop.1 U.unop.2 x).trans
    (c'.sections f g M U.unop.1 U.unop.2 x).symm

/-- The ordinary inverse-image compositor is independent of its packaged presentation.
Source: Stacks 07A7 (blueprint: lem-sf-system-pullback-compositor-identification).
Proof: conjugation is an equivalence; the direct-image compositors agree on sections. -/
theorem sequence_inverse_compositor_unique
    (o o' : IntegralSystemRealization.Operations l E)
    (c : IntegralSystemRealization.Compositors l E o)
    (c' : IntegralSystemRealization.Compositors l E o') (f : X ⟶ Y) (g : Y ⟶ Z) :
    c.ordinaryPull f g = c'.ordinaryPull f g := by
  apply (conjugateIsoEquiv ((pullbackTensorSequenceAdjunction l E g).comp
    (pullbackTensorSequenceAdjunction l E f))
    (pullbackTensorSequenceAdjunction l E (f ≫ g))).injective
  rw [c.conjugate, c'.conjugate]
  exact sequence_direct_compositor_unique l E o o' c c' f g

/-- The derived compositor is independent of its packaged presentation.
Source: Stacks 015F, 07A7 (blueprint: lem-sf-system-pullback-compositor-identification).
Proof: restriction along localization is faithful. Cancel the two exact-functor
factorizations, use the recorded localization equations, and then ordinary uniqueness. -/
theorem sequence_derived_compositor_unique
    (o o' : IntegralSystemRealization.Operations l E)
    (c : IntegralSystemRealization.Compositors l E o)
    (c' : IntegralSystemRealization.Compositors l E o') (f : X ⟶ Y) (g : Y ⟶ Z) :
    c.pullComp f g = c'.pullComp f g := by
  apply Iso.ext
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso (coefficientSequenceModules l E Z) (.up ℤ))
  intro P
  apply (cancel_mono ((IntegralSystemRealization.pull l E f).map
    ((pullbackTensorSequenceInverse l E g).mapDerivedCategoryFactors.hom.app P) ≫
    (pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.hom.app
      (((pullbackTensorSequenceInverse l E g).mapHomologicalComplex (.up ℤ)).obj P))).1
  rw [c.pullComp_model, c'.pullComp_model,
    sequence_inverse_compositor_unique l E o o' c c' f g]

end WeilConjectures
