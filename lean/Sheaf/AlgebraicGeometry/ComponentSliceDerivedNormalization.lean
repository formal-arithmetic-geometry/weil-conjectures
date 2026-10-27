/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.AlgebraicGeometry.ComponentSliceComparisonData

/-! # Derived normalization of the component slice square

Source: Hemo--Richarz--Scholbach, Proposition 4.3(1), equation (4.2).
(blueprint: lem-sfb-component-slice-derived-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing.ComponentSlice

variable (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]

/-- The normalized ordinary component square induces the normalized unbounded
closed-monoidal comparison, including its map on every shifted Hom group.

Source: HRS Proposition 4.3(1), (4.2); Stacks Tags 07A4, 08JA, 08JB and 08J9.
(blueprint: lem-sfb-component-slice-derived-normalization).

Proof: Use exact termwise localization of the four ordinary functors. Resolve tensors by
flat-term K-flat complexes and use the ordinary balanced tensor formula on each summand
of their total tensor. This gives strong derived tensor structures with exactly the
homotopy-representative and coefficient-unit equations of DerivedMonoidalNormalization;
the same calculation localizes the ordinary monoidal isomorphism e. Slice restriction of
RHom is an isomorphism, by the localized tensor-Hom adjunction, with evaluation preserved.
Uncurry both paths of evaluation_square. Naturality of the tensorators and monoidality of
e identify both paths with the same pulled-back evaluation, proving that square by the
injectivity of transposition. Exact evaluation on the w-contractible final objects gives
the ordinary section isomorphism with its unit formula. Derive it using the exact section
comparison on every homotopy representative, which gives sectionsPullback. The Hom-complex
model for RHom, using a K-injective target, identifies all its section cohomology groups
with Hom into each integer shift. Its evaluation description sends a section from the
coefficient unit to sectionTranspose; this proves the normalization of sectionsHomT and
sectionsHomU. Transpose a pulled-back section. The unit equation and naturality of the
tensorator identify its transpose with shiftedHomMap, proving cohomology_formula for all
integers. Applying right-derived sections to evaluation_square and cancelling sliceHomT,
then using naturality of sectionsPullback, gives derived_sections_square. If the lower
component functor is fully faithful, its shifted-Hom maps are bijective. Hence every
cohomology map of localSectionsComparison is invertible. A derived morphism with that
property is invertible: represent it by a map to a K-injective resolution, which is a
quasi-isomorphism and is inverted by localization. The derived-sections square and its
other invertible factors then give fully_faithful_test. Naturality follows from the
adjunction, localization and section comparisons used throughout; no bound on complexes
or finiteness of inputs is used. -/
theorem component_slice_derived_normalization
    (W : Scheme.{u}) [IsAffine W] [IsWContractibleRing Γ(W, ⊤)]
    (U : W.ProEt) [IsAffine U.left] [IsWContractibleRing Γ(U.left, ⊤)]
    (dW : PullbackData Λ W) (dU : PullbackData Λ U.left)
    (r : RestrictionData Λ (componentMap W U))
    (e : OrdinaryComparison Λ W U dW dU r)
    (he : OrdinaryMonoidal Λ W U dW dU r (schemeCanonicalMonoidal Λ W U) e) :
    Nonempty (DerivedComparison Λ W U dW dU r (schemeCanonicalMonoidal Λ W U) e) := by sorry

end AlgebraicGeometry.ProEtale.CondensedRing.ComponentSlice
