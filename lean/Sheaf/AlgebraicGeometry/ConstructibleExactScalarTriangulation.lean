/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q48
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit
public import Sheaf.AlgebraicGeometry.ProEtalePointPullback
public import Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
public import Sheaf.CategoryTheory.DerivedCategory.LeftDerivedTotalTensorExact
public import Sheaf.Paper.CondensedCoefficientComparisons
import Sheaf.AlgebraicGeometry.CondensedConstructibleSerre
import Sheaf.Paper.CohomologyInWeakSerreSubcategory
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor

/-!
# Constructible triangles and exact scalar extension to the condensed algebraic closure

Source: blueprint main-20261015, sec-six-functors-basics,
sk-thm-sfb-qlbar-two-colimit/lem-sfb-constructible-cocone-obj.proof.md, Complexes paragraph;
Stacks Project, Tags 06UQ and 015F
(blueprint: lem-sfb-constructible-exact-scalar-triangulation).

The coefficient rings, constructible category and derived extension are the recorded
constructions. The comparison is the existing uniqueness isomorphism for left derived
functors. The integer-shift structure on the derived extension is the recorded
`condensedAlgClCoefficientCommShift` (def-weil-pbc-condensed-coefficient-comparisons): the
transport of the exact termwise shifts along the inverse of this same comparison.
Every target triangle lies in the ambient derived category over the algebraic closure.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]

/-- The canonical comparison with exact termwise extension, obtained from uniqueness of
left derived functors with their specified counits. This is the existing comparison,
specialized to the recorded coefficient inclusion, with no choice of an arbitrary map.
Source: blueprint main-20261015, lem-sfb-constructible-cocone-obj.proof.md, Complexes;
Stacks Tag 015F (blueprint: lem-sfb-constructible-exact-scalar-triangulation). -/
noncomputable def constructibleScalarExactComparison (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    derivedExtendScalarsToPadicAlgCl X ℓ E ≅
      (Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ E)).mapDerivedCategory :=
  (Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ E))
    |>.leftDerivedFunctorIsoMapDerivedCategory

/-- The inherited finite-coefficient constructible triangulation and exact ambient scalar
extension, with the canonical comparison compatible with every integer shift.
Source: blueprint main-20261015, lem-sfb-constructible-cocone-obj.proof.md, Complexes;
Stacks Tags 06UQ and 015F (blueprint: lem-sfb-constructible-exact-scalar-triangulation).

Proof:
1. The small pro-etale abelian sheaf category is closed symmetric monoidal with additive
colimit-preserving tensor (`lem-weil-pbc-sheaf-tensor-closed`). Internal module categories
are abelian by `lem-sfb-modobj-abelian`; the relative coequalizer scalar extension is a
left adjoint by `sk-def-sfb-change-of-scalars`, hence preserves finite colimits.
2. The finite-field case of `lem-weil-pbc-condensed-constructible-serre`, transported using
`lem-sfb-condensed-coefficient-presentation-identification`, gives kernel, cokernel and
extension closure for precisely the stratified local-presentation predicate in
`def-sfb-constructible-module`. Zero has the zero presentation, also on the empty scheme;
isomorphisms transport presentations. Apply the bounded version of
`lem-sbc-cohomology-in-weak-serre-subcategory` to get the first assertion.
3. `def-weil-triangulated-subcategory` gives the inherited pretriangulation and triangulated
inclusion. The full inclusion preserves addition, so the ambient additive integer shifts
restrict to additive integer shifts on this full subcategory.
4. `lem-sfb-qlbar-flat` supplies preservation of finite limits. Preservation of zero and
binary biproducts identifies diagonals and codiagonals, and hence addition; equivalently
use the existing additive relative tensor construction. Thus scalar extension is exact.
5. `lem-weil-pbc-exact-functor-derived-factorization` supplies exact termwise derivation,
its factorization on complexes, its triangulation, and shift compatibility (the comparison
on complexes is the identity in each degree, since addition preserves the sign).
6. `lem-weil-pbc-exact-functor-derived-functor` makes this termwise functor itself total
left derived. Passage from complexes to the homotopy category does not change the universal
property: its quotient is a localization, and the additive functor preserves homotopies.
Uniqueness of the two counited left derived functors gives the canonical comparison above.
7. Transport the integer shifts through that comparison; this transported structure is the
recorded `condensedAlgClCoefficientCommShift`. Naturality and shift coherence follow by
cancellation of adjacent comparison inverses. The transported triangle is
isomorphic to the exact termwise image triangle, including the last square by the displayed
transport formula. Isomorphism invariance of distinguished triangles proves triangulatedness.
8. Compose with the inherited triangulated full inclusion. Whiskering the same canonical
comparison identifies this composite with the restriction of exact termwise extension,
compatibly with all integer shifts. No triangulation over constructible closure-coefficient
objects is used. -/
theorem constructible_exact_scalar_triangulation
    [TopologicalSpace.NoetherianSpace X] (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    (boundedConstructible (padicSubfieldRingObj X ℓ E)).IsTriangulated ∧
    (∀ n : ℤ, (shiftFunctor (PadicSubfieldConstructible X ℓ E) n).Additive) ∧
    (boundedConstructible (padicSubfieldRingObj X ℓ E)).ι.IsTriangulated ∧
    (Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ E)).Additive ∧
    PreservesFiniteLimits (Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ E)) ∧
    PreservesFiniteColimits (Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ E)) ∧
    NatTrans.CommShift (constructibleScalarExactComparison X ℓ E).hom ℤ ∧
    (derivedExtendScalarsToPadicAlgCl X ℓ E).IsTriangulated ∧
    ((boundedConstructible (padicSubfieldRingObj X ℓ E)).ι ⋙
      derivedExtendScalarsToPadicAlgCl X ℓ E).IsTriangulated ∧
    NatTrans.CommShift
      (Functor.isoWhiskerLeft (boundedConstructible (padicSubfieldRingObj X ℓ E)).ι
        (constructibleScalarExactComparison X ℓ E)).hom ℤ := by
  sorry

end AlgebraicGeometry.ProEtale
