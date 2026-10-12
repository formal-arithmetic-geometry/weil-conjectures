/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q2
-/
module

public import Sheaf.AlgebraicGeometry.DerivedPullbackAcrossUniverses
public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.DiagonalPushforwardStructure
import Sheaf.AlgebraicGeometry.NoetherianDerivedDirectImageRightAdjoint
import Sheaf.AlgebraicGeometry.DerivedCategory
import Sheaf.AlgebraicGeometry.DerivedPullbackTensorQCoh

/-! # Diagonal counit in independent localization universes

Source: Stacks Project, Equation 48.12.8.1, Tag 0E2Q; localization uniqueness, Tag 05RU.
(blueprint: lem-sc-diagonal-counit-across-universes).
-/

@[expose] public section

set_option autoImplicit false

universe u wX wS wP

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- The first equality of the diagonal evaluation chain, for the specified adjoints.
Source: Stacks Project, Tag 0E2Q, and localization uniqueness, Tag 05RU.
(blueprint: lem-sc-diagonal-counit-across-universes).

Proof: properness makes f finite type and quasi-compact; the base-changed projection
is again proper. Hence P = X ×_S X is Noetherian. Flat pullback preserves quasi-coherent
cohomology, so the mixed-universe pullback of a(O) has a preservation witness hK.
For each scheme compare the specified localization with the standard localization of
complexes using `schemeDerivedStandardEquivalence`. The comparison commutes with Qh by
`Localization.compUniqFunctor`. The homology comparisons then show that it restricts to
an equivalence of quasi-coherent full subcategories: evaluate the factorization of each
homology functor on Qh and use full faithfulness of precomposition with Qh. Likewise it
commutes with the single functor, by its factorization through Qh. Transport R using the
restricted equivalences. Its given comparison identifies it with the restriction of
standard derived direct image, because right derived functors commute with equivalences
of their localizations by the right Kan universal property. Transfer adj along this
comparison. Transfer adjC in the same way; changes of the preservation proof are invisible
in the full subcategory. The Noetherian direct-image theorem supplies the preservation
witnesses for the standard f and diagonal. Flat pullback supplies the first-projection
witness; the structure single objects have quasi-coherent homology. Apply
`diagonal_counit_identity` in the standard universe, with these transported adjunctions.
This gives O_X[0] isomorphic to c(Lpr_1* a(O_S[0])). Transport back, use hO through a,
and the explicit definition of `derivedPullbackAcrossUniverses` to identify the middle
object. The inverse of the resulting isomorphism has the displayed orientation. This
argument never uses perfection of the diagonal or its tensor formula. For f = id the
projection and both adjoints identify with identity functors; for an empty source all
objects involved are zero. These cases require no nonemptiness hypotheses. -/
theorem diagonal_counit_acrossUniverses
    (X S : Scheme.{u}) [IsNoetherian X] [IsNoetherian S]
    (f : X ⟶ S) [Flat f] [IsProper f]
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wS} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    [HasDerivedCategory.{wP}
      (SheafOfModules.{u} (moduleRings (pullback f f).toRingedSpace))]
    (R : schemeDerivedQCohCategory X ⥤ schemeDerivedQCohCategory S)
    (comparison : R ⋙ (schemeDerivedQCohProperty S).ι ≅
      (schemeDerivedQCohProperty X).ι ⋙ schemeDerivedDirectImage f)
    (a : schemeDerivedQCohCategory S ⥤ schemeDerivedQCohCategory X)
    (adj : R ⊣ a) (O : schemeDerivedQCohCategory S)
    (hO : O.obj ≅
      (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).obj
          (SheafOfModules.unit S.ringCatSheaf))
    (hRΔ : ∀ E : schemeDerivedQCohCategory X,
      schemeDerivedQCohProperty (pullback f f)
        ((schemeDerivedDirectImage (pullback.diagonal f)).obj E.obj))
    (c : schemeDerivedQCohCategory (pullback f f) ⥤ schemeDerivedQCohCategory X)
    (adjC : (schemeDerivedQCohProperty (pullback f f)).lift
      ((schemeDerivedQCohProperty X).ι ⋙
        schemeDerivedDirectImage (pullback.diagonal f)) hRΔ ⊣ c)
 :
    ∃ hK : schemeDerivedQCohProperty (pullback f f)
        ((derivedPullbackAcrossUniverses (pullback.fst f f)).obj (a.obj O).obj),
      Nonempty ((c.obj ⟨(derivedPullbackAcrossUniverses (pullback.fst f f)).obj
          (a.obj O).obj, hK⟩).obj ≅
        (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj
          (SheafOfModules.unit X.ringCatSheaf)) := by sorry

end AlgebraicGeometry
