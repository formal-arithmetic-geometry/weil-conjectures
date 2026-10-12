/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q3
-/
module

public import Sheaf.AlgebraicGeometry.DerivedTensorStructure
public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.DiagonalPushforwardStructure
import Sheaf.AlgebraicGeometry.DerivedPullbackComposition
import Sheaf.AlgebraicGeometry.NoetherianDerivedDirectImageRightAdjoint
import Sheaf.AlgebraicGeometry.SmoothProperDiagonalTensorFormula

/-! # Evaluation against the dualizing object of a perfect diagonal

Source: Stacks Project, Tags 0E2Q and 0A9U, combined in the first three equalities
of Tag 0BRT (blueprint: lem-sc-perfect-diagonal-dualizing-evaluation).
-/

@[expose] public section

set_option autoImplicit false

universe u wX wS wP

open CategoryTheory MonoidalCategory Limits

namespace AlgebraicGeometry

/-- The first three equalities of the diagonal evaluation chain, without any
identification of the diagonal dualizing object with a determinant.
Source: Stacks Project, Tags 0E2Q and 0A9U, displayed chain of Tag 0BRT.
(blueprint: lem-sc-perfect-diagonal-dualizing-evaluation).

Proof: Work first in one derived universe. Noetherian proper pushforward preserves
quasi-coherent cohomology, and flat pullback does too. These preservation witnesses
allow restriction of the diagonal and first-projection functors to D_QCoh. Lift the
comparison for R through the fully faithful inclusion; transfer adj along this
isomorphism so that a is right adjoint to the canonical restricted pushforward.
Tag 0E2Q gives O_X[0] isomorphic to c(Lpr_1* a(O_S[0])). The closed diagonal's
pushforward is exact, so the given perfect single complex is its derived pushforward
of the derived tensor unit. Apply Tag 0A9U to the diagonal, with K = Lpr_1* a(O_S[0]).
Its invertible adjunction mate identifies c(K) with LDelta* K tensor c(O_P[0]).
Functoriality of derived pullback and Delta followed by pr_1 = id identify LDelta* K
with a(O_S[0]). Compose these isomorphisms and invert to get the asserted evaluation.
The single structure complex is the unit of the recorded K-flat derived tensor.
Map hO through a and hOP through c to allow the specified structure objects.
For different derived universes, compare each localization with the standard one
using its localization equivalence. The comparison commutes with the localization
of complexes, single functors, shifts, derived direct images, and K-flat derived
pullback and tensor, by their universal properties. Restrict these equivalences to
quasi-coherent objects using the homology comparisons. Transfer both adjunctions,
apply the one-universe construction, and transfer the resulting isomorphism back.
Thus the result concerns the specified a and c, not chosen substitute adjoints. -/
theorem perfectDiagonal_dualizing_evaluation
    (X S : Scheme.{u}) [IsNoetherian X] [IsNoetherian S]
    (f : X ⟶ S) [Flat f] [IsProper f]
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wS} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    [HasDerivedCategory.{wP}
      (SheafOfModules.{u} (moduleRings (pullback f f).toRingedSpace))]
    [∀ U : (pullback f f).Opens, HasDerivedCategory.{wP}
      (SheafOfModules.{u} ((moduleRings (pullback f f).toRingedSpace).over U))]
    (hperfect : Scheme.IsPerfect (pullback f f)
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings (pullback f f).toRingedSpace)) 0).obj
          ((Scheme.Modules.pushforward (pullback.diagonal f)).obj
            (SheafOfModules.unit X.ringCatSheaf))))
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
    (OP : schemeDerivedQCohCategory (pullback f f))
    (hOP : OP.obj ≅
      (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings (pullback f f).toRingedSpace)) 0).obj
          (SheafOfModules.unit (pullback f f).ringCatSheaf)) :
    Nonempty (((a.obj O).obj ⊗ (c.obj OP).obj) ≅
      𝟙_ (schemeDerivedCategory X)) := by sorry

end AlgebraicGeometry
