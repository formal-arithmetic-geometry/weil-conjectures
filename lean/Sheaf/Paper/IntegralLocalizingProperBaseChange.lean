/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q97
-/
module

public import Sheaf.Paper.CondensedAmbientExchange
public import Sheaf.Paper.LocalizingClosure
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
import Sheaf.Paper.IntegralFinitePullbackComposition
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import Sheaf.Paper.CartesianCoefficients
import Sheaf.Paper.CondensedModuleDerivedPushpull
import Sheaf.Paper.IntegralProperBaseChange
import Sheaf.Paper.LocalizingAdmissibleCoefficients
import Sheaf.Paper.UnboundedBaseChangeExtension
import Sheaf.Paper.UnboundedLocalizingPullback
import Sheaf.SixFunctors.ProperImageLocalizingProper
import Sheaf.Paper.IntegralModels
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs

/-!
# Integral proper base change on localizing categories

Source: blueprint main-20261015, sec-six-functors-basics/sk-thm-sf-pf-adic,
Integral proper base change on localizing categories
(blueprint: det-thm-sf-pf-adic-base-change).

Both endpoints belong to the target localizing closure, and the specified ambient
exchange is invertible on every object of the source closure. Since these are full
subcategories, this is precisely the isomorphism of functors between the two
localizing categories. The generators are Dbc, without imposing finite Tor
amplitude or completeness on the ambient closure.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-- Integral proper base change on the localizing closure of bounded constructibles.
Source: blueprint main-20261015, sk-thm-sf-pf-adic-base-change
(blueprint: det-thm-sf-pf-adic-base-change).

Proof plan:
1. In the standing positive-characteristic scheme setting, integral proper base
   change (det-thm-sfb-proper-base-change-integral, clauses 1 and 3) gives the
   specified ordinary exchange isomorphism on Dbc. Integral-models clause 3
   preserves its endpoints under inverse image, and proper-fp-permanence makes
   the base-changed vertical arrow proper.
2. The proper-image-localizing-proper and proper-base-change-unbounded-pullback
   nodes give exact sum-preserving restrictions of the four functors. The equality
   Dctf = Dbc in sk-lem-integral-models identifies their localizing closures.
3. Cartesian condensed coefficients identify pullbacks with the coefficients at
   the other corner. The full module tensor pullback is exact, so its left derived
   functor is its termwise functor (sk-def-sfb-derived-categories).
4. Under the ordinary upper/lower-star Hom bijections, the tensor pullback
   composition comparison is conjugate to the sectionwise direct-image pasting
   comparison (def-sfb-module-upper-star-comp and lower-star-comp).
5. Proetale-derived-pullback-composition identifies the canonical derived
   comparison on K-flat representatives with that termwise comparison. Hence
   condensedAmbientExchange is exactly the unit/comparison/counit exchange of
   the unbounded extension lemma, with the derived adjunctions of the same full
   module pullback and pushforward composites.
6. Apply det-proper-base-change-unbounded-extension to the integral coefficient
   ring. Step 1 supplies its generator hypothesis; sk-lem-integral-models gives
   Dctf = Dbc. The exchange is invertible throughout the stated closure, and
   step 2 places both endpoints in the target closure.
-/
theorem integralLocalizing_properBaseChange
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (E : Type) [Field E] [Algebra ℚ_[ℓ] E] [Algebra E (PadicAlgCl ℓ)]
    [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]
    {X' X Y' Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [X'.Over (Spec (.of k))] [Y'.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (X' ↘ Spec (.of k))] [QuasiCompact (X' ↘ Spec (.of k))]
    [IsSeparated (X' ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y' ↘ Spec (.of k))] [QuasiCompact (Y' ↘ Spec (.of k))]
    [IsSeparated (Y' ↘ Spec (.of k))]
    {p : X ⟶ Y} {g : Y' ⟶ Y} {p' : X' ⟶ Y'} {g' : X' ⟶ X}
    [p.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))]
    [p'.IsOver (Spec (.of k))] [g'.IsOver (Spec (.of k))]
    [IsProper p] (sq : ChosenCartesianSquare g' p' p g)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X)))
    (hK : CategoryTheory.localizingClosure
      (constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E) X) K) :
    CategoryTheory.localizingClosure
        (constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E) Y')
        (((lowerStar (Profinite.padicIntegersRingObj ℓ E) p).rightDerivedFunctor ⋙
          (upperStar (Profinite.padicIntegersRingObj ℓ E) g).leftDerivedFunctor).obj K) ∧
      CategoryTheory.localizingClosure
        (constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E) Y')
        (((upperStar (Profinite.padicIntegersRingObj ℓ E) g').leftDerivedFunctor ⋙
          (lowerStar (Profinite.padicIntegersRingObj ℓ E) p').rightDerivedFunctor).obj K) ∧
      IsIso ((condensedAmbientExchange (Profinite.padicIntegersRingObj ℓ E) sq).app K) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
