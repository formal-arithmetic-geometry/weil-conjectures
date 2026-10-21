/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N8
-/
module

public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.Paper.ConstantModelTorAmplitude
public import Sheaf.SixFunctors.ProEtale.DerivedCompletion
public import Sheaf.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit
public import Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Sheaf.Paper.CompletedDirectImageLimits
import Sheaf.Paper.AdicCoefficientDatum
import Sheaf.CategoryTheory.DerivedCategory.StandardQuotientsPerfect
import Sheaf.AlgebraicGeometry.ConstructibleProEtaleComparison
import Sheaf.AlgebraicGeometry.OpenDirectImageFiniteCoefficients
import Sheaf.AlgebraicGeometry.ComparisonDirectImage
import Sheaf.Paper.CartesianCoefficients
import Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction
import Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
import Sheaf.Paper.DerivedNakayamaResolution
import Sheaf.Paper.IntegralModels

/-!
# Integral open direct image preserves constructibility

Source: blueprint main-20261015, sec-six-functors-basics/sk-thm-sf-pf-adic,
`sk-thm-sf-pf-adic-open.md` and its proof; Stacks Tags 099L, 09A6 and 09C1
(blueprint: det-thm-sf-pf-adic-open).

The residue comparison is specified by its adjunction equation, rather than by an
unconstrained isomorphism of objects. The coefficient-change pullback square used in that
equation is defined for the nonflat residue quotient. All derived categories below are
ordinary derived categories of internal modules over the continuous condensed coefficients.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.IntegralOpenDirectImage

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  {U X : Scheme.{u}} (j : U ⟶ X)

/-- The canonical pullback/reduction transformation, obtained by transposing the inverse
of the exact restriction-of-scalars pullback square along the two derived scalar
adjunctions. No flatness of O_E -> F_E is assumed.
Source: blueprint open-direct-image proof, Reduction paragraph and the coefficient square
(blueprint: det-thm-sf-pf-adic-open). -/
def reductionPullbackMap :
    (CondensedRing.upperStar (DerivedNakayama.integerRing l E) j).mapDerivedCategory ⋙
        AdicCompletion.derivedReduction l E U 0 ⟶
      AdicCompletion.derivedReduction l E X 0 ⋙
        (CondensedRing.upperStar (DerivedNakayama.quotientRing l E 1) j).mapDerivedCategory :=
  ((mateEquiv
    (Mod.derivedExtendMapDerivedCategoryAdjunction (AdicCompletion.quotient l E X 0))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (AdicCompletion.quotient l E U 0))).symm
      (TwoSquare.mk _ _ _ _
        (CondensedRing.derivedComapUpperStarIso (DerivedNakayama.reductionRing l E 1) j).inv)
    ).natTrans

/-- Integral open direct image is derived complete, commutes canonically with residue
reduction, and is bounded constructible; integral Dbc equals its finite-Tor subcategory.
The unique comparison is characterized by the usual pullback/reduction square and the
two geometric counits. This is the canonical coefficient-change (projection-formula) map.
Source: blueprint main-20261015, `sk-thm-sf-pf-adic-open.md` and its proof; Stacks
Tags 099L, 09A6, 09C1 (blueprint: det-thm-sf-pf-adic-open).

Proof:
1. Apply sk-lem-integral-models on U: K is complete and its residue reduction is bounded
   constructible of etale origin. The extension-integers DVR theorem gives a finite residue
   field of characteristic l, which is invertible in k.
2. det-pe-derived-nakayama-resolution identifies reduction with the uniformizer cone.
   The right derived module pushforward is triangulated and O_E-linear. The canonical
   finite-projection clause of prop-weil-pbc-direct-image-limits, with the finite perfect
   quotients of lem-weil-pbc-standard-quotients-perfect, identifies the residue comparison
   and all tower transitions. Its adjunction equation is the one displayed below.
3. Apply the direct-image/derived-limit comparison to K's reduction tower. The completion
   unit compatibility in that same node identifies the composite with the completion unit
   of Rj_*K, proving completeness (sk-def-pe-derived-completion).
4. Descend the residue reduction to the etale site by sk-thm-pe-constructible-comparison.
   cor-fin-deligne-open-finite-coefficients makes its etale open direct image bounded
   constructible, since the residue field is finite and killed by l.
5. An open immersion has identity diagonal, so quasi-compactness makes j qcqs.
6. prop-weil-pbc-comparison-direct-image identifies the residue pro-etale direct image
   with the pullback of the etale one; constructible comparison preserves its finiteness.
7. sk-prop-sfb-cartesian-coefficients and sk-def-sfb-coefficient-change give the compatible
   integral/residue ring square. lem-weil-pbc-ring-sheaf-change-adjunction compares the
   direct images after restriction, without imposing flatness on the residue quotient.
8. Exact scalar restriction (lem-weil-restriction-of-scalars-exact) identifies cohomology
   of these two residue complexes as integral modules.
9. The coefficient resolution makes O_E -> F_E an epimorphism. Lift residue scalars
   locally to integral scalars; integral linearity then gives residue linearity of the
   cohomology isomorphisms and their inverses. The actual reduction is bounded constructible.
10. Constructible comparison gives etale origin for that actual residue reduction.
11. Apply the residue criterion sk-lem-integral-models on X. It gives bounded
    constructibility and the equality of integral bounded constructible and finite-Tor
    subcategories. This proves all clauses, including the empty-open and identity cases. -/
theorem integral_open_direct_image
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
    [U.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [j.IsOver (Spec (.of k))]
    [IsOpenImmersion j] [QuasiCompact j]
    (K : DerivedCategory (AdicCompletion.Modules l E U))
    (hK : constantModelBoundedConstructible (DerivedNakayama.integerRing l E) U K) :
    IsDerivedComplete l E X
        ((CondensedRing.moduleObjectDerivedPushforward (DerivedNakayama.integerRing l E) j).obj
          K) ∧
      (∃! c :
          (AdicCompletion.derivedReduction l E X 0).obj
              ((CondensedRing.moduleObjectDerivedPushforward
                (DerivedNakayama.integerRing l E) j).obj K) ⟶
            (CondensedRing.moduleObjectDerivedPushforward
              (DerivedNakayama.quotientRing l E 1) j).obj
                ((AdicCompletion.derivedReduction l E U 0).obj K),
        IsIso c ∧
          (reductionPullbackMap l E j).app
              ((CondensedRing.moduleObjectDerivedPushforward
                (DerivedNakayama.integerRing l E) j).obj K) ≫
            (CondensedRing.upperStar (DerivedNakayama.quotientRing l E 1) j).mapDerivedCategory.map
              c ≫
            ((CondensedRing.derivedUpperStarLowerStarAdjunction
                (DerivedNakayama.quotientRing l E 1) j).ofNatIsoLeft
                  (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
                    (DerivedNakayama.quotientRing l E 1) j)).counit.app
              ((AdicCompletion.derivedReduction l E U 0).obj K) =
            (AdicCompletion.derivedReduction l E U 0).map
              (((CondensedRing.derivedUpperStarLowerStarAdjunction
                  (DerivedNakayama.integerRing l E) j).ofNatIsoLeft
                    (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
                      (DerivedNakayama.integerRing l E) j)).counit.app K)) ∧
      constantModelBoundedConstructible (DerivedNakayama.integerRing l E) X
        ((CondensedRing.moduleObjectDerivedPushforward (DerivedNakayama.integerRing l E) j).obj
          K) ∧
      constantModelBoundedConstructible (DerivedNakayama.integerRing l E) X =
        (constantModelBoundedConstructible (DerivedNakayama.integerRing l E) X ⊓
          DerivedCategory.finiteTorAmplitude (AdicCompletion.Modules l E X)) := by
  sorry

end AlgebraicGeometry.ProEtale.IntegralOpenDirectImage
