/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A2
-/
module

public import Sheaf.AlgebraicGeometry.EllAdicProperLocalizingPushforward
import Sheaf.AlgebraicGeometry.CondensedFieldLfpLocalTriviality
import Sheaf.Paper.CondensedQbarLfpLocalTriviality
import Sheaf.Paper.IntegralLfpLocalTorsionCharts
import Sheaf.Paper.IntegralLfpLocallyFreeResolution
import Sheaf.AlgebraicGeometry.BoundedConstructibleLocalizingClosure
import Sheaf.AlgebraicGeometry.EllAdicCondensedCoefficient
import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
import Sheaf.AlgebraicGeometry.FiniteConstantLocalModel
import Sheaf.Paper.CondensedConstantConstructibility
import Sheaf.Paper.IntegralLfpConstantModelComparison
import Sheaf.Paper.LocalizingAdmissibleCoefficients
import Sheaf.Paper.LocalizingClosureCtfEqualsBc
import Sheaf.Paper.LocalizingExceptionalAdjoint
import Sheaf.Paper.ProperExceptionalRestriction
import Sheaf.Paper.RationalExceptionalRestriction
import Sheaf.SixFunctors.IntegralBrownAdjoint
import Sheaf.SixFunctors.IntegralExceptionalRestriction

/-! # Constructibility of the cohomology of the localizing exceptional object
(blueprint: lem-sfb-adic-localizing-exceptional-cohomology)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (ℓ : ℕ) [Fact ℓ.Prime]
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {Z Y : Over (Spec (.of k))}
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (g : Z ⟶ Y) [IsProper g.left]
  (hΛ : IsEllAdicCoefficient ℓ Λ inferInstance)

/-- Every cohomology object of the supplied localizing right adjoint on a bounded
constructible input is constructible.

Source: blueprint `sk-thm-existence` (4), `det-existence-restriction.proof.md`, Part (2).
Proof: compare local finite-presentation charts with the field, algebraic-closure, and
integral adic models using the cited local triviality and resolution theorems.  The smooth
and closed local restriction calculations preserve constructibility; finite affine descent
and uniqueness of right adjoints identify the result with the supplied `G`.
(blueprint: lem-sfb-adic-localizing-exceptional-cohomology)
-/
theorem ellAdic_localizing_rightAdjoint_obj_homology_constructible
    (G : (boundedConstructibleLocalizingClosure Λ Y.left).FullSubcategory ⥤
      (boundedConstructibleLocalizingClosure Λ Z.left).FullSubcategory)
    (adj : ellAdicLocalizingLowerStar Λ ℓ g hΛ ⊣ G)
    (K : (boundedConstructible (condensedRingObj Λ Y.left)).FullSubcategory) :
    ∀ n : ℤ, IsConstructibleModuleObject (condensedRingObj Λ Z.left)
      ((DerivedCategory.homologyFunctor _ n).obj
        ((G.obj ((boundedConstructibleToLocalizing Λ Y.left).obj K)).obj)) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
