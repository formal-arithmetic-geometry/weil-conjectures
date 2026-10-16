/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Sheaf.SixFunctors.ProEtale.BaseChange.SmoothBaseChangeComparisons

/-! # Compatibility of canonical derived site comparisons -/

@[expose] public section

universe u
open CategoryTheory Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale
variable (Λ : Type (u + 1)) [CommRing Λ]

/-- The direct-image comparison is the counit mate of the specified pullback comparison.
Source: Stacks Project, Tag 0B65; blueprint transport proof, step 2.
(blueprint: stage3-proetale-comparison-counit)

Proof: the underived direct-image comparison is the inverse mate of the restriction
comparison. The pullback comparison is the adjoint conjugate of the same restriction
comparison. The mate counit identity therefore holds on sheaves. Apply it to complexes;
the defining unit factorization of rightDerivedFunctorPlusBaseChange and uniqueness of
right derived transformations give the identity on D+. The Plus-to-unbounded compatibility
isomorphisms transport the two counits to the indicated unbounded counit. This identifies
these fixed maps, without choosing a new direct-image isomorphism. -/
theorem comparison_counit {U V : Scheme.{u}} (f : U ⟶ V)
    [QuasiCompact f] [QuasiSeparated f]
    (K : DerivedCategory.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (leftDerivedUpperStarComparisonIso f Λ).hom.app
        (R+(Etale.lowerStar (ModuleCat.{u + 1} Λ) f).obj K) ≫
      L(ProEtale.upperStar (ModuleCat.{u + 1} Λ) f).map
        ((rightDerivedLowerStarComparisonIso' f (ModuleCat.{u + 1} Λ)).hom.app K) ≫
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).counit.app
        ((DerivedCategory.Plus.ι ⋙ D(ν^*(U)[ModuleCat.{u + 1} Λ])).obj K) =
    (DerivedCategory.Plus.ι ⋙ D(ν^*(U)[ModuleCat.{u + 1} Λ])).map
      ((Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) f).counit.app K) := by
  sorry
end AlgebraicGeometry.ProEtale
