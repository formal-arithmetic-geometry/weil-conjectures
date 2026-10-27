/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J6
-/
module

public import Sheaf.Paper.SixFunctorOperationDatumStages
public import Sheaf.Paper.IdentityFactorFixedSupport

/-! # Coefficient realization respects the two identity-factor unit maps -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 2048
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
namespace WeilConjectures.FixProjectionCompactification

attribute [local implicit_reducible] sfIntrinsicCompactSupport sfAmbientCompactSupportCandidate
attribute [local irreducible] DerivedCategory instCategoryDerivedCategory
  HasDerivedCategory.ofIsGrothendieckAbelian HasDerivedCategory.ofHasKInjectiveResolutions
  sfIntrinsicDerivedEquivalence sfIntrinsicCompactSupportComparison
  Functor.mapDerivedCategory Functor.rightDerivedFunctor

/-- The coefficient comparison commutes with the independent identity-factor unit maps.
There is no etale-origin condition or geometric composition comparison in this equation.

Source: def-sf-operation-stages, proper/open normalizations; the section and K-injective
normalizations of sfIntrinsicDerivedDirectImageComparison.
(blueprint: lem-sf-identity-factor-coefficient-comparison).

Proof: expand the three compact-support comparisons into their open and direct-image
comparisons. For the proper compactification, the open comparison followed by the
realization of the fixed-scalar identity open unit is the intrinsic identity open unit;
this follows by uniqueness of the transported left adjoint and exact-functor descent.
For the open compactification, the direct-image comparison followed by realization of
the fixed-scalar identity direct-image unit is the intrinsic identity direct-image unit.
Indeed both are right-adjoint comparisons for the same realized identity inverse image;
the section normalization and K-injective normalization identify their underived and
derived mates. Naturality of the proper direct-image comparison moves the open identity
map into proper image. Cancel the intermediate realization units. The surviving factors
are exactly the open and direct-image comparison for the actual pair (i,p). These
arguments apply to arbitrary inputs, including zero and empty schemes. -/
theorem identityFactorCoefficientComparison (A : Type u) [CommRing A] [Finite A]
    {X Z Y : Scheme.{u}} (i : X ⟶ Z) (p : Z ⟶ Y)
    [IsOpenImmersion i] [IsProper p]
    (M : DerivedCategory
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} A)))) :
    (sfIntrinsicCompactSupport (Compactification.ofIsProper p) A).map
        ((sfIntrinsicCompactSupportComparison A
          (Compactification.ofIsOpenImmersion i)).hom.app M) ≫
      (sfIntrinsicCompactSupportComparison A (Compactification.ofIsProper p)).hom.app
        ((sfFixedCompactSupport A (Compactification.ofIsOpenImmersion i)).obj M) ≫
      (sfIntrinsicDerivedEquivalence Y A).functor.map
        ((identityFactorFixedIso (ULift.{u + 1} A) i p).hom.app M) =
    (sixFunctorProperCandidateIso A p).hom.app
        ((sfIntrinsicCompactSupport (Compactification.ofIsOpenImmersion i) A).obj
          ((sfIntrinsicDerivedEquivalence X A).functor.obj M)) ≫
      (proEtaleConstantDerivedDirectImage p A).map
        ((sixFunctorOpenCandidateIso A i).hom.app
          ((sfIntrinsicDerivedEquivalence X A).functor.obj M)) ≫
      (sfIntrinsicCompactSupportComparison A (identityFactorPair i p)).hom.app M := by sorry

end WeilConjectures.FixProjectionCompactification
