/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Sheaf.Topology.ContinuousMapCondensedRingMap
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
/-!
# The all-continuous coefficient scalar mate without flatness

Source: blueprint main-20261015, direct-image proof paragraph (3), the prescribed beta.
(blueprint: def-sfb-all-continuous-scalar-mate).
The K-flat representative square fixes the canonical pullback comparison and its units.
No flatness of E to Omega, completion, or finite-subextension interpretation is assumed.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing
variable (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
/-- Postcomposition by the continuous inclusion of the finite subfield into the normed
algebraic closure. Both rings use all continuous maps on profinite sets.
Source: direct-image proof paragraph (3), coefficient convention
(blueprint: def-sfb-all-continuous-scalar-mate). -/
abbrev tameBoundaryScalarMap :
    Profinite.continuousMapRingObj.{u} E.1 ⟶
      Profinite.continuousMapRingObj (PadicAlgCl ℓ) :=
  (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
      (Profinite.continuousMapRingSheafMap E.1.subtype continuous_subtype_val)

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Ordinary unbounded derived scalar extension along the pulled-back continuous inclusion.
Source: direct-image proof paragraph (3), T_Z
(blueprint: def-sfb-all-continuous-scalar-mate). -/
abbrev tameBoundaryScalarExtension (Z : Scheme.{u}) :=
  (Mod.extendScalars (coefficientMap (tameBoundaryScalarMap ℓ E) Z)).leftDerivedFunctor

/-- The representative square defining the canonical scalar/pullback isomorphism.
Starting from Q(P), follow either the derived comparison and both counits, or the
scalar counit and exact pullback comparison. The ordinary arrow is precisely pullIso,
whose balanced tensor map preserves the insertion of 1, including in degree zero.
Source: direct-image proof paragraph (3), canonical tensor/pullback compatibility
(blueprint: def-sfb-all-continuous-scalar-mate). -/
def TameBoundaryScalarPullNormalized
    (δ : tameBoundaryScalarExtension ℓ E Y ⋙
        (upperStar (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) f).mapDerivedCategory ≅
      (upperStar (Profinite.continuousMapRingObj E.1) f).mapDerivedCategory ⋙
        tameBoundaryScalarExtension ℓ E X) : Prop :=
  ∀ P : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj E.1) Y)) ℤ,
    (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P →
    δ.hom.app (DerivedCategory.Q.obj P) ≫
      (tameBoundaryScalarExtension ℓ E X).map
        ((upperStar (Profinite.continuousMapRingObj E.1) f).mapDerivedCategoryFactorsh.hom.app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫
      (Mod.extendScalars
        (coefficientMap (tameBoundaryScalarMap ℓ E) X)).leftDerivedFunctorCounit.app
        (((upperStar (Profinite.continuousMapRingObj E.1) f).mapHomotopyCategory (.up ℤ)).obj
          ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫
      DerivedCategory.Qh.map
        ((Functor.mapHomotopyCategoryCompIso (pullIso (tameBoundaryScalarMap ℓ E) f)
          (.up ℤ)).hom.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫
      DerivedCategory.Qh.map
        ((Functor.mapHomotopyCategoryCompIso (Iso.refl
          (Mod.extendScalars (coefficientMap (tameBoundaryScalarMap ℓ E) Y) ⋙
            upperStar (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) f))
          (.up ℤ)).inv.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) =
    (upperStar (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) f).mapDerivedCategory.map
      ((Mod.extendScalars
        (coefficientMap (tameBoundaryScalarMap ℓ E) Y)).leftDerivedFunctorCounit.app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫
      (upperStar (Profinite.continuousMapRingObj (PadicAlgCl ℓ))
        f).mapDerivedCategoryFactorsh.hom.app
        (((Mod.extendScalars (coefficientMap (tameBoundaryScalarMap ℓ E) Y)).mapHomotopyCategory
          (.up ℤ)).obj ((HomotopyCategory.quotient _ (.up ℤ)).obj P))

/-- There is a unique comparison with the specified K-flat representative square.
Source: direct-image proof paragraph (3), canonical tensor/pullback compatibility
(blueprint: def-sfb-all-continuous-scalar-mate).

Proof: the underived pullIso is the conjugate of comapLowerStarIso and hence the
canonical balanced tensor comparison. Exact inverse image preserves flat modules and
K-flat complexes. On a K-flat representative P, scalar extension is computed by its
left-derived counit. Both routes through the ordinary pullIso therefore give
isomorphic representatives. Localize this representative comparison, using the
universal property of the total left derived functor. Its factorization identity
is the displayed square. K-flat resolutions are essentially surjective in the
localization and determine natural transformations there, proving uniqueness.
This does not use the flat-coefficient derivedComapLowerStarIso. -/
theorem tameBoundaryScalarPullIso_existsUnique :
    ∃! δ : tameBoundaryScalarExtension ℓ E Y ⋙
        (upperStar (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) f).mapDerivedCategory ≅
      (upperStar (Profinite.continuousMapRingObj E.1) f).mapDerivedCategory ⋙
        tameBoundaryScalarExtension ℓ E X,
      TameBoundaryScalarPullNormalized ℓ E f δ := by
  sorry

/-- The canonical scalar/pullback comparison selected from its unique representative
characterization; the selection determines the object up to equality, not just existence.
Source: direct-image proof paragraph (3), canonical tensor/pullback compatibility
(blueprint: def-sfb-all-continuous-scalar-mate). -/
def tameBoundaryScalarPullIso :
    tameBoundaryScalarExtension ℓ E Y ⋙
        (upperStar (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) f).mapDerivedCategory ≅
      (upperStar (Profinite.continuousMapRingObj E.1) f).mapDerivedCategory ⋙
        tameBoundaryScalarExtension ℓ E X :=
  (tameBoundaryScalarPullIso_existsUnique ℓ E f).exists.choose

/-- The prescribed beta is the adjunct of the canonical pullback comparison followed by
scalar extension of the direct-image counit. The exact module pullback is identified
with its total left derived functor by the published canonical comparison.
Source: direct-image proof paragraph (3), definition of beta
(blueprint: def-sfb-all-continuous-scalar-mate). -/
def tameBoundaryScalarComparison
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E.1) X))) :
    (tameBoundaryScalarExtension ℓ E Y).obj
        ((moduleObjectDerivedPushforward (Profinite.continuousMapRingObj E.1) f).obj K) ⟶
      (moduleObjectDerivedPushforward (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) f).obj
        ((tameBoundaryScalarExtension ℓ E X).obj K) :=
  (((derivedUpperStarLowerStarAdjunction
      (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) f).ofNatIsoLeft
        (leftDerivedUpperStarIsoMapDerivedCategory
          (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) f)).homEquiv _ _)
    ((tameBoundaryScalarPullIso ℓ E f).hom.app
        ((moduleObjectDerivedPushforward (Profinite.continuousMapRingObj E.1) f).obj K) ≫
      (tameBoundaryScalarExtension ℓ E X).map
        (((derivedUpperStarLowerStarAdjunction (Profinite.continuousMapRingObj E.1) f).ofNatIsoLeft
          (leftDerivedUpperStarIsoMapDerivedCategory
            (Profinite.continuousMapRingObj E.1) f)).counit.app K))

end AlgebraicGeometry.ProEtale.CondensedRing
