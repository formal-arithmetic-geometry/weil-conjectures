/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.KummerStratumScalarMaps
public import Sheaf.Paper.KummerCoefficientModels
public import Sheaf.Paper.KummerLocalSource
public import Sheaf.Paper.VectorPurityScalarSingle
public import Sheaf.Paper.CoefficientHeartStratificationDefs
public import Sheaf.CategoryTheory.CondensedDerivedInvariants
public import Sheaf.AlgebraicGeometry.CondensedHenselianLisseRigidity
public import Sheaf.Paper.KFlatScalarComparisonNormalization
public import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Sheaf.Paper.InternalScalarPullbackNormalization
import Sheaf.AlgebraicGeometry.NoetherianStratumDetection
import Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction
import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification

/-! # Detection of the geometric scalar mate by normalized Kummer stratum models

Source: main-20261015, direct-image stability proof, paragraph (3), normalized
Kummer stratum comparison criterion, geometric mate identification and detection.
(blueprint: lem-sfb-kummer-stratum-scalar-mate-detection).
All invariant functors and geometric functors are ordinary and unbounded.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing
open CategoryTheory.CondensedBar

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
variable (p : ℕ) {A : Type u} (I : Finset A)

/-- Supplied simultaneous models on an entire covering object. The square uses the
actual coefficient unit on both sides. Restriction means pulling back these maps
and using the canonical geometric and point composition comparisons.
Source: direct-image proof (3), normalized phi_(alpha,F)
(blueprint: lem-sfb-kummer-stratum-scalar-mate-detection). -/
structure KummerScalarStratumModel {W Y S : Scheme.{u}} (a : W ⟶ Y) (v : S ⟶ Y)
    (L : KummerModules (kummerCoefficientRing.{u} E.1).X W) where
  representation : PartialKummer.FiniteRepresentation E.1 (kummerStratumInertia p I)
  primeToEll : KummerFinitePrimeToEllImage p ℓ {i : A // i ∈ I} E.1 representation
  coefficients : KummerCoefficientModels ℓ E (kummerStratumInertia p I) representation
    (CondensedDerivedRestriction.scalarAction (kummerCoefficientMap ℓ E))
  finite : kummerOpenImage (kummerCoefficientRing.{u} E.1).X a v L ≅
    kummerStratumPointObject p I (kummerCoefficientRing.{u} E.1) S
      coefficients.finite.object
  closure : kummerOpenImage (kummerCoefficientRing.{u} (PadicAlgCl ℓ)).X a v
      (kummerOmegaModuleForRing ℓ E W L) ≅
    kummerStratumPointObject p I (kummerCoefficientRing.{u} (PadicAlgCl ℓ)) S
      coefficients.closureForRing
  normalized : kummerSourceScalarMapForRing ℓ E a v L ≫
      (kummerRestrictionForRing ℓ E S).map closure.hom =
    finite.hom ≫ kummerStratumPointUnit ℓ E p I S representation coefficients

/-- Restricted Theta written against the supplied whole-cover geometric model.
Source: direct-image proof (3), v^* Theta followed by phi_Omega
(blueprint: lem-sfb-kummer-stratum-scalar-mate-detection). -/
@[irreducible] def kummerModelTheta {W Y S : Scheme.{u}} (a : W ⟶ Y) (v : S ⟶ Y)
    (L : KummerModules (kummerCoefficientRing.{u} E.1).X W)
    (m : KummerScalarStratumModel ℓ E p I a v L) :
    (upperStar (kummerCoefficientRing.{u} (PadicAlgCl ℓ)).X v).mapDerivedCategory.obj
        ((kummerScalarForRing ℓ E Y).obj
          ((moduleObjectDerivedPushforward (kummerCoefficientRing.{u} E.1).X a).obj
            ((DerivedCategory.singleFunctor _ 0).obj L))) ⟶
      kummerStratumPointObject p I (kummerCoefficientRing.{u} (PadicAlgCl ℓ)) S
        m.coefficients.closureForRing :=
  (upperStar (kummerCoefficientRing.{u} (PadicAlgCl ℓ)).X v).mapDerivedCategory.map
      (kummerGeometricBeta ℓ E a L ≫
        (moduleObjectDerivedPushforward (kummerCoefficientRing.{u} (PadicAlgCl ℓ)).X a).map
          (kummerSingleForRing ℓ E W L)) ≫ m.closure.hom

/-- Scalar image of the finite model followed by point-pulled sigma and the
canonical geometric scalar/pullback comparison.
Source: direct-image proof (3), model arrow identified with v^* Theta
(blueprint: lem-sfb-kummer-stratum-scalar-mate-detection). -/
@[irreducible] def kummerModelSigma {W Y S : Scheme.{u}} (a : W ⟶ Y) (v : S ⟶ Y)
    (L : KummerModules (kummerCoefficientRing.{u} E.1).X W)
    (m : KummerScalarStratumModel ℓ E p I a v L) :
    (upperStar (kummerCoefficientRing.{u} (PadicAlgCl ℓ)).X v).mapDerivedCategory.obj
        ((kummerScalarForRing ℓ E Y).obj
          ((moduleObjectDerivedPushforward (kummerCoefficientRing.{u} E.1).X a).obj
            ((DerivedCategory.singleFunctor _ 0).obj L))) ⟶
      kummerStratumPointObject p I (kummerCoefficientRing.{u} (PadicAlgCl ℓ)) S
        m.coefficients.closureForRing :=
  kummerScalarOpenPull ℓ E v
      ((moduleObjectDerivedPushforward (kummerCoefficientRing.{u} E.1).X a).obj
        ((DerivedCategory.singleFunctor _ 0).obj L)) ≫
    (kummerScalarForRing ℓ E S).map m.finite.hom ≫
      kummerPointSigma ℓ E p I S m.representation m.coefficients

set_option backward.isDefEq.respectTransparency true in
/-- Normalized Kummer models identify the actual geometric scalar morphism and
jointly detect its invertibility on the whole scheme.
Source: main-20261015, direct-image proof (3), geometric mate-identification and
finite closed-depth detection (blueprint: lem-sfb-kummer-stratum-scalar-mate-detection).

Proof, following the five steps of the DAG node:
1. Work in section-ring modules through lem-sfb-internal-scalar-pullback-normalization.
Transpose Theta first scalarly and then geometrically. Compatibility of restriction
with the geometric adjunction (lem-weil-pbc-ring-sheaf-change-adjunction) identifies
its transpose with direct image of the actual coefficient unit. The unit equation
of lem-sfb-kflat-scalar-comparison-normalization and naturality of the scalar unit
cancel the pullback comparison; the geometric counit identity gives the claim.
The scalar-single adjunct defining iota makes this unit precisely x maps to 1 tensor x.
2. Pull back this identity along v. The scalar/pullback comparison preserves the unit,
so the scalar transpose of the restricted Theta is pullback of that unit-induced
image. The composition law makes restriction to a stratum and then a cover agree
with their composite.
3. The normalized square of the supplied models identifies this transpose with point
pullback of the actual invariant-unit map. The defining adjunct of sigma and the
point scalar comparison have this same transpose. Injectivity of the scalar
adjunction bijection proves the displayed equality of actual derived arrows.
4. The finite reduced SNC strata are disjoint and cover Y: each point belongs to the
unique subset of components containing it. Each is locally closed. Regularity
includes local Noetherianness; finite type over k gives quasi-compactness, hence Y
is Noetherian. This verifies all hypotheses of stratum detection.
5. If every sigma is invertible, its point pullback is invertible. The normalized
pullback comparisons are invertible, so step 3 makes every restricted Theta invertible.
Apply the unbounded arbitrary-ring clause of lem-weil-pbc-noetherian-stratum-detection
through the internal/section equivalence. Thus Theta is invertible. L is locally
finite free, so iota is invertible by the normalized K-flat scalar computation;
its direct image is invertible, and cancelling it gives invertibility of beta.
The empty subset, empty divisor, zero representation and empty scheme are included.
No geometric-stalk detection or constructibility of the direct image is used. -/
theorem kummer_stratum_scalar_mate_detection
    [Fact p.Prime] (_hpℓ : p ≠ ℓ) (k : Type u) [Field k] [CharP k p]
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (_hY : IsRegularScheme Y) (D : Y.IdealSheafData)
    (hD : IsStrictNormalCrossingsBoundary D)
    (L : KummerModules (kummerCoefficientRing.{u} E.1).X (tameBoundaryOpen D).toScheme)
    (_hL : IsLisseCoefficientModule (kummerCoefficientRing.{u} E.1).X L)
    (U : ∀ J : Finset (ULift.{u} (Fin hD.2.2.choose)),
      Scheme.Cover.{u} Scheme.proetalePrecoverage (ParameterStratum (kummerComponents D hD) J))
    (m : ∀ (J : Finset (ULift.{u} (Fin hD.2.2.choose))) (j : (U J).I₀),
      KummerScalarStratumModel ℓ E p J (tameBoundaryOpen D).ι
        ((U J).f j ≫ parameterStratumInclusion (kummerComponents D hD) J) L) :
    (∀ (J : Finset (ULift.{u} (Fin hD.2.2.choose))) (j : (U J).I₀),
      kummerModelTheta ℓ E p J (tameBoundaryOpen D).ι
          ((U J).f j ≫ parameterStratumInclusion (kummerComponents D hD) J) L (m J j) =
        kummerModelSigma ℓ E p J (tameBoundaryOpen D).ι
          ((U J).f j ≫ parameterStratumInclusion (kummerComponents D hD) J) L (m J j)) ∧
    ((∀ (J : Finset (ULift.{u} (Fin hD.2.2.choose))) (j : (U J).I₀),
      IsIso (kummerStratumSigma ℓ E p J (m J j).representation (m J j).coefficients)) →
      IsIso (kummerGeometricBeta ℓ E (tameBoundaryOpen D).ι L)) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
