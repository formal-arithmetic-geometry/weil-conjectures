/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NO
-/
module

public import Sheaf.Paper.ProEtaleScalarMateNormalization
import Sheaf.AlgebraicGeometry.ProjectionComparisonEtaleProEtale
public import Sheaf.Paper.FiniteCompactSupportScalarTransport
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModuleIntrinsicComparison
public import Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction
public import Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.AlgebraicGeometry.ProperBasic
import Sheaf.SixFunctors.GeometricInverseImageConstantModule
import Sheaf.AlgebraicGeometry.ProperTorsionProjectionFormula

/-! # Proper scalar comparison on bounded etale origins

Source: Stacks Project, Tag 0F0G, lemma-projection-formula-proper-mod-n;
Tags 09A6, 0E48 and 0B56 for the canonical comparison and scalar mate.
(blueprint: lem-fix-proper-etale-origin-scalar-isomorphism).

## Main definitions and statement

- `properOriginTensorIso`: canonical constant-B tensor comparison.
- `properOriginMateIso`: the specified bounded-below direct-image mate.
- `properOriginEtaleProjection`: the actual etale projection arrow.
- `properEtaleOriginScalarIsomorphism`: invertibility and the restriction formula.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 2000
universe u v w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
  Etale.scalarTensorIso Scheme.completedAdicDerivedChange

/-- The identity-on-sections change from the counit-adjoint coefficient map to
its original constant-section map. Source: Stacks 03D1 and 0H7J
(blueprint: lem-fix-proper-etale-origin-scalar-isomorphism). -/
@[irreducible] def properOriginPushIso (A : Type u) [CommRing A]
    {Z Y : Scheme.{u}} (p : Z ⟶ Y) :
    directImageConstantPush A p ≅ Scheme.proEtaleConstantDerivedDirectImage p A :=
  Functor.rightDerivedFunctorNatIso
    (SheafOfModules.pushforwardCongr
      (congrArg (fun g : Scheme.proEtaleConstantRing Y A ⟶
          (Scheme.proEtaleSheafDirectImage p CommRingCat.{u + 1}).obj
            (Scheme.proEtaleConstantRing Z A) ↦
        (sheafCompose (Scheme.ProEt.topology Y)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map g)
        ((Scheme.proEtaleSheafAdjunction p CommRingCat.{u + 1}).homEquiv _ _
          |>.apply_symm_apply (Scheme.proEtaleCoefficientDirectImageMap p A))))

/-- Restriction commutes with the specified comparison inverse image, with the
identity-on-sections realization normalization. Source: Stacks 03D2 and 00YV
(blueprint: lem-fix-proper-etale-origin-scalar-isomorphism). -/
@[irreducible] def properOriginRestrictionIso
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (T : Scheme.{u}) :
    finiteCoefficientIntrinsicDerivedComparison T B ⋙
        (scalarMateRestriction φ T).mapDerivedCategory ≅
      Sheaf.derivedRestrictScalars T.smallEtaleTopology (RingHom.ulift.{u + 1, u + 1, u, u} φ) ⋙
        finiteCoefficientIntrinsicDerivedComparison T A :=
  Functor.isoWhiskerRight (Scheme.FiniteCompactScalar.intrinsicSiteFunctorIso B T) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (Functor.mapDerivedCategorySquareIso (Scheme.sfRealizationRestriction T φ)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (pbcDerivedComparisonRestrict T
        (R := ULift.{u + 1, u} A) (S := ULift.{u + 1, u} B)
        (RingHom.ulift.{u + 1, u + 1, u, u} φ)) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Scheme.FiniteCompactScalar.intrinsicSiteFunctorIso A T).symm

/-- Ordinary etale tensor with the constant A-module B in degree zero.
This uses the existing tensor and coefficient, without changing either.
Source: Stacks 0F0G (blueprint: lem-fix-proper-etale-origin-scalar-isomorphism). -/
def properOriginEtaleTensor
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u})
    (M : Etale.DerivedCategoryModule A T) : Etale.DerivedCategoryModule A T :=
  ((Etale.derivedTensor (ModuleCat.{u + 1} A) T).obj M).obj
    (Etale.scalarCoefficient φ T)

/-- Image of the canonical scalar/tensor component under a functor. Stating this
at general coefficients keeps specialization to lifted rings small.
Source: Stacks 06YY (blueprint: lem-fix-proper-etale-origin-scalar-isomorphism). -/
@[irreducible] def properOriginScalarTensorImage
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) {C : Type v} [Category.{w} C]
    (F : Etale.DerivedCategoryModule A T ⥤ C)
    (M : Etale.DerivedCategoryModule A T) {X : C}
    (e : F.obj ((Sheaf.derivedRestrictScalars T.smallEtaleTopology φ).obj
      ((Etale.scalarExtension φ T).obj M)) ≅ X) :=
  F.mapIso ((Etale.scalarTensorIso φ T).app M).symm ≪≫ e

/-- The canonical comparison F(M tensor B) = U S F(M). It is the tensor
comparison specialized to the constant coefficient B, expressed using the
representative-normalized scalar/tensor identifications. All its factors are
published normalized comparisons, including the scalar-adjunction mate.
Source: Stacks 06YY, 07A4 and 0D6D
(blueprint: lem-fix-proper-etale-origin-scalar-isomorphism). -/
@[irreducible] def properOriginTensorIso
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (T : Scheme.{u})
    (M : Etale.DerivedCategoryModule (ULift.{u + 1, u} A) T) :=
  let e₂ := (properOriginRestrictionIso φ T).symm.app
    ((Etale.scalarExtension (A := ULift.{u + 1, u} A) (B := ULift.{u + 1, u} B)
      (RingHom.ulift.{u + 1, u + 1, u, u} φ) T).obj M)
  let e₃ := (scalarMateRestriction φ T).mapDerivedCategory.mapIso
    ((Scheme.FiniteCompactScalar.siteScalarIso φ T).symm.app M)
  properOriginScalarTensorImage
    (A := ULift.{u + 1, u} A) (B := ULift.{u + 1, u} B)
    (RingHom.ulift.{u + 1, u + 1, u, u} φ) T
    (finiteCoefficientIntrinsicDerivedComparison T A) M (e₂ ≪≫ e₃)

/-- The fixed counit mate on D+, included in the unbounded categories by the
standard endpoint compatibilities. Source: Stacks 09A6
(blueprint: lem-fix-proper-etale-origin-scalar-isomorphism). -/
@[irreducible] def properOriginFixedMateIso (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z Y : Scheme.{u}} (p : Z ⟶ Y) [QuasiCompact p] [QuasiSeparated p]
    (K : DerivedCategory.Plus (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj
        ((Etale.lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctor.obj K.obj) ≅
      (lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctor.obj
        ((comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategory.obj K.obj) :=
  (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.mapIso
      ((Etale.lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctorPlusCompatibility.app
        K).symm ≪≫
    ((comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategoryPlusCompatibility.app
      ((Etale.lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctorPlus.obj K)).symm ≪≫
    DerivedCategory.Plus.ι.mapIso
      ((@asIso _ _ _ _ (fixedComparisonDirectImageMatePlus A p)
        (isIso_fixedComparisonDirectImageMatePlus A p)).app K) ≪≫
    (lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctorPlusCompatibility.app
      ((comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategoryPlus.obj K) ≪≫
    (lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctor.mapIso
      ((comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategoryPlusCompatibility.app K)

/-- The same specified mate in intrinsic constant-ring modules. The additional
factors only change coefficient presentations and their section-normalized direct
images; they do not choose another mate. Source: Stacks 09A6 and 00YV
(blueprint: lem-fix-proper-etale-origin-scalar-isomorphism). -/
@[irreducible] def properOriginMateIso (A : Type u) [CommRing A] [Finite A]
    {Z Y : Scheme.{u}} (p : Z ⟶ Y) [QuasiCompact p] [QuasiSeparated p]
    (K : DerivedCategory.Plus
      (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) :
    (finiteCoefficientIntrinsicDerivedComparison Y A).obj
        ((Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) p).rightDerivedFunctor.obj
          K.obj) ≅
      (directImageConstantPush A p).obj
        ((finiteCoefficientIntrinsicDerivedComparison Z A).obj K.obj) :=
  (Scheme.FiniteCompactScalar.intrinsicSiteFunctorIso A Y).app _ ≪≫
    (Scheme.sfIntrinsicDerivedEquivalence Y A).functor.mapIso
      (properOriginFixedMateIso (ULift.{u + 1, u} A) p K) ≪≫
    (Scheme.sfIntrinsicDerivedDirectImageComparison p A).symm.app _ ≪≫
    (Scheme.proEtaleConstantDerivedDirectImage p A).mapIso
      ((Scheme.FiniteCompactScalar.intrinsicSiteFunctorIso A Z).app K.obj).symm ≪≫
    (properOriginPushIso A p).symm.app _

/-- The actual etale projection arrow followed only by the canonical identification
p*B_Y = B_Z. Source: Stacks 0B56 and 0F0G
(blueprint: lem-fix-proper-etale-origin-scalar-isomorphism). -/
@[irreducible] def properOriginEtaleProjection
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {Z Y : Scheme.{u}} (p : Z ⟶ Y)
    (M : Etale.DerivedCategoryModule A Z) :
    properOriginEtaleTensor φ Y
        ((Etale.lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctor.obj M) ⟶
      (Etale.lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctor.obj
        (properOriginEtaleTensor φ Z M) :=
  ((Etale.rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) p).app M).app
      (Etale.scalarCoefficient φ Y) ≫
    (Etale.lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctor.map
      (((Etale.derivedTensor (ModuleCat.{u + 1} A) Z).obj M).map
        (Etale.scalarCoefficientPullbackIso φ p).hom)

/-- The specified B-linear proper scalar mate is invertible at a bounded-below
etale origin whose tensor with B is also bounded below. The equality is the
precise conjugation formula after the canonical restriction/direct-image
identification. The two b factors are the recorded counit mates at E_e and H_e;
q = properOriginTensorIso is the constant-B tensor comparison expressed through
US = tensor B. No flatness, finite Tor dimension, Noetherian hypothesis or bound
on the tensor of Rp_* E_e is imposed.

Source: Stacks Project, etale-cohomology.tex, Tag 0F0G,
lemma-projection-formula-proper-mod-n; proetale.tex, Tag 09A6;
sites-cohomology.tex, Tags 0E48 and 0B56.
(blueprint: lem-fix-proper-etale-origin-scalar-isomorphism).

Proof:
1. Properness implies quasi-compactness and quasi-separatedness by
pqf-lem-proper-basic. Geometric inverse image preserves the constant module B
by lem-sfb-geometric-inverse-image-constant-module. Thus the two boundedness
hypotheses here are exactly those on K and L in
lem-sfb-projection-comparison-etale-proetale.
2. The additive group of finite A has positive exponent, so A is a torsion ring.
Apply lem-kun-0f0g to E_e and the degree-zero constant module B_Y. It makes
properOriginEtaleProjection invertible; its last factor is just p*B_Y = B_Z.
No flatness or Tor bound is required by that theorem.
3. Specialize lem-sfb-projection-comparison-etale-proetale to these inputs.
The tensor comparisons are those of lem-weil-pbc-ringed-topoi-derived-tensor-pullback;
the two direct-image comparisons are the actual counit mates from
lem-weil-pbc-comparison-direct-image-canonical-mate. Its equation is
R_p(h) b_H F_Y(pi_e) = pi_p (b_E tensor 1) t_Y.
4. Compose with t_Y inverse and b_E inverse tensor 1. This gives the displayed
conjugation formula. Its factors are invertible: the tensor comparisons by
construction, b_E and b_H by the two D+ hypotheses, and pi_e by step 2.
The helpers merely implement coefficient realization and the canonical
US = tensor B identifications; their section and representative normalizations
identify their q factors with these tensor comparisons.
5. lem-fix-proetale-scalar-mate-normalization identifies the restriction of the
actual directImageScalarComparison with this same pi_p, using the canonical
restriction/direct-image comparison scalarMateRestrictionPush. Hence its
restriction equals the displayed composite. Exact coefficient restriction
reflects isomorphisms by lem-weil-pbc-ring-sheaf-change-adjunction, so the
specified B-linear mate itself is invertible. -/
theorem properEtaleOriginScalarIsomorphism
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {Z Y : Scheme.{u}} (p : Z ⟶ Y) [IsProper p]
    (E : DerivedCategory.Plus
      (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A))))
    (hH : ∃ n : ℤ,
      (properOriginEtaleTensor (RingHom.ulift.{u + 1, u + 1, u, u} φ) Z E.obj).IsGE n) :
    IsIso ((directImageScalarComparison φ p).app
      ((finiteCoefficientIntrinsicDerivedComparison Z A).obj E.obj)) ∧
    (scalarMateRestriction φ Y).mapDerivedCategory.map
        ((directImageScalarComparison φ p).app
          ((finiteCoefficientIntrinsicDerivedComparison Z A).obj E.obj)) ≫
      (scalarMateRestrictionPush φ p).hom.app
        ((directImageScalarExtension φ Z).obj
          ((finiteCoefficientIntrinsicDerivedComparison Z A).obj E.obj)) =
    (directImageScalarExtension φ Y ⋙ (scalarMateRestriction φ Y).mapDerivedCategory).map
        (properOriginMateIso A p E).inv ≫
      (properOriginTensorIso φ Y
        ((Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) p).rightDerivedFunctor.obj
          E.obj)).inv ≫
      (finiteCoefficientIntrinsicDerivedComparison Y A).map
        (properOriginEtaleProjection (RingHom.ulift.{u + 1, u + 1, u, u} φ) p E.obj) ≫
      (properOriginMateIso A p
        ⟨properOriginEtaleTensor (RingHom.ulift.{u + 1, u + 1, u, u} φ) Z E.obj, hH⟩).hom ≫
      (directImageConstantPush A p).map (properOriginTensorIso φ Z E.obj).hom := by
  sorry

end AlgebraicGeometry.ProEtale
