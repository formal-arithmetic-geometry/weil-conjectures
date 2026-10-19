/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P6
-/
module

public import Sheaf.Paper.WitnessCompatibility
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.Paper.FamilyWitnessCompatibilityFromOrigins
import Sheaf.Paper.EtaleProEtaleScalarMate
import Sheaf.AlgebraicGeometry.FiniteCoefficientRealizationDirectImage
import Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit
import Sheaf.SecSmoothPurity.ProperFiniteCoefficientExtension
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import Mathlib.CategoryTheory.EssentialImage

/-! # Witness compatibility for one proper direct-image family

Source: blueprint amplification step (b), main-20261015; Stacks Tags 0GL6 and 09C7.
(blueprint: lem-weil-pbc-proper-family-witness-compatibility).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale
variable {X Y : Scheme.{u}} (f : X ⟶ Y)

@[irreducible] private def realizationDirectImage (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] :
    (finiteCoefficientRealization X Λ).mapDerivedCategory ⋙
        finiteCoefficientDerivedDirectImage f Λ ≅
      (lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctor ⋙
        (finiteCoefficientRealization Y Λ).mapDerivedCategory :=
  Functor.isoWhiskerRight
      (finiteCoefficientRealization X Λ).rightDerivedFunctorIsoMapDerivedCategory.symm _ ≪≫
    (Functor.rightDerivedFunctorCompIso _ _).symm ≪≫
    Functor.rightDerivedFunctorNatIso
      (finiteCoefficientRealization_directImage f Λ).some ≪≫
    Functor.rightDerivedFunctorCompMapDerivedCategoryIso _ _

@[irreducible] private def directImageCoordinates {A : Type (u + 1)} [CommRing A]
    (d : Scheme.AdicCoefficientDatum A) (n : ℕ) :
    pbcWitnessDirectImage f d n ≅
      (lowerStar (ModuleCat.{u + 1} (PbcQuotient d n)) f).rightDerivedFunctor := by
  let Λ := PbcQuotient d n
  let R := finiteCoefficientRealization Y Λ
  let Ri := finiteCoefficientUnrealization Y Λ
  let D := (lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctor
  letI : R.asEquivalence.functor.Additive := finiteCoefficientRealization_additive Y Λ
  exact Functor.isoWhiskerRight (realizationDirectImage f Λ) Ri.mapDerivedCategory ≪≫
    Functor.associator D R.mapDerivedCategory Ri.mapDerivedCategory ≪≫
    Functor.isoWhiskerLeft D R.asEquivalence.mapDerivedCategory.unitIso.symm ≪≫
    D.rightUnitor

@[irreducible] private def directImageOrigin {A : Type (u + 1)} [CommRing A]
    (d : Scheme.AdicCoefficientDatum A) [IsProper f]
    (P : PbcWitnessedInputTowers X d) (n : ℕ) :
    (comparisonUpperStar (ModuleCat.{u + 1} (PbcQuotient d n)) Y).mapDerivedCategory.obj
      ((Etale.lowerStar (ModuleCat.{u + 1} (PbcQuotient d n)) f).rightDerivedFunctorPlus.obj
        (P.obj.origin n).L).obj ≅
      (pbcWitnessDirectImage f d n).obj (P.obj.K n) := by
  let Λ := PbcQuotient d n
  exact (comparisonUpperStar (ModuleCat.{u + 1} Λ) Y).mapDerivedCategory.mapIso
      (((Etale.lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctorPlusCompatibility).app
        (P.obj.origin n).L) ≪≫
    directImageComparisonAmbientIso Λ f (P.obj.origin n).L.obj (P.obj.origin n).L.property ≪≫
    (lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctor.mapIso (P.obj.alpha n) ≪≫
    (directImageCoordinates f d n).symm.app _

private theorem fixedBoundedConstructible_origin
    {A : Type (u + 1)} [CommRing A] (d : Scheme.AdicCoefficientDatum A)
    (T : Scheme.{u}) (n : ℕ) (K : PbcWitnessAmbient T d n)
    (hK : pbcWitnessBoundedConstructible T d n K) :
    (DerivedCategory.Plus.ι ⋙
      (comparisonUpperStar (ModuleCat.{u + 1} (PbcQuotient d n))
        T).mapDerivedCategory).essImage K := by
  obtain ⟨L, hL, ⟨e⟩⟩ := hK
  obtain ⟨a, b, hab, hbound⟩ := hL.2
  have hplus : DerivedCategory.TStructure.t.plus L :=
    ⟨a, (DerivedCategory.isGE_iff L a).2 (fun i hi ↦ hbound i (Or.inl hi))⟩
  refine ⟨⟨L, hplus⟩, ⟨?_⟩⟩
  apply (finiteCoefficientRealization T (PbcQuotient d n)).mapDerivedCategory.preimageIso
  exact (Functor.mapDerivedCategoryCompIso
    (comparisonUpperStar (ModuleCat.{u + 1} (PbcQuotient d n)) T)
    (finiteCoefficientRealization T (PbcQuotient d n))).symm.app L ≪≫ e

private structure InputOriginLift
    (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : Scheme.AdicCoefficientDatum A) (n : ℕ) where
  functor : (pbcWitnessReductionDomain T d n).FullSubcategory ⥤
    DerivedCategory.Plus (Sheaf T.smallEtaleTopology
      (ModuleCat.{u + 1} (PbcQuotient d (n + 1))))
  comparison : functor ⋙ DerivedCategory.Plus.ι ⋙
    (comparisonUpperStar (ModuleCat.{u + 1} (PbcQuotient d (n + 1))) T).mapDerivedCategory ≅
      (pbcWitnessReductionDomain T d n).ι

@[irreducible] private def inputOriginLift
    (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : Scheme.AdicCoefficientDatum A) (n : ℕ) : InputOriginLift T d n := by
  let B := PbcQuotient d (n + 1)
  let cp := DerivedCategory.Plus.ι ⋙
    (comparisonUpperStar (ModuleCat.{u + 1} B) T).mapDerivedCategory
  let i := (pbcWitnessReductionDomain T d n).ι
  letI := isIso_compactSupportComparisonUnit T B
  have hff : cp.FullyFaithful :=
    (derivedComparisonAdjunctionPlus (ModuleCat.{u + 1} B) T).fullyFaithfulLOfIsIsoUnit.comp
      (Functor.FullyFaithful.ofFullyFaithful DerivedCategory.Plus.ι)
  letI := hff.full
  letI := hff.faithful
  have hi : ∀ K, cp.essImage (i.obj K) :=
    fun K ↦ fixedBoundedConstructible_origin d T (n + 1) K.obj K.property.1
  exact ⟨Functor.essImage.liftFunctor i cp hi,
    Functor.essImage.liftFunctorCompIso i cp hi⟩

@[irreducible] private def comparisonDirectImageOn
    {C : Type (u + 2)} [Category.{u + 1} C]
    {B : Type (u + 1)} [CommRing B] [IsProper f]
    (H : C ⥤ DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)))
    (hH : ∀ K, DerivedCategory.TStructure.t.plus (H.obj K)) :
    H ⋙ (Etale.lowerStar (ModuleCat.{u + 1} B) f).rightDerivedFunctor ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} B) Y).mapDerivedCategory ≅
      H ⋙ (comparisonUpperStar (ModuleCat.{u + 1} B) X).mapDerivedCategory ⋙
        (lowerStar (ModuleCat.{u + 1} B) f).rightDerivedFunctor := by
  have h : IsIso (Functor.whiskerLeft H (directImageComparisonAmbient B f)) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro K
    exact directImageComparisonAmbient_isIso B f _ (hH K)
  exact asIso (Functor.whiskerLeft H (directImageComparisonAmbient B f))

@[irreducible] private def reducedOriginComparison
    {A : Type (u + 1)} [CommRing A] (d : Scheme.AdicCoefficientDatum A)
    (T : Scheme.{u}) (n : ℕ) (P : InputOriginLift T d n) :
    P.functor ⋙ DerivedCategory.Plus.ι ⋙ pbcWitnessEtaleReduction T d n ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} (PbcQuotient d n)) T).mapDerivedCategory ≅
      (pbcWitnessReductionDomain T d n).ι ⋙ pbcWitnessReduction T d n :=
  (Functor.associator P.functor DerivedCategory.Plus.ι
    (pbcWitnessEtaleReduction T d n ⋙
      (comparisonUpperStar (ModuleCat.{u + 1} (PbcQuotient d n)) T).mapDerivedCategory)).symm ≪≫
    Functor.isoWhiskerLeft (P.functor ⋙ DerivedCategory.Plus.ι)
      (pbcComparisonReduction T
        (pbcWitnessQuotientMap d (n + 1) n (Nat.le_succ n))).symm ≪≫
    (Functor.associator (P.functor ⋙ DerivedCategory.Plus.ι)
      (comparisonUpperStar (ModuleCat.{u + 1} (PbcQuotient d (n + 1))) T).mapDerivedCategory
      (pbcWitnessReduction T d n)).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.associator P.functor DerivedCategory.Plus.ι
        (comparisonUpperStar (ModuleCat.{u + 1} (PbcQuotient d (n + 1))) T).mapDerivedCategory ≪≫
        P.comparison) (pbcWitnessReduction T d n)

private theorem reducedOrigin_boundedBelow
    {A : Type (u + 1)} [CommRing A] (d : Scheme.AdicCoefficientDatum A)
    (X : Scheme.{u}) (n : ℕ) (P : InputOriginLift X d n) :
    ∀ K, DerivedCategory.TStructure.t.plus
      ((P.functor ⋙ DerivedCategory.Plus.ι ⋙ pbcWitnessEtaleReduction X d n).obj K) := by
  let C := PbcQuotient d n
  let cX' := (comparisonUpperStar (ModuleCat.{u + 1} C) X).mapDerivedCategory
  let LX := P.functor ⋙ DerivedCategory.Plus.ι ⋙ pbcWitnessEtaleReduction X d n
  let eLX := reducedOriginComparison d X n P
  intro K
  obtain ⟨M, ⟨eM⟩⟩ := fixedBoundedConstructible_origin d X n
    ((pbcWitnessReduction X d n).obj K.obj) K.property.2
  -- Reflect boundedness below through the exact faithful comparison.
  have hm : DerivedCategory.TStructure.t.plus (cX'.obj (LX.obj K)) :=
    DerivedCategory.TStructure.t.plus.prop_of_iso
      (eM ≪≫ (eLX.app K).symm)
      (((comparisonUpperStar (ModuleCat.{u + 1} C) X).mapDerivedCategoryPlus.obj M).property)
  obtain ⟨a, ha⟩ := hm
  refine ⟨a, (DerivedCategory.isGE_iff _ a).2 ?_⟩
  have := isIso_comparisonAdjunction_unit (ModuleCat.{u + 1} C) X
  have := (comparisonAdjunction (ModuleCat.{u + 1} C) X).fullyFaithfulLOfIsIsoUnit.faithful
  intro j hj
  exact Functor.isZero_homologyFunctor_of_isZero_homologyFunctor_mapDerivedCategory_obj
    (comparisonUpperStar (ModuleCat.{u + 1} C) X)
    ((DerivedCategory.isGE_iff _ a).1 ha j hj)

@[irreducible] private def properEtaleReductionIso
    {A : Type (u + 1)} [CommRing A] (d : Scheme.AdicCoefficientDatum A)
    [IsProper f] [IsNoetherian X] [IsNoetherian Y] (n : ℕ) :
    (Etale.lowerStar (ModuleCat.{u + 1} (PbcQuotient d (n + 1))) f).rightDerivedFunctor ⋙
        pbcWitnessEtaleReduction Y d n ≅
      pbcWitnessEtaleReduction X d n ⋙
        (Etale.lowerStar (ModuleCat.{u + 1} (PbcQuotient d n)) f).rightDerivedFunctor := by
  let q := pbcWitnessQuotientMap d (n + 1) n (Nat.le_succ n)
  have : IsIso (Etale.scalarMate q f) := by
    rw [NatTrans.isIso_iff_isIso_app]
    exact (Etale.properFiniteCoefficientExtension q f).1
  exact asIso (Etale.scalarMate q f)

@[irreducible] private def directImageRhoFixed
    {A : Type (u + 1)} [CommRing A] (d : Scheme.AdicCoefficientDatum A)
    [IsProper f] [IsNoetherian X] [IsNoetherian Y] (n : ℕ)
    (P : InputOriginLift X d n) :
    (pbcWitnessReductionDomain X d n).ι ⋙
        (lowerStar (ModuleCat.{u + 1} (PbcQuotient d (n + 1))) f).rightDerivedFunctor ⋙
        pbcWitnessReduction Y d n ≅
      (pbcWitnessReductionDomain X d n).ι ⋙ pbcWitnessReduction X d n ⋙
        (lowerStar (ModuleCat.{u + 1} (PbcQuotient d n)) f).rightDerivedFunctor := by
  let B := PbcQuotient d (n + 1)
  let C := PbcQuotient d n
  let q := pbcWitnessQuotientMap d (n + 1) n (Nat.le_succ n)
  let i := (pbcWitnessReductionDomain X d n).ι
  let cX := (comparisonUpperStar (ModuleCat.{u + 1} B) X).mapDerivedCategory
  let cY := (comparisonUpperStar (ModuleCat.{u + 1} B) Y).mapDerivedCategory
  let cX' := (comparisonUpperStar (ModuleCat.{u + 1} C) X).mapDerivedCategory
  let cY' := (comparisonUpperStar (ModuleCat.{u + 1} C) Y).mapDerivedCategory
  let Lp := P.functor
  let L := Lp ⋙ DerivedCategory.Plus.ι
  let eL : L ⋙ cX ≅ i :=
    Functor.associator Lp DerivedCategory.Plus.ι cX ≪≫ P.comparison
  let LX := L ⋙ pbcWitnessEtaleReduction X d n
  let rX := pbcWitnessReduction X d n
  let rY := pbcWitnessReduction Y d n
  let rXe := pbcWitnessEtaleReduction X d n
  let rYe := pbcWitnessEtaleReduction Y d n
  let DX := (lowerStar (ModuleCat.{u + 1} B) f).rightDerivedFunctor
  let DX' := (lowerStar (ModuleCat.{u + 1} C) f).rightDerivedFunctor
  let DE := (Etale.lowerStar (ModuleCat.{u + 1} B) f).rightDerivedFunctor
  let DE' := (Etale.lowerStar (ModuleCat.{u + 1} C) f).rightDerivedFunctor
  let eLX : LX ⋙ cX' ≅ i ⋙ rX :=
    Functor.associator L rXe cX' ≪≫
      Functor.associator Lp DerivedCategory.Plus.ι (rXe ⋙ cX') ≪≫
      reducedOriginComparison d X n P
  let hLX := reducedOrigin_boundedBelow d X n P
  let etIso := properEtaleReductionIso f d n
  exact
    (Functor.associator i DX rY).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerRight eL.symm DX ≪≫
        Functor.associator L cX DX ≪≫
        (comparisonDirectImageOn f L (fun K ↦ (Lp.obj K).property)).symm) rY ≪≫
    Functor.associator L (DE ⋙ cY) rY ≪≫
    Functor.isoWhiskerLeft L (Functor.associator DE cY rY) ≪≫
    Functor.isoWhiskerLeft L (Functor.isoWhiskerLeft DE (pbcComparisonReduction Y q)) ≪≫
    Functor.isoWhiskerLeft L (Functor.associator DE rYe cY').symm ≪≫
    Functor.isoWhiskerLeft L (Functor.isoWhiskerRight etIso cY') ≪≫
    Functor.isoWhiskerLeft L (Functor.associator rXe DE' cY') ≪≫
    (Functor.associator L rXe (DE' ⋙ cY')).symm ≪≫
    comparisonDirectImageOn f LX hLX ≪≫
    (Functor.associator LX cX' DX').symm ≪≫
    Functor.isoWhiskerRight eLX DX' ≪≫
    Functor.associator i rX DX'

/-- Proper direct image carries retained etale origins and quotient normalizations
functorially on bounded constructible input towers over Noetherian schemes.
Source: blueprint amplification step (b), main-20261015; Stacks Tags 0GL6 and 09C7.
(blueprint: lem-weil-pbc-proper-family-witness-compatibility).

Proof: restriction to constant scalar sections commutes with the actual module direct
image. Its unit with coefficient realization is invertible, by sheafification of the
underlying sheaf. Conjugating by the realization equivalence gives the underived
coordinate comparison. Exactness of unrealization and preservation of K-injectives
by equivalences give its total right-derived comparison. Thus the specified finite
coefficient functor is naturally isomorphic to fixed-ring derived direct image.

Lift the full reduction-domain inclusion to bounded-below etale origins through the
fully faithful comparison, using its bounded-constructible essential-image definition.
The lift is determined up to its unique comparison-compatible isomorphism. Transport
the proper finite-coefficient-extension isomorphism through this lift and the canonical
site-comparison and scalar-reduction isomorphisms. The etale reduction of the lift is
bounded below: its exact faithful comparison is isomorphic to the bounded constructible
input reduction, so comparison reflects its lower bound. Thus both direct-image site
comparisons are used only where their bounded-below hypotheses hold. This gives a
natural rho on the full reduction-domain category. No intermediate quotient is assumed
perfect, and boundedness of scalar extension of the direct image is not assumed.

For each input witnessed tower retain the actual etale right-derived direct images of
its supplied origins. They are bounded below. Site comparison and direct image of the
input alpha, followed by the inverse coordinate comparison, identify their comparison
images with the actual specified output levels. Apply the generic witness assembly:
full faithfulness lifts the normalization and all maps uniquely, checks their three
compatibility squares, and proves the functor laws with exactly these levels and rho.
This works also for empty schemes and the zero coefficient ring. -/
theorem pbcFamilyWitnessCompatibility_directImage_of_isProper
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    [IsNoetherian X] [IsNoetherian Y]
    {A : Type (u + 1)} [CommRing A] (d : Scheme.AdicCoefficientDatum A) :
    PbcFamilyWitnessCompatibility X Y d (pbcWitnessDirectImage f d) := by
  apply pbcFamilyWitnessCompatibility_of_origins d (pbcWitnessDirectImage f d)
    (fun n ↦
      Functor.isoWhiskerLeft (pbcWitnessReductionDomain X d n).ι
        (Functor.isoWhiskerRight (directImageCoordinates f d (n + 1))
          (pbcWitnessReduction Y d n)) ≪≫
        directImageRhoFixed f d n (inputOriginLift X d n) ≪≫
        (Functor.associator (pbcWitnessReductionDomain X d n).ι
          (pbcWitnessReduction X d n)
          ((lowerStar (ModuleCat.{u + 1} (PbcQuotient d n)) f).rightDerivedFunctor)).symm ≪≫
        Functor.isoWhiskerLeft
          ((pbcWitnessReductionDomain X d n).ι ⋙ pbcWitnessReduction X d n)
          (directImageCoordinates f d n).symm ≪≫
        Functor.associator (pbcWitnessReductionDomain X d n).ι
          (pbcWitnessReduction X d n) (pbcWitnessDirectImage f d n))
    (fun P n ↦
      (Etale.lowerStar (ModuleCat.{u + 1} (PbcQuotient d n)) f).rightDerivedFunctorPlus.obj
        (P.obj.origin n).L)
  exact directImageOrigin f d

end AlgebraicGeometry.ProEtale
