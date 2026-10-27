/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NI
-/
module

public import Sheaf.Paper.RationalScalarBalancedLocalization
public import Sheaf.Paper.RationalScalarCompletionUnitSquare
public import Sheaf.Paper.RationalPullbackCompositionCoherence
public import Sheaf.CategoryTheory.LocalizationInverseImageCoherence
import all Sheaf.Paper.CompletedAdicCoefficientDatum
import Mathlib.CategoryTheory.Adjunction.CompositionIso
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryCocycle

/-! # Cancellation in the specified mixed rational realization square

Source: Bhatt--Scholze, Remark 6.8.15, pp. 61--62; Stacks Tags 0G7E, 0D6D and 07A4
(blueprint: lem-per-rational-scalar-mixed-unit-cancellation).

Theta and D below are rationalBalancedTheta and extension along
rationalBalancedCoefficient. The completed comparison is rationalScalarStrictBeta.
The pullback alpha is the supplied, generator-normalized dependency record's alpha.
The ordinary zeta is normalized on tensor generators and derived computation counits.
No declarations from the downstream parent scalar-coherence module are imported.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOf false
set_option genInjectivity false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

variable (l : ℕ) [Fact l.Prime]
variable (E F : Type u) [Field E] [Field F]
  [Algebra ℚ_[l] E] [Algebra ℚ_[l] F]
  [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] F]
variable (i : E →ₐ[ℚ_[l]] F)
variable {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
  [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
  [Fact (∃ n : ℕ, topologicalKrullDim Y ≤ n)]
  [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
  [Fact (∀ y : Y, IsUnit (l : Y.presheaf.stalk y))]

/-- The specified strict beta, restricted and rationalized, on every unchanged raw object.
Source: BS 6.8.15; Stacks 0A0E, 099N
(blueprint: lem-per-rational-scalar-mixed-unit-cancellation). -/
def rationalMixedBetaComponent (g : X ⟶ Y)
    (sXE : RationalModuleRealization l E X) (sYE : RationalModuleRealization l E Y)
    (sXF : RationalModuleRealization l F X) (sYF : RationalModuleRealization l F Y)
    (aE : RationalRealizationPullbackComparison l E g sXE sYE)
    (aF : RationalRealizationPullbackComparison l F g sXF sYF)
    (K : PbcRationalDerivedCategory l E Y Fact.out Fact.out) :
    (pbcRationalScalarExtension l E F i X Fact.out Fact.out).obj (aE.rawPull.obj K) ≅
      aF.rawPull.obj ((pbcRationalScalarExtension l E F i Y Fact.out Fact.out).obj K) :=
  (pbcRationalScalarExtension l E F i X Fact.out Fact.out).mapIso
      (eqToIso (aE.raw_objects K.obj)) ≪≫
    (pbcRationalization X (pbcIntegralDatum l F) (pbcUniformizer l F)).mapIso
      (ObjectProperty.isoMk _
        (X := (pbcEmbeddingIntegralTensor l E F i X Fact.out Fact.out).obj
          ((aE.integral.completedFunctor l E).obj K.obj))
        (Y := (aF.integral.completedFunctor l F).obj
          ((pbcEmbeddingIntegralTensor l E F i Y Fact.out Fact.out).obj K.obj))
        ((rationalScalarStrictBeta l E F i g).app K.obj.obj)) ≪≫
    (eqToIso (aF.raw_objects
      ((pbcEmbeddingIntegralTensor l E F i Y Fact.out Fact.out).obj K.obj))).symm

/-- Scalar extension of the actual invertible completion unit, including raw-object transports.
Source: BS 6.8.15 (blueprint: lem-per-rational-scalar-mixed-unit-cancellation). -/
def rationalMixedUnitPrecomposition (g : X ⟶ Y)
    (sXE : RationalModuleRealization l E X) (sYE : RationalModuleRealization l E Y)
    (sXF : RationalModuleRealization l F X)
    (aE : RationalRealizationPullbackComparison l E g sXE sYE)
    (K : PbcBoundedConstructibleComplete Y (pbcIntegralDatum l E)) :=
  sXF.J.map
    ((pbcRationalScalarExtension l E F i X Fact.out Fact.out).map
      ((pbcRationalization X (pbcIntegralDatum l E) (pbcUniformizer l E)).map
        (ObjectProperty.homMk
          (X := ⟨(pbcActualDerivedPull g (pbcIntegralDatum l E)).obj K.obj,
            aE.integral.ordinary_mem K⟩)
          (Y := (aE.integral.completedFunctor l E).obj K)
          ((pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) g).app K.obj)) ≫
        eqToHom (aE.raw_objects K).symm))

/-- The mixed square for the specific alpha and the specified scalar/pullback comparison.
The ordinary comparison is fixed on tensor units and on derived computation counits;
its section formula determines the balanced map, including all coefficient factors.
Source: BS 6.8.15; Stacks 0D6D, 0A0E and 0A0G
(blueprint: lem-per-rational-scalar-mixed-unit-cancellation). -/
structure RationalScalarMixedUnitCancellation (g : X ⟶ Y)
    (sXE : RationalModuleRealization l E X) (sYE : RationalModuleRealization l E Y)
    (sXF : RationalModuleRealization l F X) (sYF : RationalModuleRealization l F Y)
    (aE : RationalRealizationPullbackComparison l E g sXE sYE)
    (aF : RationalRealizationPullbackComparison l F g sXF sYF)
    where
  /-- The localized finite-quotient coefficient square. -/
  coefficient_square : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map
      (rationalBalancedCoefficient l E F i Y) ≫ aF.rationalCoefficient = aE.rationalCoefficient ≫
      (rationalBalancedCoefficient l E F i X)
  /-- The ordinary scalar/pullback comparison. -/
  ordinary : pbcExtend (rationalBalancedCoefficient l E F i Y) ⋙ rationalPullModule l F g
      aF.rationalCoefficient ≅
    rationalPullModule l E g aE.rationalCoefficient ⋙ pbcExtend (rationalBalancedCoefficient l E F
      i X)
  /-- Inserting tensor units gives the same pulled-back generator on both sides.
  Scalar linearity then gives l' tensor b' tensor k ↦ l'b' tensor g⁻¹k. -/
  ordinary_units : ∀ (M : pbcModules Y (rationalCoefficientSheaf l Y E))
      (V : Y.ProEt) (m : M.val.obj (op V)),
    (ordinary.hom.app M).val.app (op ((proEtaleBaseChange g).obj V))
      (pbcTensorSection aF.rationalCoefficient
        ((proEtaleRingModulePullback g (rationalCoefficientSheaf l Y F)
          ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
            (rationalCoefficientSheaf l Y F)) (Iso.refl _)).obj
              ((pbcExtend (rationalBalancedCoefficient l E F i Y)).obj M))
        (op ((proEtaleBaseChange g).obj V)) 1
        (proEtaleRingModuleUnitSection g (rationalCoefficientSheaf l Y F)
          ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
            (rationalCoefficientSheaf l Y F)) (Iso.refl _)
          ((pbcExtend (rationalBalancedCoefficient l E F i Y)).obj M) V
          (pbcTensorSection (rationalBalancedCoefficient l E F i Y) M (op V) 1 m))) =
    pbcTensorSection (rationalBalancedCoefficient l E F i X)
      ((rationalPullModule l E g aE.rationalCoefficient).obj M)
      (op ((proEtaleBaseChange g).obj V)) 1
      (pbcTensorSection aE.rationalCoefficient
        ((proEtaleRingModulePullback g (rationalCoefficientSheaf l Y E)
          ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
            (rationalCoefficientSheaf l Y E)) (Iso.refl _)).obj M)
        (op ((proEtaleBaseChange g).obj V)) 1
        (proEtaleRingModuleUnitSection g (rationalCoefficientSheaf l Y E)
          ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
            (rationalCoefficientSheaf l Y E)) (Iso.refl _) M V m))
  /-- Its derived comparison. -/
  zeta : rationalPullDerived l E g aE.rationalCoefficient ⋙
      pbcDerivedExtend (rationalBalancedCoefficient l E F i X) ≅
    pbcDerivedExtend (rationalBalancedCoefficient l E F i Y) ⋙
      rationalPullDerived l F g aF.rationalCoefficient
  /-- The ordinary balanced map is the computation of that derived comparison. -/
  ambient_normalization : ∀ P : CochainComplex
      (pbcModules Y (rationalCoefficientSheaf l Y E)) ℤ,
    zeta.inv.app (DerivedCategory.Q.obj P) ≫
        (pbcDerivedExtend (rationalBalancedCoefficient l E F i X)).map
          (rationalPullComplexCounit l E g aE.rationalCoefficient P) ≫
        pbcComplexCounit (rationalBalancedCoefficient l E F i X)
          (((rationalPullModule l E g aE.rationalCoefficient).mapHomologicalComplex
            (.up ℤ)).obj P) =
      (rationalPullDerived l F g aF.rationalCoefficient).map
          (pbcComplexCounit (rationalBalancedCoefficient l E F i Y) P) ≫
        rationalPullComplexCounit l F g aF.rationalCoefficient
          (((pbcExtend (rationalBalancedCoefficient l E F i Y)).mapHomologicalComplex (.up ℤ)).obj
      P) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex ordinary (.up ℤ)).hom.app P)
  /-- The raw comparison is the actual rationalScalarStrictBeta, with no new choice. -/
  beta : aE.rawPull ⋙ pbcRationalScalarExtension l E F i X Fact.out Fact.out ≅
    pbcRationalScalarExtension l E F i Y Fact.out Fact.out ⋙ aF.rawPull
  /-- All components, not just their endpoint isomorphism classes, are fixed. -/
  beta_normalization : ∀ K : PbcRationalDerivedCategory l E Y Fact.out Fact.out,
    beta.app K = rationalMixedBetaComponent l E F i g sXE sYE sXF sYF aE aF K
  /-- The displayed equation, in the node's orientation, for every raw rational object. -/
  compatibility : ∀ K : PbcRationalDerivedCategory l E Y Fact.out Fact.out,
    (rationalBalancedTheta l E F i X sXE sXF).hom.app (aE.rawPull.obj K) ≫
        (pbcDerivedExtend (rationalBalancedCoefficient l E F i X)).map
          (aE.alpha.hom.app K) ≫ zeta.hom.app (sYE.J.obj K) =
      sXF.J.map (beta.hom.app K) ≫
        aF.alpha.hom.app
          ((pbcRationalScalarExtension l E F i Y Fact.out Fact.out).obj K) ≫
        (rationalPullDerived l F g aF.rationalCoefficient).map
          ((rationalBalancedTheta l E F i Y sYE sYF).hom.app K)

variable (g : X ⟶ Y)
  (sXE : RationalModuleRealization l E X) (sYE : RationalModuleRealization l E Y)
  (sXF : RationalModuleRealization l F X) (sYF : RationalModuleRealization l F Y)
  (aE : RationalRealizationPullbackComparison l E g sXE sYE)
  (aF : RationalRealizationPullbackComparison l F g sXF sYF)

/-- The mixed equation uses exactly the owning dependencies' theta, D, strict beta and alpha.
Source: BS Remark 6.8.15, pp. 61--62; Stacks 0G7E, 0D6D, 07A4
(blueprint: lem-per-rational-scalar-mixed-unit-cancellation).

Proof, following the seven steps of this node:
1. Ordinary pullback and finite scalar extension preserve the three integral
constructibility conditions. The actual quotient-completion units are invertible.
2. Precompose by scalar extension of that unit. Naturality of rationalBalancedTheta
and alpha_normalization cancel the E unit. The actual unit equation for
rationalScalarStrictBeta and alpha_normalization cancel the F unit on the other path.
3. On a simultaneous flat-term K-flat model the remaining normalized maps flatten
l' tensor b' tensor p to l' i(b') tensor p. The finite-projection coefficient square
makes this balanced. It commutes with restrictions and differentials, hence descends.
Cancel the invertible precomposition to obtain compatibility for the specified maps.
4. Multiply integral naturality by the reciprocal denominator. The annihilating-power
fraction criterion proves descent even when the integral Hom groups have torsion.
5. For two geometric maps use the canonical inverse-image compositor. Both remaining
ordinary routes send l'' tensor l' tensor p to l'' c_h(l') tensor p; identity is
multiplication. The derived computation counits retain these particular maps.
6. Substitute alpha as ordinary balancing after inverse completion unit. The reflected
unit and compositor equations cancel every adjacent inverse-unit/unit pair.
7. For successive fields the specified scalar associators flatten to multiplication;
three scalar factors have product nml independently of parentheses. Thus the four-field
pentagon, identity and both orders of mixed pasting agree. Reinsert the same outer
units, and descend all these equations to raw fractions as in step 4. -/
theorem rationalScalarMixedUnitCancellation :
    Nonempty (RationalScalarMixedUnitCancellation l E F i g sXE sYE sXF sYF aE aF) := by
  sorry

/-- The left route of the specified raw mixed square.
Source: BS 6.8.15 (blueprint: lem-per-rational-scalar-mixed-unit-cancellation). -/
def rationalMixedLeft (m : RationalScalarMixedUnitCancellation l E F i g sXE sYE sXF sYF aE aF)
    (K : PbcRationalDerivedCategory l E Y Fact.out Fact.out) :=
  (rationalBalancedTheta l E F i X sXE sXF).hom.app (aE.rawPull.obj K) ≫
    (pbcDerivedExtend (rationalBalancedCoefficient l E F i X)).map
      (aE.alpha.hom.app K) ≫ m.zeta.hom.app (sYE.J.obj K)

/-- The right route of the specified raw mixed square.
Source: BS 6.8.15 (blueprint: lem-per-rational-scalar-mixed-unit-cancellation). -/
def rationalMixedRight (m : RationalScalarMixedUnitCancellation l E F i g sXE sYE sXF sYF aE aF)
    (K : PbcRationalDerivedCategory l E Y Fact.out Fact.out) :=
  sXF.J.map (m.beta.hom.app K) ≫
    aF.alpha.hom.app ((pbcRationalScalarExtension l E F i Y Fact.out Fact.out).obj K) ≫
    (rationalPullDerived l F g aF.rationalCoefficient).map
      ((rationalBalancedTheta l E F i Y sYE sYF).hom.app K)

/-- The common ordinary balanced map after precomposing by the specified unit.
Source: BS 6.8.15; Stacks 0D6D
(blueprint: lem-per-rational-scalar-mixed-unit-cancellation). -/
def rationalMixedOrdinaryPath
    (m : RationalScalarMixedUnitCancellation l E F i g sXE sYE sXF sYF aE aF)
    (K : PbcBoundedConstructibleComplete Y (pbcIntegralDatum l E)) :=
  (rationalBalancedTheta l E F i X sXE sXF).hom.app
      ((pbcRationalization X (pbcIntegralDatum l E) (pbcUniformizer l E)).obj
        ⟨(pbcActualDerivedPull g (pbcIntegralDatum l E)).obj K.obj,
          aE.integral.ordinary_mem K⟩) ≫
    (pbcDerivedExtend (rationalBalancedCoefficient l E F i X)).map
      (eqToHom (sXE.objects
        ⟨(pbcActualDerivedPull g (pbcIntegralDatum l E)).obj K.obj,
          aE.integral.ordinary_mem K⟩) ≫
        aE.ordinaryComparison.hom.app K.obj ≫
        (rationalPullDerived l E g aE.rationalCoefficient).map
          (eqToHom (sYE.objects K).symm)) ≫
    m.zeta.hom.app (sYE.J.obj
      ((pbcRationalization Y (pbcIntegralDatum l E) (pbcUniformizer l E)).obj K))

private theorem mixed_scalar_map
    {W : Scheme.{u}} [IsNoetherian W]
    [Fact (∃ n : ℕ, topologicalKrullDim W ≤ n)]
    [Fact (∀ w : W, IsUnit (l : W.presheaf.stalk w))]
    {A B : PbcBoundedConstructibleComplete W (pbcIntegralDatum l E)} (f : A ⟶ B) :
    (pbcRationalScalarExtension l E F i W Fact.out Fact.out).map
        ((pbcRationalization W (pbcIntegralDatum l E) (pbcUniformizer l E)).map f) =
      (pbcRationalization W (pbcIntegralDatum l F) (pbcUniformizer l F)).map
        ((pbcEmbeddingIntegralTensor l E F i W Fact.out Fact.out).map f) := by
  change pbcRationalScalarHom l E F i W Fact.out Fact.out A B
    ((pbcRationalization W (pbcIntegralDatum l E) (pbcUniformizer l E)).map f) = _
  have h := (pbcRationalScalarHom_exists l E F i W Fact.out Fact.out A B).exists.choose_spec
    (1 : Localization.Away (pbcUniformizer l E)) f
  simpa only [map_one, one_smul, pbcRationalScalarHom] using h

private theorem mixed_raw_map
    {A B : PbcBoundedConstructibleComplete Y (pbcIntegralDatum l E)} (f : A ⟶ B) :
    aE.rawPull.map
        ((pbcRationalization Y (pbcIntegralDatum l E) (pbcUniformizer l E)).map f) =
      eqToHom (aE.raw_objects A) ≫
        (pbcRationalization X (pbcIntegralDatum l E) (pbcUniformizer l E)).map
          ((aE.integral.completedFunctor l E).map f) ≫ eqToHom (aE.raw_objects B).symm := by
  simpa only [rationalPullFraction, pow_zero, one_smul] using aE.raw_fractions A B f 0

private theorem mixed_realization_map
    {W : Scheme.{u}} [IsNoetherian W]
    [Fact (∃ n : ℕ, topologicalKrullDim W ≤ n)]
    [Fact (∀ w : W, IsUnit (l : W.presheaf.stalk w))]
    (s : RationalModuleRealization l E W)
    {A B : PbcBoundedConstructibleComplete W (pbcIntegralDatum l E)} (f : A ⟶ B) :
    s.J.map ((pbcRationalization W (pbcIntegralDatum l E) (pbcUniformizer l E)).map f) =
      eqToHom (s.objects A) ≫ (pbcDerivedExtend (rationalPullScalar l E s)).map f.hom ≫
        eqToHom (s.objects B).symm := by
  simpa only [pow_zero, inv_one, map_one, one_smul] using s.fractions A B f 0

/-- Both routes become the same ordinary map after the specified isomorphism.
Source: BS 6.8.15; Stacks 0G7E, 0D6D
(blueprint: lem-per-rational-scalar-mixed-unit-cancellation).

Proof, following the seven steps of this node:
1. Ordinary pullback and finite scalar extension preserve the three integral
constructibility conditions. The actual quotient-completion units are invertible.
2. Precompose by scalar extension of that unit. Naturality of rationalBalancedTheta
and alpha_normalization cancel the E unit. The actual unit equation for
rationalScalarStrictBeta and alpha_normalization cancel the F unit on the other path.
3. On a simultaneous flat-term K-flat model the remaining normalized maps flatten
l' tensor b' tensor p to l' i(b') tensor p. The finite-projection coefficient square
makes this balanced. It commutes with restrictions and differentials, hence descends.
Cancel the invertible precomposition to obtain compatibility for the specified maps.
4. Multiply integral naturality by the reciprocal denominator. The annihilating-power
fraction criterion proves descent even when the integral Hom groups have torsion.
5. For two geometric maps use the canonical inverse-image compositor. Both remaining
ordinary routes send l'' tensor l' tensor p to l'' c_h(l') tensor p; identity is
multiplication. The derived computation counits retain these particular maps.
6. Substitute alpha as ordinary balancing after inverse completion unit. The reflected
unit and compositor equations cancel every adjacent inverse-unit/unit pair.
7. For successive fields the specified scalar associators flatten to multiplication;
three scalar factors have product nml independently of parentheses. Thus the four-field
pentagon, identity and both orders of mixed pasting agree. Reinsert the same outer
units, and descend all these equations to raw fractions as in step 4. -/
theorem rationalMixedUnitPrecomposition_eq
    (m : RationalScalarMixedUnitCancellation l E F i g sXE sYE sXF sYF aE aF)
    (K : PbcBoundedConstructibleComplete Y (pbcIntegralDatum l E)) :
    IsIso (rationalMixedUnitPrecomposition l E F i g sXE sYE sXF aE K) ∧
    (rationalMixedUnitPrecomposition l E F i g sXE sYE sXF aE K ≫
      rationalMixedLeft l E F i g sXE sYE sXF sYF aE aF m
        ((pbcRationalization Y (pbcIntegralDatum l E) (pbcUniformizer l E)).obj K) =
      rationalMixedOrdinaryPath l E F i g sXE sYE sXF sYF aE aF m K) ∧
    (rationalMixedUnitPrecomposition l E F i g sXE sYE sXF aE K ≫
      rationalMixedRight l E F i g sXE sYE sXF sYF aE aF m
        ((pbcRationalization Y (pbcIntegralDatum l E) (pbcUniformizer l E)).obj K) =
      rationalMixedOrdinaryPath l E F i g sXE sYE sXF sYF aE aF m K) := by
  let A : PbcBoundedConstructibleComplete X (pbcIntegralDatum l E) :=
    ⟨(pbcActualDerivedPull g (pbcIntegralDatum l E)).obj K.obj,
      aE.integral.ordinary_mem K⟩
  let B := (aE.integral.completedFunctor l E).obj K
  let f : A ⟶ B := ObjectProperty.homMk
    ((pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) g).app K.obj)
  have hf : IsIso f := (ObjectProperty.isIso_hom_iff f).mp (aE.integral.unit_isIso K)
  let n := (pbcRationalization X (pbcIntegralDatum l E) (pbcUniformizer l E)).map f ≫
    eqToHom (aE.raw_objects K).symm
  have hn : sXE.J.map n ≫ aE.alpha.hom.app
        ((pbcRationalization Y (pbcIntegralDatum l E) (pbcUniformizer l E)).obj K) =
      eqToHom (sXE.objects A) ≫ aE.ordinaryComparison.hom.app K.obj ≫
        (rationalPullDerived l E g aE.rationalCoefficient).map
          (eqToHom (sYE.objects K).symm) := by
    dsimp only [n]
    rw [sXE.J.map_comp, mixed_realization_map]
    have h := congrArg (fun q ↦ eqToHom (sXE.objects A) ≫ q ≫
      (rationalPullDerived l E g aE.rationalCoefficient).map
        (eqToHom (sYE.objects K).symm)) (aE.alpha_normalization K)
    simp only [Category.assoc] at h
    rw [← Functor.map_comp, eqToHom_trans, eqToHom_refl,
      CategoryTheory.Functor.map_id] at h
    erw [Category.comp_id] at h
    dsimp only [f, ObjectProperty.homMk]
    simpa only [Category.assoc] using h
  have hleft : rationalMixedUnitPrecomposition l E F i g sXE sYE sXF aE K ≫
      rationalMixedLeft l E F i g sXE sYE sXF sYF aE aF m
        ((pbcRationalization Y (pbcIntegralDatum l E) (pbcUniformizer l E)).obj K) =
      rationalMixedOrdinaryPath l E F i g sXE sYE sXF sYF aE aF m K := by
    unfold rationalMixedUnitPrecomposition rationalMixedLeft rationalMixedOrdinaryPath
    change sXF.J.map ((pbcRationalScalarExtension l E F i X Fact.out Fact.out).map n) ≫
      (rationalBalancedTheta l E F i X sXE sXF).hom.app _ ≫ _ = _
    have ht := (rationalBalancedTheta l E F i X sXE sXF).hom.naturality n
    simp only [Functor.comp_map] at ht
    rw [← Category.assoc, ht]
    simp only [Category.assoc]
    rw [← Functor.map_comp_assoc, hn]
  refine ⟨?_, hleft, ?_⟩
  · change IsIso (sXF.J.map
      ((pbcRationalScalarExtension l E F i X Fact.out Fact.out).map n))
    dsimp only [n]
    infer_instance
  · simpa only [rationalMixedRight, rationalMixedLeft, m.compatibility] using hleft

private theorem mixed_tensor_smul {W : Scheme.{u}}
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (φ : R ⟶ S)
    (M : pbcModules W R) (U : W.ProEtᵒᵖ) (c : S.obj.obj U) (x : M.val.obj U) :
    pbcTensorSection φ M U c x = c • pbcTensorSection φ M U 1 x := by
  change completedAdicChangeTensor W φ M U c x =
    c • completedAdicChangeTensor W φ M U 1 x
  simpa only [mul_one] using completedTensor_smul W φ M U c 1 x

private theorem mixed_tensor_unit_smul {W : Scheme.{u}}
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (φ : R ⟶ S)
    (M : pbcModules W R) (U : W.ProEtᵒᵖ) (b : R.obj.obj U) (x : M.val.obj U) :
    pbcTensorSection φ M U 1 (b • x) =
      φ.hom.app U b • pbcTensorSection φ M U 1 x := by
  have hunit := (pbcScalarAdjunction_exists φ).exists.choose_spec
  conv_lhs => rw [← hunit M U (b • x)]
  conv_rhs => rw [← hunit M U x]
  change _ = b • ((pbcScalarAdjunction φ).unit.app M).val.app U x
  exact (((pbcScalarAdjunction φ).unit.app M).val.app U).hom.map_smul b x

/-- The ordinary zeta has the full local formula, before tensor flattening.
Source: BS 6.8.15, pp. 61--62; Stacks 0G7E, 0D6D and 07A4
(blueprint: lem-per-rational-scalar-mixed-unit-cancellation).

Proof: precompose with scalar extension of the actual completion units. Substitute
the recorded alpha normalization and rationalScalarCompletionUnitSquare. Adjacent
inverse-unit/unit factors cancel. On the same flat-term K-flat representative all
remaining comparisons are the generator-normalized ordinary tensor maps. Geometric
composition uses the canonical inverse-image compositor and scalar insertion; coefficient
composition multiplies the scalar factors. Their associative product is independent of
parentheses. The normalized derived computation counits descend these maps, and the
annihilating-power fraction criterion extends the equations to raw rational morphisms. -/
theorem rationalMixedOrdinarySections
    (m : RationalScalarMixedUnitCancellation l E F i g sXE sYE sXF sYF aE aF)
    (M : pbcModules Y (rationalCoefficientSheaf l Y E)) (V : Y.ProEt)
    (p : M.val.obj (op V))
    (b : (rationalCoefficientSheaf l X E).obj.obj (op ((proEtaleBaseChange g).obj V)))
    (c : (rationalCoefficientSheaf l X F).obj.obj (op ((proEtaleBaseChange g).obj V))) :
    (m.ordinary.inv.app M).val.app (op ((proEtaleBaseChange g).obj V))
      (pbcTensorSection (rationalBalancedCoefficient l E F i X)
        ((rationalPullModule l E g aE.rationalCoefficient).obj M)
        (op ((proEtaleBaseChange g).obj V)) c
        (b • rationalCoherenceUnit l E g aE.rationalCoefficient M V p)) =
      (c * (rationalBalancedCoefficient l E F i X).hom.app
        (op ((proEtaleBaseChange g).obj V)) b) •
        rationalCoherenceUnit l F g aF.rationalCoefficient
          ((pbcExtend (rationalBalancedCoefficient l E F i Y)).obj M) V
          (pbcTensorSection (rationalBalancedCoefficient l E F i Y) M (op V) 1 p) := by
  let U := op ((proEtaleBaseChange g).obj V)
  let N := (rationalPullModule l E g aE.rationalCoefficient).obj M
  let φ := rationalBalancedCoefficient l E F i X
  let x := rationalCoherenceUnit l E g aE.rationalCoefficient M V p
  let y := rationalCoherenceUnit l F g aF.rationalCoefficient
    ((pbcExtend (rationalBalancedCoefficient l E F i Y)).obj M) V
    (pbcTensorSection (rationalBalancedCoefficient l E F i Y) M (op V) 1 p)
  have hunit : (m.ordinary.hom.app M).val.app U y =
      pbcTensorSection φ N U 1 x := by
    dsimp only [x, y]
    unfold rationalCoherenceUnit
    exact m.ordinary_units M V p
  have hinv : (m.ordinary.inv.app M).val.app U
      (pbcTensorSection φ N U 1 x) = y := by
    rw [← hunit]
    have h := congrArg (fun f ↦ f.val.app U y) (m.ordinary.hom_inv_id_app M)
    exact h
  change (m.ordinary.inv.app M).val.app U (pbcTensorSection φ N U c (b • x)) =
    (c * φ.hom.app U b) • y
  rw [mixed_tensor_smul, mixed_tensor_unit_smul, map_smul, map_smul, hinv, mul_smul]

section GeometricHelpers
variable {Z : Scheme.{u}} [IsNoetherian Z]
  [Fact (∃ n : ℕ, topologicalKrullDim Z ≤ n)]
  [Fact (∀ z : Z, IsUnit (l : Z.presheaf.stalk z))]
variable (h : Z ⟶ X) (sZE : RationalModuleRealization l E Z)
  (ahE : RationalRealizationPullbackComparison l E h sZE sXE)
  (acE : RationalRealizationPullbackComparison l E (h ≫ g) sZE sYE)

/-- The ambient compositor extracted from the full normalized dependency theorem.
Its tensor-generator, inverse-image-pasting, computation-counit and strict-unit equations
fix its maps; this does not select from an unnormalized endpoint-isomorphism existence.
Source: BS 6.8.15; Stacks 0D6D, 099N
(blueprint: lem-per-rational-scalar-mixed-unit-cancellation). -/
def rationalMixedGeometricCompositor :
    rationalPullDerived l E g aE.rationalCoefficient ⋙
      rationalPullDerived l E h ahE.rationalCoefficient ≅
    rationalPullDerived l E (h ≫ g) acE.rationalCoefficient := by
  have hc := rationalPullbackCompositionCoherence l E g h sYE sXE sZE aE ahE acE
  unfold HasRationalPullbackCompositionCoherence at hc
  exact hc.2.2.2.2.choose_spec.2.choose

/-- The raw compositor extracted from the full normalized dependency theorem.
Its tensor-generator, inverse-image-pasting, computation-counit and strict-unit equations
fix its maps; this does not select from an unnormalized endpoint-isomorphism existence.
Source: BS 6.8.15; Stacks 0D6D, 099N
(blueprint: lem-per-rational-scalar-mixed-unit-cancellation). -/
def rationalMixedRawCompositor :
    aE.rawPull ⋙ ahE.rawPull ≅ acE.rawPull := by
  have hc := rationalPullbackCompositionCoherence l E g h sYE sXE sZE aE ahE acE
  unfold HasRationalPullbackCompositionCoherence at hc
  exact hc.2.2.2.2.choose_spec.2.choose_spec.2.choose_spec.2.choose

end GeometricHelpers

section IdentityHelpers
variable (a : RationalRealizationPullbackComparison l E (𝟙 X) sXE sXE)

/-- The ambient identity extracted from the full normalized dependency theorem.
The tensor multiplication, canonical identity fiber product and strict-unit equations
specify this map, including the identity case, before any unit is cancelled.
Source: BS 6.8.15; Stacks 0D6D, 099N
(blueprint: lem-per-rational-scalar-mixed-unit-cancellation). -/
def rationalMixedGeometricUnitor :
    rationalPullDerived l E (𝟙 X) a.rationalCoefficient ≅ 𝟭 _ := by
  have hc := rationalPullbackIdentityCoherence l E sXE a
  unfold HasRationalPullbackIdentityCoherence at hc
  exact hc.2.2.2.choose_spec.2.choose

/-- The raw identity extracted from the full normalized dependency theorem.
The tensor multiplication, canonical identity fiber product and strict-unit equations
specify this map, including the identity case, before any unit is cancelled.
Source: BS 6.8.15; Stacks 0D6D, 099N
(blueprint: lem-per-rational-scalar-mixed-unit-cancellation). -/
def rationalMixedRawUnitor :
    a.rawPull ≅ 𝟭 _ := by
  have hc := rationalPullbackIdentityCoherence l E sXE a
  unfold HasRationalPullbackIdentityCoherence at hc
  exact hc.2.2.2.choose_spec.2.choose_spec.2.choose_spec.2.choose

end IdentityHelpers

section GeometricCoherence
variable {Z : Scheme.{u}} [IsNoetherian Z]
  [Fact (∃ n : ℕ, topologicalKrullDim Z ≤ n)]
  [Fact (∀ z : Z, IsUnit (l : Z.presheaf.stalk z))]
variable (h : Z ⟶ X) (sZE : RationalModuleRealization l E Z)
  (sZF : RationalModuleRealization l F Z)
  (ahE : RationalRealizationPullbackComparison l E h sZE sXE)
  (acE : RationalRealizationPullbackComparison l E (h ≫ g) sZE sYE)
  (ahF : RationalRealizationPullbackComparison l F h sZF sXF)
  (acF : RationalRealizationPullbackComparison l F (h ≫ g) sZF sYF)
  (mg : RationalScalarMixedUnitCancellation l E F i g sXE sYE sXF sYF aE aF)
  (mh : RationalScalarMixedUnitCancellation l E F i h sZE sXE sZF sXF ahE ahF)
  (mc : RationalScalarMixedUnitCancellation l E F i (h ≫ g) sZE sYE sZF sYF acE acF)

/-- The same zeta comparisons commute with geometric composition.
Source: BS 6.8.15, pp. 61--62; Stacks 0G7E, 0D6D and 07A4
(blueprint: lem-per-rational-scalar-mixed-unit-cancellation).

Proof: precompose with scalar extension of the actual completion units. Substitute
the recorded alpha normalization and rationalScalarCompletionUnitSquare. Adjacent
inverse-unit/unit factors cancel. On the same flat-term K-flat representative all
remaining comparisons are the generator-normalized ordinary tensor maps. Geometric
composition uses the canonical inverse-image compositor and scalar insertion; coefficient
composition multiplies the scalar factors. Their associative product is independent of
parentheses. The normalized derived computation counits descend these maps, and the
annihilating-power fraction criterion extends the equations to raw rational morphisms. -/
theorem rationalMixedGeometricComposition
    (K : DerivedCategory (pbcModules Y (rationalCoefficientSheaf l Y E))) :
    mh.zeta.hom.app ((rationalPullDerived l E g aE.rationalCoefficient).obj K) ≫
        (rationalPullDerived l F h ahF.rationalCoefficient).map (mg.zeta.hom.app K) =
      (pbcDerivedExtend (rationalBalancedCoefficient l E F i Z)).map
          ((rationalMixedGeometricCompositor l E g sXE sYE aE h sZE ahE acE).hom.app K) ≫
        mc.zeta.hom.app K ≫
        (rationalMixedGeometricCompositor l F g sXF sYF aF h sZF ahF acF).inv.app
          ((pbcDerivedExtend (rationalBalancedCoefficient l E F i Y)).obj K) := by
  sorry

/-- The actual strict-beta rationalizations obey the same geometric pasting.
Source: BS 6.8.15, pp. 61--62; Stacks 0G7E, 0D6D and 07A4
(blueprint: lem-per-rational-scalar-mixed-unit-cancellation).

Proof: precompose with scalar extension of the actual completion units. Substitute
the recorded alpha normalization and rationalScalarCompletionUnitSquare. Adjacent
inverse-unit/unit factors cancel. On the same flat-term K-flat representative all
remaining comparisons are the generator-normalized ordinary tensor maps. Geometric
composition uses the canonical inverse-image compositor and scalar insertion; coefficient
composition multiplies the scalar factors. Their associative product is independent of
parentheses. The normalized derived computation counits descend these maps, and the
annihilating-power fraction criterion extends the equations to raw rational morphisms. -/
theorem rationalMixedRawGeometricComposition
    (K : PbcRationalDerivedCategory l E Y Fact.out Fact.out) :
    (pbcRationalScalarExtension l E F i Z Fact.out Fact.out).map
        ((rationalMixedRawCompositor l E g sXE sYE aE h sZE ahE acE).hom.app K) ≫
      mc.beta.hom.app K =
    mh.beta.hom.app (aE.rawPull.obj K) ≫
      ahF.rawPull.map (mg.beta.hom.app K) ≫
      (rationalMixedRawCompositor l F g sXF sYF aF h sZF ahF acF).hom.app
        ((pbcRationalScalarExtension l E F i Y Fact.out Fact.out).obj K) := by
  sorry

end GeometricCoherence

/-- Identity geometric maps give the ambient tensor unitor and the actual raw unitor.
Source: BS 6.8.15, pp. 61--62; Stacks 0G7E, 0D6D and 07A4
(blueprint: lem-per-rational-scalar-mixed-unit-cancellation).

Proof: precompose with scalar extension of the actual completion units. Substitute
the recorded alpha normalization and rationalScalarCompletionUnitSquare. Adjacent
inverse-unit/unit factors cancel. On the same flat-term K-flat representative all
remaining comparisons are the generator-normalized ordinary tensor maps. Geometric
composition uses the canonical inverse-image compositor and scalar insertion; coefficient
composition multiplies the scalar factors. Their associative product is independent of
parentheses. The normalized derived computation counits descend these maps, and the
annihilating-power fraction criterion extends the equations to raw rational morphisms. -/
theorem rationalMixedGeometricIdentity
    (aIE : RationalRealizationPullbackComparison l E (𝟙 X) sXE sXE)
    (aIF : RationalRealizationPullbackComparison l F (𝟙 X) sXF sXF)
    (m : RationalScalarMixedUnitCancellation l E F i (𝟙 X)
      sXE sXE sXF sXF aIE aIF) :
    (∀ K : DerivedCategory (pbcModules X (rationalCoefficientSheaf l X E)),
      m.zeta.hom.app K ≫ (rationalMixedGeometricUnitor l F sXF aIF).hom.app
          ((pbcDerivedExtend (rationalBalancedCoefficient l E F i X)).obj K) =
        (pbcDerivedExtend (rationalBalancedCoefficient l E F i X)).map
          ((rationalMixedGeometricUnitor l E sXE aIE).hom.app K)) ∧
    (∀ K : PbcRationalDerivedCategory l E X Fact.out Fact.out,
      m.beta.hom.app K ≫ (rationalMixedRawUnitor l F sXF aIF).hom.app
          ((pbcRationalScalarExtension l E F i X Fact.out Fact.out).obj K) =
        (pbcRationalScalarExtension l E F i X Fact.out Fact.out).map
          ((rationalMixedRawUnitor l E sXE aIE).hom.app K)) := by
  sorry

section CoefficientCoherence
variable (G : Type u) [Field G] [Algebra ℚ_[l] G] [FiniteDimensional ℚ_[l] G]
  (j : F →ₐ[ℚ_[l]] G)
  (sXG : RationalModuleRealization l G X) (sYG : RationalModuleRealization l G Y)
  (aG : RationalRealizationPullbackComparison l G g sXG sYG)
  (mEF : RationalScalarMixedUnitCancellation l E F i g sXE sYE sXF sYF aE aF)
  (mFG : RationalScalarMixedUnitCancellation l F G j g sXF sYF sXG sYG aF aG)
  (mEG : RationalScalarMixedUnitCancellation l E G (j.comp i) g
    sXE sYE sXG sYG aE aG)

private theorem mixed_inverse_square {C D : Type*} [Category C] [Category D]
    (T : C ⥤ D) {A B : C} {U V W : D}
    (e : A ≅ B) (f : U ≅ T.obj A) (q : V ≅ W)
    (a : T.obj B ⟶ W) (b : U ⟶ V)
    (h : f.hom ≫ T.map e.hom ≫ a = b ≫ q.hom) :
    T.map e.inv ≫ f.inv ≫ b = a ≫ q.inv := by
  apply (cancel_epi (T.map e.hom)).1
  apply (cancel_epi f.hom).1
  have ht := congrArg (fun k ↦ k ≫ q.inv) h
  simpa only [Category.assoc, ← T.map_comp_assoc, Iso.hom_inv_id,
    T.map_id, Category.id_comp, Category.comp_id, Iso.hom_inv_id_assoc] using ht.symm

private theorem mixed_strict_coefficient_tower
    (K : PbcCompletedDerived Y (pbcIntegralDatum l E)) :
    (pbcEmbeddingAmbientTensor l F G j X).map
        ((rationalScalarStrictBeta l E F i g).hom.app K) ≫
      (rationalScalarStrictBeta l F G j g).hom.app
        ((pbcEmbeddingAmbientTensor l E F i Y).obj K) ≫
      (pbcActualStrictCompletedPull (pbcIntegralDatum l G) g).map
        ((pbcAmbientScalarComp l E F G i j Y).hom.app K) =
    (pbcAmbientScalarComp l E F G i j X).hom.app
        ((pbcActualStrictCompletedPull (pbcIntegralDatum l E) g).obj K) ≫
      (rationalScalarStrictBeta l E G (j.comp i) g).hom.app K := by
  let C := pbcEmbeddingAmbientTensor l F G j X
  let B := pbcActualCompletedPull g (pbcIntegralDatum l G)
  let eE := pbcActualAmbientCompletedPullbackIso (pbcIntegralDatum l E) g
  let eF := pbcActualAmbientCompletedPullbackIso (pbcIntegralDatum l F) g
  let eG := pbcActualAmbientCompletedPullbackIso (pbcIntegralDatum l G) g
  let bEF := rationalScalarReflectedBeta l E F i g
  let bFG := rationalScalarReflectedBeta l F G j g
  let bEG := rationalScalarReflectedBeta l E G (j.comp i) g
  let cX := pbcAmbientScalarComp l E F G i j X
  let cY := pbcAmbientScalarComp l E F G i j Y
  have hr : C.map (bEF.hom.app K) ≫
      bFG.hom.app ((pbcEmbeddingAmbientTensor l E F i Y).obj K) ≫
      B.map (cY.hom.app K) =
    cX.hom.app ((pbcActualCompletedPull g (pbcIntegralDatum l E)).obj K) ≫
      bEG.hom.app K := by
    exact mixed_inverse_square C
      ((pbcScalarCompletedPullIso l E F i g).app K)
      ((pbcScalarCompletedPullIso l F G j g).app
        ((pbcEmbeddingAmbientTensor l E F i Y).obj K))
      ((pbcScalarCompletedPullIso l E G (j.comp i) g).app K)
      (cX.hom.app ((pbcActualCompletedPull g (pbcIntegralDatum l E)).obj K))
      (B.map (cY.hom.app K))
      (rationalScalarCompletionUnitSquare_coefficients l E F i g G j K)
  have hn : eG.inv.app ((pbcEmbeddingAmbientTensor l F G j Y).obj
      ((pbcEmbeddingAmbientTensor l E F i Y).obj K)) ≫
      (pbcActualStrictCompletedPull (pbcIntegralDatum l G) g).map (cY.hom.app K) =
    B.map (cY.hom.app K) ≫
      eG.inv.app ((pbcEmbeddingAmbientTensor l E G (j.comp i) Y).obj K) :=
    (eG.inv.naturality (cY.hom.app K)).symm
  have ha : C.map ((pbcEmbeddingAmbientTensor l E F i X).map (eE.hom.app K)) ≫
      cX.hom.app ((pbcActualCompletedPull g (pbcIntegralDatum l E)).obj K) =
    cX.hom.app ((pbcActualStrictCompletedPull (pbcIntegralDatum l E) g).obj K) ≫
      (pbcEmbeddingAmbientTensor l E G (j.comp i) X).map (eE.hom.app K) :=
    cX.hom.naturality (eE.hom.app K)
  simp only [rationalScalarStrictBeta, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.map_comp,
    Category.assoc]
  change C.map ((pbcEmbeddingAmbientTensor l E F i X).map (eE.hom.app K)) ≫
    C.map (bEF.hom.app K) ≫ C.map (eF.inv.app _) ≫
    C.map (eF.hom.app _) ≫ bFG.hom.app _ ≫ eG.inv.app _ ≫
    (pbcActualStrictCompletedPull (pbcIntegralDatum l G) g).map (cY.hom.app K) =
    cX.hom.app _ ≫ (pbcEmbeddingAmbientTensor l E G (j.comp i) X).map
      (eE.hom.app K) ≫ bEG.hom.app K ≫ eG.inv.app _
  erw [(eF.app ((pbcEmbeddingAmbientTensor l E F i Y).obj K)).map_inv_hom_id_assoc C]
  erw [hn, reassoc_of% hr, reassoc_of% ha]
  rfl

/-- The same zeta comparisons respect the specified coefficient associators.
Source: BS 6.8.15, pp. 61--62; Stacks 0G7E, 0D6D and 07A4
(blueprint: lem-per-rational-scalar-mixed-unit-cancellation).

Proof: precompose with scalar extension of the actual completion units. Substitute
the recorded alpha normalization and rationalScalarCompletionUnitSquare. Adjacent
inverse-unit/unit factors cancel. On the same flat-term K-flat representative all
remaining comparisons are the generator-normalized ordinary tensor maps. Geometric
composition uses the canonical inverse-image compositor and scalar insertion; coefficient
composition multiplies the scalar factors. Their associative product is independent of
parentheses. The normalized derived computation counits descend these maps, and the
annihilating-power fraction criterion extends the equations to raw rational morphisms. -/
theorem rationalMixedCoefficientTower
    (K : DerivedCategory (pbcModules Y (rationalCoefficientSheaf l Y E))) :
    (pbcDerivedExtend (rationalBalancedCoefficient l F G j X)).map (mEF.zeta.hom.app K) ≫
      mFG.zeta.hom.app ((pbcDerivedExtend (rationalBalancedCoefficient l E F i Y)).obj K) ≫
      (rationalPullDerived l G g aG.rationalCoefficient).map
        ((pbcReductionNormalization (rationalBalancedCoefficient l E F i Y)
          (rationalBalancedCoefficient l F G j Y)
          (rationalBalancedCoefficient l E G (j.comp i) Y)
          (rationalBalancedCoefficient_comp l E F i Y G j) K).hom) =
    (pbcReductionNormalization (rationalBalancedCoefficient l E F i X)
      (rationalBalancedCoefficient l F G j X)
      (rationalBalancedCoefficient l E G (j.comp i) X)
      (rationalBalancedCoefficient_comp l E F i X G j)
      ((rationalPullDerived l E g aE.rationalCoefficient).obj K)).hom ≫
        mEG.zeta.hom.app K := by
  sorry

/-- The beta comparisons respect precisely the published raw scalar associators.
Source: BS 6.8.15, pp. 61--62; Stacks 0A0E, 0A0G and 0D6D
(blueprint: lem-per-rational-scalar-mixed-unit-cancellation).

Proof: invert the published reflected coefficient-tower equation. Conjugate it
by the quotient-unit-normalized ambient pullback isomorphisms. Naturality of
those isomorphisms and of the scalar associator cancels the intermediate pair
and proves the tower equation for rationalScalarStrictBeta. The denominator-one
formulas show that both raw scalar extension and raw pullback carry integral
maps to their prescribed integral images, retaining the recorded object transports.
Substitute beta_normalization and the published rational scalar associator. Its
naturality removes the initial raw-object transport; the remaining transports
cancel in pairs. Functoriality of rationalization now takes the strict integral
tower equation to exactly the required raw equation. -/
theorem rationalMixedRawCoefficientTower
    (K : PbcRationalDerivedCategory l E Y Fact.out Fact.out) :
    (pbcRationalScalarExtension l F G j X Fact.out Fact.out).map (mEF.beta.hom.app K) ≫
      mFG.beta.hom.app ((pbcRationalScalarExtension l E F i Y Fact.out Fact.out).obj K) ≫
      aG.rawPull.map ((pbcRationalScalarComp l E F G i j Y Fact.out Fact.out).hom.app K) =
    (pbcRationalScalarComp l E F G i j X Fact.out Fact.out).hom.app (aE.rawPull.obj K) ≫
      mEG.beta.hom.app K := by
  have hbEF := congrArg Iso.hom (mEF.beta_normalization K)
  have hbFG := congrArg Iso.hom (mFG.beta_normalization
    ((pbcRationalScalarExtension l E F i Y Fact.out Fact.out).obj K))
  have hbEG := congrArg Iso.hom (mEG.beta_normalization K)
  change mEF.beta.hom.app K = _ at hbEF
  change mFG.beta.hom.app _ = _ at hbFG
  change mEG.beta.hom.app K = _ at hbEG
  rw [hbEF, hbFG, hbEG]
  simp only [rationalMixedBetaComponent, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, eqToIso.hom, eqToIso.inv, Functor.map_comp, Category.assoc]
  have hn := (pbcRationalScalarComp l E F G i j X Fact.out Fact.out).hom.naturality
    (eqToHom (aE.raw_objects K.obj))
  simp only [Functor.comp_map] at hn
  erw [← reassoc_of% hn]
  congr 1
  simp only [eqToHom_map, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  simp only [pbcRationalScalarComp, NatIso.ofComponents_hom_app,
    pbcRationalScalarCompComponent, Functor.mapIso_hom, ObjectProperty.isoMk]
  rw [mixed_raw_map]
  simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [mixed_scalar_map]
  simp only [← Category.assoc]
  congr 1
  simp only [← Functor.map_comp]
  congr 1
  apply ObjectProperty.hom_ext
  simpa only [pbcEmbeddingIntegralTensor, RationalPullIntegral.completedFunctor,
    pbcConditionalIntegral, pbcRationalScalarExtension, pbcRationalization,
    ScalarLocalization.localization, ObjectProperty.lift, Functor.comp_obj,
    Functor.comp_map, ObjectProperty.ι_obj, ObjectProperty.ι_map,
    ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom,
    Iso.app_hom, Category.assoc] using
    mixed_strict_coefficient_tower l E F i g G j K.obj.obj

end CoefficientCoherence

private theorem mixed_normalization_mate {W : Scheme.{u}}
    {R S T : Sheaf (ProEt.topology W) CommRingCat.{u + 1}}
    (a : R ⟶ S) (b : S ⟶ T) (c : R ⟶ T) (h : a ≫ b = c)
    (K : DerivedCategory (pbcModules W R)) :
    (pbcReductionNormalization a b c h K).hom =
      (Adjunction.leftAdjointCompIso (pbcDerivedScalarAdjunction a)
        (pbcDerivedScalarAdjunction b) (pbcDerivedScalarAdjunction c)
        (pbcDerivedRestrictComp a b c h)).hom.app K := by
  dsimp [pbcReductionNormalization, pbcReductionNormalizationHom, pbcReductionTransition]
  simp only [Adjunction.leftAdjointCompIso_hom_app, Adjunction.homEquiv_counit,
    Functor.map_comp, Category.assoc]

private theorem mixed_normalization_assoc {W : Scheme.{u}}
    {R S T V : Sheaf (ProEt.topology W) CommRingCat.{u + 1}}
    (a : R ⟶ S) (b : S ⟶ T) (c : T ⟶ V)
    (ab : R ⟶ T) (bc : S ⟶ V) (abc : R ⟶ V)
    (hab : a ≫ b = ab) (hbc : b ≫ c = bc)
    (hl : ab ≫ c = abc) (hr : a ≫ bc = abc)
    (K : DerivedCategory (pbcModules W R)) :
    (pbcDerivedExtend c).map ((pbcReductionNormalization a b ab hab K).hom) ≫
        (pbcReductionNormalization ab c abc hl K).hom =
      (pbcReductionNormalization b c bc hbc ((pbcDerivedExtend a).obj K)).hom ≫
        (pbcReductionNormalization a bc abc hr K).hom := by
  have ho (M : pbcModules W V) :
      (pbcRestrict a).map ((pbcRestrictComp b c bc hbc).hom.app M) ≫
          (pbcRestrictComp a bc abc hr).hom.app M =
        (pbcRestrictComp a b ab hab).hom.app ((pbcRestrict c).obj M) ≫
          (pbcRestrictComp ab c abc hl).hom.app M := by
    ext U x
    change ((pbcRestrictComp a bc abc hr).hom.app M).val.app U
        (((pbcRestrictComp b c bc hbc).hom.app M).val.app U x) =
      ((pbcRestrictComp ab c abc hl).hom.app M).val.app U
        (((pbcRestrictComp a b ab hab).hom.app ((pbcRestrict c).obj M)).val.app U x)
    simp only [pbcRestrictComp, (pbcRestrictComp_exists a bc abc hr).exists.choose_spec,
      (pbcRestrictComp_exists b c bc hbc).exists.choose_spec,
      (pbcRestrictComp_exists ab c abc hl).exists.choose_spec,
      (pbcRestrictComp_exists a b ab hab).exists.choose_spec]
  have hd (M : DerivedCategory (pbcModules W V)) :=
    Functor.mapDerivedCategoryCompNatIso_cocycle
      (pbcRestrictComp b c bc hbc) (pbcRestrictComp a bc abc hr)
      (pbcRestrictComp a b ab hab) (pbcRestrictComp ab c abc hl) ho M
  have hrest :
      Functor.isoWhiskerLeft (pbcDerivedRestrict c) (pbcDerivedRestrictComp a b ab hab) ≪≫
          pbcDerivedRestrictComp ab c abc hl =
        (Functor.associator _ _ _).symm ≪≫
          Functor.isoWhiskerRight (pbcDerivedRestrictComp b c bc hbc) (pbcDerivedRestrict a) ≪≫
            pbcDerivedRestrictComp a bc abc hr := by
    apply Iso.ext
    apply NatTrans.ext
    funext M
    simpa only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_inv_app, Category.id_comp, pbcDerivedRestrictComp,
      pbcDerivedRestrict, Functor.mapDerivedCategoryCompNatIso] using (hd M).symm
  have he := Adjunction.leftAdjointCompIso_assoc
    (pbcDerivedScalarAdjunction a) (pbcDerivedScalarAdjunction b)
    (pbcDerivedScalarAdjunction c) (pbcDerivedScalarAdjunction ab)
    (pbcDerivedScalarAdjunction bc) (pbcDerivedScalarAdjunction abc)
    (pbcDerivedRestrictComp a b ab hab) (pbcDerivedRestrictComp b c bc hbc)
    (pbcDerivedRestrictComp a bc abc hr) (pbcDerivedRestrictComp ab c abc hl) hrest
  have heK := congrArg (fun e ↦ e.hom.app K) he
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Category.id_comp] at heK
  simpa only [mixed_normalization_mate] using heK.symm

section Pentagon
variable (G H : Type u) [Field G] [Field H]
  [Algebra ℚ_[l] G] [Algebra ℚ_[l] H]
  [FiniteDimensional ℚ_[l] G] [FiniteDimensional ℚ_[l] H]
  (j : F →ₐ[ℚ_[l]] G) (k : G →ₐ[ℚ_[l]] H)
  (sXH : RationalModuleRealization l H X) (sYH : RationalModuleRealization l H Y)
  (aH : RationalRealizationPullbackComparison l H g sXH sYH)
  (mEH : RationalScalarMixedUnitCancellation l E H (k.comp (j.comp i)) g
    sXE sYE sXH sYH aE aH)

/-- The four-field pentagon and mixed pasting use the same zeta and scalar products.
Source: BS 6.8.15, pp. 61--62; Stacks 0G7E, 0D6D and 07A4
(blueprint: lem-per-rational-scalar-mixed-unit-cancellation).

Proof: precompose with scalar extension of the actual completion units. Substitute
the recorded alpha normalization and rationalScalarCompletionUnitSquare. Adjacent
inverse-unit/unit factors cancel. On the same flat-term K-flat representative all
remaining comparisons are the generator-normalized ordinary tensor maps. Geometric
composition uses the canonical inverse-image compositor and scalar insertion; coefficient
composition multiplies the scalar factors. Their associative product is independent of
parentheses. The normalized derived computation counits descend these maps, and the
annihilating-power fraction criterion extends the equations to raw rational morphisms. -/
theorem rationalMixedPentagon
    (K : DerivedCategory (pbcModules Y (rationalCoefficientSheaf l Y E))) :
    (pbcDerivedExtend (rationalBalancedCoefficient l G H k X)).map
        ((pbcReductionNormalization (rationalBalancedCoefficient l E F i X)
          (rationalBalancedCoefficient l F G j X)
          (rationalBalancedCoefficient l E G (j.comp i) X)
          (rationalBalancedCoefficient_comp l E F i X G j)
          ((rationalPullDerived l E g aE.rationalCoefficient).obj K)).hom) ≫
      (pbcReductionNormalization (rationalBalancedCoefficient l E G (j.comp i) X)
        (rationalBalancedCoefficient l G H k X)
        (rationalBalancedCoefficient l E H (k.comp (j.comp i)) X)
        (rationalBalancedCoefficient_comp l E G (j.comp i) X H k)
        ((rationalPullDerived l E g aE.rationalCoefficient).obj K)).hom ≫
      mEH.zeta.hom.app K =
    (pbcReductionNormalization (rationalBalancedCoefficient l F G j X)
      (rationalBalancedCoefficient l G H k X)
      (rationalBalancedCoefficient l F H (k.comp j) X)
      (rationalBalancedCoefficient_comp l F G j X H k)
      ((pbcDerivedExtend (rationalBalancedCoefficient l E F i X)).obj
        ((rationalPullDerived l E g aE.rationalCoefficient).obj K))).hom ≫
      (pbcReductionNormalization (rationalBalancedCoefficient l E F i X)
        (rationalBalancedCoefficient l F H (k.comp j) X)
        (rationalBalancedCoefficient l E H (k.comp (j.comp i)) X)
        (rationalBalancedCoefficient_comp l E F i X H (k.comp j))
        ((rationalPullDerived l E g aE.rationalCoefficient).obj K)).hom ≫
      mEH.zeta.hom.app K := by
  have h := mixed_normalization_assoc
    (rationalBalancedCoefficient l E F i X) (rationalBalancedCoefficient l F G j X)
    (rationalBalancedCoefficient l G H k X)
    (rationalBalancedCoefficient l E G (j.comp i) X)
    (rationalBalancedCoefficient l F H (k.comp j) X)
    (rationalBalancedCoefficient l E H (k.comp (j.comp i)) X)
    (rationalBalancedCoefficient_comp l E F i X G j)
    (rationalBalancedCoefficient_comp l F G j X H k)
    (rationalBalancedCoefficient_comp l E G (j.comp i) X H k)
    (rationalBalancedCoefficient_comp l E F i X H (k.comp j))
    ((rationalPullDerived l E g aE.rationalCoefficient).obj K)
  simpa only [Category.assoc] using congrArg (fun f ↦ f ≫ mEH.zeta.hom.app K) h

end Pentagon

/-- Naturality of both equal routes on all raw morphisms, including fractions with torsion.
Source: BS 6.8.15; Stacks 00CO and 0D6D
(blueprint: lem-per-rational-scalar-mixed-unit-cancellation).

Proof: theta, alpha, zeta and the normalized raw beta are natural transformations.
Whiskering and composing their naturality equations proves the two formulas. For
f/t^n use the recorded realization and pullback fraction formulas. Multiplying the
integral equation by the reciprocal denominator yields precisely the same formula.
If a further power kills a numerator difference, its image is invertible on rational
coefficients; multiplying by that reciprocal proves independence without cancelling
any integral torsion. -/
theorem rationalMixedRawNaturality
    (m : RationalScalarMixedUnitCancellation l E F i g sXE sYE sXF sYF aE aF)
    {K L : PbcRationalDerivedCategory l E Y Fact.out Fact.out} (f : K ⟶ L) :
    (sXF.J.map ((pbcRationalScalarExtension l E F i X Fact.out Fact.out).map
        (aE.rawPull.map f)) ≫ rationalMixedLeft l E F i g sXE sYE sXF sYF aE aF m L =
      rationalMixedLeft l E F i g sXE sYE sXF sYF aE aF m K ≫
        (rationalPullDerived l F g aF.rationalCoefficient).map
          ((pbcDerivedExtend (rationalBalancedCoefficient l E F i Y)).map (sYE.J.map f))) ∧
    (sXF.J.map ((pbcRationalScalarExtension l E F i X Fact.out Fact.out).map
        (aE.rawPull.map f)) ≫ rationalMixedRight l E F i g sXE sYE sXF sYF aE aF m L =
      rationalMixedRight l E F i g sXE sYE sXF sYF aE aF m K ≫
        (rationalPullDerived l F g aF.rationalCoefficient).map
          ((pbcDerivedExtend (rationalBalancedCoefficient l E F i Y)).map (sYE.J.map f))) := by
  let t := Functor.whiskerLeft aE.rawPull (rationalBalancedTheta l E F i X sXE sXF).hom ≫
    Functor.whiskerRight aE.alpha.hom (pbcDerivedExtend (rationalBalancedCoefficient l E F i X)) ≫
      Functor.whiskerLeft sYE.J m.zeta.hom
  have hleft : sXF.J.map ((pbcRationalScalarExtension l E F i X Fact.out Fact.out).map
        (aE.rawPull.map f)) ≫ rationalMixedLeft l E F i g sXE sYE sXF sYF aE aF m L =
      rationalMixedLeft l E F i g sXE sYE sXF sYF aE aF m K ≫
        (rationalPullDerived l F g aF.rationalCoefficient).map
          ((pbcDerivedExtend (rationalBalancedCoefficient l E F i Y)).map (sYE.J.map f)) := by
    simpa only [t, rationalMixedLeft, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.comp_map] using t.naturality f
  refine ⟨hleft, ?_⟩
  simpa only [rationalMixedLeft, rationalMixedRight, m.compatibility] using hleft

/-- The derived coefficient unitor from the owning node's multiplication-normalized theorem.
Its section formula a tensor m maps to a*m, its derived computation and its raw theta
normalization determine the selected data. No new unit comparison is assumed.
Source: BS 6.8.14(2), 6.8.15; Stacks 0D6D
(blueprint: lem-per-rational-scalar-mixed-unit-cancellation). -/
def rationalMixedCoefficientUnitor (W : Scheme.{u}) [IsNoetherian W]
    [Fact (∃ n : ℕ, topologicalKrullDim W ≤ n)]
    [Fact (∀ w : W, IsUnit (l : W.presheaf.stalk w))]
    (sW : RationalModuleRealization l E W) :
    pbcDerivedExtend (rationalBalancedCoefficient l E E (AlgHom.id ℚ_[l] E) W) ≅ 𝟭 _ :=
  (rationalBalancedIdentity l E W sW).2.choose_spec.choose

/-- Equal coefficient fields give the very same multiplication and raw tensor unitors.
Source: BS 6.8.14(2), 6.8.15; Stacks 0D6D
(blueprint: lem-per-rational-scalar-mixed-unit-cancellation).

Proof: specialize the balanced coefficient map to the identity. Its ordinary tensor
unitor is multiplication, and the derived computation retains this normalization.
On tensor generators both routes remove the same unit factor. Thus zeta has the
first equation. Precompose strict beta by the actual completion unit, apply its
unit equation and cancel that unit. This gives the raw equation after scalar
localization, including the annihilating-power relation. The specified stage
normalization identifies this raw tensor unit with the literal identity functor. -/
theorem rationalMixedCoefficientIdentity
    (m : RationalScalarMixedUnitCancellation l E E (AlgHom.id ℚ_[l] E) g
      sXE sYE sXE sYE aE aE) :
    (∀ K : DerivedCategory (pbcModules Y (rationalCoefficientSheaf l Y E)),
      m.zeta.hom.app K ≫ (rationalPullDerived l E g aE.rationalCoefficient).map
          ((rationalMixedCoefficientUnitor l E Y sYE).hom.app K) =
        (rationalMixedCoefficientUnitor l E X sXE).hom.app
          ((rationalPullDerived l E g aE.rationalCoefficient).obj K)) ∧
    (∀ K : PbcRationalDerivedCategory l E Y Fact.out Fact.out,
      m.beta.hom.app K ≫ aE.rawPull.map
          ((pbcRationalScalarUnit l E Y Fact.out Fact.out).hom.app K) =
        (pbcRationalScalarUnit l E X Fact.out Fact.out).hom.app (aE.rawPull.obj K)) := by
  sorry

/-- Flatten the common target to F_X tensor over g-inverse B_E,Y of g-inverse K.
Every arrow is an existing normalized comparison; in particular the inverse zeta
and ordinary alpha comparison use the same localized coefficient square.
Source: BS 6.8.15; Stacks 0D6D
(blueprint: lem-per-rational-scalar-mixed-unit-cancellation). -/
def rationalMixedTargetFlatten
    (m : RationalScalarMixedUnitCancellation l E F i g sXE sYE sXF sYF aE aF)
    (K : PbcBoundedConstructibleComplete Y (pbcIntegralDatum l E)) :=
  (rationalPullDerived l F g aF.rationalCoefficient).map
      ((pbcDerivedExtend (rationalBalancedCoefficient l E F i Y)).map
        (eqToHom (sYE.objects K))) ≫
    m.zeta.inv.app ((pbcDerivedExtend (rationalPullScalar l E sYE)).obj K.obj) ≫
    (pbcDerivedExtend (rationalBalancedCoefficient l E F i X)).map
      (aE.ordinaryComparison.inv.app K.obj) ≫
    (rationalBalancedT l E F i X sXE
      ((pbcActualDerivedPull g (pbcIntegralDatum l E)).obj K.obj)).hom

/-- After the actual unit precomposition, both maps flatten by s to the same single tensor.
This identifies their common ordinary value, rather than only comparing endpoints.
Source: BS 6.8.15; Stacks 0G7E, 0D6D, 07A4
(blueprint: lem-per-rational-scalar-mixed-unit-cancellation).

Proof: substitute the two precomposition equations. In the target flattening the
recorded object transports, zeta and ordinary alpha cancel with their inverses.
The remaining theta followed by t is s, by the definition of rationalBalancedTheta.
The recorded realization object equation supplies exactly the initial transport.
The balanced tensor-model theorem computes s by multiplying the adjacent coefficient
factors. Its finite-projection coefficient square makes this l' i(b') tensor p on
simultaneous flat-term K-flat models; all maps commute with site restrictions.
The computation counits identify that chain formula in the unbounded derived category. -/
theorem rationalMixedCommonTensor
    (m : RationalScalarMixedUnitCancellation l E F i g sXE sYE sXF sYF aE aF)
    (K : PbcBoundedConstructibleComplete Y (pbcIntegralDatum l E)) :
    (rationalMixedUnitPrecomposition l E F i g sXE sYE sXF aE K ≫
      rationalMixedLeft l E F i g sXE sYE sXF sYF aE aF m
        ((pbcRationalization Y (pbcIntegralDatum l E) (pbcUniformizer l E)).obj K) ≫
      rationalMixedTargetFlatten l E F i g sXE sYE sXF sYF aE aF m K =
      eqToHom (sXF.objects
        ((pbcEmbeddingIntegralTensor l E F i X Fact.out Fact.out).obj
          ⟨(pbcActualDerivedPull g (pbcIntegralDatum l E)).obj K.obj,
            aE.integral.ordinary_mem K⟩)) ≫
        (rationalBalancedS l E F i X sXE sXF
          ((pbcActualDerivedPull g (pbcIntegralDatum l E)).obj K.obj)).hom) ∧
    (rationalMixedUnitPrecomposition l E F i g sXE sYE sXF aE K ≫
      rationalMixedRight l E F i g sXE sYE sXF sYF aE aF m
        ((pbcRationalization Y (pbcIntegralDatum l E) (pbcUniformizer l E)).obj K) ≫
      rationalMixedTargetFlatten l E F i g sXE sYE sXF sYF aE aF m K =
      eqToHom (sXF.objects
        ((pbcEmbeddingIntegralTensor l E F i X Fact.out Fact.out).obj
          ⟨(pbcActualDerivedPull g (pbcIntegralDatum l E)).obj K.obj,
            aE.integral.ordinary_mem K⟩)) ≫
        (rationalBalancedS l E F i X sXE sXF
          ((pbcActualDerivedPull g (pbcIntegralDatum l E)).obj K.obj)).hom) := by
  obtain ⟨_, hleft, hright⟩ :=
    rationalMixedUnitPrecomposition_eq l E F i g sXE sYE sXF sYF aE aF m K
  have hcommon : rationalMixedOrdinaryPath l E F i g sXE sYE sXF sYF aE aF m K ≫
      rationalMixedTargetFlatten l E F i g sXE sYE sXF sYF aE aF m K =
      eqToHom (sXF.objects
        ((pbcEmbeddingIntegralTensor l E F i X Fact.out Fact.out).obj
          ⟨(pbcActualDerivedPull g (pbcIntegralDatum l E)).obj K.obj,
            aE.integral.ordinary_mem K⟩)) ≫
        (rationalBalancedS l E F i X sXE sXF
          ((pbcActualDerivedPull g (pbcIntegralDatum l E)).obj K.obj)).hom := by
    unfold rationalMixedOrdinaryPath rationalMixedTargetFlatten
    simp only [Functor.map_comp, Category.assoc]
    have hz := m.zeta.hom.naturality (eqToHom (sYE.objects K))
    simp only [Functor.comp_map] at hz
    rw [← reassoc_of% hz]
    simp only [Iso.hom_inv_id_app_assoc, ← Functor.map_comp_assoc,
      eqToHom_trans, eqToHom_refl, CategoryTheory.Functor.map_id,
      Category.id_comp, Iso.hom_inv_id_app]
    change (rationalBalancedComponent l E F i X sXE sXF _).hom ≫ _ = _
    dsimp only [rationalBalancedComponent]
    simp only [Iso.trans_hom, Iso.symm_hom, eqToIso.hom, eqToIso.inv,
      Functor.mapIso_hom, Category.assoc, ← Functor.map_comp_assoc]
    erw [Category.comp_id, eqToHom_trans, eqToHom_refl,
      CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id, Category.comp_id]
    rfl
  constructor
  · rw [← Category.assoc, hleft]
    exact hcommon
  · rw [← Category.assoc, hright]
    exact hcommon

end AlgebraicGeometry.Scheme
