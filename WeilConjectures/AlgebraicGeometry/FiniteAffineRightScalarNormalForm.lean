/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Ordered.OrderedAffineTraceNormalForm
public import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceRightNormalForm
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalObjects
public import WeilConjectures.AlgebraicGeometry.ChartScalarReassociation
public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothCoefficientArrows
public import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitudePresentations
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf

/-! # Ordered affine scalar exchange and its single normal form

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-reduction/
sk-lem-sp-reduction-exceptional.proof.md, Charts, retained Steps 4 and 10--11
(blueprint: lem-sp-finite-affine-right-scalar-normal-form).

The single reassociation is constructed independently of the tower exchange from
scalar shift, tensor, inverse image and ordinary root balancing. All tensor powers
retain their order. The left-Tate convention of the published chart operation is
related to the right-Tate convention of the ordered tower by its canonical symmetry.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

/-- Derived change of coefficients of the actual finite Tate power, by the ordinary
balanced map on roots. The scalar/single map is the adjunction transpose of the scalar
unit. Source: Charts, flat Tate line (blueprint: lem-sp-finite-affine-right-scalar-normal-form).
-/
def finiteAffineTateScalarMap
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) (N : ℕ)
    (hA : (N : A) = 0) (hB : (N : B) = 0) (d : ℕ) :
    (scalarExtension φ T).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj
        (Scheme.finiteEtaleTateTwist T N A hA d)) ⟶
      (_root_.DerivedCategory.singleFunctor _ 0).obj
        (Scheme.finiteEtaleTateTwist T N B hB d) :=
  WeilConjectures.PurityFiniteSetting.purityScalarSingleMap φ T _ ≫
    (_root_.DerivedCategory.singleFunctor _ 0).map
      (ProEtale.chartEtaleTateScalarIso φ T N hA hB d).hom

/-- Single scalar/tensor/pullback reassociation, with the Tate factor on the right.
It uses the normalized scalar tensorator, inverse scalar/pullback comparison, ordinary
Tate balancing, then the shift. Source: Charts, displayed single reassociation
(blueprint: lem-sp-finite-affine-right-scalar-normal-form). -/
def finiteAffineNormalScalarMap
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (N : ℕ) (hA : (N : A) = 0) (hB : (N : B) = 0)
    {X S : Scheme.{u}} (f : X ⟶ S) (d : ℕ) (b : ℤ)
    (K : DerivedCategoryModule A S) :
    (scalarExtension φ X).obj
        ((ordinaryFinitePullback A f ⋙ derivedTensorRight (ModuleCat.{u + 1} A) X
          ((_root_.DerivedCategory.singleFunctor _ 0).obj
            (Scheme.finiteEtaleTateTwist X N A hA d)) ⋙ shiftFunctor _ b).obj K) ⟶
      (ordinaryFinitePullback B f ⋙ derivedTensorRight (ModuleCat.{u + 1} B) X
        ((_root_.DerivedCategory.singleFunctor _ 0).obj
          (Scheme.finiteEtaleTateTwist X N B hB d)) ⋙ shiftFunctor _ b).obj
            ((scalarExtension φ S).obj K) :=
  (FiniteSmoothPurity.scalarShiftIso φ X b).hom.app _ ≫
    (shiftFunctor _ b).map
      ((ExceptionalCoefficients.tensorIso φ X).hom.app
          ((ordinaryFinitePullback A f).obj K,
            (_root_.DerivedCategory.singleFunctor _ 0).obj
              (Scheme.finiteEtaleTateTwist X N A hA d)) ≫
        derivedTensorHom (ModuleCat.{u + 1} B)
          ((scalarPullbackIso φ f).inv.app K) (finiteAffineTateScalarMap φ X N hA hB d))

/-- The single normal-form comparison, with the literal identity at zero coordinates.
Source: Charts, unit conventions (blueprint: lem-sp-finite-affine-right-scalar-normal-form). -/
def finiteAffineOrderedScalarMap
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (N : ℕ) (hA : (N : A) = 0) (hB : (N : B) = 0)
    (S : Scheme.{u}) : (d : ℕ) → (K : DerivedCategoryModule A S) →
    (scalarExtension φ (affineTraceTower S d)).obj
        ((orderedAffineRight A N hA S d).obj K) ⟶
      (orderedAffineRight B N hB S d).obj ((scalarExtension φ S).obj K)
  | 0, K => 𝟙 ((scalarExtension φ S).obj K)
  | d + 1, K =>
      finiteAffineNormalScalarMap φ N hA hB (affineTraceProjection S (d + 1))
        (d + 1) (2 * ((d + 1 : ℕ) : ℤ)) K

/-- Exact-derived version of the scalar/pullback comparison, using the canonical
exact-to-left-derived identifications. Source: Charts, etale chart restriction
(blueprint: lem-sp-finite-affine-right-scalar-normal-form). -/
def finiteAffineExactPullbackScalarIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {X S : Scheme.{u}} (f : X ⟶ S) :
    (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory ⋙ scalarExtension φ X ≅
      scalarExtension φ S ⋙ (upperStar (ModuleCat.{u + 1} B) f).mapDerivedCategory :=
  Functor.isoWhiskerRight
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).symm _ ≪≫
    (scalarPullbackIso φ f).symm ≪≫
    Functor.isoWhiskerLeft _
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) f)

/-- The same single reassociation in the published chart operation's left-Tate
convention. Source: Charts, restriction to e (blueprint:
lem-sp-finite-affine-right-scalar-normal-form). -/
def finiteAffineChartScalarMap
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (N : ℕ) (hA : (N : A) = 0) (hB : (N : B) = 0)
    {X S : Scheme.{u}} (f : X ⟶ S) (d : ℕ) (b : ℤ)
    (K : DerivedCategoryModule A S) :
    (scalarExtension φ X).obj
        ((ProEtale.AdjunctionTransfer.etaleChartOperation A N hA f d b).obj K) ⟶
      (ProEtale.AdjunctionTransfer.etaleChartOperation B N hB f d b).obj
        ((scalarExtension φ S).obj K) :=
  (FiniteSmoothPurity.scalarShiftIso φ X b).hom.app _ ≫
    (shiftFunctor _ b).map
      ((ExceptionalCoefficients.tensorIso φ X).hom.app
          ((_root_.DerivedCategory.singleFunctor _ 0).obj
              (Scheme.finiteEtaleTateTwist X N A hA d),
            (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory.obj K) ≫
        derivedTensorHom (ModuleCat.{u + 1} B) (finiteAffineTateScalarMap φ X N hA hB d)
          ((finiteAffineExactPullbackScalarIso φ f).hom.app K))

/-- Expand the identity normal form at zero into its canonical pullback, Tate-unit
and zero-shift presentation; positive dimensions already have that presentation.
Source: Charts, zero-coordinate units (blueprint:
lem-sp-finite-affine-right-scalar-normal-form). -/
def finiteAffineExpandOrderedIso
    (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    (S : Scheme.{u}) : (d : ℕ) →
    orderedAffineRight A N hA S d ≅
      ordinaryFinitePullback A (affineTraceProjection S d) ⋙
        derivedTensorRight (ModuleCat.{u + 1} A) (affineTraceTower S d)
          ((_root_.DerivedCategory.singleFunctor _ 0).obj
            (Scheme.finiteEtaleTateTwist (affineTraceTower S d) N A hA d)) ⋙
        shiftFunctor _ (2 * (d : ℤ))
  | 0 =>
      (Functor.isoWhiskerRight (leftDerivedUpperStarId (ModuleCat.{u + 1} A) S) _ ≪≫
        Functor.leftUnitor _ ≪≫
        Functor.isoWhiskerRight
          ((derivedTensorRightFunctor (ModuleCat.{u + 1} A) S).mapIso
            (singleFunctorObjUnitIso (ModuleCat.{u + 1} A) S) ≪≫
              derivedTensorRightUnitorNatIso (ModuleCat.{u + 1} A) S) _ ≪≫
        Functor.leftUnitor _ ≪≫ shiftFunctorZero _ ℤ).symm
  | _ + 1 => Iso.refl _

/-- Expand the prescribed tower normal form and restrict it to a chart. The ordered
Tate pullback is followed by the canonical symmetry converting to the chart operation's
left-Tate convention. Source: Charts, ordered normal form and chart restriction
(blueprint: lem-sp-finite-affine-right-scalar-normal-form). -/
def finiteAffineChartNormalIso
    (A : Type (u + 1)) [CommRing A] [Finite A] (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤)))
    (d : ℕ) {U : Scheme.{u}} (e : U ⟶ affineTraceTower S d)
    (K : DerivedCategoryModule A S) :
    (ordinaryFinitePullback A e).obj ((affineTraceRight A N hA S d).obj K) ≅
      (ProEtale.AdjunctionTransfer.etaleChartOperation A N hA
        (e ≫ affineTraceProjection S d) d (2 * (d : ℤ))).obj K :=
  (ordinaryFinitePullback A e).mapIso
      (((orderedAffineRightIso A N hN hA S hS d).app K) ≪≫
        (finiteAffineExpandOrderedIso A N hA S d).app K) ≪≫
    (tensorEPullback (ModuleCat.{u + 1} A) N
      (fun X r ↦ Scheme.finiteEtaleTateSheaf A N X hA (r : ℤ))
      (fun f hX r ↦ (Scheme.finiteEtaleTwistPullbackData A N hN hA).c f hX
        (affineTracePullbackInvertible N f hX) r)
      e (affineTraceInvertible N S hS d) d (2 * (d : ℤ))).app
        ((ordinaryFinitePullback A (affineTraceProjection S d)).obj K) ≪≫
    (shiftFunctor _ (2 * (d : ℤ))).mapIso
      ((derivedTensorRight (ModuleCat.{u + 1} A) U
          ((_root_.DerivedCategory.singleFunctor _ 0).obj
            (Scheme.finiteEtaleTateTwist U N A hA d))).mapIso
          ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) e
            (affineTraceProjection S d)).symm.app K) ≪≫
        ((derivedTensorSymmetry (ModuleCat.{u + 1} A) U).app
          ((ordinaryFinitePullback A (e ≫ affineTraceProjection S d)).obj K)).app
            ((_root_.DerivedCategory.singleFunctor _ 0).obj
              (Scheme.finiteEtaleTateTwist U N A hA d)) ≪≫
        ((derivedTensor (ModuleCat.{u + 1} A) U).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj
            (Scheme.finiteEtaleTateTwist U N A hA d))).mapIso
              ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A)
                (e ≫ affineTraceProjection S d)).app K))

/-- The ordered coordinate exchange agrees with the independently constructed
single scalar reassociation after the specified ordered normal forms.

Source: Charts, retained Steps 4 and 10 (blueprint:
lem-sp-finite-affine-right-scalar-normal-form).
Proof: induct on d, starting with identity exchanges and normal forms. At a successor,
expand the coordinate exchange and the recursion defining orderedAffineRightIso.
Scalar/pullback composition and tensor compatibility move the old scalar exchange
through the new pullback. Balanced Tate change commutes with the ordered Tate product
and its pullback; the pure-section map is (z tensor a) tensor b mapped to
z tensor phi(a)b. Shift compatibility adds the two even shifts. The two resulting
composites are equal by tensor associativity and unit coherence, with no permutation
of Tate factors. Flatness of the Tate line makes its scalar/single map invertible.
All comparisons in the single reassociation are therefore invertible. -/
theorem finiteAffineRightScalarNormalForm
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (K : DerivedCategoryModule A S)
    (_hBounded : _root_.DerivedCategory.TStructure.t.bounded K)
    (_hConstructible : ∀ i : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
      ((_root_.DerivedCategory.homologyFunctor
        (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)) i).obj K))
    (_hTor : ∃ a b : ℤ, a ≤ b ∧ _root_.DerivedCategory.torAmplitudeIn
      (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)) a b K) :
    IsIso (finiteAffineOrderedScalarMap φ N hA hB S d K) ∧
      (ProEtale.reductionEtaleAffineScalarIso φ S N hA hB hS d K).hom ≫
          (orderedAffineRightIso B N hN hB S hS d).hom.app ((scalarExtension φ S).obj K) =
        (scalarExtension φ (affineTraceTower S d)).map
            ((orderedAffineRightIso A N hN hA S hS d).hom.app K) ≫
          finiteAffineOrderedScalarMap φ N hA hB S d K := by
  sorry

end AlgebraicGeometry.Etale
