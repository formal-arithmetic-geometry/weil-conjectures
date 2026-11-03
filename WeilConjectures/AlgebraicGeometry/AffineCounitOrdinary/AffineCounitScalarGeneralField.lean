/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceConstruction
public import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveLineTraceSupplement
public import WeilConjectures.AlgebraicGeometry.FiniteCompactCoefficients.FiniteCoefficientCompactSupportCompatibility
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.CoefficientScalarRepresentatives.CoefficientScalarRepresentatives
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ReductionExtendScalars
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure

/-!
# Ordered affine counit under ordinary coefficient extension

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-change-of-finite-coefficients/sk-lem-sp-reduction/
sk-lem-sp-reduction-exceptional.proof.md, Charts: iterated projective-line integration
(blueprint: lem-sp-affine-counit-scalar).
All coefficient arrows use the ordinary scalar left adjoint to exact restriction.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale
open ProEtale.OrdinaryScalarSite

namespace AffineCounitOrdinary

/-- The ordinary scalar tensorator, transported through the unit-compatible uniqueness
of scalar left adjoints. The middle map is the K-flat derived tensor comparison.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-change-of-finite-coefficients/sk-lem-sp-reduction/
sk-lem-sp-reduction-exceptional.proof.md, Charts (blueprint: lem-sp-affine-counit-scalar). -/
def tensorIso {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) (M L : DerivedCategoryModule A T) :
    (scalar T.smallEtaleTopology φ).obj (M ⊗ L) ≅
      (scalar T.smallEtaleTopology φ).obj M ⊗ (scalar T.smallEtaleTopology φ).obj L := by
  let E := CoefficientScalarRepresentatives.ordinaryExtension T.smallEtaleTopology φ
  let J := T.smallEtaleTopology
  letI : E.PreservesKFlatQuasiIso := by
    classical
    let E := CoefficientScalarRepresentatives.ordinaryExtension J φ
    let U := Sheaf.restrictScalars J φ
    let adj : E ⊣ U :=
      Sheaf.adjunction J (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} φ)
    have : E.Additive := adj.left_adjoint_additive
    let coef := (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} φ).obj (ModuleCat.of B B)
    let X := (Functor.const T.Etaleᵒᵖ).obj coef
    let a := presheafToSheaf J (ModuleCat.{u + 1} A)
    let a' := presheafToSheaf J (ModuleCat.{u + 1} B)
    let F := sheafToPresheaf J (ModuleCat.{u + 1} A)
    let W := (Functor.whiskeringRight T.Etaleᵒᵖ _ _).obj
      (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ)
    have : J.PreservesSheafification (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} φ) :=
      Sheaf.preservesSheafification_of_adjunction J
        (ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} φ)
    let e : E ⋙ U ≅ MonoidalCategory.tensorRight (a.obj X) :=
      Functor.associator F (W ⋙ a') U ≪≫
        Functor.isoWhiskerLeft F (Functor.associator W a' U) ≪≫
        Functor.isoWhiskerLeft F (Functor.isoWhiskerLeft W
          (sheafComposeNatIso J (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} φ)
            (sheafificationAdjunction J (ModuleCat.{u + 1} B))
            (sheafificationAdjunction J (ModuleCat.{u + 1} A))).symm) ≪≫
        Functor.isoWhiskerLeft F (Functor.associator W _ a).symm ≪≫
        Functor.isoWhiskerLeft F (Functor.isoWhiskerRight
          (Functor.whiskeringRightObjCompIso _ _ ≪≫
            (Functor.whiskeringRight _ _ _).mapIso
              (ModuleCat.extendScalarsCompRestrictScalarsIso.{u + 1} φ) ≪≫
            whiskeringRightTensorRightIso _) a) ≪≫
        Functor.isoWhiskerLeft F (Sheaf.presheafToSheafCompTensorRightIso X).symm ≪≫
        (Functor.associator F a (MonoidalCategory.tensorRight (a.obj X))).symm ≪≫
        Functor.isoWhiskerRight
          (asIso (sheafificationAdjunction J (ModuleCat.{u + 1} A)).counit)
          (MonoidalCategory.tensorRight (a.obj X)) ≪≫ Functor.leftUnitor _
    have hU : U.Faithful := inferInstance
    have : HasColimitsOfSize.{u + 1, u + 1} (Sheaf J (ModuleCat.{u + 1} A)) :=
      IsGrothendieckAbelian.hasColimits _
    have : HasColimitsOfSize.{0, 0} (Sheaf J (ModuleCat.{u + 1} A)) :=
      hasColimitsOfSizeShrink.{0, 0, u + 1, u + 1} _
    have : HasCountableCoproducts (Sheaf J (ModuleCat.{u + 1} A)) :=
      ⟨fun K _ ↦ HasColimitsOfSize.has_colimits_of_shape (Discrete K)⟩
    have : E.PreservesKFlatQuasiIso := by
      apply CategoryTheory.Functor.PreservesKFlatQuasiIso.mk'
      intro K hK hKa
      have ht := CochainComplex.acyclic_tensorRight_of_kFlat K hK hKa (a.obj X)
      have hEU := ht.of_iso
        ((NatIso.mapHomologicalComplex e (.up ℤ)).app K).symm
      have hUK : ((U.mapHomologicalComplex (.up ℤ)).obj
          ((E.mapHomologicalComplex (.up ℤ)).obj K)).Acyclic :=
        hEU.of_iso ((CategoryTheory.Functor.mapHomologicalComplexCompIso
          (Iso.refl (E ⋙ U)) (.up ℤ)).app K)
      intro n
      exact (ShortComplex.exact_map_iff_of_faithful _ U).1 (hUK n)
    infer_instance
  let e := (CoefficientScalarRepresentatives.adjunction T.smallEtaleTopology φ).leftAdjointUniq
    ((CoefficientScalarRepresentatives.ordinaryAdjunction T.smallEtaleTopology φ).derivedAdjunction
      |>.ofNatIsoRight
        (Sheaf.restrictScalars T.smallEtaleTopology φ).rightDerivedFunctorIsoMapDerivedCategory)
  letI : E.Monoidal := Sheaf.monoidal_extendScalars T.smallEtaleTopology φ
  letI : E.IsLeftAdjoint :=
    (CoefficientScalarRepresentatives.ordinaryAdjunction T.smallEtaleTopology φ).isLeftAdjoint
  letI : E.PreservesFlat := Sheaf.preservesFlat_extendScalars T.smallEtaleTopology (f := φ)
  letI : E.leftDerivedFunctor.Monoidal := E.leftDerivedFunctorMonoidal
  exact e.app (M ⊗ L) ≪≫ (Functor.Monoidal.μIso E.leftDerivedFunctor M L).symm ≪≫
    ((e.symm.app M) ⊗ᵢ (e.symm.app L))

/-- Inverse-image balancing for the ordinary scalar functor, with the existing exact
inverse-image identifications at both ends.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-change-of-finite-coefficients/sk-lem-sp-reduction/
sk-lem-sp-reduction-exceptional.proof.md, Charts (blueprint: lem-sp-affine-counit-scalar). -/
def pullbackIso {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ordinaryFinitePullback A f ⋙ scalar X.smallEtaleTopology φ ≅
      scalar Y.smallEtaleTopology φ ⋙ ordinaryFinitePullback B f :=
  Functor.isoWhiskerRight
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f) _ ≪≫
    (etaleIso φ f).symm ≪≫ Functor.isoWhiskerLeft _
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) f).symm

/-- Scalar balancing on the concrete root line. Adjoint uniqueness for the two
sheafified Z/N extension functors fixes the map on every scalar/root tensor.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-change-of-finite-coefficients/sk-lem-sp-reduction/
sk-lem-sp-reduction-exceptional.proof.md, Charts (blueprint: lem-sp-affine-counit-scalar). -/
def tateSheafIso {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) (N : ℕ) (hA : (N : A) = 0) (hB : (N : B) = 0) :
    (CoefficientScalarRepresentatives.ordinaryExtension T.smallEtaleTopology φ).obj
        (Scheme.finiteEtaleTateLine T N A hA) ≅ Scheme.finiteEtaleTateLine T N B hB := by
  let J := T.smallEtaleTopology
  let rA := Scheme.finiteEtaleTwistScalar N A hA
  let rB := Scheme.finiteEtaleTwistScalar N B hB
  have hr : rB = φ.comp rA := Subsingleton.elim _ _
  let a := (ModuleCat.extendRestrictScalarsAdj.{u + 1, 0, u + 1} rA).whiskerRight
    T.Etaleᵒᵖ |>.comp (sheafificationAdjunction J (ModuleCat.{u + 1} A))
  let b := (ModuleCat.extendRestrictScalarsAdj.{u + 1, 0, u + 1} rB).whiskerRight
    T.Etaleᵒᵖ |>.comp (sheafificationAdjunction J (ModuleCat.{u + 1} B))
  let c := a.comp (CoefficientScalarRepresentatives.ordinaryAdjunction J φ)
  let r : Sheaf.restrictScalars J φ ⋙
      (sheafToPresheaf J (ModuleCat.{u + 1} A) ⋙
        (Functor.whiskeringRight T.Etaleᵒᵖ _ _).obj (ModuleCat.restrictScalars rA)) ≅
      sheafToPresheaf J (ModuleCat.{u + 1} B) ⋙
        (Functor.whiskeringRight T.Etaleᵒᵖ _ _).obj (ModuleCat.restrictScalars rB) :=
    NatIso.ofComponents (fun L ↦
      Functor.isoWhiskerLeft L.obj (ModuleCat.restrictScalarsComp' rA φ rB hr).symm)
      (by intro L M f; ext W x; rfl)
  exact ((c.ofNatIsoRight r).leftAdjointUniq b).app (Scheme.finiteEtaleMuModulePresheaf T N)

/-- The derived scalar arrow on one Tate line is the transpose of its ordinary
root-normalized map, with the exact restriction/single comparison displayed.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-change-of-finite-coefficients/sk-lem-sp-reduction/
sk-lem-sp-reduction-exceptional.proof.md, Charts (blueprint: lem-sp-affine-counit-scalar). -/
def tateMap {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) (N : ℕ) (hA : (N : A) = 0) (hB : (N : B) = 0) :
    (scalar T.smallEtaleTopology φ).obj (ordinaryFiniteLine A N hA T) ⟶
      ordinaryFiniteLine B N hB T :=
  ((CoefficientScalarRepresentatives.adjunction T.smallEtaleTopology φ).homEquiv _ _).symm
    ((_root_.DerivedCategory.singleFunctor _ 0).map
      ((CoefficientScalarRepresentatives.ordinaryAdjunction T.smallEtaleTopology φ).homEquiv
        _ _ (tateSheafIso φ T N hA hB).hom) ≫
      ((Sheaf.restrictScalars T.smallEtaleTopology φ).mapDerivedCategorySingleFunctor 0).inv.app
        (Scheme.finiteEtaleTateLine T N B hB))

/-- Commute ordinary scalar extension with the even shift on the root line.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-change-of-finite-coefficients/sk-lem-sp-reduction/
sk-lem-sp-reduction-exceptional.proof.md, Charts (blueprint: lem-sp-affine-counit-scalar). -/
def shiftedLineMap {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) (N : ℕ) (hA : (N : A) = 0) (hB : (N : B) = 0) :
    (scalar T.smallEtaleTopology φ).obj ((ordinaryFiniteLine A N hA T)⟦(2 : ℤ)⟧) ⟶
      (ordinaryFiniteLine B N hB T)⟦(2 : ℤ)⟧ :=
  letI : (scalar T.smallEtaleTopology φ).CommShift ℤ :=
    (CoefficientScalarRepresentatives.adjunction T.smallEtaleTopology φ).leftAdjointCommShift ℤ
  ((scalar T.smallEtaleTopology φ).commShiftIso (2 : ℤ)).hom.app _ ≫
    (tateMap φ T N hA hB)⟦(2 : ℤ)⟧'

/-- One projective coordinate: tensor balancing, pullback balancing, and the shifted
root-line map, in that order.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-change-of-finite-coefficients/sk-lem-sp-reduction/
sk-lem-sp-reduction-exceptional.proof.md, Charts (blueprint: lem-sp-affine-counit-scalar). -/
def p1Map {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (S : Scheme.{u}) (N : ℕ) (hA : (N : A) = 0) (hB : (N : B) = 0)
    (K : DerivedCategoryModule A S) :
    (scalar (ProjectiveLine S).smallEtaleTopology φ).obj
        ((ordinaryFiniteP1Right A N hA S).obj K) ⟶
      (ordinaryFiniteP1Right B N hB S).obj ((scalar S.smallEtaleTopology φ).obj K) :=
  (tensorIso φ (ProjectiveLine S)
      ((ordinaryFinitePullback A (ProjectiveLine S ↘ S)).obj K)
      ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧)).hom ≫
    ((pullbackIso φ (ProjectiveLine S ↘ S)).hom.app K ⊗ₘ
      shiftedLineMap φ (ProjectiveLine S) N hA hB)

/-- Restrict the projective-coordinate scalar comparison to its standard affine chart.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-change-of-finite-coefficients/sk-lem-sp-reduction/
sk-lem-sp-reduction-exceptional.proof.md, Charts (blueprint: lem-sp-affine-counit-scalar). -/
def lineMap {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (S : Scheme.{u}) (N : ℕ) (hA : (N : A) = 0) (hB : (N : B) = 0)
    (K : DerivedCategoryModule A S) :
    (scalar (AffineSpace PUnit.{u + 1} S).smallEtaleTopology φ).obj
        ((affineTraceLineRight A N hA S).obj K) ⟶
      (affineTraceLineRight B N hB S).obj ((scalar S.smallEtaleTopology φ).obj K) :=
  (pullbackIso φ (ProjectiveLine.affineChart S)).hom.app _ ≫
    (ordinaryFinitePullback B (ProjectiveLine.affineChart S)).map (p1Map φ S N hA hB K)

/-- The canonical arrow a_(d,K), recursively on ordered coordinates; at zero it is
literally the identity. Its factors are ordinary tensor/pullback, Tate, and shift maps.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-change-of-finite-coefficients/sk-lem-sp-reduction/
sk-lem-sp-reduction-exceptional.proof.md, Charts (blueprint: lem-sp-affine-counit-scalar). -/
def rightMap {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (S : Scheme.{u}) (N : ℕ) (hA : (N : A) = 0) (hB : (N : B) = 0) :
    (d : ℕ) → (K : DerivedCategoryModule A S) →
      (scalar (affineTraceTower S d).smallEtaleTopology φ).obj
          ((affineTraceRight A N hA S d).obj K) ⟶
        (affineTraceRight B N hB S d).obj ((scalar S.smallEtaleTopology φ).obj K)
  | 0, _K => 𝟙 _
  | d + 1, K => lineMap φ (affineTraceTower S d) N hA hB
      ((affineTraceRight A N hA S d).obj K) ≫
      (affineTraceLineRight B N hB (affineTraceTower S d)).map (rightMap φ S N hA hB d K)

/-- The coefficient-free ordered left comparison with the specified compactification.
Its factors are the canonical proper/open composition and refinement comparisons.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-change-of-finite-coefficients/sk-lem-sp-reduction/
sk-lem-sp-reduction-exceptional.proof.md, Charts (blueprint: lem-sp-affine-counit-scalar). -/
def leftIso (A : Type (u + 1)) [CommRing A] [Finite A]
    (S : Scheme.{u}) [IsNoetherian S] (d : ℕ) :
    (c : Compactification (affineTraceProjection S d)) →
    affineTraceLeft A S d ≅
      rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c :=
  Nat.rec (motive := fun n ↦ ∀ c : Compactification (affineTraceProjection S n),
      affineTraceLeft A S n ≅
        rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c)
    (fun c ↦
      (Functor.isoWhiskerRight
          (mapDerivedCategoryOpenImmersionLowerShriekId (ModuleCat.{u + 1} A) S) _ ≪≫
        Functor.leftUnitor _ ≪≫ rightDerivedLowerStarIdIso A S).symm ≪≫
        rightDerivedLowerShriekOfCompactificationIso A
          (Compactification.ofIsProper (𝟙 S)) c)
    (fun n ih c ↦
      let cp := HasCompactification.compactification (affineTraceProjection S n)
      let ce := c.ofComp cp
      Functor.isoWhiskerRight
          (rightDerivedLowerShriekOfCompactificationIso A
            (affineTraceLineCompactification (affineTraceTower S n)) ce.restrict) _ ≪≫
        Functor.isoWhiskerLeft _ (ih cp) ≪≫
        rightDerivedLowerShriekOfCompactificationCompIso A cp ce ≪≫
        rightDerivedLowerShriekOfCompactificationIso A (cp.comp ce) c) d


/-- Transport the actual ordered counit along the coefficient-free left comparison.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-change-of-finite-coefficients/sk-lem-sp-reduction/
sk-lem-sp-reduction-exceptional.proof.md, Charts (blueprint: lem-sp-affine-counit-scalar). -/
def counit (N : ℕ) (hN : 0 < N) (A : Type (u + 1)) [CommRing A] [Finite A]
    (hA : (N : A) = 0) (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (c : Compactification (affineTraceProjection S d)) (K : DerivedCategoryModule A S) :
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj
      ((affineTraceRight A N hA S d).obj K) ⟶ K :=
  (leftIso A S d c).inv.app _ ≫
    (affineTraceAdjunction A N hA (projectiveLineTraceTransport N hN A hA)
      (fun T _ hT ↦ projectiveLineTraceDatum N hN A hA T hT) S hS d).counit.app K

end AffineCounitOrdinary

/-- The ordered affine-space counit compatibility over a finite or algebraically closed field.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-change-of-finite-coefficients/sk-lem-sp-reduction/
sk-lem-sp-reduction-exceptional.proof.md, Charts: iterated projective-line integration
(blueprint: lem-sp-affine-counit-scalar).

Proof (the four DAG steps; deferred to stage 3):
1. Transport bounded constructibility and finite Tor amplitude through the ordered right
   normal form and the chart-domain theorem. Finite type over the field makes every
   coordinate scheme Noetherian. Since the characteristic differs from ell, the common
   annihilator ell^n is invertible, also in characteristic zero.
2. Apply the canonical single-coordinate scalar-counit identity at every right-tower input.
   Induct on the actual composite adjunction tower. Naturality of the last line counit and
   the previous coefficient arrow pastes the equations. The right exchange tower is exactly
   AffineCounitOrdinary.rightMap. At d = 0 its factors and counit are identities.
3. Apply orderedCompactification_scalar_square to the bounded-below right input. Identify
   both bounded comparison components with AffineCounitOrdinary.leftIso using the affine
   compactification normalization. This fixes the coefficient map for the chosen c.
4. Precompose the claimed equation with scalar extension of the left comparison hom.
   Substitute the square of step 3 and use naturality of the inverse B-left comparison at
   the right scalar comparison. Cancel these isomorphisms and apply step 2 and functoriality.
   This proves the actual transported compactification-counit equation, including d = 0.
-/
theorem affine_counit_scalar_general_field (ell : ℕ) [Fact ell.Prime]
    (k : Type u) [Field k] (_hk : Finite k ∨ IsAlgClosed k)
    (_hchar : ringChar k ≠ ell)
    (A B : Type (u + 1)) [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (n : ℕ) (hA : ((ell ^ n : ℕ) : A) = 0)
    (hB : ((ell ^ n : ℕ) : B) = 0)
    (S : Scheme.{u}) [S.Over (Spec (.of k))]
    [LocallyOfFiniteType (S ↘ Spec (.of k))]
    [QuasiCompact (S ↘ Spec (.of k))]
    [IsSeparated (S ↘ Spec (.of k))] (d : ℕ)
    (c : Compactification (affineTraceProjection S d))
    (K : DerivedCategoryModule A S)
    (_hK : ProEtale.FiniteCompactCoefficients.Input A S K) :
    ∃ (hNoeth : IsNoetherian S) (hS : IsUnit ((ell ^ n : ℕ) : Γ(S, ⊤))),
      (ProEtale.FiniteCompactCoefficients.beta φ c).app
          ((affineTraceRight A (ell ^ n) hA S d).obj K) ≫
        (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c).map
          (AffineCounitOrdinary.rightMap φ S (ell ^ n) hA hB d K) ≫
        @AffineCounitOrdinary.counit.{u} (ell ^ n)
          (pow_pos (Fact.out : ell.Prime).pos n) B _ _ hB S hNoeth hS d c
          ((scalar S.smallEtaleTopology φ).obj K) =
      (scalar S.smallEtaleTopology φ).map (@AffineCounitOrdinary.counit.{u} (ell ^ n)
        (pow_pos (Fact.out : ell.Prime).pos n) A _ _ hA S hNoeth hS d c K) := by
  sorry

end AlgebraicGeometry.Etale
