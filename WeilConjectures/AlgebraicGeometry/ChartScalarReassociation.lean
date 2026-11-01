/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AdjunctionTransfer.EtaleCtfChartDomain
public import WeilConjectures.AlgebraicGeometry.EtaleProEtaleExceptionalTransport
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars.Trace
public import WeilConjectures.CategoryTheory.Sites.SheafComposeMonoidal
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Canonical scalar reassociation on a smooth chart

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-lem-sp-reduction/sk-lem-sp-reduction-exceptional.proof.md, Charts;
Stacks Tags 06YY, 07A4 and 0D6D.
(blueprint: lem-sp-reduction-exceptional-chart-scalar-reassociation).

The fixed-coefficient presentation keeps the small site's object and morphism universes
separate. All scalar maps below are the actual derived-adjunction and tensor maps.
The Tate comparison is constructed by extension from the same roots-of-unity presheaf.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale

/-- Ordinary balancing for the first etale Tate line. Both composite left adjoints
have the same right adjoint, via the actual composition of scalar restrictions.
Source: Charts, free rank-one summands; Stacks 03EK.
(blueprint: lem-sp-reduction-exceptional-chart-scalar-reassociation). -/
def chartEtaleTateOneScalarIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) (N : ℕ) (hA : (N : A) = 0) (hB : (N : B) = 0) :
    (etaleSheafExtendScalars φ T).obj (Scheme.finiteEtaleTateLine T N A hA) ≅
      Scheme.finiteEtaleTateLine T N B hB :=
  let J := T.smallEtaleTopology
  let rA := Scheme.finiteEtaleTwistScalar N A hA
  let rB := Scheme.finiteEtaleTwistScalar N B hB
  let a := (ModuleCat.extendRestrictScalarsAdj.{u + 1, 0, u + 1} rA).whiskerRight
    T.Etaleᵒᵖ |>.comp (sheafificationAdjunction J (ModuleCat.{u + 1} A))
  let b := (ModuleCat.extendRestrictScalarsAdj.{u + 1, 0, u + 1} rB).whiskerRight
    T.Etaleᵒᵖ |>.comp (sheafificationAdjunction J (ModuleCat.{u + 1} B))
  let c := a.comp (etaleSheafExtendScalarsAdjunction φ T)
  let r : Sheaf.restrictScalars J φ ⋙
      (sheafToPresheaf J (ModuleCat.{u + 1} A) ⋙
        (Functor.whiskeringRight T.Etaleᵒᵖ _ _).obj (ModuleCat.restrictScalars rA)) ≅
      sheafToPresheaf J (ModuleCat.{u + 1} B) ⋙
        (Functor.whiskeringRight T.Etaleᵒᵖ _ _).obj (ModuleCat.restrictScalars rB) :=
    NatIso.ofComponents (fun L ↦
      Functor.isoWhiskerLeft L.obj
        (ModuleCat.restrictScalarsComp' rA φ rB (Subsingleton.elim _ _)).symm)
      (by intro L M f; ext W x; rfl)
  ((c.ofNatIsoRight r).leftAdjointUniq b).app (Scheme.finiteEtaleMuModulePresheaf T N)

/-- Ordinary balancing of all nonnegative Tate powers, including the coefficient unit.
Source: Charts and scalar-extension clause (3); Stacks 03EK and 03PK.
(blueprint: lem-sp-reduction-exceptional-chart-scalar-reassociation). -/
def chartEtaleTateScalarIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) (N : ℕ) (hA : (N : A) = 0) (hB : (N : B) = 0) :
    (d : ℕ) →
      (etaleSheafExtendScalars φ T).obj (Scheme.finiteEtaleTateTwist T N A hA d) ≅
        Scheme.finiteEtaleTateTwist T N B hB d :=
  letI : (etaleSheafExtendScalars φ T).Monoidal :=
    composeAndSheafifyMonoidal T.smallEtaleTopology
    (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} φ)
  fun d ↦ match d with
  | 0 => (Functor.Monoidal.εIso (etaleSheafExtendScalars φ T)).symm
  | 1 => chartEtaleTateOneScalarIso φ T N hA hB
  | d + 2 =>
    (Functor.Monoidal.μIso (etaleSheafExtendScalars φ T)
      (Scheme.finiteEtaleTateTwist T N A hA (d + 1))
      (Scheme.finiteEtaleTateLine T N A hA)).symm ≪≫
    tensorIso (chartEtaleTateScalarIso φ T N hA hB (d + 1))
      (chartEtaleTateOneScalarIso φ T N hA hB)

/-- The same balancing after exact comparison to the pro-etale site. The comparison
is the conjugate of the identity square of scalar restriction and site direct image.
Source: Charts; Stacks 07A4.
(blueprint: lem-sp-reduction-exceptional-chart-scalar-reassociation). -/
def chartProEtaleTateScalarIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) (N : ℕ) (hA : (N : A) = 0) (hB : (N : B) = 0)
    (d : ℕ) :
    (sheafExtendScalars φ T).obj
        ((comparisonUpperStar (ModuleCat.{u + 1} A) T).obj
          (Scheme.finiteEtaleTateTwist T N A hA d)) ≅
      (comparisonUpperStar (ModuleCat.{u + 1} B) T).obj
        (Scheme.finiteEtaleTateTwist T N B hB d) :=
  (etaleSheafExtendScalarsCompComparisonUpperStarIso φ T).symm.app _ ≪≫
    (comparisonUpperStar (ModuleCat.{u + 1} B) T).mapIso
      (chartEtaleTateScalarIso φ T N hA hB d)

/-- The actual scalar/single map, transposed from the ordinary scalar unit.
Source: Stacks 06YY, the K-flat computation in scalar-extension clause (1).
(blueprint: lem-sp-reduction-exceptional-chart-scalar-reassociation). -/
def chartScalarSingleMap
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u})
    (F : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)) :
    L(sheafExtendScalars φ T).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj F) ⟶
      (_root_.DerivedCategory.singleFunctor _ 0).obj ((sheafExtendScalars φ T).obj F) :=
  letI := φ.toAlgebra
  (leftDerivedSheafExtendScalarsAdjunction A B T).homEquiv _ _ |>.symm <|
    (_root_.DerivedCategory.singleFunctor _ 0).map
        ((sheafExtendScalarsAdjunction φ T).unit.app F) ≫
      (Functor.mapDerivedCategorySingleFunctor
        (sheafCompose (Scheme.ProEt.topology T)
          (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} φ)) 0).inv.app _

/-- Derived extension of the transported finite etale Tate line. The map is fixed by
ordinary root balancing; no isomorphism between unspecified lines is chosen.
Source: Charts; Stacks 06YY and 07A4.
(blueprint: lem-sp-reduction-exceptional-chart-scalar-reassociation). -/
def chartDerivedTateScalarMap
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) (N : ℕ) (hA : (N : A) = 0) (hB : (N : B) = 0)
    (d : ℕ) :
    L(sheafExtendScalars φ T).obj
        ((comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj
            (Scheme.finiteEtaleTateTwist T N A hA d))) ⟶
      (comparisonUpperStar (ModuleCat.{u + 1} B) T).mapDerivedCategory.obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj
          (Scheme.finiteEtaleTateTwist T N B hB d)) :=
  L(sheafExtendScalars φ T).map
      ((Functor.mapDerivedCategorySingleFunctor
        (comparisonUpperStar (ModuleCat.{u + 1} A) T) 0).hom.app _) ≫
    chartScalarSingleMap φ T _ ≫
    (_root_.DerivedCategory.singleFunctor _ 0).map
      (chartProEtaleTateScalarIso φ T N hA hB d).hom ≫
    (Functor.mapDerivedCategorySingleFunctor
      (comparisonUpperStar (ModuleCat.{u + 1} B) T) 0).inv.app _

/-- The canonical B-linear pullback/scalar comparison, with exact inverse images.
Source: Stacks 0D6D, 07A4; the commuting constant-ring square in Charts.
(blueprint: lem-sp-reduction-exceptional-chart-scalar-reassociation). -/
def chartPullbackScalarIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [IsNoetherianRing A]
    (φ : A →+* B) {U Y : Scheme.{u}} (f : U ⟶ Y) :
    (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory ⋙
        L(sheafExtendScalars φ U) ≅
      L(sheafExtendScalars φ Y) ⋙
        (upperStar (ModuleCat.{u + 1} B) f).mapDerivedCategory :=
  letI := φ.toAlgebra
  Functor.isoWhiskerRight
      (upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctorIsoMapDerivedCategory.symm _ ≪≫
    (leftDerivedUpperStarExtendScalarsIso A B f).symm ≪≫
    Functor.isoWhiskerLeft _
      (upperStar (ModuleCat.{u + 1} B) f).leftDerivedFunctorIsoMapDerivedCategory

/-- The prescribed composite: commute with the shift, apply the derived scalar
 tensorator, balance the Tate line, and compare scalar extension with inverse image.
The existing chart operation tensors the Tate line on the left, using the canonical
symmetry convention for M(d). Source: Charts, displayed canonical isomorphism.
(blueprint: lem-sp-reduction-exceptional-chart-scalar-reassociation). -/
def chartScalarReassociationMap
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [IsNoetherianRing A]
    (φ : A →+* B) (N : ℕ) (hA : (N : A) = 0) (hB : (N : B) = 0)
    {U Y : Scheme.{u}} (f : U ⟶ Y) (d : ℕ) (b : ℤ)
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A))) :
    L(sheafExtendScalars φ U).obj
        ((AdjunctionTransfer.proEtaleChartOperation A N hA f d b).obj K) ⟶
      (AdjunctionTransfer.proEtaleChartOperation B N hB f d b).obj
        (L(sheafExtendScalars φ Y).obj K) :=
  letI := φ.toAlgebra
  letI : L(sheafExtendScalars φ U).CommShift ℤ :=
    (leftDerivedSheafExtendScalarsAdjunction A B U).leftAdjointCommShift ℤ
  (L(sheafExtendScalars φ U).commShiftIso b).hom.app _ ≫
    (shiftFunctor _ b).map
      (((sheafExtendScalars φ U).leftDerivedTensorComparison.app _).app _ ≫
        (chartDerivedTateScalarMap φ U N hA hB d ⊗ₘ
          (chartPullbackScalarIso φ f).hom.app K))

/-- The canonical identity-pullback, degree-zero-twist, zero-shift identification.
Source: Charts, zero-dimensional unit case; Stacks 07A4.
(blueprint: lem-sp-reduction-exceptional-chart-scalar-reassociation). -/
def chartZeroUnitIso (R : Type (u + 1)) [CommRing R] (T : Scheme.{u})
    (N : ℕ) (hR : (N : R) = 0)
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} R))) :
    (AdjunctionTransfer.proEtaleChartOperation R N hR (𝟙 T) 0 0).obj K ≅ K :=
  (shiftFunctorZero _ ℤ).app _ ≪≫
    (tensorIso
      ((Functor.mapDerivedCategorySingleFunctor
          (comparisonUpperStar (ModuleCat.{u + 1} R) T) 0).app _ ≪≫
        (_root_.DerivedCategory.singleFunctor _ 0).mapIso
          (Functor.Monoidal.εIso (comparisonUpperStar (ModuleCat.{u + 1} R) T)).symm ≪≫
        _root_.DerivedCategory.singleFunctorObjUnitIso _)
      ((Functor.mapDerivedCategoryNatIso (upperStarId (ModuleCat.{u + 1} R) T) ≪≫
        Functor.mapDerivedCategoryIdIso _).app K)) ≪≫
    λ_ K

end AlgebraicGeometry.ProEtale
