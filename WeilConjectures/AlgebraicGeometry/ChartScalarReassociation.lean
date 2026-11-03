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

/-- The published K-flat preservation instance for an arbitrary displayed ring map.
The algebra structure is induced by that very map, so no extra hypothesis is added.
Source: Stacks 06YY, scalar-extension clause (1).
(blueprint: lem-sp-reduction-exceptional-chart-scalar-reassociation). -/
instance chartScalarPreservesKFlat
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) :
    (sheafExtendScalars φ T).PreservesKFlatQuasiIso :=
  letI := φ.toAlgebra
  preservesKFlatQuasiIso_sheafExtendScalars (R := A) (S := B) T

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

/-- The tensor, Tate and inverse-image part of the prescribed scalar chart map.
Source: Charts, the canonical reassociation composite
(blueprint: lem-sp-reduction-exceptional-chart-scalar-reassociation).
This names the existing composite before its final shift. -/
def chartPreScalarReassociationMap
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [IsNoetherianRing A]
    (φ : A →+* B) (N : ℕ) (hA : (N : A) = 0) (hB : (N : B) = 0)
    {U Y : Scheme.{u}} (f : U ⟶ Y) (d : ℕ)
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A))) :
    L(sheafExtendScalars φ U).obj
        (((derivedTensor (ModuleCat.{u + 1} A) U).obj
          ((comparisonUpperStar (ModuleCat.{u + 1} A) U).mapDerivedCategory.obj
            ((_root_.DerivedCategory.singleFunctor _ 0).obj
              (Scheme.finiteEtaleTateTwist U N A hA d)))).obj
          ((upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory.obj K)) ⟶
      ((derivedTensor (ModuleCat.{u + 1} B) U).obj
        ((comparisonUpperStar (ModuleCat.{u + 1} B) U).mapDerivedCategory.obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj
            (Scheme.finiteEtaleTateTwist U N B hB d)))).obj
        ((upperStar (ModuleCat.{u + 1} B) f).mapDerivedCategory.obj
          (L(sheafExtendScalars φ Y).obj K)) :=
  letI := φ.toAlgebra
  ((sheafExtendScalars φ U).leftDerivedTensorComparison.app _).app _ ≫
    (chartDerivedTateScalarMap φ U N hA hB d ⊗ₘ
      (chartPullbackScalarIso φ f).hom.app K)

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

/-- Canonical scalar reassociation on every etale smooth chart, in the full intrinsic
bounded constructible finite-Tor subcategory; naturality and the unit normalization
specify the actual arrow, not just the existence of some isomorphism.

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-lem-sp-reduction/sk-lem-sp-reduction-exceptional.proof.md, Charts;
Stacks 06YY, 07A4 and 0D6D.
(blueprint: lem-sp-reduction-exceptional-chart-scalar-reassociation).

Proof:
1. The chart-domain lemma preserves bounded constructible cohomology and finite Tor
   amplitude under inverse image, Tate tensor powers and shift. Scalar extension
   preserves this domain and its Tor bounds without flatness of B over A.
2. Since ell differs from the characteristic, N is invertible. The finite-root site
   comparison identifies the transported etale line with the root-tensor line and
   fixes constant scalars. Ordinary balancing therefore gives chartEtaleTateScalarIso,
   including its coefficient-unit component in degree zero.
3. The line is locally free of rank one, so its degree-zero complex is K-flat. The
   scalar/single adjunct is an isomorphism, and chartDerivedTateScalarMap is the
   canonical derived extension of the same root balancing.
4. Derived tensor pullback for the identity-topos coefficient morphism gives the
   tensorator. The commuting constant-ring square gives chartPullbackScalarIso;
   on flat-term K-flat representatives it sends x tensor b to x tensor b.
5. Compose with scalar extension's shift comparison. Every factor is invertible
   and natural, proving the displayed isomorphism and naturality. The intrinsic
   domain is strictly full, so the ambient isomorphism is an isomorphism there.
6. In degree zero with identity pullback the tensor, scalar-line, identity and shift
   comparisons are the unit comparisons. Their coherence gives the final equation
   through chartZeroUnitIso, namely the specified tensor-unit identification. -/
theorem chartScalarReassociation
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    (hbase : Finite k ∨ IsAlgClosed k) (hchar : ringChar k ≠ ℓ)
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (n : ℕ) (hA : ((ℓ ^ n : ℕ) : A) = 0)
    (hB : ((ℓ ^ n : ℕ) : B) = 0)
    {Y U : Scheme.{u}} [Y.Over (Spec (.of k))] [U.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))]
    (d : ℕ) (e : U ⟶ AffineSpace (ULift.{u} (Fin d)) Y) [Etale e]
    [(e ≫ (AffineSpace (ULift.{u} (Fin d)) Y ↘ Y)).IsOver (Spec (.of k))] :
    (∀ K, exceptionalTransportProEtaleObjects A Y K →
      exceptionalTransportProEtaleObjects B U
        (L(sheafExtendScalars φ U).obj
          ((AdjunctionTransfer.proEtaleChartOperation A (ℓ ^ n) hA
            (e ≫ (AffineSpace (ULift.{u} (Fin d)) Y ↘ Y)) d (2 * (d : ℤ))).obj K)) ∧
      exceptionalTransportProEtaleObjects B U
        ((AdjunctionTransfer.proEtaleChartOperation B (ℓ ^ n) hB
          (e ≫ (AffineSpace (ULift.{u} (Fin d)) Y ↘ Y)) d (2 * (d : ℤ))).obj
            (L(sheafExtendScalars φ Y).obj K)) ∧
      IsIso (chartScalarReassociationMap φ (ℓ ^ n) hA hB
        (e ≫ (AffineSpace (ULift.{u} (Fin d)) Y ↘ Y)) d (2 * (d : ℤ)) K)) ∧
    (∀ K L (v : K ⟶ L), exceptionalTransportProEtaleObjects A Y K →
      exceptionalTransportProEtaleObjects A Y L →
      L(sheafExtendScalars φ U).map
          ((AdjunctionTransfer.proEtaleChartOperation A (ℓ ^ n) hA
            (e ≫ (AffineSpace (ULift.{u} (Fin d)) Y ↘ Y)) d (2 * (d : ℤ))).map v) ≫
        chartScalarReassociationMap φ (ℓ ^ n) hA hB
          (e ≫ (AffineSpace (ULift.{u} (Fin d)) Y ↘ Y)) d (2 * (d : ℤ)) L =
      chartScalarReassociationMap φ (ℓ ^ n) hA hB
          (e ≫ (AffineSpace (ULift.{u} (Fin d)) Y ↘ Y)) d (2 * (d : ℤ)) K ≫
        (AdjunctionTransfer.proEtaleChartOperation B (ℓ ^ n) hB
          (e ≫ (AffineSpace (ULift.{u} (Fin d)) Y ↘ Y)) d (2 * (d : ℤ))).map
            (L(sheafExtendScalars φ Y).map v)) ∧
    (∀ K, exceptionalTransportProEtaleObjects A Y K →
      chartScalarReassociationMap φ (ℓ ^ n) hA hB (𝟙 Y) 0 0 K ≫
        (chartZeroUnitIso B Y (ℓ ^ n) hB (L(sheafExtendScalars φ Y).obj K)).hom =
      L(sheafExtendScalars φ Y).map (chartZeroUnitIso A Y (ℓ ^ n) hA K).hom) := by
  sorry

end AlgebraicGeometry.ProEtale
