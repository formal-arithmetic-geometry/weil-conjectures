/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CompactSupportFiniteProjection.ConstructibleProjectionMates
public import WeilConjectures.SmoothPurity.Supporting.ProjectionFiniteReduction
public import WeilConjectures.SmoothPurity.Finite.FinitePullbackTensorConstruction
public import WeilConjectures.SixFunctors.PurCompactSupport.IntegralCompactSupportCoefficientComparison
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingPullbackComparison
public import WeilConjectures.SixFunctors.IntegralHom.Reduction.IntegralHomReductionModels
import WeilConjectures.SixFunctors.Finite.Scalar.FiniteScalarProperProjectionPresentation

/-! # The finite projection in intrinsic tensor coordinates

Source: def-exchange-projection, the finite coefficient realization, and
prop-sf-pf-reduction, the specified finite projection map.
(blueprint: lem-sf-finite-projection-operation-presentation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

section FiniteReductionCoordinates

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] WeilConjectures.IntegralHom.derivedCategory
open PurCompactSupport
open scoped CategoryTheory.Functor

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]

/-- The existing counit/open projection at the positive finite level, in intrinsic
constant-ring coordinates. The tensor presentations are the recorded normalized ones.
Source: blueprint prop-sf-pf-reduction, maps PF (blueprint: prop-sf-pf-reduction). -/
def finiteReductionProjection (n : ℕ) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f)
    (K : proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E (n + 1)))
    (L : proEtaleDerivedCategory Y (Padic.coefficientExtensionRing l E (n + 1))) :=
  ((projectionMap (finite l E (n + 1) (Nat.succ_pos n)) c
    (pullbackTensorFiniteModel l E X n) (pullbackTensorFiniteModel l E c.Z n)
    (pullbackTensorFiniteModel l E Y n)
    (proEtaleConstantRingCompositeCoefficients_eq c.i c.g
      (Padic.coefficientExtensionRing l E (n + 1))).symm).app K).app L

/-- The left vertical arrow u: tensor reduction followed by compact-support reduction
on its first tensor factor. Source: blueprint prop-sf-pf-reduction, proof step 2
(blueprint: prop-sf-pf-reduction). -/
def finiteProjectionReductionSource (m n : ℕ) (h : m ≤ n)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E (n + 1)))
    (L : proEtaleDerivedCategory Y (Padic.coefficientExtensionRing l E (n + 1))) :=
  (scalarTensor
    ((finiteQuotientChange l E (n + 1) (m + 1) (Nat.succ_pos n) (Nat.succ_pos m)
      (Nat.succ_le_succ h)).map Y)
    (pullbackTensorFiniteModel l E Y n) (pullbackTensorFiniteModel l E Y m)).hom.app
      ((image (finite l E (n + 1) (Nat.succ_pos n)) c).obj K, L) ≫
    (pullbackTensorFiniteModel l E Y m).tensor.map (Prod.mkHom
      ((comparison
        (finiteQuotientChange l E (n + 1) (m + 1) (Nat.succ_pos n) (Nat.succ_pos m)
          (Nat.succ_le_succ h)) c).app K) (𝟙 _))

/-- The right vertical arrow v: compact-support reduction, then compact support of
tensor reduction followed by the pullback comparison. Source: blueprint
prop-sf-pf-reduction, proof step 2 (blueprint: prop-sf-pf-reduction). -/
def finiteProjectionReductionTarget (m n : ℕ) (h : m ≤ n)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E (n + 1)))
    (L : proEtaleDerivedCategory Y (Padic.coefficientExtensionRing l E (n + 1))) :=
  (comparison
    (finiteQuotientChange l E (n + 1) (m + 1) (Nat.succ_pos n) (Nat.succ_pos m)
      (Nat.succ_le_succ h)) c).app
        ((pullbackTensorFiniteModel l E X n).tensor.obj
          (K, (pull (finite l E (n + 1) (Nat.succ_pos n)) f).obj L)) ≫
    (image (finite l E (m + 1) (Nat.succ_pos m)) c).map
      ((scalarTensor
        ((finiteQuotientChange l E (n + 1) (m + 1) (Nat.succ_pos n) (Nat.succ_pos m)
          (Nat.succ_le_succ h)).map X)
        (pullbackTensorFiniteModel l E X n) (pullbackTensorFiniteModel l E X m)).hom.app
          (K, (pull (finite l E (n + 1) (Nat.succ_pos n)) f).obj L) ≫
        (pullbackTensorFiniteModel l E X m).tensor.map (Prod.mkHom (𝟙 _)
          ((scalarPull
            (finiteQuotientChange l E (n + 1) (m + 1) (Nat.succ_pos n) (Nat.succ_pos m)
              (Nat.succ_le_succ h)) f).hom.app L)))

end FiniteReductionCoordinates

private def arrowPostIso {A : Type*} [Category* A] {U V W : A}
    (f : U ⟶ V) (e : V ≅ W) : Arrow.mk f ≅ Arrow.mk (f ≫ e.hom) :=
  Arrow.isoMk (Iso.refl _) e (by simp)

private def mapArrowIso {A B : Type*} [Category* A] [Category* B]
    (F : A ⥤ B) {f g : Arrow A} (e : f ≅ g) :
    Arrow.mk (F.map f.hom) ≅ Arrow.mk (F.map g.hom) :=
  F.mapArrow.mapIso e

private def bifunctorArrowIso {A B T : Type*} [Category* A] [Category* B] [Category* T]
    {P Q : A ⥤ B ⥤ T} (α : P ⟶ Q) {K K' : A} {L L' : B}
    (eK : K ≅ K') (eL : L ≅ L') :
    Arrow.mk ((α.app K).app L) ≅ Arrow.mk ((α.app K').app L') :=
  Arrow.isoMk (((P.mapIso eK).app L) ≪≫ (P.obj K').mapIso eL)
    (((Q.mapIso eK).app L) ≪≫ (Q.obj K').mapIso eL) (by
      simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Arrow.mk_hom]
      rw [Category.assoc, (α.app K').naturality, ← Category.assoc,
        NatTrans.naturality_app, Category.assoc])

attribute [-instance] WeilConjectures.IntegralHom.derivedCategory in
private theorem intrinsicProperFactor
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (m : ℕ)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E (m + 1)))
    (L : proEtaleDerivedCategory Y (Padic.coefficientExtensionRing l E (m + 1))) :
    Nonempty (Arrow.mk (finiteReductionProjection l E m c K L) ≅
      Arrow.mk (finiteScalarProperProjection (Padic.coefficientExtensionRing l E (m + 1)) c.g
        (pullbackTensorFiniteModel l E c.Z m) (pullbackTensorFiniteModel l E Y m)
        (((PurCompactSupport.openExtension
          (PurCompactSupport.finite l E (m + 1) (Nat.succ_pos m)) c.i).mapDerivedCategory).obj K)
        L)) := by
  let R := PurCompactSupport.finite l E (m + 1) (Nat.succ_pos m)
  let aX : ProEtaleTensorModel X (R.ring X) := pullbackTensorFiniteModel l E X m
  let aZ : ProEtaleTensorModel c.Z (R.ring c.Z) := pullbackTensorFiniteModel l E c.Z m
  let aY : ProEtaleTensorModel Y (R.ring Y) := pullbackTensorFiniteModel l E Y m
  let hc := (proEtaleConstantRingCompositeCoefficients_eq c.i c.g
    (Padic.coefficientExtensionRing l E (m + 1))).symm
  let data := (PurCompactSupport.projectionComparisons_existsUnique R c aX aZ aY hc).exists.choose
  let J := (PurCompactSupport.openExtension R c.i).mapDerivedCategory
  let G := PurCompactSupport.push R c.g
  let adj := proEtaleRingDerivedAdjunction c.g (R.ring Y) (R.ring c.Z) (R.pull c.g)
  let p := ((adj.rightAdjointProjectionMap data.tensorPullback.hom).app (J.obj K)).app L
  let e := G.mapIso ((data.openProjection.app K).app L)
  have hp : p = finiteScalarProperProjection
      (Padic.coefficientExtensionRing l E (m + 1)) c.g aZ aY (J.obj K) L := by
    unfold finiteScalarProperProjection
    change adj.homEquiv _ _
      ((data.tensorPullback.hom.app
        ((proEtaleRingDerivedDirectImage c.g (R.ring Y) (R.ring c.Z) (R.pull c.g)).obj
          (J.obj K))).app L ≫
        aZ.tensor.map (Prod.mkHom (adj.counit.app (J.obj K)) (𝟙 _))) = _
    exact congrArg
      (fun t ↦ adj.homEquiv _ _
        (t ≫ aZ.tensor.map (Prod.mkHom (adj.counit.app (J.obj K)) (𝟙 _))))
      (data.tensorPullback_eq _ _)
  have h : finiteReductionProjection l E m c K L = p ≫ e.hom := by
    rfl
  rw [h]
  exact ⟨(arrowPostIso p e).symm ≪≫ eqToIso (congrArg Arrow.mk hp)⟩

private theorem fixedProperFactor
    (A : Type*) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    [AlgebraicGeometry.ProEtale.UpperStarPreservesFlat A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : DerivedCategory (Sheaf (ProEt.topology X) A))
    (L : DerivedCategory (Sheaf (ProEt.topology Y) A)) :
    Nonempty (Arrow.mk
      (((AlgebraicGeometry.ProEtale.rightDerivedLowerStarProjectionMap A c.g).app
        ((AlgebraicGeometry.ProEtale.openImmersionLowerShriek A c.i).mapDerivedCategory.obj K)).app
          L) ≅ Arrow.mk (projectionTensorCoordinateComponent A c K L)) := by
  let G := (AlgebraicGeometry.ProEtale.lowerStar A c.g).rightDerivedFunctor
  let J := (AlgebraicGeometry.ProEtale.openImmersionLowerShriek A c.i).mapDerivedCategory
  let e := G.mapIso
    (((AlgebraicGeometry.ProEtale.derivedOpenImmersionLowerShriekProjectionIso
      A c.i).app K).symm.app
      ((AlgebraicGeometry.ProEtale.upperStar A c.g).leftDerivedFunctor.obj L)) ≪≫
    G.mapIso (J.mapIso
      (((AlgebraicGeometry.ProEtale.derivedTensor A X).obj K).mapIso
        ((AlgebraicGeometry.ProEtale.leftDerivedUpperStarCompactificationIso A c).app L)))
  let p := (((AlgebraicGeometry.ProEtale.rightDerivedLowerStarProjectionMap A c.g).app
    (J.obj K)).app L)
  have h : Arrow.mk (projectionTensorCoordinateComponent A c K L) =
      Arrow.mk (p ≫ e.hom) := by
    simp only [projectionTensorCoordinateComponent,
      AlgebraicGeometry.ProEtale.projectionMapOfCompactification_app_app, e, J, G, p,
      Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Iso.app_inv, Iso.symm_hom]
    all_goals rfl
  exact ⟨arrowPostIso p e ≪≫ (eqToIso h).symm⟩

attribute [-instance] WeilConjectures.IntegralHom.derivedCategory in
private def finiteOpenRealizationIso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (m : ℕ)
    {U V : Scheme.{u}} (j : U ⟶ V) [IsOpenImmersion j]
    (K : proEtaleDerivedCategory U (Padic.coefficientExtensionRing l E (m + 1))) :
    ((PurCompactSupport.openExtension
      (PurCompactSupport.finite l E (m + 1) (Nat.succ_pos m)) j).mapDerivedCategory).obj K ≅
    (sfIntrinsicDerivedEquivalence V (Padic.coefficientExtensionRing l E (m + 1))).functor.obj
      (((AlgebraicGeometry.ProEtale.openImmersionLowerShriek
        (ModuleCat.{u + 1} (ULift.{u + 1}
          (Padic.coefficientExtensionRing l E (m + 1)))) j).mapDerivedCategory).obj
        ((sfIntrinsicDerivedEquivalence U
          (Padic.coefficientExtensionRing l E (m + 1))).inverse.obj K)) := by
  let O := PurCompactSupport.openExtension
    (PurCompactSupport.finite l E (m + 1) (Nat.succ_pos m)) j
  let M := sfIntrinsicExtensionByZero j (Padic.coefficientExtensionRing l E (m + 1))
  let e : O ≅ M := PurCompactSupport.finiteOpenIso l E m j
  letI : M.Additive :=
    (sfIntrinsicExtensionByZero_exact j (Padic.coefficientExtensionRing l E (m + 1))).1
  letI : Limits.PreservesFiniteLimits M :=
    (sfIntrinsicExtensionByZero_exact j (Padic.coefficientExtensionRing l E (m + 1))).2.1
  letI : Limits.PreservesFiniteColimits M :=
    (sfIntrinsicExtensionByZero_exact j (Padic.coefficientExtensionRing l E (m + 1))).2.2
  have hAdd : M.Additive := inferInstance
  let ed := @Functor.mapDerivedCategoryNatIso _ _ _ _ _ _ _ _ O M
    inferInstance hAdd inferInstance inferInstance
    (sfIntrinsicExtensionByZero_exact j (Padic.coefficientExtensionRing l E (m + 1))).2.1
    (sfIntrinsicExtensionByZero_exact j (Padic.coefficientExtensionRing l E (m + 1))).2.2 e
  exact ed.app K ≪≫
    (Functor.mapDerivedCategoryCompIso
      (sfIntrinsicModuleEquivalence U (Padic.coefficientExtensionRing l E (m + 1))).inverse
      (AlgebraicGeometry.ProEtale.openImmersionLowerShriek
        (ModuleCat.{u + 1} (ULift.{u + 1}
          (Padic.coefficientExtensionRing l E (m + 1)))) j ⋙
        (sfIntrinsicModuleEquivalence V
          (Padic.coefficientExtensionRing l E (m + 1))).functor)).app K ≪≫
    (Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryCompIso _ _)).app K

attribute [local irreducible] sfIntrinsicDerivedEquivalence
  CategoryTheory.Functor.mapDerivedCategory

attribute [-instance] WeilConjectures.IntegralHom.derivedCategory in
private theorem properToFixedCompactification
    (R : Type u) [CommRing R] [Finite R]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (aZ : ProEtaleTensorModel c.Z (proEtaleConstantRing c.Z R))
    (aY : ProEtaleTensorModel Y (proEtaleConstantRing Y R))
    (M : proEtaleDerivedCategory c.Z R) (K : proEtaleDerivedCategory X R)
    (L : proEtaleDerivedCategory Y R)
    (eJ : M ≅ (sfIntrinsicDerivedEquivalence c.Z R).functor.obj
      (((AlgebraicGeometry.ProEtale.openImmersionLowerShriek
        (ModuleCat.{u + 1} (ULift.{u + 1} R)) c.i).mapDerivedCategory).obj
        ((sfIntrinsicDerivedEquivalence X R).inverse.obj K))) :
    Nonempty (Arrow.mk (finiteScalarProperProjection R c.g aZ aY M L) ≅
      Arrow.mk ((sfIntrinsicDerivedEquivalence Y R).functor.map
        (projectionTensorCoordinateComponent (ModuleCat.{u + 1} (ULift.{u + 1} R)) c
          ((sfIntrinsicDerivedEquivalence X R).inverse.obj K)
          ((sfIntrinsicDerivedEquivalence Y R).inverse.obj L)))) := by
  let eK := (sfIntrinsicDerivedEquivalence c.Z R).inverse.mapIso eJ ≪≫
    ((sfIntrinsicDerivedEquivalence c.Z R).unitIso.app _).symm
  obtain ⟨h₂⟩ := finiteScalarProperProjection_presentation R c.g aZ aY M L
  let h₃ := mapArrowIso (sfIntrinsicDerivedEquivalence Y R).functor (bifunctorArrowIso
    (AlgebraicGeometry.ProEtale.rightDerivedLowerStarProjectionMap
      (ModuleCat.{u + 1} (ULift.{u + 1} R)) c.g) eK
    (Iso.refl ((sfIntrinsicDerivedEquivalence Y R).inverse.obj L)))
  obtain ⟨h₄⟩ := fixedProperFactor (ModuleCat.{u + 1} (ULift.{u + 1} R)) c
    ((sfIntrinsicDerivedEquivalence X R).inverse.obj K)
    ((sfIntrinsicDerivedEquivalence Y R).inverse.obj L)
  let h₅ := mapArrowIso (sfIntrinsicDerivedEquivalence Y R).functor h₄
  exact ⟨h₂ ≪≫ h₃ ≪≫ h₅⟩

attribute [-instance] WeilConjectures.IntegralHom.derivedCategory in
/-- The finite proper/open projection and its operation-coordinate presentation
are isomorphic as arrows. Both inputs are already finite-coefficient objects;
there is no integral object, scalar reduction, or projection invertibility claim.

Source: fix-prop-projection-formula.proof.md, specified-map compatibility;
def-exchange-projection, finite coefficient realization, and prop-sf-pf-reduction;
the finite presentation step of lem-sf-integral-stage-projection-reduction.
(blueprint: lem-sf-finite-projection-operation-presentation).

Proof: factor finiteReductionProjection into its proper counit projection and
proper image of the open projection isomorphism. Postcomposition by this
isomorphism does not change the isomorphism class of the arrow. Apply the
constant-scalar presentation comparison to the proper factor. The canonical
finiteOpenIso and exact derived composition comparisons identify its inverse
realization input with the fixed-scalar extension by zero of K. Naturality of the
fixed proper projection transports along this input isomorphism. Its inverse open
projection and pullback compositor are isomorphisms, so postcomposing gives the
fixed compactification projection. Finally sourceComparison and targetComparison
conjugate its realization to component. Cancel the source comparison to obtain
its arrow isomorphism. No finite-Tor condition on K or separated structure map is
used. This argument concerns the arrow isomorphism class requested in the
statement; no identity of prescribed endpoint comparisons is asserted. -/
theorem finiteProjection_operationPresentation
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {m : ℕ}
    (F : SixFunctorFiniteOperations D C E (m + 1)
      (Nat.succ_le_succ (Nat.zero_le m)))
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (c : Compactification f.hom.left)
    (K : sixFunctorFiniteCategory D C E (m + 1)
      (Nat.succ_le_succ (Nat.zero_le m)) X)
    (L : finiteTorConstructibleCategory C.l E (m + 1)
      (Nat.succ_le_succ (Nat.zero_le m)) Y.obj.left) :
    Nonempty (Arrow.mk (finiteReductionProjection C.l E m c K.obj L.obj) ≅
      Arrow.mk (CompactSupportFiniteProjection.component F f c K L).hom)  := by
  let A := Padic.coefficientExtensionRing C.l E (m + 1)
  let : Finite A := Padic.finite_coefficientExtensionRing C.l E (m + 1) (Nat.succ_pos m)
  let RX := sfIntrinsicDerivedEquivalence X.obj.left A
  let RY := sfIntrinsicDerivedEquivalence Y.obj.left A
  let J := (PurCompactSupport.openExtension
    (PurCompactSupport.finite C.l E (m + 1) (Nat.succ_pos m)) c.i).mapDerivedCategory
  let K' := RX.inverse.obj K.obj
  let L' := RY.inverse.obj L.obj
  let eJ := finiteOpenRealizationIso C.l E m c.i K.obj
  obtain ⟨h₁⟩ := intrinsicProperFactor C.l E m c K.obj L.obj
  obtain ⟨h₂⟩ := properToFixedCompactification A c
    (pullbackTensorFiniteModel C.l E c.Z m)
    (pullbackTensorFiniteModel C.l E Y.obj.left m) (J.obj K.obj) K.obj L.obj eJ
  let a := RY.functor.map
    (CompactSupportFiniteProjection.fixedComponent
      (C := C) (E := E) (n := m + 1) (hn := Nat.succ_pos m) f c K' L')
  let sc := CompactSupportFiniteProjection.sourceComparison F f c K L
  let tc := CompactSupportFiniteProjection.targetComparison F f c K L
  have h₆ : Arrow.mk a ≅ Arrow.mk (CompactSupportFiniteProjection.component F f c K L).hom :=
    Arrow.isoMk sc.symm tc.symm (by
      change sc.inv ≫ (sc.hom ≫ a ≫ tc.inv) = a ≫ tc.inv
      rw [Iso.inv_hom_id_assoc]
      rfl)
  exact ⟨h₁ ≪≫ h₂ ≪≫ h₆⟩

end WeilConjectures
