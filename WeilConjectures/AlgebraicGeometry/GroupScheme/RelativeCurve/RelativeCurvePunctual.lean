/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.L2NativePunctualWeights
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Bounded.BoundedConstructiblePushforwardRestriction
public import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationOverField
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.BaseChange
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import WeilConjectures.CategoryTheory.Adjunction.ExchangeRightPaste
public import WeilConjectures.SixFunctors.FiniteFieldDatum.FrobeniusSquareCartesian
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

import WeilConjectures.WeilSheaf.StalkUpperStar
import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.Topology.Connected.Clopen
import WeilConjectures.Mathlib.Topology.NoetherianSpace
import WeilConjectures.AlgebraicGeometry.DescendQCOpenFGSubalgebra
import WeilConjectures.AlgebraicGeometry.Compactification.GeometricallyConnectedAlgebraicClosure
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule.Exact
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOrdinaryCompactCohomology
public import WeilConjectures.AlgebraicGeometry.AffineGeometricComponentsFiniteExtension
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.DerivedConstructibleLowerShriek

/-! # Punctual bounds for a relative affine curve

Source: literature/blueprint/latest/blueprint/part-weights-riemann-hypothesis/
sec-deligne-laumon-general/sec-mixedness-for-a-relative-affine-curve/
sk-p-dl-general-relative-line/lem-zl-relative-curve-punctual.md and its proof
(blueprint: lem-zl-relative-curve-punctual).

The cohomology Weil module is constructed from the actual condensed module lower shriek.
Its structure is the proper/open automorphism-square exchange followed by the given Weil
isomorphism. A compactification is a presentation of this canonical operation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace WeilConjectures.RelativeCurve
open CondensedRing

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  {U₀ Y₀ : Over (Spec (.of D.k₀))}
  [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]
  [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]

/-- The compactification's middle model with its inherited finite-field structure.
Source: the compact-support construction in proof step 1
(blueprint: lem-zl-relative-curve-punctual). -/
def middle (h₀ : U₀ ⟶ Y₀) (c₀ : Compactification h₀.left) :
    Over (Spec (.of D.k₀)) := Over.mk (c₀.g ≫ Y₀.hom)

/-- The model open immersion, retaining its actual factorization over the finite field.
Source: proof step 1, compactification presentation
(blueprint: lem-zl-relative-curve-punctual). -/
def modelOpen (h₀ : U₀ ⟶ Y₀) (c₀ : Compactification h₀.left) :
    U₀ ⟶ middle D h₀ c₀ :=
  Over.homMk c₀.i (by
    change c₀.i ≫ (c₀.g ≫ Y₀.hom) = U₀.hom
    rw [← Category.assoc, ← c₀.comm]
    exact h₀.w)

/-- The model proper factor as a morphism over the finite field.
Source: proof step 1, compactification presentation
(blueprint: lem-zl-relative-curve-punctual). -/
def modelProper (h₀ : U₀ ⟶ Y₀) (c₀ : Compactification h₀.left) :
    middle D h₀ c₀ ⟶ Y₀ := Over.homMk c₀.g

/-- The geometric compactification obtained by applying the existing base-change functor.
Source: proof step 1, actual condensed compact-support operation
(blueprint: lem-zl-relative-curve-punctual). -/
def geometricCompactification (h₀ : U₀ ⟶ Y₀) (c₀ : Compactification h₀.left) :
    Compactification (((Over.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map h₀).left) where
  Z := (D.geometricFiber (middle D h₀ c₀)).left
  i := ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map
    (modelOpen D h₀ c₀)).left
  g := ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map
    (modelProper D h₀ c₀)).left
  comm := by
    let B := Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))
    have e : h₀ = modelOpen D h₀ c₀ ≫ modelProper D h₀ c₀ :=
      Over.OverMorphism.ext c₀.comm
    exact (congrArg (fun f ↦ (B.map f).left) e).trans
      (congrArg (fun f ↦ f.left) (B.map_comp (modelOpen D h₀ c₀) (modelProper D h₀ c₀)))
  isProper := MorphismProperty.overPullbackMap (P := @IsProper)
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))
    (modelProper D h₀ c₀) c₀.isProper
  isOpenImmersion := MorphismProperty.overPullbackMap (P := @IsOpenImmersion)
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))
    (modelOpen D h₀ c₀) c₀.isOpenImmersion

/-- The native proper exchange for an automorphism square, as its specified right mate.
Source: proof step 1, canonical Frobenius exchange
(blueprint: lem-zl-relative-curve-punctual). -/
def properExchange {Z S : Scheme.{u}} (p : Z ⟶ S) (aZ : Z ≅ Z) (aS : S ≅ S)
    (hp : CommSq aZ.hom p p aS.hom) :
    (lowerStar (Profinite.padicAlgClRingObj l) p).rightDerivedFunctor ⋙
        (upperStar (Profinite.padicAlgClRingObj l) aS.hom).mapDerivedCategory ⟶
      (upperStar (Profinite.padicAlgClRingObj l) aZ.hom).mapDerivedCategory ⋙
        (lowerStar (Profinite.padicAlgClRingObj l) p).rightDerivedFunctor :=
  let Λ := Profinite.padicAlgClRingObj l
  Adjunction.exchangeRight
    ((upperStarLowerStarAdjunction Λ p).mapDerivedCategoryRightDerivedAdjunction)
    ((upperStarLowerStarAdjunction Λ p).mapDerivedCategoryRightDerivedAdjunction)
    ((Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
      Functor.mapDerivedCategoryNatIso (upperStarSquareComparison Λ hp) ≪≫
      Functor.mapDerivedCategoryCompIso _ _)

/-- The native open exchange, inverse to the left-adjoint mate of the pullback square.
Source: proof step 1, canonical Frobenius exchange
(blueprint: lem-zl-relative-curve-punctual). -/
def openExchange {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    (aX : X ≅ X) (aZ : Z ≅ Z) (hj : CommSq aX.hom j j aZ.hom) :
    openImmersionLowerShriek (Profinite.padicAlgClRingObj l) j ⋙
        upperStar (Profinite.padicAlgClRingObj l) aZ.hom ≅
      upperStar (Profinite.padicAlgClRingObj l) aX.hom ⋙
        openImmersionLowerShriek (Profinite.padicAlgClRingObj l) j :=
  let Λ := Profinite.padicAlgClRingObj l
  let eX := CategoryTheory.Equivalence.mk (upperStar Λ aX.hom) (upperStar Λ aX.inv)
    ((upperStarId Λ X).symm ≪≫ upperStarCongr Λ aX.inv_hom_id.symm ≪≫
      upperStarComp Λ aX.inv aX.hom)
    ((upperStarComp Λ aX.hom aX.inv).symm ≪≫ upperStarCongr Λ aX.hom_inv_id ≪≫
      upperStarId Λ X)
  let eZ := CategoryTheory.Equivalence.mk (upperStar Λ aZ.hom) (upperStar Λ aZ.inv)
    ((upperStarId Λ Z).symm ≪≫ upperStarCongr Λ aZ.inv_hom_id.symm ≪≫
      upperStarComp Λ aZ.inv aZ.hom)
    ((upperStarComp Λ aZ.hom aZ.inv).symm ≪≫ upperStarCongr Λ aZ.hom_inv_id ≪≫
      upperStarId Λ Z)
  (conjugateIsoEquiv
    (eX.toAdjunction.comp (openImmersionLowerShriekUpperStarAdjunction Λ j))
    ((openImmersionLowerShriekUpperStarAdjunction Λ j).comp eZ.toAdjunction)).symm
      (upperStarSquareComparison Λ hj.horiz_inv).symm

/-- The canonical condensed compact-support Frobenius exchange as an isomorphism.
Source: proof step 1, Rh_!(theta)e_g, with the native proper/open mates
(blueprint: lem-zl-relative-curve-punctual). -/
def exchange (h₀ : U₀ ⟶ Y₀) (c₀ : Compactification h₀.left) :
    rightDerivedLowerShriekOfCompactification (Profinite.padicAlgClRingObj l)
        (geometricCompactification D h₀ c₀) ⋙
      (upperStar (Profinite.padicAlgClRingObj l)
        (D.geometricFrobenius Y₀).hom).mapDerivedCategory ≅
    (upperStar (Profinite.padicAlgClRingObj l)
        (D.geometricFrobenius U₀).hom).mapDerivedCategory ⋙
      rightDerivedLowerShriekOfCompactification (Profinite.padicAlgClRingObj l)
        (geometricCompactification D h₀ c₀) :=
  let c := geometricCompactification D h₀ c₀
  let aU := D.geometricFrobenius U₀
  let aZ := D.geometricFrobenius (middle D h₀ c₀)
  let aY := D.geometricFrobenius Y₀
  let hj : CommSq aU.hom c.i c.i aZ.hom :=
    ⟨(D.frobenius_square_cartesian U₀ (middle D h₀ c₀)
      (modelOpen D h₀ c₀)).2.2.2.2.1⟩
  let hp : CommSq aZ.hom c.g c.g aY.hom :=
    ⟨(D.frobenius_square_cartesian (middle D h₀ c₀) Y₀
      (modelProper D h₀ c₀)).2.2.2.2.1⟩
  letI : IsIso (properExchange l c.g aZ aY hp) :=
    Adjunction.isIso_exchangeRight_of_isEquivalence _ _ _
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (asIso (properExchange l c.g aZ aY hp)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      ((Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
        Functor.mapDerivedCategoryNatIso (openExchange l c.i aU aZ hj) ≪≫
        Functor.mapDerivedCategoryCompIso _ _) _ ≪≫
    Functor.associator _ _ _

/-- R^i h_! of the actual condensed Weil module, with its induced cohomology structure.
The carrier is H^i of the compactification composite applied to F in degree zero.
Source: the statement and first proof step, canonical direct-image Weil structure
(blueprint: lem-zl-relative-curve-punctual). -/
@[irreducible] def higherShriek (h₀ : U₀ ⟶ Y₀) (c₀ : Compactification h₀.left)
    (F : NativeL2.WeilModule D l U₀) (i : ℕ) : NativeL2.WeilModule D l Y₀ :=
  let Λ := Profinite.padicAlgClRingObj.{u} l
  let F₀ := (CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIso
    ((upperStar Λ (D.geometricFrobenius U₀).hom).mapDerivedCategorySingleFunctor 0)).obj F
  let R₀ := (CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIso
    (exchange D l h₀ c₀)).obj F₀
  (CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIso
    ((upperStar Λ (D.geometricFrobenius Y₀).hom).mapDerivedCategoryHomologyFunctorIso
      (i : ℤ))).obj R₀

end WeilConjectures.RelativeCurve
