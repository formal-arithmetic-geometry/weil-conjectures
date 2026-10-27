/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P6
-/
module

public import Sheaf.Paper.FinitePartialPullbackTensor

/-! # Fixed coefficient coordinates for finite projection calculations

Source: the proper-factor calculation of prop-sf-pf-coherence.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.CompactSupportFiniteProjection

variable {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
  {E : Type u} [Field E] [Algebra (Padic C.l) E]
  [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}

/-- The full constructible inclusion followed by the inverse coefficient realization.
Source: the proper-factor calculation (blueprint: def-sf-finite-projection-fixed-coordinates). -/
def coordinates (X : SixFunctorSpace D) :=
  (intrinsicFiniteTorsionConstructible C.l E n hn X.obj.left).ι ⋙
    (realization (C := C) (E := E) (n := n) (hn := hn) X).inverse

/-- Direct image in fixed coefficient coordinates.
Source: the proper-factor calculation (blueprint: def-sf-finite-projection-fixed-coordinates). -/
def fixedDirect {X Y : SixFunctorSpace D} (f : X ⟶ Y) :=
  (AlgebraicGeometry.ProEtale.lowerStar
    (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)))
      f.hom.left).rightDerivedFunctor

/-- The canonical fixed coefficient adjunction.
Source: the proper-factor calculation (blueprint: def-sf-finite-projection-fixed-coordinates). -/
def fixedAdjunction {X Y : SixFunctorSpace D} (f : X ⟶ Y) :
    fixedDerivedPull (C := C) (E := E) (n := n) f ⊣
      fixedDirect (C := C) (E := E) (n := n) f :=
  letI := Padic.finite_coefficientExtensionRing C.l E n hn
  AlgebraicGeometry.ProEtale.derivedUpperStarLowerStarAdjunction
    (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n))) f.hom.left

/-- The tensor coordinate comparison cancels precisely the coefficient unit.
Source: the proper-factor calculation (blueprint: def-sf-finite-projection-fixed-coordinates). -/
def tensorCoordinates (S : SixFunctorFiniteOperations D C E n hn)
    (X : SixFunctorSpace D) (K : sixFunctorFiniteCategory D C E n hn X)
    (L : finiteTorConstructibleCategory C.l E n hn X.obj.left) :
    (coordinates (C := C) (E := E) (n := n) (hn := hn) X).obj
        (((partialTensor S X).obj K).obj L) ≅
      ((fixedTensor (C := C) (E := E) (n := n) X).obj
        ((coordinates (C := C) (E := E) (n := n) (hn := hn) X).obj K)).obj
        ((realization (C := C) (E := E) (n := n) (hn := hn) X).inverse.obj L.obj) :=
  ((realization (C := C) (E := E) (n := n) (hn := hn) X).unitIso.app _).symm

/-- Direct image comparison obtained from the specified direct realization and the
published K-injective-normalized coefficient comparison; both coefficient units are fixed.
Source: the proper-factor calculation (blueprint: def-sf-finite-projection-fixed-coordinates). -/
def directCoordinates (S : SixFunctorFiniteOperations D C E n hn)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (K : sixFunctorFiniteCategory D C E n hn X) :
    (coordinates (C := C) (E := E) (n := n) (hn := hn) Y).obj
        ((S.finite.direct f).obj K) ≅
      (fixedDirect (C := C) (E := E) (n := n) f).obj
        ((coordinates (C := C) (E := E) (n := n) (hn := hn) X).obj K) := by
  letI := Padic.finite_coefficientExtensionRing C.l E n hn
  let RX := realization (C := C) (E := E) (n := n) (hn := hn) X
  let RY := realization (C := C) (E := E) (n := n) (hn := hn) Y
  let Q := proEtaleConstantDerivedDirectImage f.hom.left (Padic.coefficientExtensionRing C.l E n)
  exact RY.inverse.mapIso ((S.finiteDirectImage f).app K ≪≫
    Q.mapIso (RX.counitIso.app K.obj).symm ≪≫
    (sfIntrinsicDerivedDirectImageComparison f.hom.left
      (Padic.coefficientExtensionRing C.l E n)).app (RX.inverse.obj K.obj)) ≪≫
    (RY.unitIso.app _).symm

/-- Coordinates of the target tensor, retaining the fixed pullback of the second input.
Source: the proper-factor calculation (blueprint: def-sf-finite-projection-fixed-coordinates). -/
def targetCoordinates (S : SixFunctorFiniteOperations D C E n hn)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (K : sixFunctorFiniteCategory D C E n hn X)
    (L : finiteTorConstructibleCategory C.l E n hn Y.obj.left) :=
  tensorCoordinates S X K ((torPull S f).obj L) ≪≫
    ((fixedTensor (C := C) (E := E) (n := n) X).obj
      ((coordinates (C := C) (E := E) (n := n) (hn := hn) X).obj K)).mapIso
        (fixedPullRealization S f ⟨L.obj, L.property.1⟩)

/-- Coordinates of the source tensor, retaining the fixed direct image of the first input.
Source: the proper-factor calculation (blueprint: def-sf-finite-projection-fixed-coordinates). -/
def directTensorCoordinates (S : SixFunctorFiniteOperations D C E n hn)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (K : sixFunctorFiniteCategory D C E n hn X)
    (L : finiteTorConstructibleCategory C.l E n hn Y.obj.left) :=
  tensorCoordinates S Y ((S.finite.direct f).obj K) L ≪≫
    ((fixedTensor (C := C) (E := E) (n := n) Y).mapIso
      (directCoordinates S f K)).app
        ((realization (C := C) (E := E) (n := n) (hn := hn) Y).inverse.obj L.obj)

/-- Faithfulness is inherited from the full inclusion and coefficient equivalence.
Source: full subcategory and equivalence
(blueprint: def-sf-finite-projection-fixed-coordinates). -/
instance coordinatesFaithful (X : SixFunctorSpace D) :
    (coordinates (C := C) (E := E) (n := n) (hn := hn) X).Faithful := by
  unfold coordinates
  infer_instance

/-- The existing pullback coordinate comparisons form a natural isomorphism.
Source: naturality in the proper-factor calculation
(blueprint: def-sf-finite-projection-fixed-coordinates). -/
def pullCoordinatesIso (S : SixFunctorFiniteOperations D C E n hn)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) :
    S.finite.pull f ⋙ coordinates (C := C) (E := E) (n := n) (hn := hn) X ≅
      coordinates (C := C) (E := E) (n := n) (hn := hn) Y ⋙
        fixedDerivedPull (C := C) (E := E) (n := n) f := by
  letI := Padic.finite_coefficientExtensionRing C.l E n hn
  let A := Padic.coefficientExtensionRing C.l E n
  let RX := realization (C := C) (E := E) (n := n) (hn := hn) X
  let RY := realization (C := C) (E := E) (n := n) (hn := hn) Y
  let IY := (intrinsicFiniteTorsionConstructible C.l E n hn Y.obj.left).ι
  let cmp := (Functor.mapDerivedCategoryCompIso
    (sfIntrinsicModuleEquivalence Y.obj.left A).inverse
    (AlgebraicGeometry.ProEtale.upperStar
      (ModuleCat.{u + 1} (ULift.{u + 1} A)) f.hom.left ⋙
        (sfIntrinsicModuleEquivalence X.obj.left A).functor)) ≪≫
      Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryCompIso _ _)
  exact Functor.isoWhiskerRight
      (S.finitePullback f ≪≫ Functor.isoWhiskerLeft IY cmp) RX.inverse ≪≫
    Functor.isoWhiskerLeft (coordinates (C := C) (E := E) (n := n) (hn := hn) Y ⋙
      AlgebraicGeometry.ProEtale.sfFixedDerivedPullback A f.hom.left) RX.unitIso.symm ≪≫
    Functor.isoWhiskerLeft (coordinates (C := C) (E := E) (n := n) (hn := hn) Y)
      (fixedPullComparison (C := C) (E := E) (n := n) f).symm

/-- Its components are the previously specified comparisons, without new choices.
Source: the same calculation (blueprint: def-sf-finite-projection-fixed-coordinates). -/
theorem pullCoordinatesIso_hom_app (S : SixFunctorFiniteOperations D C E n hn)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (M : sixFunctorFiniteCategory D C E n hn Y) :
    (pullCoordinatesIso S f).hom.app M = (fixedPullRealization S f M).hom := by
  simp only [pullCoordinatesIso, fixedPullRealization, pullRealization,
    Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, NatTrans.comp_app, CategoryTheory.Functor.map_comp, Category.assoc]
  rfl

attribute [local irreducible] realization

/-- Tensor coordinates are natural in the unrestricted first input.
Source: unit naturality (blueprint: def-sf-finite-projection-fixed-coordinates). -/
theorem tensorCoordinates_naturality (S : SixFunctorFiniteOperations D C E n hn)
    (X : SixFunctorSpace D) {K K' : sixFunctorFiniteCategory D C E n hn X}
    (a : K ⟶ K') (L : finiteTorConstructibleCategory C.l E n hn X.obj.left) :
    (coordinates (C := C) (E := E) (n := n) (hn := hn) X).map
        (((partialTensor S X).map a).app L) ≫ (tensorCoordinates S X K' L).hom =
      (tensorCoordinates S X K L).hom ≫
        ((fixedTensor (C := C) (E := E) (n := n) X).map
          ((coordinates (C := C) (E := E) (n := n) (hn := hn) X).map a)).app
            ((realization (C := C) (E := E) (n := n) (hn := hn) X).inverse.obj L.obj) := by
  let RX := realization (C := C) (E := E) (n := n) (hn := hn) X
  let t := ((fixedTensor (C := C) (E := E) (n := n) X).map
    (RX.inverse.map a.hom)).app (RX.inverse.obj L.obj)
  have h : (((partialTensor S X).map a).app L).hom = RX.functor.map t := by
    change RX.functor.map t ≫ RX.functor.map
      (((fixedTensor (C := C) (E := E) (n := n) X).obj
        (RX.inverse.obj K'.obj)).map (RX.inverse.map (𝟙 L.obj))) = RX.functor.map t
    simp only [CategoryTheory.Functor.map_id, Category.comp_id]
  exact (congrArg (fun v ↦ RX.inverse.map v ≫ RX.unitIso.inv.app _) h).trans
    (RX.unitInv_naturality t)

/-- Target coordinates are natural in the unrestricted first input.
Source: unit and tensor naturality
(blueprint: def-sf-finite-projection-fixed-coordinates). -/
theorem targetCoordinates_naturality (S : SixFunctorFiniteOperations D C E n hn)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    {K K' : sixFunctorFiniteCategory D C E n hn X} (a : K ⟶ K')
    (L : finiteTorConstructibleCategory C.l E n hn Y.obj.left) :
    (coordinates (C := C) (E := E) (n := n) (hn := hn) X).map
        (((partialTensor S X).map a).app ((torPull S f).obj L)) ≫
          (targetCoordinates S f K' L).hom =
      (targetCoordinates S f K L).hom ≫
        ((fixedTensor (C := C) (E := E) (n := n) X).map
          ((coordinates (C := C) (E := E) (n := n) (hn := hn) X).map a)).app
            ((fixedDerivedPull (C := C) (E := E) (n := n) f).obj
              ((realization (C := C) (E := E) (n := n) (hn := hn) Y).inverse.obj L.obj)) := by
  simp only [targetCoordinates, Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  rw [reassoc_of% (tensorCoordinates_naturality S X a ((torPull S f).obj L))]
  rw [NatTrans.naturality]

end WeilConjectures.CompactSupportFiniteProjection
