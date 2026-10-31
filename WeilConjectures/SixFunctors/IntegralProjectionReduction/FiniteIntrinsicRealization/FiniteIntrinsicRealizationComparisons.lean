/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralProjectionReduction.FiniteIntrinsicProjectionCoordinates.FiniteIntrinsicProjectionCoordinates

/-! # Inverse realization coordinates for finite projection

Source: Stacks 07A4, 07A6 and the specified coefficient realization.
(blueprint: def-sf-finite-intrinsic-realization-comparisons).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale

namespace WeilConjectures.IntegralProjectionReduction
namespace FiniteIntrinsicRealization

/-- Conjugate a functor comparison by its two specified equivalences.
Source: uniqueness of equivalence inverses, Stacks 003G.
(blueprint: def-sf-finite-intrinsic-realization-comparisons). -/
def inverseComparison
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (e : A ≌ B) (f : C ≌ D) (P : B ⥤ D) (Q : A ⥤ C)
    (r : e.functor ⋙ P ≅ Q ⋙ f.functor) : P ⋙ f.inverse ≅ e.inverse ⋙ Q :=
  Functor.isoWhiskerRight e.counitIso.symm (P ⋙ f.inverse) ≪≫
    Functor.isoWhiskerLeft e.inverse (Functor.isoWhiskerRight r f.inverse) ≪≫
    Functor.isoWhiskerLeft (e.inverse ⋙ Q) f.unitIso.symm

variable {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
  {E : Type u} [Field E] [Algebra (Padic C.l) E]
  [FiniteDimensional (Padic C.l) E]

attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
  AlgebraicGeometry.Scheme.residueField sfIntrinsicModuleEquivalence
attribute [-instance] WeilConjectures.IntegralHom.derivedCategory

/-- The exact pullback comparison used in midpoint, before cancelling the target unit.
Source: exact localization of composite functors, Stacks 07A6.
(blueprint: def-sf-finite-intrinsic-realization-comparisons). -/
def pullback (m : ℕ) {X Y : SixFunctorSpace D} (f : X ⟶ Y) :
    finiteDerivedPullback C.l E m f.hom.left ≅
      (CompactSupportFiniteProjection.realization (C := C) (E := E)
        (n := m + 1) (hn := Nat.le_add_left 1 m) Y).inverse ⋙
      (upperStar (ModuleCat.{u + 1}
        (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E (m + 1))))
          f.hom.left).leftDerivedFunctor ⋙
      (CompactSupportFiniteProjection.realization (C := C) (E := E)
        (n := m + 1) (hn := Nat.le_add_left 1 m) X).functor :=
  Functor.mapDerivedCategoryCompIso
      (sfIntrinsicModuleEquivalence Y.obj.left
        (Padic.coefficientExtensionRing C.l E (m + 1))).inverse
      ((upperStar (ModuleCat.{u + 1}
        (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E (m + 1)))) f.hom.left) ⋙
        (sfIntrinsicModuleEquivalence X.obj.left
          (Padic.coefficientExtensionRing C.l E (m + 1))).functor) ≪≫
    Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryCompIso _ _) ≪≫
    Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight
      (leftDerivedUpperStarIsoMapDerivedCategory _ f.hom.left).symm _)

/-- Inverse coordinates for the actual finite pullback.
Source: the preceding exact comparison and the coefficient unit, Stacks 07A6.
(blueprint: def-sf-finite-intrinsic-realization-comparisons). -/
def inversePullback (m : ℕ) {X Y : SixFunctorSpace D} (f : X ⟶ Y) :
    finiteDerivedPullback C.l E m f.hom.left ⋙
      (CompactSupportFiniteProjection.realization (C := C) (E := E)
        (n := m + 1) (hn := Nat.le_add_left 1 m) X).inverse ≅
    (CompactSupportFiniteProjection.realization (C := C) (E := E)
      (n := m + 1) (hn := Nat.le_add_left 1 m) Y).inverse ⋙
      (upperStar (ModuleCat.{u + 1}
        (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E (m + 1))))
          f.hom.left).leftDerivedFunctor := by
  let RX := CompactSupportFiniteProjection.realization (C := C) (E := E)
    (n := m + 1) (hn := Nat.le_add_left 1 m) X
  let RY := CompactSupportFiniteProjection.realization (C := C) (E := E)
    (n := m + 1) (hn := Nat.le_add_left 1 m) Y
  exact Functor.isoWhiskerRight (pullback (C := C) (E := E) m f) RX.inverse ≪≫
    Functor.isoWhiskerLeft (RY.inverse ⋙ _) RX.unitIso.symm

/-- Inverse coordinates for the K-injective-normalized finite direct image.
Source: Stacks 07A5, normalized direct-image realization.
(blueprint: def-sf-finite-intrinsic-realization-comparisons). -/
def inverseDirectImage (m : ℕ) {X Y : SixFunctorSpace D} (f : X ⟶ Y) :=
  inverseComparison
    (CompactSupportFiniteProjection.realization (C := C) (E := E)
      (n := m + 1) (hn := Nat.le_add_left 1 m) X)
    (CompactSupportFiniteProjection.realization (C := C) (E := E)
      (n := m + 1) (hn := Nat.le_add_left 1 m) Y)
    (proEtaleConstantDerivedDirectImage f.hom.left
      (Padic.coefficientExtensionRing C.l E (m + 1)))
    (lowerStar (ModuleCat.{u + 1}
      (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E (m + 1))))
        f.hom.left).rightDerivedFunctor
    (sfIntrinsicDerivedDirectImageComparison f.hom.left _)

end FiniteIntrinsicRealization
end WeilConjectures.IntegralProjectionReduction

namespace WeilConjectures.IntegralProjectionReduction.FiniteIntrinsicRealization
open CompactSupportFiniteProjection
attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
  AlgebraicGeometry.Scheme.residueField sfIntrinsicModuleEquivalence
attribute [local implicit_reducible] Equivalence.mapDerivedCategory
  sfIntrinsicDerivedEquivalence CompactSupportFiniteProjection.realization
  sixFunctorFiniteRealization
attribute [-instance] WeilConjectures.IntegralHom.derivedCategory

/-- The specified exact open coefficient comparison, localized with its compositors.
Source: Stacks 03DA, 07A6; the specified open-extension comparison.
(blueprint: def-sf-finite-intrinsic-realization-comparisons). -/
def openComparison
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (m : ℕ)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) (c : Compactification f.hom.left) :
    let A := Padic.coefficientExtensionRing C.l E (m + 1)
    let B := ModuleCat.{u + 1} (ULift.{u + 1} A)
    let RX := realization (C := C) (E := E) (n := m + 1)
      (hn := Nat.le_add_left 1 m) X
    let RZ := realization (C := C) (E := E) (n := m + 1)
      (hn := Nat.le_add_left 1 m) (compactSupportProjectionSquare f c).Z
    RX.functor ⋙ (sfIntrinsicExtensionByZero c.i A).mapDerivedCategory ≅
      (openImmersionLowerShriek B c.i).mapDerivedCategory ⋙ RZ.functor := by
  dsimp only
  change (sfIntrinsicModuleEquivalence X.obj.left _).functor.mapDerivedCategory ⋙
    (sfIntrinsicExtensionByZero c.i _).mapDerivedCategory ≅
    (openImmersionLowerShriek _ c.i).mapDerivedCategory ⋙
      (sfIntrinsicModuleEquivalence c.Z _).functor.mapDerivedCategory
  exact (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (sfIntrinsicOpenExtensionComparison _ c.i) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- The actual open endpoint in inverse coefficient coordinates.
Source: Stacks 003G, 03DA; coefficient unit and exact open realization.
(blueprint: def-sf-finite-intrinsic-realization-comparisons). -/
def openCoordinate
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (m : ℕ)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) (c : Compactification f.hom.left)
    (K : sixFunctorFiniteCategory D C E (m + 1) (Nat.le_add_left 1 m) X)
    (U : normalizedDVRDerived C.l E X.obj.left m) (k : U ≅ K.obj) :
    let A := Padic.coefficientExtensionRing C.l E (m + 1)
    let B := ModuleCat.{u + 1} (ULift.{u + 1} A)
    let RX := realization (C := C) (E := E) (n := m + 1)
      (hn := Nat.le_add_left 1 m) X
    let RZ := realization (C := C) (E := E) (n := m + 1)
      (hn := Nat.le_add_left 1 m) (compactSupportProjectionSquare f c).Z
    RZ.inverse.obj ((sfIntrinsicExtensionByZero c.i A).mapDerivedCategory.obj U) ≅
      (openImmersionLowerShriek B c.i).mapDerivedCategory.obj (RX.inverse.obj K.obj) := by
  dsimp only
  let A := Padic.coefficientExtensionRing C.l E (m + 1)
  let RX := realization (C := C) (E := E) (n := m + 1)
    (hn := Nat.le_add_left 1 m) X
  let RZ := realization (C := C) (E := E) (n := m + 1)
    (hn := Nat.le_add_left 1 m) (compactSupportProjectionSquare f c).Z
  let J := (sfIntrinsicExtensionByZero c.i A).mapDerivedCategory
  exact RZ.inverse.mapIso
    (J.mapIso (k ≪≫ (RX.counitIso.app K.obj).symm) ≪≫
      (openComparison (C := C) (E := E) m f c).app (RX.inverse.obj K.obj)) ≪≫
    (RZ.unitIso.app _).symm

end WeilConjectures.IntegralProjectionReduction.FiniteIntrinsicRealization
