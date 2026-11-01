/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CompactSupportFiniteProjection.FiniteProjectionIterationRealization
public import WeilConjectures.AlgebraicGeometry.CompactCompositionProjection.CompositionProjectionData
public import WeilConjectures.AlgebraicGeometry.AmbientProperOpen.PullbackEqualityTransport

/-! # Fixed coordinates and the binary composition endpoint structure -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option maxRecDepth 2048

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.AmbientProperOpen
open AlgebraicGeometry.ProEtale.CompactCompositionProjection

namespace WeilConjectures.CompactSupportFiniteProjection
attribute [local irreducible] sfIntrinsicDerivedEquivalence
attribute [local irreducible] AlgebraicGeometry.ProEtale.derivedTensor
attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
  Functor.leftDerivedFunctor
attribute [local irreducible] DerivedCategory instCategoryDerivedCategory
  HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions

/-- The ordinary tensor data with the published fixed tensor kept as a named functor.
Source: finite tensor convention (blueprint: def-sf-finite-projection-composition-data). -/
def fixedScalarTensorData
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n} :
    letI := Padic.finite_coefficientExtensionRing C.l E n hn
    TensorData (ordinary D (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n))) :=
  letI := Padic.finite_coefficientExtensionRing C.l E n hn
  let A := ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)
  { tensor X := Functor.uncurry.obj (fixedTensor (C := C) (E := E) (n := n) X)
    pi f M N := properOpenProjection A f.hom.left M N
    delta j hj M N := by
      letI : IsOpenImmersion j.hom.left := hj
      exact (properOpenTensorIso A j.hom.left M N).hom }

/-- This is a presentation of the existing raw tensor data, including its two maps.
Source: finite tensor convention (blueprint: def-sf-finite-projection-composition-data). -/
theorem fixedScalarTensorData_eq
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n} :
    letI := Padic.finite_coefficientExtensionRing C.l E n hn
    fixedScalarTensorData (C := C) (E := E) (n := n) (hn := hn) =
      ordinaryTensor D (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)) := by
  rfl

attribute [local irreducible] fixedTensor

/-- Realize a target transport through a functor and a fixed tensor factor.
Source: coefficient transport (blueprint: def-sf-finite-projection-composition-data). -/
def realizedPullTargetIso
    {A B C₀ : Type*} [Category A] [Category B] [Category C₀]
    (R : A ⥤ B) (H : C₀ ⥤ A) (T : C₀ ⥤ C₀)
    {a b : C₀} (e : a ≅ b) {N : B} (s : N ≅ R.obj (H.obj (T.obj a))) :
    N ≅ R.obj (H.obj (T.obj b)) :=
  s ≪≫ R.mapIso (H.mapIso (T.mapIso e))

/-- Realize the triangle arrow and then its tensor pullback transport.
Source: coefficient transport (blueprint: def-sf-finite-projection-composition-data). -/
def realizedTriangleTargetIso
    {A B C₀ : Type*} [Category A] [Category B] [Category C₀]
    (R : A ⥤ B) (F H : C₀ ⥤ A) (alpha : F ⟶ H) (ha : IsIso alpha)
    (T : C₀ × C₀ ⥤ C₀) (k : C₀) {a b : C₀} (e : a ≅ b)
    {N : B} (s : N ≅ R.obj (F.obj (T.obj (k, a)))) :
    N ≅ R.obj (H.obj (T.obj (k, b))) :=
  letI := ha
  s ≪≫ R.mapIso ((asIso alpha).app (T.obj (k, a))) ≪≫
    R.mapIso (H.mapIso (T.mapIso (Iso.prod (Iso.refl k) e)))

/-- Forward formula for the triangle comparison, with no concrete derived reductions.
Source: coefficient transport (blueprint: def-sf-finite-projection-composition-data). -/
theorem realizedTriangleTargetIso_hom
    {A B C₀ : Type*} [Category A] [Category B] [Category C₀]
    (R : A ⥤ B) (F H : C₀ ⥤ A) (alpha : F ⟶ H) (ha : IsIso alpha)
    (T : C₀ × C₀ ⥤ C₀) (k : C₀) {a b : C₀} (e : a ≅ b)
    {N : B} (s : N ≅ R.obj (F.obj (T.obj (k, a)))) :
    (realizedTriangleTargetIso R F H alpha ha T k e s).hom =
      s.hom ≫ R.map (alpha.app (T.obj (k, a))) ≫
        R.map (H.map (T.map (Prod.mkHom (𝟙 k) e.hom))) := by
  rfl

variable {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
  {E : Type u} [Field E] [Algebra (Padic C.l) E]
  [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
  (S : SixFunctorFiniteOperations D C E n hn)
  {X V W Y B Z : SixFunctorSpace D}
  (j : X ⟶ V) (b : V ⟶ W) (q : V ⟶ Y) (p : W ⟶ B) (i : Y ⟶ B) (s : B ⟶ Z)
  [IsOpenImmersion ((geometry D).map j)] [IsOpenImmersion ((geometry D).map b)]
  [IsOpenImmersion ((geometry D).map i)] [QuasiCompact ((geometry D).map b)]
    [QuasiCompact ((geometry D).map i)]
  [IsProper ((geometry D).map q)] [IsProper ((geometry D).map p)] [IsProper ((geometry D).map s)]
  (hb : b ≫ p = q ≫ i)

/-- The first factor compactification of a supplied triangle.
Source: Stacks 0F7J (blueprint: def-sf-finite-projection-composition-data). -/
def binaryFirst :=
  sixFunctorFactorCompactification j q
    ‹IsOpenImmersion ((geometry D).map j)› ‹IsProper ((geometry D).map q)› (j ≫ q) rfl

/-- The prescribed outer factor compactification of a supplied triangle.
Source: Stacks 0F7J (blueprint: def-sf-finite-projection-composition-data). -/
def binarySecond :=
  sixFunctorFactorCompactification i s
    ‹IsOpenImmersion ((geometry D).map i)› ‹IsProper ((geometry D).map s)› (i ≫ s) rfl

/-- The total factor compactification, indexed by the original composite.
Source: Stacks 0F7J (blueprint: def-sf-finite-projection-composition-data). -/
def binaryTotal :=
  sixFunctorFactorCompactification (j ≫ b) (p ≫ s)
    (mappedCompositeOpen (geo := geometry D) j b)
    (mappedCompositeProper (geo := geometry D) p s) ((j ≫ q) ≫ (i ≫ s)) (by
      simp only [Category.assoc]
      rw [← Category.assoc q i s, ← hb]
      simp only [Category.assoc])

/-- Change only the index of total pullback from (j q)(i s) to (j b)(p s).
Source: Stacks 0F7J (blueprint: def-sf-finite-projection-composition-data). -/
def binaryPullCast (A : Type (u + 1)) [CommRing A] [Finite A] :=
  morphismPullbackCongr (ordinary D A) (show (j ≫ q) ≫ (i ≫ s) = (j ≫ b) ≫ (p ≫ s) by
    simp only [Category.assoc]
    rw [← Category.assoc q i s, ← hb]
    simp only [Category.assoc])

/-- Realize the total projection's target, retaining its final equality transport.
Source: Stacks 0F7J (blueprint: def-sf-finite-projection-composition-data). -/
def binaryTargetComparison
    (K : sixFunctorFiniteCategory D C E n hn X)
    (L : finiteTorConstructibleCategory C.l E n hn Z.obj.left) :=
  letI := Padic.finite_coefficientExtensionRing C.l E n hn
  let A := ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)
  let RX := realization (C := C) (E := E) (n := n) (hn := hn) X
  let RZ := realization (C := C) (E := E) (n := n) (hn := hn) Z
  let TX := fixedTensor (C := C) (E := E) (n := n) X
  let H := compact (ordinary D A) (j ≫ b) (p ≫ s)
  realizedPullTargetIso RZ.functor H (TX.obj (RX.inverse.obj K.obj))
    ((binaryPullCast j b q p i s hb A).app (RZ.inverse.obj L.obj))
    (targetComparison S ((j ≫ q) ≫ (i ≫ s)) (binaryTotal j b q p i s hb) K L)

/-- Realize the iterated tensor target and then apply the raw forward triangle arrow.
Source: Stacks 0F7J (blueprint: def-sf-finite-projection-composition-data). -/
def binaryIterationTargetComparison
    (K : sixFunctorFiniteCategory D C E n hn X)
    (L : finiteTorConstructibleCategory C.l E n hn Z.obj.left)
    (ha : letI := Padic.finite_coefficientExtensionRing C.l E n hn
      IsIso (alpha (ordinary D
        (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n))) j b q p i s hb)) :=
  letI := Padic.finite_coefficientExtensionRing C.l E n hn
  let A := ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)
  let RX := realization (C := C) (E := E) (n := n) (hn := hn) X
  let RZ := realization (C := C) (E := E) (n := n) (hn := hn) Z
  let t := fixedScalarTensorData (C := C) (E := E) (n := n) (hn := hn)
  let c := ordinary D A
  let H := compact c (j ≫ b) (p ≫ s)
  realizedTriangleTargetIso RZ.functor (compact c j q ⋙ compact c i s) H
    (alpha c j b q p i s hb) ha (t.tensor X) (RX.inverse.obj K.obj)
    ((trianglePull c j b q p i s hb).app (RZ.inverse.obj L.obj))
    (iterationTargetComparison S (j ≫ q) (i ≫ s) (binaryFirst j q) (binarySecond i s) K L)

attribute [local irreducible] fixedComponent

/-- Iteration realization at the two factor compactifications, in raw calculus coordinates.
Source: coefficient transport in the blueprint projection formula
(blueprint: def-sf-finite-projection-composition-data). -/
theorem iteration_realization_factors
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    (S : SixFunctorFiniteOperations D C E n hn)
    {X V Y B Z : SixFunctorSpace D}
    (j : X ⟶ V) (q : V ⟶ Y) (i : Y ⟶ B) (s : B ⟶ Z)
    [IsOpenImmersion ((geometry D).map j)] [IsOpenImmersion ((geometry D).map i)]
    [IsProper ((geometry D).map q)] [IsProper ((geometry D).map s)]
    (K : sixFunctorFiniteCategory D C E n hn X)
    (L : finiteTorConstructibleCategory C.l E n hn Z.obj.left)
    :
    letI := Padic.finite_coefficientExtensionRing C.l E n hn
    let A := ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)
    let c := ordinary D A
    let RX := realization (D := D) (C := C) (E := E) (n := n) (hn := hn) X
    let RZ := realization (D := D) (C := C) (E := E) (n := n) (hn := hn) Z
    let I := (intrinsicFiniteTorsionConstructible C.l E n hn Z.obj.left).ι
    let f := j ≫ q
    let g := i ≫ s
    let cf := binaryFirst j q
    let cg := binarySecond i s
    let k := RX.inverse.obj K.obj
    let l := RZ.inverse.obj L.obj
    let sb := iterationSourceComparison S (X := X) (Y := Y) (Z := Z) f g cf cg K L
    I.map (component S (X := Y) (Y := Z) g cg
      ((S.finite.support (X := X) (Y := Y) f cf).obj K) L ≫
      (S.finite.support (X := Y) (Y := Z) g cg).map
        (component S (X := X) (Y := Y) f cf K
          ((torPull S (X := Y) (Y := Z) g).obj L))) ≫
      (iterationTargetComparison S f g cf cg K L).hom = sb.hom ≫ RZ.functor.map
        (fixedComponent (D := D) (C := C) (E := E) (n := n) (hn := hn) g cg
          ((compact c j q).obj k) l ≫ (compact c i s).map
            (fixedComponent (D := D) (C := C) (E := E) (n := n) (hn := hn) f cf k
              ((c.P g).obj l))) := by
  exact iteration_realization S (j ≫ q) (i ≫ s) (binaryFirst j q) (binarySecond i s) K L

/-- The projection-free source and target equations, kept behind a proposition structure.
Source: composition normalization (blueprint: def-sf-finite-projection-composition-data). -/
structure BinaryCompositionRealization
    (sq : IsPullback b.hom.left q.hom.left p.hom.left i.hom.left)
    (K : sixFunctorFiniteCategory D C E n hn X)
    (L : finiteTorConstructibleCategory C.l E n hn Z.obj.left)
    (ha : letI := Padic.finite_coefficientExtensionRing C.l E n hn
      IsIso (alpha (ordinary D
        (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n))) j b q p i s hb)) : Prop where
  source :
      letI := Padic.finite_coefficientExtensionRing C.l E n hn
      let A := ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)
      let RX := realization (C := C) (E := E) (n := n) (hn := hn) X
      let RZ := realization (C := C) (E := E) (n := n) (hn := hn) Z
      let I := (intrinsicFiniteTorsionConstructible C.l E n hn Z.obj.left).ι
      let f := j ≫ q
      let g := i ≫ s
      let cf := binaryFirst j q
      let cg := binarySecond i s
      let cfg := binaryTotal j b q p i s hb
      I.map (((partialTensor S Z).map
        ((S.finite.composition f g cf cg cfg).hom.app K)).app L) ≫
        (iterationSourceComparison S f g cf cg K L).hom ≫
          RZ.functor.map
            (((fixedScalarTensorData (C := C) (E := E) (n := n) (hn := hn)).tensor Z).map
              (Prod.mkHom ((alpha (ordinary D A) j b q p i s hb).app
                (RX.inverse.obj K.obj)) (𝟙 (RZ.inverse.obj L.obj)))) =
        (sourceComparison S (f ≫ g) cfg K L).hom
  target :
      letI := Padic.finite_coefficientExtensionRing C.l E n hn
      let I := (intrinsicFiniteTorsionConstructible C.l E n hn Z.obj.left).ι
      let f := j ≫ q
      let g := i ≫ s
      let cf := binaryFirst j q
      let cg := binarySecond i s
      let cfg := binaryTotal j b q p i s hb
      let M := ((partialTensor S X).obj K).obj ((torPull S (f ≫ g)).obj L)
      (I.map ((S.finite.composition f g cf cg cfg).hom.app M ≫
          (S.finite.support g cg).map ((S.finite.support f cf).map
            (((partialTensor S X).obj K).map (torPullComposition S f g L).hom))) ≫
        (binaryIterationTargetComparison S j b q p i s hb K L ha).hom =
        (binaryTargetComparison S j b q p i s hb K L).hom)

end WeilConjectures.CompactSupportFiniteProjection
