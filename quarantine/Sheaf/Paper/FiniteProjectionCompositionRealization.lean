/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B6
-/
module

public import Sheaf.Paper.FiniteProjectionIterationRealization
public import Sheaf.SixFunctors.CompositionProjectionData

/-! # Tensor endpoints of the finite binary support compositor

This normalization has no projection morphism in its statement.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.AmbientProperOpen
open AlgebraicGeometry.ProEtale.CompactCompositionProjection

namespace WeilConjectures.CompactSupportFiniteProjection

attribute [local irreducible] AlgebraicGeometry.ProEtale.derivedTensor
attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
  Functor.leftDerivedFunctor
attribute [local irreducible] DerivedCategory instCategoryDerivedCategory
  HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions

/-- The ordinary tensor data with the published fixed tensor kept as a named functor.
Source: finite tensor convention (blueprint: lem-sf-finite-projection-composition-realization). -/
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
Source: finite tensor convention (blueprint: lem-sf-finite-projection-composition-realization). -/
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
Source: coefficient transport (blueprint: lem-sf-finite-projection-composition-realization). -/
def realizedPullTargetIso
    {A B C₀ : Type*} [Category A] [Category B] [Category C₀]
    (R : A ⥤ B) (H : C₀ ⥤ A) (T : C₀ ⥤ C₀)
    {a b : C₀} (e : a ≅ b) {N : B} (s : N ≅ R.obj (H.obj (T.obj a))) :
    N ≅ R.obj (H.obj (T.obj b)) :=
  s ≪≫ R.mapIso (H.mapIso (T.mapIso e))

/-- The forward formula is checked before specializing any derived functor.
Source: coefficient transport (blueprint: lem-sf-finite-projection-composition-realization). -/
theorem realizedPullTargetIso_hom
    {A B C₀ : Type*} [Category A] [Category B] [Category C₀]
    (R : A ⥤ B) (H : C₀ ⥤ A) (T : C₀ ⥤ C₀)
    {a b : C₀} (e : a ≅ b) {N : B} (s : N ≅ R.obj (H.obj (T.obj a))) :
    (realizedPullTargetIso R H T e s).hom = s.hom ≫ R.map (H.map (T.map e.hom)) := by
  rfl

/-- Realize the triangle arrow and then its tensor pullback transport.
Source: coefficient transport (blueprint: lem-sf-finite-projection-composition-realization). -/
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
Source: coefficient transport (blueprint: lem-sf-finite-projection-composition-realization). -/
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
Source: Stacks 0F7J (blueprint: lem-sf-finite-projection-composition-realization). -/
def binaryFirst :=
  sixFunctorFactorCompactification j q
    ‹IsOpenImmersion ((geometry D).map j)› ‹IsProper ((geometry D).map q)› (j ≫ q) rfl

/-- The prescribed outer factor compactification of a supplied triangle.
Source: Stacks 0F7J (blueprint: lem-sf-finite-projection-composition-realization). -/
def binarySecond :=
  sixFunctorFactorCompactification i s
    ‹IsOpenImmersion ((geometry D).map i)› ‹IsProper ((geometry D).map s)› (i ≫ s) rfl

/-- The total factor compactification, indexed by the original composite.
Source: Stacks 0F7J (blueprint: lem-sf-finite-projection-composition-realization). -/
def binaryTotal :=
  sixFunctorFactorCompactification (j ≫ b) (p ≫ s)
    (mappedCompositeOpen (geo := geometry D) j b)
    (mappedCompositeProper (geo := geometry D) p s) ((j ≫ q) ≫ (i ≫ s)) (by
      simp only [Category.assoc]
      rw [← Category.assoc q i s, ← hb]
      simp only [Category.assoc])

/-- Change only the index of total pullback from (j q)(i s) to (j b)(p s).
Source: Stacks 0F7J (blueprint: lem-sf-finite-projection-composition-realization). -/
def binaryPullCast (A : Type (u + 1)) [CommRing A] [Finite A] :=
  (ordinary D A).pCongr (show (j ≫ q) ≫ (i ≫ s) = (j ≫ b) ≫ (p ≫ s) by
    simp only [Category.assoc]
    rw [← Category.assoc q i s, ← hb]
    simp only [Category.assoc])

/-- Realize the total projection's target, retaining its final equality transport.
Source: Stacks 0F7J (blueprint: lem-sf-finite-projection-composition-realization). -/
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
Source: Stacks 0F7J (blueprint: lem-sf-finite-projection-composition-realization). -/
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

attribute [local irreducible] realization fixedComponent

/-- Iteration realization at the two factor compactifications, in raw calculus coordinates.
Source: coefficient transport in the blueprint projection formula
(blueprint: lem-sf-finite-projection-composition-realization). -/
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

/-- Forward formula for the concrete iteration target, through the generic comparison API.
Source: coefficient transport in the blueprint projection formula
(blueprint: lem-sf-finite-projection-composition-realization). -/
theorem binaryIterationTargetComparison_hom
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
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
    (K : sixFunctorFiniteCategory D C E n hn X)
    (L : finiteTorConstructibleCategory C.l E n hn Z.obj.left)
    (ha : letI := Padic.finite_coefficientExtensionRing C.l E n hn
      IsIso (alpha (ordinary D
        (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n))) j b q p i s hb)) :
    letI := Padic.finite_coefficientExtensionRing C.l E n hn
    let A := ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)
    let c := ordinary D A
    let t := fixedScalarTensorData (D := D) (C := C) (E := E) (n := n) (hn := hn)
    let RX := realization (D := D) (C := C) (E := E) (n := n) (hn := hn) X
    let RZ := realization (D := D) (C := C) (E := E) (n := n) (hn := hn) Z
    let f := j ≫ q
    let g := i ≫ s
    let cf := binaryFirst j q
    let cg := binarySecond i s
    let k := RX.inverse.obj K.obj
    let l := RZ.inverse.obj L.obj
    let td := binaryIterationTargetComparison S
      (X := X) (V := V) (W := W) (Y := Y) (B := B) (Z := Z) j b q p i s hb K L ha
    td.hom = (iterationTargetComparison S f g cf cg K L).hom ≫
      RZ.functor.map ((alpha c j b q p i s hb).app
        ((t.tensor X).obj (k, (c.P f).obj ((c.P g).obj l)))) ≫
      RZ.functor.map ((compact c (j ≫ b) (p ≫ s)).map
        ((t.tensor X).map
          (Prod.mkHom (𝟙 k) ((trianglePull c j b q p i s hb).hom.app l)))) := by
  let := Padic.finite_coefficientExtensionRing C.l E n hn
  let c := ordinary D (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n))
  let RX := realization (D := D) (C := C) (E := E) (n := n) (hn := hn) X
  let RZ := realization (D := D) (C := C) (E := E) (n := n) (hn := hn) Z
  let t := fixedScalarTensorData (D := D) (C := C) (E := E) (n := n) (hn := hn)
  exact realizedTriangleTargetIso_hom RZ.functor
    (compact c j q ⋙ compact c i s) (compact c (j ≫ b) (p ≫ s))
    (alpha c j b q p i s hb) ha (t.tensor X) (RX.inverse.obj K.obj)
    ((trianglePull c j b q p i s hb).app (RZ.inverse.obj L.obj))
    (iterationTargetComparison S (j ≫ q) (i ≫ s) (binaryFirst j q) (binarySecond i s) K L)

/-- The projection-free source and target equations, kept behind a proposition structure.
Source: composition normalization (blueprint: lem-sf-finite-projection-composition-realization). -/
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

/-- The two tensor endpoints of the prescribed binary compositor agree with the
raw Cartesian triangle compositor. This statement concerns support, pullback and
tensor comparisons only: it contains no projection component or projection equation.

Source: fix-prop-projection-formula.proof.md, composition normalization;
finiteCompositionNormalization and finitePullCompositionNormalization of
SixFunctorFiniteOperations; Stacks 0F7J
(blueprint: lem-sf-finite-projection-composition-realization).

Proof: use originSupportComparison_composition at K and its tensor with the pulled-back
finite-Tor input, which is constructible by domains. Expand originSupportComparison and
cancel its tower candidate comparisons. This identifies the operation compositor with
the canonical origin compositor at the three factor compactifications. The
Cartesian compositor theorem identifies that origin compositor with alpha for this
triangle. For the first equation apply inverse coefficient realization, tensor its
forward component with the fixed presentation of L, and realize back; unit naturality cancels
the intermediate coefficient units. For the second equation expand the two iterated
support realizations, use finitePullCompositionNormalization, and cancel the units
in iterationTensorComparison. The resulting pullback arrow is trianglePull, including
binaryPullCast at its endpoint. Naturality cancels the chosen origin witnesses.
Only L needs finite Tor amplitude. The same formulas apply to zero objects, identity
morphisms and empty schemes, and do not use invertibility of any projection. -/
theorem binary_composition_realization
    (sq : IsPullback b.hom.left q.hom.left p.hom.left i.hom.left)
    (K : sixFunctorFiniteCategory D C E n hn X)
    (L : finiteTorConstructibleCategory C.l E n hn Z.obj.left)
    (ha : letI := Padic.finite_coefficientExtensionRing C.l E n hn
      IsIso (alpha (ordinary D
        (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n))) j b q p i s hb)) :
    BinaryCompositionRealization S j b q p i s hb sq K L ha := by sorry

end WeilConjectures.CompactSupportFiniteProjection
