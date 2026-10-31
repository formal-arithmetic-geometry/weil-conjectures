/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CompactSupportFiniteProjection.FiniteProjectionIterationRealization
public import WeilConjectures.SixFunctors.CompactSupportFiniteProjection.FiniteProjectionCompositionData
public import WeilConjectures.AlgebraicGeometry.CompactCompositionProjection.CompositionProjectionData
import all WeilConjectures.SixFunctors.CompactSupportFiniteProjection.FiniteProjectionCompositionEndpointProofs

/-! # Tensor endpoints of the finite binary support compositor

This normalization has no projection morphism in its statement.
-/

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

attribute [local irreducible] fixedTensor
attribute [local implicit_reducible] fixedScalarTensorData realizedPullTargetIso
  realizedTriangleTargetIso binaryPullCast binaryTargetComparison
  binaryIterationTargetComparison

attribute [local irreducible] sfIntrinsicDerivedEquivalence
attribute [local irreducible] AlgebraicGeometry.ProEtale.derivedTensor
attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
  Functor.leftDerivedFunctor
attribute [local irreducible] DerivedCategory instCategoryDerivedCategory
  HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions

private theorem target_paste_coordinates
    {A B C₀ : Type*} [Category A] [Category B] [Category C₀]
    (R : B ⥤ C₀) (F G : A ⥤ B) (alpha : F ⟶ G) (ha : IsIso alpha)
    (T : A ⥤ A ⥤ A) (k : A)
    {x₀ x₁ w₀ l₀ l₁ l₂ : A} {b₀ b₁ b₂ c₀ c₁ : C₀}
    (e : x₀ ⟶ x₁) (d : x₁ ≅ (T.obj k).obj l₁)
    (t : l₁ ≅ l₂) (z₀ : x₀ ≅ w₀) (z₁ : w₀ ≅ (T.obj k).obj l₀)
    (z₂ : l₀ ≅ l₂) (p : b₀ ⟶ b₂) (a : b₀ ⟶ b₁) (v : b₁ ⟶ b₂)
    (hp : p = a ≫ v)
    (s₀ : b₁ ≅ c₀) (s₀' : c₀ ≅ R.obj (F.obj x₀))
    (s₁ : b₂ ≅ c₁) (s₁' : c₁ ≅ R.obj (F.obj x₁))
    (h₀ : b₀ ≅ R.obj (G.obj x₀))
    (hs : a ≫ s₀.hom ≫ s₀'.hom ≫ R.map (alpha.app x₀) = h₀.hom)
    (hn : v ≫ s₁.hom ≫ s₁'.hom = s₀.hom ≫ s₀'.hom ≫ R.map (F.map e))
    (hi : e ≫ d.hom ≫ ((T.obj k).mapIso t).hom =
      z₀.hom ≫ z₁.hom ≫ ((T.obj k).mapIso z₂).hom) :
    p ≫ (realizedTriangleTargetIso R F G alpha ha (Functor.uncurry.obj T) k t
      (s₁ ≪≫ s₁' ≪≫ R.mapIso (F.mapIso d))).hom =
    (realizedPullTargetIso R G (T.obj k) z₂
      (h₀ ≪≫ R.mapIso (G.mapIso (z₀ ≪≫ z₁)))).hom := by
  rw [hp]
  dsimp only [realizedTriangleTargetIso, realizedPullTargetIso]
  rw [uncurry_refl_iso]
  exact target_paste_iso R F G alpha ha e d ((T.obj k).mapIso t)
    z₀ z₁ ((T.obj k).mapIso z₂) a v s₀ s₀' s₁ s₁' h₀ hs hn hi

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

section FinalProof
attribute [local implicit_reducible] realization sixFunctorFiniteRealization
  sixFunctorFiniteSupport sfIntrinsicCompactSupport sfAmbientCompactSupportCandidate
  originInclusion ordinary sixFunctorFactorCompactification compact
  binaryFirst binarySecond binaryTotal finiteTorConstructible
attribute [local irreducible] sfIntrinsicCompactSupportComparison
  alpha towerCandidateComparison originCompositionAmbient
  ProjectionTriangleAssembly.candidateCompositor

omit [IsOpenImmersion ((geometry D).map j)] [IsOpenImmersion ((geometry D).map b)]
  [IsOpenImmersion ((geometry D).map i)] [QuasiCompact ((geometry D).map b)]
  [QuasiCompact ((geometry D).map i)] [IsProper ((geometry D).map q)]
  [IsProper ((geometry D).map p)] [IsProper ((geometry D).map s)] in
private theorem tensor_binary_input_iso
    (K : sixFunctorFiniteCategory D C E n hn X)
    (L : finiteTorConstructibleCategory C.l E n hn Z.obj.left) :
    letI := Padic.finite_coefficientExtensionRing C.l E n hn
    let A := ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)
    let RX := realization (C := C) (E := E) (n := n) (hn := hn) X
    let RZ := realization (C := C) (E := E) (n := n) (hn := hn) Z
    let IX := (intrinsicFiniteTorsionConstructible C.l E n hn X.obj.left).ι
    let TX := fixedTensor (C := C) (E := E) (n := n) X
    let f := j ≫ q
    let g := i ≫ s
    let k := RX.inverse.obj K.obj
    RX.inverse.map (IX.map
        (((partialTensor S X).obj K).map (torPullComposition S f g L).hom)) ≫
      (iterationTensorComparison S f g K L).hom ≫
      ((TX.obj k).mapIso ((trianglePull (ordinary D A) j b q p i s hb).app
        (RZ.inverse.obj L.obj))).hom =
    (RX.unitIso.app
      ((TX.obj k).obj (RX.inverse.obj ((torPull S (f ≫ g)).obj L).obj))).inv ≫
      (TX.obj k).map (fixedPullRealization S (f ≫ g) ⟨L.obj, L.property.1⟩).hom ≫
      ((TX.obj k).mapIso ((binaryPullCast j b q p i s hb A).app
        (RZ.inverse.obj L.obj))).hom := by
  exact tensor_binary_input S j b q p i s hb K L

/-- The two tensor endpoints of the prescribed binary compositor agree with the
raw Cartesian triangle compositor. This statement concerns support, pullback and
tensor comparisons only: it contains no projection component or projection equation.

Source: fix-prop-projection-formula.proof.md, composition normalization;
finiteCompositionNormalization and finitePullCompositionNormalization of
SixFunctorFiniteOperations; Stacks 0F7J
(blueprint: lem-sf-finite-projection-composition-realization).

Proof: use fixedSupportComparison_composition_app in inverse coefficient coordinates.
Its explicit four-factor candidate compositor agrees with candidateCompositor because
candidate comparisons reverse under inversion. The Cartesian compositor theorem then
identifies it with alpha for the supplied triangle. For the source equation, take
the forward support comparison and tensor it with the fixed presentation of L.
For the target equation, use fixedPullRealization_composition before tensoring;
unit naturality cancels the intermediate coefficient units and trianglePull cancels
the pullback compositor, leaving binaryPullCast. Support naturality and naturality
of alpha paste this tensor equation with the forward support equation. The generic
pasting calculation keeps all three comparisons in their specified coordinates.
Only L needs finite Tor amplitude. The same formulas apply to zero objects, identity
morphisms and empty schemes, and do not use invertibility of any projection. -/
theorem binary_composition_realization
    (sq : IsPullback b.hom.left q.hom.left p.hom.left i.hom.left)
    (K : sixFunctorFiniteCategory D C E n hn X)
    (L : finiteTorConstructibleCategory C.l E n hn Z.obj.left)
    (ha : letI := Padic.finite_coefficientExtensionRing C.l E n hn
      IsIso (alpha (ordinary D
        (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n))) j b q p i s hb)) :
    BinaryCompositionRealization S j b q p i s hb sq K L ha := by
  let := Padic.finite_coefficientExtensionRing C.l E n hn
  let A := ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)
  let RX := realization (C := C) (E := E) (n := n) (hn := hn) X
  let RZ := realization (C := C) (E := E) (n := n) (hn := hn) Z
  let TX := fixedTensor (C := C) (E := E) (n := n) X
  let I := (intrinsicFiniteTorsionConstructible C.l E n hn Z.obj.left).ι
  let f := j ≫ q
  let g := i ≫ s
  let cf := binaryFirst j q
  let cg := binarySecond i s
  let cfg := binaryTotal j b q p i s hb
  let F := compact (ordinary D A) j q
  let G := compact (ordinary D A) i s
  let H := compact (ordinary D A) (j ≫ b) (p ≫ s)
  let k := RX.inverse.obj K.obj
  let l := RZ.inverse.obj L.obj
  let M := ((partialTensor S X).obj K).obj ((torPull S (f ≫ g)).obj L)
  let N := ((partialTensor S X).obj K).obj ((torPull S f).obj ((torPull S g).obj L))
  let a := ((partialTensor S X).obj K).map (torPullComposition S f g L).hom
  refine ⟨binary_composition_source S j b q p i s hb sq K L, ?_⟩
  have hs := support_binary_forward S j b q p i s hb sq M
  have hn := iteration_support_naturality S f g cf cg a
  have hi' := tensor_binary_input_iso S j b q p i s hb K L
  exact target_paste_coordinates RZ.functor (F ⋙ G) H
    (alpha (ordinary D A) j b q p i s hb) ha TX k
    (RX.inverse.map a.hom) (iterationTensorComparison S f g K L)
    ((trianglePull (ordinary D A) j b q p i s hb).app l)
    (RX.unitIso.app ((TX.obj k).obj (RX.inverse.obj ((torPull S (f ≫ g)).obj L).obj))).symm
    ((TX.obj k).mapIso (fixedPullRealization S (f ≫ g) ⟨L.obj, L.property.1⟩))
    ((binaryPullCast j b q p i s hb A).app l)
    (I.map ((S.finite.composition f g cf cg cfg).hom.app M ≫
      (S.finite.support g cg).map ((S.finite.support f cf).map a)))
    (I.map ((S.finite.composition f g cf cg cfg).hom.app M))
    (I.map ((S.finite.support g cg).map ((S.finite.support f cf).map a)))
    (I.map_comp _ _)
    (supportRealization S g cg ((S.finite.support f cf).obj M))
    (RZ.functor.mapIso (G.mapIso (fixedSupportRealization S f cf M)))
    (supportRealization S g cg ((S.finite.support f cf).obj N))
    (RZ.functor.mapIso (G.mapIso (fixedSupportRealization S f cf N)))
    (supportRealization S (f ≫ g) cfg M) hs hn hi'

end FinalProof

end WeilConjectures.CompactSupportFiniteProjection
