/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q140
-/
module

public import Sheaf.AlgebraicGeometry.ProperCurveModuli
public import Mathlib.LinearAlgebra.Prod

/-! # Marked curve deformations and their square-zero operations

Source: Stacks Project, quot.tex, Tag 0D57 and situation-curves; artin.tex,
sections tangent-spaces and inf (blueprint: def-sfb-marked-curve-deformations).

The operations are relations defined by actual cartesian squares. Their existence,
uniqueness and vector-space identities are assertions, not data chosen in a definition.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProperCurveFamily

variable {S : Scheme.{u}} (K : Type u) [Field K] (a : Spec (.of K) ⟶ S)

/-- The split square-zero base with direction module `M`. For `M = K` this is
`dualBase K a`, definitionally.
Source: Stacks, artin.tex, section-inf
(blueprint: def-sfb-marked-curve-deformations). -/
def directionBase (M : Type u) [AddCommGroup M] [Module K M]
    [Module Kᵐᵒᵖ M] [IsCentralScalar K M] : Over S :=
  Over.mk (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.inlHom K M)) ≫ a)

/-- Reduction of a split square-zero base. At `M = K` this is the existing
`dualReduction K a` (with the same underlying scheme morphism).
Source: Stacks, artin.tex, section-inf
(blueprint: def-sfb-marked-curve-deformations). -/
def directionReduction (M : Type u) [AddCommGroup M] [Module K M]
    [Module Kᵐᵒᵖ M] [IsCentralScalar K M] :
    Over.mk a ⟶ directionBase K a M :=
  Over.homMk (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K M).toRingHom)) (by
    have h : CommRingCat.ofHom (TrivSqZeroExt.inlHom K M) ≫
        CommRingCat.ofHom (TrivSqZeroExt.fstHom K K M).toRingHom = 𝟙 (CommRingCat.of K) := by
      ext x
      rfl
    change Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K M).toRingHom) ≫
      (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.inlHom K M)) ≫ a) = a
    rw [← Category.assoc, ← Spec.map_comp, h]
    simp)

/-- The base map induced contravariantly by a linear map on square-zero directions.
Source: Stacks, artin.tex, section-inf
(blueprint: def-sfb-marked-curve-deformations). -/
def directionMap {M N : Type u} [AddCommGroup M] [Module K M]
    [Module Kᵐᵒᵖ M] [IsCentralScalar K M]
    [AddCommGroup N] [Module K N]
    [Module Kᵐᵒᵖ N] [IsCentralScalar K N] (f : M →ₗ[K] N) :
    directionBase K a N ⟶ directionBase K a M :=
  Over.homMk (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map f).toRingHom)) (by
    have h : CommRingCat.ofHom (TrivSqZeroExt.inlHom K M) ≫
        CommRingCat.ofHom (TrivSqZeroExt.map f).toRingHom =
        CommRingCat.ofHom (TrivSqZeroExt.inlHom K N) := by
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro x
      exact TrivSqZeroExt.map_inl f x
    change Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map f).toRingHom) ≫
      (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.inlHom K M)) ≫ a) = _
    rw [← Category.assoc, ← Spec.map_comp, h]
    rfl)

variable {K a}

/-- A family together with an identification of its fibre along `i` with the given curve.
The identification is the cartesian arrow from that curve, so no arbitrary marking is lost.
Source: Stacks, artin.tex, sections tangent-spaces and inf; quot.tex, Tag 0D57
(blueprint: def-sfb-marked-curve-deformations). -/
structure MarkedDeformation (X : ProperCurveFamily (Over.mk a)) {T : Over S}
    (i : Over.mk a ⟶ T) where
  family : ProperCurveFamily T
  marking : X.space.obj.obj ⟶ family.space.obj.obj
  square : IsPullback marking X.projection family.projection (yoneda.map i)

namespace MarkedDeformation

variable {X : ProperCurveFamily (Over.mk a)} {T U : Over S}
  {i : Over.mk a ⟶ T} {j : Over.mk a ⟶ U}

/-- Isomorphism of marked deformations fixes the base and the specified special fibre.
Source: Stacks, artin.tex, sections tangent-spaces and inf
(blueprint: def-sfb-marked-curve-deformations). -/
def Rel (Y Z : MarkedDeformation X i) : Prop :=
  ∃ e : Y.family.space.obj.obj ≅ Z.family.space.obj.obj,
    e.hom ≫ Z.family.projection = Y.family.projection ∧ Y.marking ≫ e.hom = Z.marking

/-- Being the pullback along a specified base map, including compatibility of markings.
Source: Stacks, artin.tex, section-inf
(blueprint: def-sfb-marked-curve-deformations). -/
def IsBaseChange (Y : MarkedDeformation X i) (Z : MarkedDeformation X j)
    (b : T ⟶ U) : Prop :=
  i ≫ b = j ∧ ∃ q : Y.family.space.obj.obj ⟶ Z.family.space.obj.obj,
    IsPullback q Y.family.projection Z.family.projection (yoneda.map b) ∧
      Y.marking ≫ q = Z.marking

end MarkedDeformation

/-- Isomorphism classes of marked curve deformations over the dual numbers.
The generated quotient agrees with isomorphism classes, since `Rel` is already an
equivalence relation (identity, inverse, and composition of marking-preserving isomorphisms).
Source: Stacks, quot.tex, Tag 0D57; artin.tex, section-inf
(blueprint: def-sfb-marked-curve-deformations). -/
def Tangent (X : ProperCurveFamily (Over.mk a)) : Type (u + 1) :=
  Quot (MarkedDeformation.Rel (X := X) (i := dualReduction K a))

/-- The class of a marked dual-number deformation.
Source: Stacks, quot.tex, Tag 0D57
(blueprint: def-sfb-marked-curve-deformations). -/
def tangentClass {X : ProperCurveFamily (Over.mk a)}
    (Y : MarkedDeformation X (dualReduction K a)) : Tangent X :=
  Quot.mk _ Y

/-- The zero class is the trivial deformation, characterized by its cartesian projection
back to `X` and the identity on the marked fibre.
Source: Stacks, artin.tex, section-inf
(blueprint: def-sfb-marked-curve-deformations). -/
def IsTangentZero (X : ProperCurveFamily (Over.mk a)) (t : Tangent X) : Prop :=
  ∃ Y : MarkedDeformation X (dualReduction K a), tangentClass Y = t ∧
    ∃ q : Y.family.space.obj.obj ⟶ X.space.obj.obj,
      IsPullback q Y.family.projection X.projection (yoneda.map (dualProjection K a)) ∧
        Y.marking ≫ q = 𝟙 _

/-- Scalar multiplication is pullback by `(b,m) ↦ (b,c*m)` on the dual numbers.
Source: Stacks, artin.tex, section-inf
(blueprint: def-sfb-marked-curve-deformations). -/
def IsTangentSMul (X : ProperCurveFamily (Over.mk a))
    (c : K) (t s : Tangent X) : Prop :=
  ∃ Y Z : MarkedDeformation X (dualReduction K a),
    tangentClass Y = t ∧ tangentClass Z = s ∧
      Z.IsBaseChange Y (directionMap K a (c • (LinearMap.id : K →ₗ[K] K)))

/-- Addition glues over the common special fibre to the two-direction square-zero base,
then pulls back by addition on directions. The first two restrictions use the projections
`K × K → K`, and the result uses `(m,n) ↦ m+n`.
Source: Stacks, quot.tex, Tag 0D57; artin.tex, sections tangent-spaces and inf
(blueprint: def-sfb-marked-curve-deformations). -/
def IsTangentAdd (X : ProperCurveFamily (Over.mk a)) (t s r : Tangent X) : Prop :=
  ∃ Z : MarkedDeformation X (directionReduction K a (K × K)),
    ∃ Y₁ Y₂ Y₃ : MarkedDeformation X (dualReduction K a),
      tangentClass Y₁ = t ∧ tangentClass Y₂ = s ∧ tangentClass Y₃ = r ∧
      Y₁.IsBaseChange Z (directionMap K a (LinearMap.fst K K K)) ∧
      Y₂.IsBaseChange Z (directionMap K a (LinearMap.snd K K K)) ∧
      Y₃.IsBaseChange Z (directionMap K a
        (LinearMap.fst K K K + LinearMap.snd K K K))

/-- The actual automorphisms of the trivial dual-number family fixing its base and
restricting to the identity on `X`. They need not fix the projection back to `X`.
Source: Stacks, quot.tex, Tag 0D57; artin.tex, section-inf
(blueprint: def-sfb-marked-curve-deformations). -/
def InfinitesimalAut (X : ProperCurveFamily (Over.mk a)) : Type (u + 1) :=
  {α : Aut (pullback X.projection (yoneda.map (dualProjection K a))) //
    infinitesimalReduction K a X.projection ≫ α.hom =
      infinitesimalReduction K a X.projection ∧
    α.hom ≫ pullback.snd X.projection (yoneda.map (dualProjection K a)) =
      pullback.snd X.projection (yoneda.map (dualProjection K a))}

/-- Scalar pullback for an infinitesimal automorphism. The map `q` is the canonical
map of the trivial family induced by scaling the base: its two projections determine it
uniquely. The last equation gives the first projection of the pulled-back automorphism;
the second projection is fixed by membership in `InfinitesimalAut`.
Source: Stacks, artin.tex, section-inf
(blueprint: def-sfb-marked-curve-deformations). -/
def IsInfinitesimalAutSMul (X : ProperCurveFamily (Over.mk a))
    (c : K) (α β : InfinitesimalAut X) : Prop :=
  ∃ q : pullback X.projection (yoneda.map (dualProjection K a)) ⟶
      pullback X.projection (yoneda.map (dualProjection K a)),
    q ≫ pullback.fst X.projection (yoneda.map (dualProjection K a)) =
      pullback.fst X.projection (yoneda.map (dualProjection K a)) ∧
    q ≫ pullback.snd X.projection (yoneda.map (dualProjection K a)) =
      pullback.snd X.projection (yoneda.map (dualProjection K a)) ≫
        yoneda.map (directionMap K a (c • (LinearMap.id : K →ₗ[K] K))) ∧
    β.val.hom ≫ pullback.fst X.projection (yoneda.map (dualProjection K a)) =
      q ≫ α.val.hom ≫ pullback.fst X.projection (yoneda.map (dualProjection K a))

end AlgebraicGeometry.ProperCurveFamily
