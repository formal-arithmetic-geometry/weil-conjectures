/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ConstructibleSheaf.RankOne
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import Mathlib.Topology.LocallyConstant.Algebra
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Etale
public import WeilConjectures.Topology.LocallyConstantMapsPresheaf

/-!
# Automorphisms of the constant finite trace line

Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-the-orientation-from-the-diagonal/sk-prop-sp-orientation/
 sk-prop-sp-orientation-vector-bundle.proof.md`, Step 1, sentence identifying the
translation action on the trace line with multiplication by a locally constant unit
(blueprint: lem-pur-constant-trace-line-automorphism-unit).

The scalar is a section of the constant sheaf of units, represented by a
`LocallyConstant` function through `AlgebraicGeometry.constantSheaf_sections_locallyConstant`.
The multiplication automorphism is characterized stalkwise, so the definition does not
choose an unrelated endomorphism.  Pullback is composition with the underlying continuous
map of the scheme morphism.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory MonoidalClosed
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.Etale

/-- The constant finite trace line on the small étale site of `X`.

Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-the-orientation-from-the-diagonal/sk-prop-sp-orientation/
 sk-prop-sp-orientation-vector-bundle.proof.md`, Step 1
(blueprint: lem-pur-constant-trace-line-automorphism-unit). -/
abbrev constantTraceLine (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A) :=
  (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A)

/-- Pull a locally constant unit-valued function back along a scheme morphism.

Source: the pullback clause of the constant trace-line statement, using the inverse-image
construction of `prop-weil-pbc-inverse-image-modules-exact` (blueprint:
lem-pur-constant-trace-line-automorphism-unit). -/
def pullbackConstantTraceUnit {X Y : Scheme.{u}} {A : Type (u + 1)} [CommRing A]
    (f : Y ⟶ X) (u : LocallyConstant X Aˣ) : LocallyConstant Y Aˣ :=
  LocallyConstant.comap (ContinuousMap.mk f.base.hom f.base.hom.continuous) u

/-- Stalkwise meaning of multiplication by a locally constant unit.

The scalar is evaluated at every point of every geometric test scheme.  The stalk map is
therefore multiplication by the corresponding element of `A`; this also covers empty and
disconnected schemes without a connectedness assumption.

Source: Stacks Project, Etale Cohomology, Remark 59.23.2 (Tag 03P5), and the
constant rank-one calculation in the cited blueprint proof (blueprint:
lem-pur-constant-trace-line-automorphism-unit). -/
def constantTraceLineScalarCorresponds (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (u : LocallyConstant X Aˣ) (e : (End (constantTraceLine X A))ˣ) : Prop :=
  ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    (s : Spec (.of Ω) ⟶ X) (x : Spec (.of Ω)),
    (Scheme.pointSmallEtale s).sheafFiber.map e.val =
      ((u (s.base.hom x) : A) • 𝟙
        ((Scheme.pointSmallEtale s).sheafFiber.obj (constantTraceLine X A)))

/-- Existence and uniqueness of multiplication by a locally constant unit.

Source: Stacks Project, Etale Cohomology, Remark 59.23.2 (Tag 03P5), together with
`MonoidalCategory.unitsUnitEndMulEquivAut` for the constant rank-one line
(blueprint: lem-pur-constant-trace-line-automorphism-unit).
-/
theorem constantTraceLine_multiplication_exists (X : Scheme.{u}) (A : Type (u + 1))
    [CommRing A] (u : LocallyConstant X Aˣ) :
    ∃! e : (End (constantTraceLine X A))ˣ,
      constantTraceLineScalarCorresponds X A u e := by
  sorry


end AlgebraicGeometry.Etale
