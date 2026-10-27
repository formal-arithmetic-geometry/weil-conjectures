/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q34
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicModuliStack
public import Sheaf.AlgebraicGeometry.ArtinDeformationTestCategory
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import Mathlib.LinearAlgebra.Prod

/-! # Marked deformations of objects of a stack

Source: Stacks Project, artin.tex, Tag 07X1 (lemma-finite-dimension), tangent assertion,
and Tag 07T4 (equation-predeformation-category)
(blueprint: def-sfb-marked-stack-deformations).

Marked objects and their transport relations below spell out the objects introduced in
this statement. No vector operations or stack objects are selected from existence proofs.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.StackDeformation

variable {R k : Type u} [CommRing R] [IsNoetherianRing R] [Field k]
  [Algebra R k] [Algebra.FiniteType R k]

/-- The spectrum of an R-algebra with its structural map.
Source: Stacks, artin.tex, equation-factor
(blueprint: def-sfb-marked-stack-deformations). -/
def affine (A : CommAlgCat.{u} R) : Over (Spec (.of R)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A)))

/-- The actual contravariant affine map over Spec R.
Source: Stacks, artin.tex, equation-factor
(blueprint: def-sfb-marked-stack-deformations). -/
def affineMap {A B : CommAlgCat.{u} R} (f : A ⟶ B) : affine B ⟶ affine A :=
  Over.homMk (Spec.map (CommRingCat.ofHom f.hom.toRingHom)) (by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1
    ext r
    exact f.hom.commutes r)

/-- The residue-preserving map `(a,v) ↦ (a,f v)` between square-zero test algebras,
used for the scalar, projection and addition transports of tangent classes.
Source: Stacks, artin.tex, equation-tangent-space; formal-defos.tex, Tag 06IH
(blueprint: def-sfb-marked-stack-deformations). -/
def squareZeroTransport {V W : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W] (f : V →ₗ[k] W) :
    ArtinDeformation.squareZeroTest (R := R) (k := k) V ⟶
      ArtinDeformation.squareZeroTest (R := R) (k := k) W := by
  letI : Module kᵐᵒᵖ V := Module.compHom V (RingEquiv.toOpposite k).symm.toRingHom
  letI : IsCentralScalar k V := ⟨fun _ _ ↦ rfl⟩
  letI : Algebra R (TrivSqZeroExt k V) := Algebra.restrictScalars R k _
  letI : IsScalarTower R k (TrivSqZeroExt k V) :=
    IsScalarTower.of_algebraMap_eq' (R := R) (S := k) (A := TrivSqZeroExt k V) rfl
  letI : Module kᵐᵒᵖ W := Module.compHom W (RingEquiv.toOpposite k).symm.toRingHom
  letI : IsCentralScalar k W := ⟨fun _ _ ↦ rfl⟩
  letI : Algebra R (TrivSqZeroExt k W) := Algebra.restrictScalars R k _
  letI : IsScalarTower R k (TrivSqZeroExt k W) :=
    IsScalarTower.of_algebraMap_eq' (R := R) (S := k) (A := TrivSqZeroExt k W) rfl
  let gk : TrivSqZeroExt k V →ₐ[k] TrivSqZeroExt k W := TrivSqZeroExt.map f
  let g : TrivSqZeroExt k V →ₐ[R] TrivSqZeroExt k W :=
    { toRingHom := gk.toRingHom
      commutes' := by
        intro r
        rw [IsScalarTower.algebraMap_apply R k (TrivSqZeroExt k V) r,
          IsScalarTower.algebraMap_apply R k (TrivSqZeroExt k W) r]
        exact gk.commutes (algebraMap R k r) }
  apply ObjectProperty.homMk
  refine Over.homMk (CommAlgCat.ofHom g) ?_
  ext x
  change TrivSqZeroExt.fst (gk x) = TrivSqZeroExt.fst x
  simp [gk]

variable (F : BasedCategory.{v, w} (Over (Spec (.of R))))
  (x : Functor.Fiber F.p (affine (CommAlgCat.of R k)))

/-- The marked groupoid F_x(A): arrows in the fibre commute with the marking.
A marking is the cartesian arrow from x over the residue immersion. In a fibred
groupoid every arrow is cartesian, so it is precisely an isomorphism of the reduction
with x. Source: Stacks, artin.tex, Tag 07T4, equation-predeformation-category
(blueprint: def-sfb-marked-stack-deformations). -/
abbrev Marked (A : ArtinDeformation.TestCategory R k) :=
  ObjectProperty.FullSubcategory
    (fun Y : StructuredArrow x.val
      (Functor.Fiber.fiberInclusion (p := F.p) (S := affine (ArtinDeformation.ring A))) ↦
      F.p.IsHomLift (affineMap A.obj.hom) Y.hom)

/-- Isomorphism classes of marked objects over any test algebra.
Source: Stacks, artin.tex, Tag 07T4
(blueprint: def-sfb-marked-stack-deformations). -/
def Classes (A : ArtinDeformation.TestCategory R k) :=
  Quotient (isIsomorphicSetoid (Marked F x A))

/-- The quotient map retains the marking before taking isomorphism classes.
Source: Stacks, artin.tex, Tag 07T4
(blueprint: def-sfb-marked-stack-deformations). -/
def classOf {A : ArtinDeformation.TestCategory R k} (Y : Marked F x A) : Classes F x A :=
  Quotient.mk _ Y

/-- Transport is the actual pullback relation, including the equality on markings.
Source: Stacks, artin.tex, Tag 07T4
(blueprint: def-sfb-marked-stack-deformations). -/
def PullsBack {A B : ArtinDeformation.TestCategory R k} (f : A ⟶ B)
    (Y : Marked F x A) (Z : Marked F x B) : Prop :=
  ∃ a : Z.obj.right.val ⟶ Y.obj.right.val,
    F.p.IsHomLift (affineMap f.hom.left) a ∧ Z.obj.hom ≫ a = Y.obj.hom

/-- The tangent set π₀ F_x(k[ε]), using the recorded square-zero test algebra.
Source: Stacks, artin.tex, Tag 07X1 and equation-tangent-space
(blueprint: def-sfb-marked-stack-deformations). -/
abbrev Tangent := Classes F x (ArtinDeformation.squareZeroTest (R := R) (k := k) k)

/-- The inclusion of the constant coefficients into the recorded dual-number test.
Its opposite action is the one used by squareZeroAlgebra.
Source: Stacks, artin.tex, equation-tangent-space
(blueprint: def-sfb-marked-stack-deformations). -/
def constantMap : CommAlgCat.of R k ⟶
    ArtinDeformation.squareZeroAlgebra (R := R) (k := k) k :=
  letI : Module kᵐᵒᵖ k := Module.compHom k (RingEquiv.toOpposite k).symm.toRingHom
  letI : IsCentralScalar k k := ⟨fun _ _ ↦ rfl⟩
  letI : Algebra R (TrivSqZeroExt k k) := Algebra.restrictScalars R k _
  CommAlgCat.ofHom
    { toRingHom := TrivSqZeroExt.inlHom k k
      commutes' := fun _ ↦ rfl }

/-- Zero is the constant lift, with a projection back to x splitting its marking.
Source: Stacks, artin.tex, equation-tangent-space
(blueprint: def-sfb-marked-stack-deformations). -/
def IsZeroClass (t : Tangent F x) : Prop :=
  ∃ Y : Marked F x (ArtinDeformation.squareZeroTest (R := R) (k := k) k),
    classOf F x Y = t ∧ ∃ a : Y.obj.right.val ⟶ x.val,
      F.p.IsHomLift (affineMap (constantMap (R := R) (k := k))) a ∧
      Y.obj.hom ≫ a = 𝟙 x.val

/-- Scalar transport along ε ↦ cε, on the marked quotient.
Source: Stacks, artin.tex, equation-tangent-space
(blueprint: def-sfb-marked-stack-deformations). -/
def IsScalarClass (c : k) (t s : Tangent F x) : Prop :=
  ∃ Y Z : Marked F x (ArtinDeformation.squareZeroTest (R := R) (k := k) k),
    classOf F x Y = t ∧ classOf F x Z = s ∧
      PullsBack F x (squareZeroTransport (c • (LinearMap.id : k →ₗ[k] k))) Y Z

/-- A two-direction lift restricts to the prescribed pair of marked tangent classes.
Source: Stacks, artin.tex, equation-tangent-space; formal-defos.tex, Tag 06IH
(blueprint: def-sfb-marked-stack-deformations). -/
def IsPairLift (t s : Tangent F x)
    (Z : Marked F x (ArtinDeformation.squareZeroTest (R := R) (k := k) (k × k))) : Prop :=
  ∃ Y₁ Y₂ : Marked F x (ArtinDeformation.squareZeroTest (R := R) (k := k) k),
    classOf F x Y₁ = t ∧ classOf F x Y₂ = s ∧
      PullsBack F x (squareZeroTransport (LinearMap.fst k k k)) Z Y₁ ∧
      PullsBack F x (squareZeroTransport (LinearMap.snd k k k)) Z Y₂

/-- Addition is gluing over the marked special fibre followed by ε₁,ε₂ ↦ ε.
Source: Stacks, artin.tex, equation-tangent-space; formal-defos.tex, Tag 06IH
(blueprint: def-sfb-marked-stack-deformations). -/
def IsSumClass (t s r : Tangent F x) : Prop :=
  ∃ Z : Marked F x (ArtinDeformation.squareZeroTest (R := R) (k := k) (k × k)),
    IsPairLift F x t s Z ∧
      ∃ Y : Marked F x (ArtinDeformation.squareZeroTest (R := R) (k := k) k),
        classOf F x Y = r ∧ PullsBack F x
          (squareZeroTransport (LinearMap.fst k k k + LinearMap.snd k k k)) Z Y

end AlgebraicGeometry.StackDeformation
