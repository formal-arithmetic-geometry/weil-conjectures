/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q136
-/
module

public import Sheaf.AlgebraicGeometry.SpaceCoherentStackGeneral
public import Sheaf.AlgebraicGeometry.MarkedCurveDeformations
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Sheaf.AlgebraicGeometry.SpaceLocalPropertiesChartTest
import Sheaf.AlgebraicGeometry.SchemeEtaleSourceTargetProperties
import Sheaf.AlgebraicGeometry.RepresentableSourceAlgebraic
import Sheaf.AlgebraicGeometry.AlgebraicStackTangentFinite
import Sheaf.AlgebraicGeometry.ArtinDeformationTestCategory
import Sheaf.AlgebraicGeometry.ArtinRSTangentTensor
import Sheaf.AlgebraicGeometry.SplitModuleDeformationExt
import Sheaf.AlgebraicGeometry.SchemeAffineThickeningPushout

/-! # Finite tangent and infinitesimal automorphism spaces of coherent families

Source: Stacks Project, quot.tex, Situation 08KB and Lemma 08W8
(blueprint: lem-sfb-space-coherent-tangent-finite).

The existing CoherentModuli category supplies exactly the modules and cartesian arrows
of Situation 08KB. Markings below are arrows from the special fibre over the actual
reduction map. The operations are relations defined by tensor pullback and gluing;
no vector-space structure is selected as data of a definition.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace.CoherentModuli.Deformation

variable {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
  {k : Type u} [Field k] (a : Spec (.of k) ⟶ S)
  (x : Functor.Fiber (CoherentModuli.category f).p (Over.mk a))

/-- Marked coherent deformations over the specified split square-zero base.
A cartesian arrow from x over the reduction is the marking i*Y ≅ x.
Source: Stacks, 08KB and 08W8 (blueprint: lem-sfb-space-coherent-tangent-finite). -/
abbrev Marked (V : Type u) [AddCommGroup V] [Module k V]
    [Module kᵐᵒᵖ V] [IsCentralScalar k V] :=
  ObjectProperty.FullSubcategory
    (fun Y : StructuredArrow x.val
      (Functor.Fiber.fiberInclusion (p := (CoherentModuli.category f).p)
        (S := ProperCurveFamily.directionBase k a V)) ↦
      (CoherentModuli.category f).p.IsHomLift (ProperCurveFamily.directionReduction k a V)
        Y.hom)

/-- Isomorphism classes with their markings retained before quotienting.
Source: Stacks, 08W8 (blueprint: lem-sfb-space-coherent-tangent-finite). -/
def Classes (V : Type u) [AddCommGroup V] [Module k V]
    [Module kᵐᵒᵖ V] [IsCentralScalar k V] :=
  Quotient (isIsomorphicSetoid (Marked f a x V))

/-- The marked class map.
Source: Stacks, 08W8 (blueprint: lem-sfb-space-coherent-tangent-finite). -/
def classOf {V : Type u} [AddCommGroup V] [Module k V]
    [Module kᵐᵒᵖ V] [IsCentralScalar k V] (Y : Marked f a x V) : Classes f a x V :=
  Quotient.mk _ Y

/-- Transport along a linear direction map is actual cartesian pullback, preserving markings.
Source: Stacks, 08W8 and formal-defos.tex, 06IH
(blueprint: lem-sfb-space-coherent-tangent-finite). -/
def PullsBack {V W : Type u} [AddCommGroup V] [Module k V]
    [Module kᵐᵒᵖ V] [IsCentralScalar k V] [AddCommGroup W] [Module k W]
    [Module kᵐᵒᵖ W] [IsCentralScalar k W] (l : V →ₗ[k] W)
    (Y : Marked f a x V) (Z : Marked f a x W) : Prop :=
  ∃ q : Z.obj.right.val ⟶ Y.obj.right.val,
    (CoherentModuli.category f).p.IsHomLift (ProperCurveFamily.directionMap k a l) q ∧
      Z.obj.hom ≫ q = Y.obj.hom

/-- The tangent set of marked isomorphism classes over k[ε].
Source: Stacks, 08W8 (blueprint: lem-sfb-space-coherent-tangent-finite). -/
abbrev Tangent := Classes f a x k

/-- Zero is the class of the constant pullback, characterized by its cartesian retraction.
Source: Stacks, 08W8 (blueprint: lem-sfb-space-coherent-tangent-finite). -/
def IsZeroClass (t : Tangent f a x) : Prop :=
  ∃ Y : Marked f a x k, classOf f a x Y = t ∧
    ∃ q : Y.obj.right.val ⟶ x.val,
      (CoherentModuli.category f).p.IsHomLift (ProperCurveFamily.dualProjection k a) q ∧
        Y.obj.hom ≫ q = 𝟙 x.val

/-- Scaling ε is scalar pullback on the marked quotient.
Source: Stacks, 08W8 and formal-defos.tex, 06IH
(blueprint: lem-sfb-space-coherent-tangent-finite). -/
def IsScalarClass (c : k) (t s : Tangent f a x) : Prop :=
  ∃ Y Z : Marked f a x k,
    classOf f a x Y = t ∧ classOf f a x Z = s ∧
      PullsBack f a x (c • (LinearMap.id : k →ₗ[k] k)) Y Z

/-- Sum is gluing over the special fibre and pulling back by addition on directions.
Source: Stacks, 08W8 and formal-defos.tex, 06IH
(blueprint: lem-sfb-space-coherent-tangent-finite). -/
def IsSumClass (t s r : Tangent f a x) : Prop :=
  ∃ Z : Marked f a x (k × k), ∃ Y₁ Y₂ Y₃ : Marked f a x k,
    classOf f a x Y₁ = t ∧ classOf f a x Y₂ = s ∧ classOf f a x Y₃ = r ∧
      PullsBack f a x (LinearMap.fst k k k) Z Y₁ ∧
      PullsBack f a x (LinearMap.snd k k k) Z Y₂ ∧
      PullsBack f a x (LinearMap.fst k k k + LinearMap.snd k k k) Z Y₃

/-- A model of the actual trivial pullback, retaining its cartesian projection and marking.
The projection characterizes it uniquely up to its unique cartesian isomorphism.
Source: Stacks, 08W8 (blueprint: lem-sfb-space-coherent-tangent-finite). -/
structure TrivialLift where
  marked : Marked f a x k
  projection : marked.obj.right.val ⟶ x.val
  overProjection : (CoherentModuli.category f).p.IsHomLift
    (ProperCurveFamily.dualProjection k a) projection
  specialFibre : marked.obj.hom ≫ projection = 𝟙 x.val

/-- Automorphisms of the trivial lift over k[ε] restricting to the identity over k.
They need not fix its projection to x.
Source: Stacks, 08W8 (blueprint: lem-sfb-space-coherent-tangent-finite). -/
def InfAut (Y : TrivialLift f a x) :=
  {g : Y.marked.obj.right.val ≅ Y.marked.obj.right.val //
    (CoherentModuli.category f).p.map g.hom = 𝟙 _ ∧
      Y.marked.obj.hom ≫ g.hom = Y.marked.obj.hom}

/-- Scalar pullback of an infinitesimal automorphism using the canonical scaling map
on the trivial pullback. Its projection to x characterizes this map; cartesianness
then characterizes the pulled-back automorphism, including scalar zero.
Source: Stacks, 08W8 and artin.tex, section-tangent-spaces
(blueprint: lem-sfb-space-coherent-tangent-finite). -/
def IsAutScalar (Y : TrivialLift f a x) (c : k) (g h : InfAut f a x Y) : Prop :=
  ∃ q : Y.marked.obj.right.val ⟶ Y.marked.obj.right.val,
    (CoherentModuli.category f).p.IsHomLift
      (ProperCurveFamily.directionMap k a (c • (LinearMap.id : k →ₗ[k] k))) q ∧
    q ≫ Y.projection = Y.projection ∧ q ≫ g.val.hom = h.val.hom ≫ q

/-- The tangent and infinitesimal automorphism spaces of coherent families are finite
 dimensional, with exactly the scalar and gluing operations in the node.
Source: Stacks, quot.tex, Situation 08KB and Lemma 08W8
(blueprint: lem-sfb-space-coherent-tangent-finite).

Proof:
1. Choose an affine Noetherian neighbourhood Spec R of the image of Spec k in S.
All split square-zero tests have this same underlying point and factor uniquely through
this open. Restriction changes neither marked objects, arrows nor their operations.
2. The chart base-change tests of lem-weil-pbc-finite-presentation-base-change-composition,
lem-sfb-space-local-properties-chart-test, lem-trf-space-fibre-products-etale-covers and
lem-sfb-scheme-etale-source-target-properties show X₀/k is finitely presented. Apply
lem-sfb-stack-representable-source-algebraic to B over Spec R; its smooth locally finitely
presented atlas is locally of finite type. Thus lem-sfb-algebraic-stack-tangent-finite
makes the tangent space at the underlying point b₀ of B finite dimensional.
3. By lem-sfb-scheme-affine-thickening-pushout and
lem-sfb-infinitesimal-pushout-affine-charts, Artinian local ring fibre products give the
scheme pushouts needed in lem-sfb-space-coherent-pushout. Markings preserve its full
faithfulness and essential surjectivity. Hence the marked category satisfies (RS) of
def-sfb-artin-deformation-test-category; lem-sfb-artin-rs-tangent-tensor supplies exactly
the scalar and gluing operations above, both for X/B and for the fixed fibre X₀/k.
4. Forget the module to obtain a linear map T → T_b₀B. It preserves scalar pullback;
it preserves addition because the glued base map is unique. This uniqueness follows by
applying lem-sfb-space-coherent-pushout to id_B and zero modules. The kernel is exactly
the fixed-base tangent space T₀: B is set-valued, so there are no base isomorphisms.
The kernel identification is linear because its inclusion preserves pullback and gluing.
5. Apply lem-sfb-space-proper-support-module-ext-finite to X₀/k and M=N=M₀.
The given object's proper carrier supplies proper support, and finite presentation makes
M₀ coherent. Thus E¹=Ext¹(M₀,M₀) and E⁰=Ext⁰(M₀,M₀) are finite dimensional.
No properness of the ambient space X₀ is used.
6. Forget finiteness and proper support in a fixed-base marked lift. This is a full
inclusion into all flat module lifts. Use lem-sfb-space-module-flat-chart-test and
lem-sfb-space-module-split-deformation-ext to inject T₀ into E¹. Zero and scalar
pullback agree; uniqueness of gluing in all flat modules identifies coherent gluing
with the ambient sum. The injection is therefore linear.
7. Infinitesimal automorphisms of the trivial lift are unchanged by forgetting those
conditions on objects. There are no base automorphisms. The same split-deformation
classification identifies them with E⁰; composition is addition and scaling is pullback.
8. The injection into E¹ makes ker(T → T_b₀B) finite dimensional. Its image is a
subspace of finite-dimensional T_b₀B. A basis of the kernel together with lifts of a
basis of the image spans T. This proves both asserted finiteness conclusions. -/
theorem coherent_tangent_finite
    (hfp : ProperQuotFinitePresentation f) [IsLocallyNoetherian S]
    (hB : ∀ U : B.EtaleSite, LocallyOfFinitePresentation U.obj.left.hom)
    [LocallyOfFiniteType a] [QuasiCompact a] :
    ∃ (_ : AddCommGroup (Tangent f a x)) (_ : Module k (Tangent f a x)),
      FiniteDimensional k (Tangent f a x) ∧
      (∀ t : Tangent f a x, IsZeroClass f a x t ↔ t = 0) ∧
      (∀ (c : k) (t s : Tangent f a x), IsScalarClass f a x c t s ↔ s = c • t) ∧
      (∀ t s r : Tangent f a x, IsSumClass f a x t s r ↔ r = t + s) ∧
      ∃ Y : TrivialLift f a x,
        ∃ (_ : AddCommGroup (InfAut f a x Y)) (_ : Module k (InfAut f a x Y)),
          FiniteDimensional k (InfAut f a x Y) ∧
          (∀ g : InfAut f a x Y, g = 0 ↔ g.val = Iso.refl _) ∧
          (∀ g h : InfAut f a x Y, (g + h).val = g.val ≪≫ h.val) ∧
          ∀ (c : k) (g h : InfAut f a x Y), IsAutScalar f a x Y c g h ↔ h = c • g := by
  sorry

end AlgebraicGeometry.AlgebraicSpace.CoherentModuli.Deformation
