/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q32
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace

import Sheaf.AlgebraicGeometry.SpaceSmoothReducedLocality
import Sheaf.AlgebraicGeometry.SplitSolvableTorsorsAndVariety
import Sheaf.AlgebraicGeometry.StandardGroupSchemes
import Sheaf.AlgebraicGeometry.ProjectiveLineGenusZero
import Sheaf.AlgebraicGeometry.SmoothConnectedCurveLocalRings
import Sheaf.AlgebraicGeometry.ProjectiveSpaceStandardCharts
import Sheaf.AlgebraicGeometry.Curve.ProperFunctionFieldMorphisms
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.FieldTheory.RatFunc.Luroth

/-! # Complete curves with a nontrivial connected linear-group action

Source: Milne, Algebraic Groups (2017), Proposition 20.5 and 20.2--20.3, printed p.408
(blueprint: lem-sfb-complete-curve-connected-linear-action).

The tensor product in `Over (Spec (.of F))` is the fibre product over `F`.
The action is an actual morphism over `F`, with its two action identities written explicitly.
The conclusion uses the base-change projective-space model with two homogeneous coordinates.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory

namespace AlgebraicGeometry

/-- A nontrivial action of a smooth connected affine algebraic group on a smooth proper
integral curve over an algebraically closed field identifies the curve with the projective line.
Source: Milne, Algebraic Groups (2017), Proposition 20.5 and 20.2--20.3, printed p.408
(blueprint: lem-sfb-complete-curve-connected-linear-action).

Proof plan (the accepted coordinate version of Milne's solvable reduction):
1. Put T = H ×_F C. Smooth base change and composition
   (lem-sfb-stack-smooth-permanence), followed by lem-sfb-space-smooth-reduced-locality over
   the reduced scheme Spec F, show that T is reduced. It is of finite type by
   lem-sfb-finite-type-composition-base-change. Its closed points are dense by
   lem-sc-lft-over-field-jacobson-space and F-rational by
   lem-weil-pbc-closed-point-residue-field-base. If all pairs of rational points were fixed,
   a and the second projection would agree on the disjoint union of those points
   (def-pc-fibre-product). Properness makes C separated (def-weil-proper-morphism), so
   lem-sfb-relative-separated-dominant-ext would imply a = pr2. Choose h,x with hx ≠ x.
2. By lem-sfb-borel-conjugation-cover, write h = gbg⁻¹ with b in a Borel subgroup B.
   For y = g⁻¹x the action identities give by ≠ y. Thus B acts nontrivially.
3. By lem-sfb-split-solvable-torsors-and-variety, choose a scheme isomorphism
   θ : A^r × (Gm)^s ≅ B. Join θ⁻¹(1) to θ⁻¹(b) by changing one coordinate at a time.
   The orbit values at the endpoints differ, so some consecutive values differ.
   Fixing the other coordinates gives a morphism u : Q → C, where Q is Ga or Gm,
   with two different rational-point images. Coordinate substitution constructs this map
   (def-sc-gm-ga, def-weil-affine-spectrum); it cannot factor through an F-point.
   If r+s = 0 the endpoints would coincide, so that case cannot occur.
4. The rings F[t] and F[t,t⁻¹] are domains, by the leading-coefficient calculation and
   clearing powers of t, and both have fraction field F(t) (def-weil-rational-function-field).
   Thus Q is integral with function field F(t), by
   lem-weil-pbc-spec-domain-stalks-function-field and def-sc-gm-ga.
5. The nonconstant map u gives an injective F-map F(C) → F(t) by
   lem-sfb-curve-nonconstant-generic-criterion. Its image E is an intermediate field.
   By lem-sfb-curve-function-field-arithmetic, F(C) has transcendence degree one over F.
   Consequently E is strictly larger than F, and F(C) is F-isomorphic to its image E.
6. Apply lem-sfb-luroth-rational-intermediate-field to E to obtain an F-isomorphism
   F(t) ≅ E ≅ F(C). No separability assertion about u is used.
7. For the specified projective line P, lem-asd-projective-line-genus-zero gives smoothness,
   properness, connectedness and dimension one. The integral clause of
   lem-sc-smooth-connected-curve-local-rings gives integrality. The two-coordinate case of
   lem-weil-pbc-projective-space-standard-charts gives a nonempty affine chart with ring F[t].
   By lem-sc-integral-function-field-affine-fraction and def-weil-rational-function-field,
   F(P) ≅ F(t). Compose with step 6 to get an F-isomorphism α : F(P) ≅ F(C).
8. By lem-sfb-proper-curve-function-field-morphisms, α and its inverse give F-morphisms
   f : C → P and g : P → C. Its identity and composition clauses identify the function-field
   maps of both composites with identities. Injectivity of the correspondence gives
   f ≫ g = id and g ≫ f = id, yielding the required F-isomorphism. -/
theorem complete_curve_connected_linear_action (F : Type u) [Field F] [IsAlgClosed F]
    (H C : Over (Spec (.of F))) [GrpObj H] [IsAffine H.left]
    [LocallyOfFiniteType H.hom] [QuasiCompact H.hom] [Smooth H.hom]
    [ConnectedSpace H.left] [Smooth C.hom] [IsProper C.hom] [IsIntegral C.left]
    (hdim : topologicalKrullDim C.left = 1) (a : H ⊗ C ⟶ C)
    (hunit : MonObj.one (X := H) ▷ C ≫ a = (λ_ C).hom)
    (hmul : MonObj.mul (X := H) ▷ C ≫ a = (α_ H H C).hom ≫ H ◁ a ≫ a)
    (hnontrivial : a ≠ CartesianMonoidalCategory.snd H C) :
    ∃ e : C.left ≅ ProjectiveSpace (ULift.{u} (Fin 2)) (Spec (.of F)),
      e.hom ≫ (ProjectiveSpace (ULift.{u} (Fin 2)) (Spec (.of F)) ↘ Spec (.of F)) = C.hom := by
  sorry

end AlgebraicGeometry
