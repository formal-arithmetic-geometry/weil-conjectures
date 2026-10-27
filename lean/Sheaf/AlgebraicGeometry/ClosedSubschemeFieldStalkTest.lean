/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q10
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.FieldTheory.Separable
public import Mathlib.Topology.JacobsonSpace
public import WeilConjectures.ZetaSeries
public import Sheaf.AlgebraicGeometry.UnramifiedMorphism
import WeilConjectures.AlgebraicGeometry.SpecLocalRingCanonicalMorphism
import Sheaf.AlgebraicGeometry.UnramifiedOverFieldLocalCriterion

/-! # A closed-point field-stalk test for a closed subscheme

Source: Stacks Project, Varieties, Tag 0478; Schemes, Tag 01J7;
Morphisms, Tag 02G7; Curves, Tag 0C4E, final paragraph
(blueprint: lem-trf-closed-subscheme-field-stalk-test).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A closed subscheme of a scheme locally of finite type over a field is unramified
if its stalks at points closed in the ambient scheme are their finite separable residue
fields. Every point of the subscheme then has these properties and is closed in the
ambient scheme. The field extension is always the canonical one induced by `i ≫ f`.

Source: Stacks Project, Tags 0478, 01J7 and 02G7, elaborating the final paragraph of
Curves, Tag 0C4E (blueprint: lem-trf-closed-subscheme-field-stalk-test).

Proof:
1. Cover X by affine opens Spec B with B finitely generated over k
   (def-weil-finite-type-morphism). Their inverse images in Y are Spec (B/I)
   (def-weil-closed-immersion). Images of generators of B generate B/I, so the
   composite Y → Spec k is locally of finite type; no finite subcover is needed.
2. For y in Y, the closure Z of {i(y)} has a dense set of ambient closed points by
   lem-sc-lft-over-field-jacobson-space. Since Z is nonempty, choose one such point x.
   The closed image i(Y) contains Z, so x = i(z) for a unique z in Y.
   The homeomorphism onto the closed image identifies the relevant closures, so z
   is a specialization of y. The hypothesis applies at z.
3. The residue isomorphism makes O_{Y,z} a field. By clause (1) of
   lem-weil-pbc-spec-local-ring-canonical-morphism, the image of Spec O_{Y,z} in Y
   is the set of generalizations of z and contains z. The spectrum of a field has
   one point (def-weil-affine-spectrum), so this image is {z}. Hence y = z.
   Thus every y maps to an ambient closed point and satisfies the residue-field
   isomorphism and finite-separability conclusions (def-weil-residue-field and
   def-weil-pbc-separable-algebraic-extension).
4. Since i is injective and continuous, {y} is the inverse image of the closed
   singleton {i(y)}, and is closed (def-weil-closed-points). Apply the reverse
   implication of lem-trf-unramified-over-field-local-criterion, using step 1 and
   the pointwise conclusions, to obtain unramifiedness. If Y is empty, the pointwise
   statements are vacuous and the same criterion applies. -/
theorem closed_subscheme_unramified_of_closed_point_field_stalks
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    (i : Y ⟶ X) [IsClosedImmersion i]
    (h : ∀ y : Y, i y ∈ closedPoints X →
      Function.Bijective (Y.residue y) ∧
      ((i ≫ f).residueFieldAlgebraMap y).Finite ∧
      @Algebra.IsSeparable k (Y.residueField y) _ _
        ((i ≫ f).residueFieldAlgebraMap y).toAlgebra) :
    LocallyOfFiniteType (i ≫ f) ∧ IsUnramified (i ≫ f) ∧
      ∀ y : Y, i y ∈ closedPoints X ∧ Function.Bijective (Y.residue y) ∧
        ((i ≫ f).residueFieldAlgebraMap y).Finite ∧
        @Algebra.IsSeparable k (Y.residueField y) _ _
          ((i ≫ f).residueFieldAlgebraMap y).toAlgebra := by
  sorry

end AlgebraicGeometry
