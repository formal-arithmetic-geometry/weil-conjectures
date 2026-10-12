/- Copyright (c) 2026 The SHEAF contributors. -/
module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Fullness of finite étale restriction to the generic point

Source: Stacks Project, Tag 0BQM, full faithfulness in the proof.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Any morphism between the generic restrictions of finite étale covers of a
normal integral scheme extends uniquely over that scheme.

Source: Stacks Project, Tag 0BQM, full faithfulness of generic-point restriction.
(blueprint: lem-sbc-normal-integral-generic-hom-full)

Proof: Cover B by affine opens Spec A. A is an integrally closed domain and
its fraction field is B's function field. Finite étale A-algebras are normal
and equal the integral closure of A in their generic algebras, componentwise.
The given generic algebra homomorphism carries elements integral over A to
elements integral over A; it therefore restricts to an A-algebra homomorphism
between these integral closures, in the contravariant direction. This gives
a morphism on each affine open. The finite étale algebras are torsion free
over A, so these extensions agree on overlaps whenever their generic
restrictions agree. They glue to f over B. The given cartesian squares identify
its generic restriction with fη and yield the compatibility equation.
Uniqueness follows from the same torsion-freeness on each affine chart.
Empty covers and disconnected finite étale algebras are included; the
integral-closure argument applies to their finite products, including zero. -/
theorem finiteEtale_normalIntegral_generic_hom_full {B : Scheme.{u}} [IsIntegral B]
    (hB : ∀ x : B, IsIntegrallyClosed (B.presheaf.stalk x))
    {X Y Xη Yη : Scheme.{u}} (πX : X ⟶ B) (πY : Y ⟶ B)
    [IsFinite πX] [Etale πX] [IsFinite πY] [Etale πY]
    (πXη : Xη ⟶ Spec B.functionField) (πYη : Yη ⟶ Spec B.functionField)
    (ψX : Xη ⟶ X) (ψY : Yη ⟶ Y)
    (hX : IsPullback ψX πXη πX (B.fromSpecStalk (genericPoint B)))
    (hY : IsPullback ψY πYη πY (B.fromSpecStalk (genericPoint B)))
    (fη : Xη ⟶ Yη) (hfη : fη ≫ πYη = πXη) :
    ∃! f : X ⟶ Y, f ≫ πY = πX ∧ ψX ≫ f = fη ≫ ψY := by sorry

end AlgebraicGeometry.Scheme
