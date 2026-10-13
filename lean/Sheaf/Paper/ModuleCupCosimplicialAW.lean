/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.Paper.ModuleCupGodementCosimplicialInput
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal

/-! # Alexander--Whitney map for cosimplicial module sheaves -/

@[expose] public section

universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry TopologicalSpace AlgebraicTopology Simplicial

namespace AlgebraicGeometry.Scheme.Modules


/-- A pointwise cosimplicial multiplication induces a tensor cochain map.
Source: Banerjee, Tensor Structure on Smooth Motives, arXiv:1004.1491,
§1.1.4, p. 16, Alexander--Whitney front/back formula and (1.1.2).
The same formula applies to the sheaf tensor product since tensoring is additive
and the simplex identities are identities of sheaf morphisms.
(blueprint: lem-sc-module-cup-cosimplicial-aw)
Proof: on the summand in bidegree (r,s), r,s nonnegative, apply to the first
factor the cofaces associated with the inclusion [r] → [r+s] of the first
r+1 vertices, and to the second factor those associated with the inclusion
[s] → [r+s] of the last s+1 vertices. Tensor these two maps and follow by
μ in degree r+s. The other summands have a zero factor. The coproduct universal
property assembles these maps into the components of the total-complex map.
Expand the alternating coface differential. Naturality of μ moves each coface
past μ; the front/back inclusion identities cancel all interior terms and
leave exactly the left differential and (-1)^r times the right differential.
This is the cochain-map identity. In bidegree (0,0) both inclusions are identities,
so the resulting map is precisely μ in degree zero, conjugated by the extension
identifications. No exactness, flasqueness, or augmentations are used. -/
theorem moduleCup_cosimplicial_aw (X : Scheme.{u}) [MonoidalPreadditive X.Modules]
    (A B C : CosimplicialObject X.Modules) (μ : moduleCup_cosimplicialTensor X A B ⟶ C) :
    ∃ t : HomologicalComplex.tensorObj (moduleCup_cosimplicialComplex X A)
        (moduleCup_cosimplicialComplex X B) ⟶ moduleCup_cosimplicialComplex X C,
      HomologicalComplex.ιTensorObj (moduleCup_cosimplicialComplex X A)
        (moduleCup_cosimplicialComplex X B) 0 0 0 (by simp) ≫ t.f 0 =
        moduleCup_cosimplicialZeroPair X A B C μ := by sorry

end AlgebraicGeometry.Scheme.Modules
