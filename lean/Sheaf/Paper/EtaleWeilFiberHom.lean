/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P6
-/
module

public import Sheaf.Paper.EtaleWeilFundamentalRepresentation

/-! # The Hom dictionary for normalized etale Weil fibres

Source: Weil II (1.1.12), the intertwiner argument in step 5 of
prop-wf-weil-sheaf-representation-equivalence.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
open FiniteEtale

variable (l : ℕ) [Fact l.Prime] (Q : Type (u + 1)) [Field Q]
  [Algebra ℚ_[l] Q] [IsAlgClosure ℚ_[l] Q]
  {Y : Scheme.{u}} [IsNoetherian Y] [Y.IsSeparated]
  [∀ x : Y, Invertible (l : Y.residueField x)]
  (h : Y ≅ Y) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
  (t : Spec (.of Ω) ⟶ Y) {G : Type v} [Group G]
  (d : Monodromy.DegreeDatum G) (D : EtaleWeilDegreeData h t G d)

/-- The actual etale stalk maps identify Weil morphisms with intertwiners.
Source: Weil II (1.1.12); step 5 of prop-wf-weil-sheaf-representation-equivalence.
(blueprint: new-p6-etale-weil-fiber-hom)

Proof: the finite evaluation dictionary of cor-galois-lisse-representations, followed
by inverse limits, rationalization and common coefficient extension, identifies
underlying lisse morphisms with geometric intertwiners. Its finite evaluation rule
agrees with etaleFinitePathIso on every finite-cover germ; the limit projections
and pure tensors then identify its geometric action with etaleGeometricRep.
For an underlying morphism a, naturality of the normalized path and of the
pullback-fibre comparison identifies the descent square with the equation
A T_F = T_H A. Conversely this equation and faithfulness of the underlying
dictionary imply the descent square. The degree datum writes every group element
as a geometric element times an integral power of its degree-one lift, so a map
is a Weil intertwiner exactly when it is a geometric intertwiner and satisfies
this single equation. This proves both directions and uniqueness. The resulting
bijection has exactly the displayed underlying linear map, including zero objects
and zero-rank fibres; no invertibility is required of a morphism. -/
theorem etaleWeilFiberHom [ConnectedSpace Y]
    (F H : EtaleLisseWeilSheaf l Q h) :
    ∃ e : (F ⟶ H) ≃
        (etaleFundamentalRep l Q h t d D F).IntertwiningMap
          (etaleFundamentalRep l Q h t d D H),
      ∀ a : F ⟶ H, (e a).toLinearMap =
        (etaleAlgebraicFiberMap l Q t
          ((Endofunctor.IsoAlgebra.forget
            (lisseAlgebraicAutomorphismPullback h l Q)).map a)).hom := by sorry

end AlgebraicGeometry.Scheme
