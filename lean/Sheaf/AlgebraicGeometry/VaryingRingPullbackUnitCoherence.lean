/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q25
-/
module

public import Sheaf.AlgebraicGeometry.VaryingRingOperations
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Identity unit coherence for varying-ring inverse image

Source: Stacks Project, Tag 07A7 (remark-base-change), with the sectionwise
identity-graph normalization of `def-sp-varying-ring-operations` and the isolated
OrdinaryUnits argument (blueprint: lem-sp-varying-ring-pullback-unit-coherence).

The ordinary and derived unit equations hold on the actual semilinear system
categories, before any coefficient evaluation. Equality transport is explicit.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale.VaryingRing

/-- The specified inverse-image compositor followed by the specified identity
comparison equals the comparison induced by `(𝟙 X) ≫ f = f`, both on ordinary
systems and on their ordinary unbounded derived categories.

Source: Stacks Project, Tag 07A7 (remark-base-change), with the ordinary
sectionwise comparisons of `def-sp-varying-ring-operations`; isolated
OrdinaryUnits argument (blueprint: lem-sp-varying-ring-pullback-unit-coherence).

Proof:
1. Put `P = push f`, `S = push (𝟙 X)` and `r = modulePId X`. After source
transport the direct-image compositor `d : P ⋙ S ≅ P` equals `P` whiskered
with `r`. At index n and a test object H over Y, set V = H ×_Y X. Both maps
restrict sections from V ×_X X to V along the graph with projections the
identity of V and its structural map to X. Fibre-product uniqueness identifies
the graphs. These restrictions respect scalars and semilinear transitions;
equality on sections gives equality of system maps and natural isomorphisms.
2. Put `L = pull f`, `I = pull (𝟙 X)`, and let η and u be their adjunction
units. The composite adjunction of `def-weil-pbc-composite-adjunction` has unit
η followed by P(u). By `lem-weil-pbc-conjugate-iso-unit-equation`, the
transported compositor c and identity e obey P(c)η = d P(u)η and S(e)u = r⁻¹.
These are the unit-preserving comparisons specified by the operations node.
3. Naturality of d and d = P(r) give
P(e c)η = P(e)d P(u)η = d P(S(e))P(u)η = d P(r⁻¹)η = η.
Uniqueness in `lem-weil-pbc-conjugate-iso-unit-equation` identifies e c with
the identity of L. Undoing transport gives the first displayed equality.
4. Apply `lem-sp-exact-derived-transformation-pasting` to this ordinary
equality. Its edges L, I, the composite pullback and identities are additive
exact; the nonexact right adjoints used in the proof are not localized.
The specified gComp is D(c) followed by the exact composition comparison, and
gId is D(e) followed by the exact identity comparison. Pasting identifies
their composite with D(e c). Equality elimination shows that localization
of the ordinary equality transport is the equality transport of G. Hence
the second equality holds intrinsically on the unbounded derived system
category, without an evaluation functor or a boundedness hypothesis. -/
theorem pullback_unit_coherence
    (R : ℕ → CommRingCat.{u + 1}) (φ : ∀ n : ℕ, R (n + 1) ⟶ R n)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ((moduleGComp R φ (𝟙 X) f).hom ≫
        Functor.whiskerLeft (pull R φ f)
          (Adjunction.leftAdjointIdIso (moduleAdj R φ (𝟙 X)) (modulePId R φ X)).hom =
      (eqToIso (congrArg (pull R φ) (Category.id_comp f))).hom) ∧
    ((gComp R φ (𝟙 X) f).hom ≫
        Functor.whiskerLeft (G R φ f) (gId R φ X).hom =
      (eqToIso (congrArg (G R φ) (Category.id_comp f))).hom) := by
  sorry

end AlgebraicGeometry.ProEtale.VaryingRing
