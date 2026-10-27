/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H5
-/
module

public import Sheaf.Paper.ProductOpenTensorProjectionData

/-! # The two supported product-open tensor maps

Source: the second step of lem-pur-product-open-tensor-projection.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory AlgebraicGeometry
open SheafOfModules.OpenTensorNormalization WeilConjectures.FiniteOpenProduct

namespace WeilConjectures.ProductOpenTensorProjection

/-- The open counit comparison chi intertwines the two-stage tensor map with w.
Only open geometry enters; no proper morphism or exchange map is used.

Source: blueprint latest, sec-six-functors/sk-thm-sf-kunneth-relative/
lem-sf-kunneth-coherence.proof.md, symmetry paragraph; parent proof Step 2.
(blueprint: lem-pur-product-open-support-normalization).

Proof: open tensor normalization for j_q and i makes d and the first factor of
w invertible. Identify P_iP_t k_!N with P_vN using the specified square and the
open unit. The canonical open compositor then identifies the source of w with
u_!D. Restriction of these factors along u gives the tensor pullback comparison,
the units at P_pM and N, and the open composition unit; these are precisely
restrictW inverse followed by the unit at D. This proves the restriction equation.
The two-stage comparison e is normalized by the two open units. Restriction of
chi is beta inverse by the open adjunction triangle; restricting further to j_q
uses beta's unit normalization. Hence w and (chi tensor 1) followed by e have
the same restriction under restrictW. Their source and target are in the fully
faithful image of u_!, so they agree. No inverse of chi is used. For identity
opens these formulas are the tensor unit coherences; for empty opens both
supported source and target are zero. -/
theorem productOpenSupportNormalization
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {Xb Zb B X Z : Scheme.{u}}
    (a : Xb ⟶ B) (b : Zb ⟶ B) (j : X ⟶ Xb) (k : Z ⟶ Zb)
    [IsOpenImmersion j] [IsOpenImmersion k]
    (M : FiniteD A X) (N : FiniteD A Z) :
    w A a b j k M N =
      tensorMap A (product a b) (chi A a b j k M)
        (𝟙 ((pull A (second a b)).obj (J A k N))) ≫ e A a b j k M N ∧
    Nonempty (tensor A (product a b) (m A a b j k M)
      ((pull A (second a b)).obj (J A k N)) ≅
        (finiteShriek A (productOpen a b j k)).obj (D A a b j k M N)) ∧
    (restrictW A a b j k M N).inv ≫
        (pull A (productOpen a b j k)).map (w A a b j k M N) =
      (openUnit A (productOpen a b j k) (D A a b j k M N)).hom := by sorry

end WeilConjectures.ProductOpenTensorProjection
