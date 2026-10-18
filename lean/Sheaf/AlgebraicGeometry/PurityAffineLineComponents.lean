/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q10
-/
module

public import Sheaf.Paper.PurityFiniteSetting
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Topology.Connected.Basic

import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Field.Defs
import Mathlib.Topology.Connected.Clopen

/-!
# Connected components of the affine and punctured affine lines

Source: blueprint sec-smooth-purity/sk-prop-a1-inv/lem-pur-a1-components.md;
Stacks Project, Tags 01UA, 01M0, 01K1 and 0377 (blueprint: lem-pur-a1-components).

The affine line and its open complement of the zero section have connected components
pulled back from the base; the unit section meets every such component.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry

/-- The connected components of the relative affine line and of the open complement of its
zero section are pulled back from the base, and every component meets the unit section.
Source: blueprint sec-smooth-purity/sk-prop-a1-inv/lem-pur-a1-components.md;
Stacks Project, Tags 01UA, 01M0, 01K1 and 0377 (blueprint: lem-pur-a1-components).

Proof, following the ten steps of the node:
1. Write X for the affine line, G for the open complement, p for the projection and q for
   its restriction. By sbc-lem-affine-space-smooth, p is smooth of relative dimension one.
   The forward implication of sbc-lem-smooth-criterion makes it flat and locally of finite
   presentation, so lem-weil-pbc-flat-lfp-open (Stacks 01UA) makes p open.
2. The zero section is a closed immersion, so G is open in X. An open subset of G is open
   in X, and its q-image is its p-image; hence q is open. The unit section lies in G and
   projects to the identity on B, so both p and q are surjective. Scheme maps are continuous.
3. For y in B, let K be its residue field. By def-pc-scheme-fibre, the topological fibre
   of p is the space of its scheme-theoretic fibre. The fibre-product construction of
   def-sbc-affine-space and def-pc-fibre-product identifies that fibre with Spec K[t]:
   compatible maps to B, Spec Z[t] and Spec K reduce to the pair of maps to Spec Z[t]
   and Spec K, since the map to B is forced. The affine-base formula gives Spec K[t].
4. K[t] is a domain: the leading coefficient of a product of two nonzero polynomials is
   the product of their nonzero leading coefficients (def-weil-polynomial-ring,
   def-weil-field). Its zero ideal is prime and is dense in its spectrum
   (def-weil-affine-spectrum), since a closed V(I) containing it has I contained in zero.
   Thus every nonempty open contains this prime, and the fibre is nonempty and connected
   (def-weil-connected-scheme).
5. The q-fibre is the open subspace G intersected with the p-fibre and contains the unit
   point. Every nonempty relative open is nonempty open in the p-fibre and contains its
   dense zero prime. A separation is impossible, so each q-fibre is connected too.
6. For either f = p or f = q and any base component D, restrict to f_D : f⁻¹(D) → D.
   A relative open is f⁻¹(D) intersected with an ambient open O, and its image is D
   intersected with f(O); hence f_D is an open continuous surjection. If the preimage
   of T is closed, the image of its open complement is D minus T, making T closed in D.
   Conversely continuity preserves closed preimages. This proves the quotient topology,
   with the connected fibres already established.
7. Apply lem-weil-pbc-connected-fibres-quotient-preimage-connected (Stacks 0377) to f_D
   and the whole space D, which is closed in itself, nonempty and connected. It follows
   that f⁻¹(D) is connected; no openness or closedness of D in B is needed here.
8. This inverse image E is maximal connected. Any connected C containing E has connected
   image f(C), by pulling a separation back along f. Surjectivity gives D contained in
   f(C); maximality of D gives f(C) = D and hence C contained in E.
9. Every base point y lies in its component D_y: the union of all connected subsets
   containing y is connected, since each lies on the side containing y in a separation,
   and is maximal by construction. If C is a source component containing x, the inverse
   image of D_(f(x)) is connected and contains x. Its union with C is connected because
   they meet at x, so maximality on both sides gives equality. This proves both component
   formulas, including that all base components occur.
10. Choose y in any base component D. The unit point lies in G and projects to y, so
    it belongs to the corresponding components of X and G. Thus each X-component meets
    G and the unit-section image, and each G-component meets the image of its unit section. -/
theorem affineLine_connectedComponents
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {B : Scheme.{u}}
    (b : B ⟶ Spec (.of P.field.k)) [Nonempty B]
    [IsSeparated b] [LocallyOfFiniteType b] [QuasiCompact b]
    {G : Scheme.{u}}
    (j : G ⟶ AffineSpace (ULift.{u} (Fin 1)) B) [IsOpenImmersion j]
    (hj : Set.range j.base =
      (Set.range (AffineSpace.zeroSection (ULift.{u} (Fin 1)) B).base)ᶜ)
    (i₁ : B ⟶ G)
    (hi₁ : i₁ ≫ j = AffineSpace.oneSection (ULift.{u} (Fin 1)) B) :
    (∀ x : AffineSpace (ULift.{u} (Fin 1)) B,
      connectedComponent x =
        (AffineSpace (ULift.{u} (Fin 1)) B ↘ B).base ⁻¹'
          connectedComponent ((AffineSpace (ULift.{u} (Fin 1)) B ↘ B).base x)) ∧
    (∀ x : G,
      connectedComponent x =
        (j ≫ (AffineSpace (ULift.{u} (Fin 1)) B ↘ B)).base ⁻¹'
          connectedComponent ((j ≫ (AffineSpace (ULift.{u} (Fin 1)) B ↘ B)).base x)) ∧
    (∀ x : AffineSpace (ULift.{u} (Fin 1)) B,
      (connectedComponent x ∩ Set.range j.base).Nonempty) ∧
    (∀ x : AffineSpace (ULift.{u} (Fin 1)) B,
      (connectedComponent x ∩
        Set.range (AffineSpace.oneSection (ULift.{u} (Fin 1)) B).base).Nonempty) ∧
    (∀ x : G,
      (connectedComponent x ∩ Set.range i₁.base).Nonempty) := by
  sorry

end AlgebraicGeometry
