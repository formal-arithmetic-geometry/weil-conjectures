/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import WeilConjectures.AlgebraicGeometry.QuotientBaseChangeIdeal
import WeilConjectures.AlgebraicGeometry.Thickening
import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.AlgebraicGeometry.LocallyOfFiniteTypeThickening
import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Properness reflected by nilpotent base change

Source: Stacks Project, More on Morphisms, Tag 09ZW, part (7), applied to the
finite order thickening Spec(A/I) → Spec(A)
(blueprint: lem-sfb-proper-nilpotent-base-change-reflection).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Properness is equivalent to properness after base change to a nilpotent quotient.
Source: Stacks Project, Tag 09ZW, part (7), using Tag 09ZV, parts (3), (4), (6)
(blueprint: lem-sfb-proper-nilpotent-base-change-reflection).

Proof:
1. Properness passes to the base change by lem-pc-proper-base-change, clause (1).
2. Put S = Spec(A), S₀ = Spec(A/I), and Y₀ = Y ×[S] S₀. The quotient-ideal
   calculation lem-weil-pbc-quotient-base-change-closed-immersion-ideal, clauses
   (1) and (2), makes S₀ → S and Y₀ → Y closed immersions with defining ideals
   I O_S and I O_Y. Their Nth powers vanish because I^N = 0. Since N ≥ 1,
   these are finite order thickenings of order N - 1 (def-sbc-first-order-thickening).
   On affine charts the defining ideals lie in every prime, so both immersions are
   surjective. By lem-weil-pbc-surjective-closed-immersion-universal-homeomorphism
   they and all their base changes are homeomorphisms. The pullback square commutes.
3. Suppose the base change f₀ is proper. It is locally of finite type. Apply
   lem-weil-pbc-thickening-lft-cartesian to the cartesian square to obtain local
   finite type of f. This step uses nilpotence, not just the homeomorphisms.
4. Regard the square as one of representable algebraic spaces via
   def-trf-scheme-algebraic-space. Fibre products have the same universal property
   (def-pc-fibre-product), and scheme closed immersions remain closed immersions of
   spaces by lem-weil-pbc-closed-immersion-base-change. Conversely test with the target
   scheme. Identity atlases recover the scheme topology. Apply the separatedness
   clause of lem-sfb-space-thickening-topological-properties with its four spaces
   (X, X', Y, Y') = (Y₀, Y, S₀, S) and its maps (f, f') = (f₀, f).
   Its commutativity is the pullback identity. Testing the resulting diagonal with
   Y ×[S] Y gives separatedness of the scheme morphism f.
5. For an affine open U of S, its inverse image in S₀ is quasi-compact. A finite
   affine cover of that inverse image, and quasi-compactness of f₀, show that its
   inverse image in Y₀ is quasi-compact (def-weil-finite-type-morphism). Transport
   across the homeomorphism Y₀ → Y gives quasi-compactness of f. For any T → S,
   put T₀ = T ×[S] S₀. Fibre-product pasting identifies Y₀ ×[S₀] T₀ with
   (Y ×[S] T) ×[T] T₀. Both horizontal maps to T and Y ×[S] T are homeomorphisms.
   For a closed subset C of Y ×[S] T, its inverse image C₀ has closed image under
   the base change p₀ of f₀. If h : T₀ → T, commutativity and surjectivity of
   the upper homeomorphism give p(C) = h(p₀(C₀)). This image is closed, proving
   universal closedness (def-weil-proper-morphism).
6. Local finite type and quasi-compactness give finite type. Together with
   separatedness and universal closedness they give properness of f
   (def-weil-finite-type-morphism, def-weil-proper-morphism). No flatness,
   Noetherianity, or finite-type hypothesis on f was used. -/
theorem isProper_iff_of_nilpotent_quotient
    {A : Type u} [CommRing A] (I : Ideal A) (N : ℕ) (hN : 1 ≤ N)
    (hI : I ^ N = ⊥) {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of A)) :
    IsProper f ↔
      IsProper (pullback.snd f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) := by
  sorry

end AlgebraicGeometry
