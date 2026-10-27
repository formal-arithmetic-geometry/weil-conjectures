/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q86
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.RingTheory.Smooth.Basic
import WeilConjectures.RingTheory.SmoothNormalRing

/-!
# Normality ascends along smooth morphisms

Source: Stacks Project, Descent, Tag 034F, lemma-normal-local-smooth, ascent part
(blueprint: lem-sfb-smooth-normal-ascent).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A smooth morphism with normal target has normal source, expressed on all local rings.
No Noetherianity, quasi-compactness, connectedness or surjectivity is required.

Source: Stacks Project, Descent, Tag 034F, lemma-normal-local-smooth, ascent part
(blueprint: lem-sfb-smooth-normal-ascent).

Proof:
1. Fix v in V and put w = g(v). By lem-weil-pbc-affine-opens-basis, choose an affine
   open B of W containing w and an affine open A of V containing v inside g⁻¹(B).
   Put R = O_W(B), S = O_V(A), and let φ : R → S be the induced section map.
2. By lem-weil-pbc-morphism-factors-through-open-subscheme, g restricts to A → B.
   Lem-weil-pbc-smooth-restrict-open-subschemes gives smoothness of this restriction.
   Lem-weil-pbc-affine-open-spec-points identifies the charts with Spec S and Spec R;
   lem-weil-pbc-affine-opens-induced-ring-map-spec-square identifies their map with
   Spec φ. Smoothness is invariant under these isomorphisms, so
   lem-weil-pbc-smooth-ring-map-iff-smooth-affine makes φ a smooth ring map.
3. For every prime p of R, lem-weil-pbc-affine-open-stalk-localization identifies R_p
   with the corresponding stalk of W. The hypothesis makes that stalk an integrally
   closed domain. Transporting across the ring isomorphism shows R is normal in the
   sense of def-weil-pbc-normal-ring; R itself need not be a domain.
4. Lem-weil-pbc-smooth-over-normal-ring-normal, applied to φ and step 3, shows every
   prime localization of S is an integrally closed domain, without Noetherianity.
5. The prime of S corresponding to v has localization isomorphic to O_{V,v}, by
   lem-weil-pbc-affine-open-stalk-localization. Transport domainhood and integral
   closedness across this isomorphism. Since v was arbitrary, the conclusion follows.
   For empty V it is vacuous; a map to empty W forces V empty. The construction is
   pointwise, so no finite cover, connected chart or surjectivity is needed. -/
theorem normalStalks_of_smooth {V W : Scheme.{u}} (g : V ⟶ W) [Smooth g]
    (hW : ∀ w : W,
      IsDomain (W.presheaf.stalk w) ∧ IsIntegrallyClosed (W.presheaf.stalk w)) :
    ∀ v : V, IsDomain (V.presheaf.stalk v) ∧ IsIntegrallyClosed (V.presheaf.stalk v) := by
  sorry

end AlgebraicGeometry.Scheme
