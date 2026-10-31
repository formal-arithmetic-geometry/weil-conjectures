/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StablePointedCurve

/-! # Base change of stable labelled pointed curves

Source: de Jong, Families of curves and alterations (1997), §3.6; the base-change
argument of Pikaart--de Jong (1995), §2.3.3
(blueprint: lem-sfb-stable-pointed-curve-base-change).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Stability is preserved by the actual fibre product with its labelled paired sections.
Source: de Jong (1997), §3.6; Pikaart--de Jong (1995), §2.3.3
(blueprint: lem-sfb-stable-pointed-curve-base-change).

Proof: Projective-bundle projectivity, flatness, and local finite presentation are
preserved by base change. A geometric fibre of the new family at b is canonically
isomorphic, over the same algebraically closed field, to the old fibre at b followed
by a. Thus nodality, reducedness, and pure dimension one are unchanged. The paired
sections stay disjoint: intersecting their images would give intersecting original
sections after projection. Smoothness at the markings is preserved by base change.
The fibre isomorphism identifies each irreducible component and its reduced
normalization with the corresponding old one. It identifies their structure maps,
and therefore their genera, smooth loci, and labelled marking sets. Its bijection
on normalization points preserves the encard of the union of branches over nodes
and markings. Transfer the old bounds of three points on genus-zero components and
one on genus-one components. These statements are universal over geometric points,
so the proof also applies to an empty base and to an empty marking set. -/
theorem isStablePointedCurve_baseChange {W T T' : Scheme.{u}} (f : W ⟶ T) {n : ℕ}
    (s : Fin n → (T ⟶ W)) (hs : ∀ i, s i ≫ f = 𝟙 T)
    (h : IsStablePointedCurve f s hs) (a : T' ⟶ T) :
    IsStablePointedCurve (pullback.snd f a)
      (fun i ↦ f.baseChangeSection (s i) (hs i) a)
      (fun i ↦ f.baseChangeSection_snd (s i) (hs i) a) := by sorry

end AlgebraicGeometry
