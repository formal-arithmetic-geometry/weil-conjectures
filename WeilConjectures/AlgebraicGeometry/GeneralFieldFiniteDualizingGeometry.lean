/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GeneralFieldFiniteDualizingComponents

/-! # Local geometry of finite dualizing coefficient change
(blueprint: lem-sf-general-field-finite-dualizing-geometry). -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry.Etale

/-- The local affine-space calculation identifies the specified ordinary dualizing
counit mate as an isomorphism; its ordinary and pro-etale realizations are natural
under scheme isomorphisms and independent of the compactification.

Source: latest blueprint, `lem-coef-finite-dualizing.proof.md`, paragraphs 2--3,
and `lem-coef-finite-free-extension.proof.md`, locality paragraph.
(blueprint: lem-sf-general-field-finite-dualizing-geometry).

Proof: use etale ambient adjoint locality to restrict to affine open charts. Embed
such a chart as a closed subscheme of affine space. The affine-space adjunction
identifies its dualizing object with the closed exceptional inverse image of
A(r)[2r]. The finite closed-shriek coefficient comparison, the coefficient
comparison for the rank-one Tate object, and compatibility with shifts identify
the scalar extension with the corresponding B-object. Transpose this local map
under the composite closed-immersion and affine-space adjunctions: its adjunct
is the scalar extension of the structure-morphism counit. Injectivity of the
exceptional Hom equivalence identifies it with generalFieldFiniteDualizingMap.
Hence the local isomorphisms agree on overlaps and give its invertibility.
For a scheme isomorphism, pull back that same counit equation, insert the
canonical scalar/pullback comparison, and transpose; this gives the displayed
ordinary naturality equation. Paste the scalar/site/pullback cube with it to
obtain the pro-etale equation. Compare compactifications through a common proper
refinement; compact scalar coherence identifies the two compact-support adjuncts.
The counit-normalized right-adjoint uniqueness isomorphisms therefore carry both
mates to the same canonical map, proving both independence equalities. -/
theorem generalFieldFiniteDualizingGeometry
    (k : Type u) [Field k] (p l : ℕ) (hp : p.Prime) (hkp : ringChar k = p)
    (hk : Finite k ∨ IsAlgClosed k) (hl : l.Prime) (hlp : l ≠ p)
    {X : Scheme.{u}} {a : X ⟶ Spec (CommRingCat.of k)}
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a] [HasCompactification a]
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (hA : ∃ n : ℕ, ∀ x : A, (l ^ n : A) * x = 0)
    (hB : ∃ n : ℕ, ∀ x : B, (l ^ n : B) * x = 0) (φ : A →+* B) :
    GeneralFieldFiniteDualizingGeometry l φ a := by
  sorry

end AlgebraicGeometry.Etale
