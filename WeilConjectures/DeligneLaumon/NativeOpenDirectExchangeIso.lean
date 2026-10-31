/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Localizing
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.WeaklyEtale

/-! # Native derived direct-image exchange along an open immersion

Source: Bhatt--Scholze, Lemma 6.2.3, and Stacks Tag 0F4X, as implemented in
`ProEtale.CondensedRing.isIso_baseChangeMap_of_weaklyEtale`.
(blueprint: lem-zl-native-open-direct-exchange-isomorphism).
-/

@[expose] public section

set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The native total-derived direct-image exchange is invertible along every target open,
for arbitrary commutative condensed coefficients and all ordinary derived inputs.

Source: Bhatt--Scholze, Lemma 6.2.3; Stacks Tag 0F4X; the source library's ambient
weakly etale base-change theorem.
(blueprint: lem-zl-native-open-direct-exchange-isomorphism).

Proof: the Cartesian square makes its source horizontal arrow a base change of the
open immersion, hence an open immersion. Both horizontal arrows are therefore weakly
etale. Apply the existing native ambient weakly etale base-change theorem. Its map is
exactly the adjunction mate of the native total-derived pullback-square comparison,
so no identification with a separately chosen restriction isomorphism is required.
This includes the empty open and the identity open and imposes no finiteness condition.
-/
theorem nativeOpenDirectExchangeIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {j : Y' ⟶ Y}
    {f' : X' ⟶ Y'} {i : X' ⟶ X} [IsOpenImmersion j]
    (sq : IsPullback i f' f j) : IsIso (baseChangeMap Λ sq.toCommSq) := by
  have : IsOpenImmersion i :=
    MorphismProperty.of_isPullback sq.flip (inferInstance : IsOpenImmersion j)
  exact isIso_baseChangeMap_of_weaklyEtale Λ sq

end AlgebraicGeometry.ProEtale.CondensedRing
