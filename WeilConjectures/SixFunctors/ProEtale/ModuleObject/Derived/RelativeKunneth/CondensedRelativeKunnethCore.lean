/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.RelativeKunneth.CondensedRelativeKunnethDefs

/-! # Domains and construction of the normalized relative product

Source: the domains and six-arrow word in the relative product theorem.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing.RelativeKunneth

/-- Cartesian compact-support base change for the native proper/open exchange,
restricted to the localizing domain and followed by the normalized model comparison.
Source: det-prop-sf-cbc, condensed compact-support base change; relative Künneth step 2
(blueprint: sk-thm-sf-kunneth-relative).

Proof: use proper base change on the proper square of the pulled-back compactification
and the inverse open exchange on its open square. Their composite is exactly the native
squareExchange by its defining equation. The finite coefficient case follows by étale
origin and the pro-étale comparison; the ordinary integral and field cases use condensed
compact-support base change. Extend from constructible finite-Tor generators to the
localizing closure by exactness and coproduct preservation. Whiskering preserves the
resulting isomorphism, and the final sfCompComparison is an isomorphism. This includes
identity squares and every choice of target compactification. -/
theorem canonicalExchange_isIso {k : Type u} [Field k] (Λ : ScalarSixRing.{u})
    (H : CanonicalCompositionData Λ.X k)
    {X Y X' Y' : SepFinType k} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {a : X' ⟶ X} {v : Y' ⟶ Y}
    (sq : IsPullback a.hom.left f'.hom.left f.hom.left v.hom.left)
    (c : Compactification f.hom.left) (d : Compactification f'.hom.left) :
    IsIso (canonicalExchangeOnLocalizing Λ H (f := f) (f' := f')
      (a := a) (v := v) sq c d) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing.RelativeKunneth
