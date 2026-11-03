/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteReductionCoherenceMaps

/-! # The specified smooth pullback exchange

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-sp-grp-trace/sec-base-change-and-composition/
sk-prop-sp-purity-bc/def-pur-smooth-pullback-exchange.md, typed three-factor composite
(blueprint: def-pur-smooth-pullback-exchange).

The inverse is totalized by zero outside its isomorphism locus. The finite-reduction
assertions restrict to normalized smooth purity and ctf, where it is the inverse.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.Etale.FiniteSmoothPurity

/-- The specified smooth pullback exchange: inverse pulled-back purity, the canonical
source comparison, then primed purity. Source: def-pur-smooth-pullback-exchange
(blueprint: def-pur-smooth-pullback-exchange). -/
def proSmoothExchange (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (f' : X' ⟶ Y')
    [HasCompactification f] [HasCompactification f']
    (a : X' ⟶ X) (b : Y' ⟶ Y) (sq : IsPullback a f' f b)
    (hX : IsUnit (N : Γ(X, ⊤))) (d : ℕ)
    (alpha : dualizingComplex A f ≅ line A N hA X d)
    (alpha' : dualizingComplex A f' ≅ line A N hA X' d) (K : proCategory A Y) :
    (proPullback A a).obj ((exceptional A f).obj K) ⟶
      (exceptional A f').obj ((proPullback A b).obj K) :=
  open Classical in
  let invGamma := if h : IsIso (proGamma A f _ alpha K) then
    @inv _ _ _ _ (proGamma A f _ alpha K) h else 0
  (proPullback A a).map invGamma ≫
    (proBaseChangeSource A N hN hA f f' a b sq hX d K).hom ≫
    proGamma A f' _ alpha' ((proPullback A b).obj K)

end AlgebraicGeometry.Etale.FiniteSmoothPurity
