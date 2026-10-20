/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMaps
public import Mathlib.AlgebraicGeometry.OpenImmersion
import Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChangeSquare
import Sheaf.AlgebraicGeometry.ProperUnboundedBaseChange

/-! # Restriction of the canonical exceptional base-change mate

Source: blueprint `prop-asd-smooth-base-change`, coherences (i) and (iii).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

/-- Restriction to an open of the original base preserves the canonical base-change square.
Source: blueprint `prop-asd-smooth-base-change`, proof, coherences (i) and (iii).

Proof: write D(T) for the ordinary unbounded etale derived category, L for exact
inverse image, F for compact support, and R for its right adjoint. Restrict the chosen
compactification of f along j, and base change that diagram along c. Proper exchange
and degreewise open-extension exchange give the two compact-support maps. Compare
compactifications by the graph-factorization construction of unbounded compact-support
composition; this requires no quasi-compactness of f or p. Normalize those comparisons
by the identity on the source open. Their cocycle law
and horizontal proper-exchange pasting identify the two maps on the cube.

The open-composition identification j! Fp = Ff a! is obtained on the same diagram:
proper/open interchange moves j! through the proper factor, and composition combines
the two open extensions. Taking right adjoints gives an isomorphism
lambda_f : La* Rf = Rp Lj*. Construct lambda_f' in the same way. These constructions
use exact extension by zero for j and a and do not require those opens to be
quasi-compact. Unlike the named exceptional base-change maps, they do not use a
chosen compact-support comparison for j or a.

Transpose the cube equation under the exceptional adjunctions, using the counit
equation defining the mate. With sigma : La'* Lg'* = Lb* La* from w and
tau : Lc* Lj* = Lj'* Lg* from sqj, the resulting equation at K is

  La'* beta(f,g)_K ; lambda_f'(Lg* K)
    = sigma(Rf K) ; Lb*(lambda_f(K)) ; beta(p,c)_(Lj* K) ; Rp'(tau(K)).

Here semicolons mean composition from left to right. This equality follows from
injectivity of the adjunction Hom bijection: after applying Fp' and composing with
its counit, both sides are inverse compact-support exchange followed by the pullback
of the same original counit. Naturality moves the open-composition comparisons past
that counit; their intermediate factors cancel by the cocycle identity above.
All factors other than beta(p,c) are isomorphisms. The hypothesis makes that last
factor invertible as well, and cancellation with lambda_f' proves the claim.
Only f' and p' must be quasi-compact, to type the two named base-change maps. Empty
schemes, the zero coefficient ring, identity restrictions, and arbitrary unbounded K
are covered by the same identities.
(blueprint: lem-asd-exceptional-base-change-open-restriction) -/
theorem isIso_leftDerivedUpperStar_map_baseChange_of_open_restriction
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y X' Y' U V U' V' : Scheme.{u}}
    {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}
    [HasCompactification f] [HasCompactification f'] [QuasiCompact f']
    (sq : IsPullback g' f' f g)
    {j : U ⟶ Y} [IsOpenImmersion j] {a : V ⟶ X} {p : V ⟶ U}
    (sqU : IsPullback a p f j) [HasCompactification p]
    {c : U' ⟶ U} {j' : U' ⟶ Y'} (sqj : IsPullback c j' j g)
    {b : V' ⟶ V} {p' : V' ⟶ U'} (sq' : IsPullback b p' p c)
    [HasCompactification p'] [QuasiCompact p']
    {a' : V' ⟶ X'} (sqV : IsPullback a' p' f' j')
    (w : b ≫ a = a' ≫ g')
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (h : IsIso ((rightDerivedUpperShriekBaseChangeMap Λ sq').app
      ((L((j)^*[ModuleCat.{u + 1} Λ])).obj K))) :
    IsIso ((L((a')^*[ModuleCat.{u + 1} Λ])).map
      ((rightDerivedUpperShriekBaseChangeMap Λ sq).app K)) := by sorry

end AlgebraicGeometry.Etale
