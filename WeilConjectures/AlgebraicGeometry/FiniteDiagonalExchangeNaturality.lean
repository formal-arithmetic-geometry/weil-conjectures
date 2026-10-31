/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteTraceDiagonalCanonicalMaps

/-! Canonical diagonal-unit naturality, isolated from the trace-diagonal datum. -/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.ProEtale.FiniteTraceDiagonal

variable (A : Type (u + 1)) [CommRing A] [Finite A]
variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Naturality of the final canonical diagonal-unit isomorphism.
Source: blueprint def-pur-td-datum, final unit isomorphism and canonical-map paragraph.
(blueprint: lem-pur-finite-diagonal-exchange-naturality).

Proof: set V = Lp1*, U = Lf*, S = Rf!, T = Rp2!, and B = Lp2*(L).
The exchange component is inverse projection
T(V(K) tensor B) --> T(V(K)) tensor L followed by inverse self-square exchange
on the first tensor factor, giving U(S(K)) tensor L. Naturality of the projection
transformation in its first input gives its commuting square for V(a); invert its
finite-Tor isomorphism components by composing with their inverses on both sides.
The compact-support self-square base-change transformation is natural in K;
invert its finite-Tor components in exactly the same way. Apply the functor
(- tensor L) to this second square. Composing these two squares, with functoriality
and associativity, gives the displayed equation. The five finite-Tor hypotheses
certify the indicated projection and base-change inverses; no extra hypothesis on
a, K, or L is required. This also covers zero maps, the identity morphism, and
empty schemes. The remaining formal work is categorical composition of these
squares with the native derived functors kept folded. -/
theorem exchangeCore_naturality (c : Compactification f)
    (K K' L : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) X K)
    (hK' : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) X K')
    (hL : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) X L)
    (hP : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) (pullback f f)
      ((pullFor A (pullback.fst f f)).obj K))
    (hP' : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) (pullback f f)
      ((pullFor A (pullback.fst f f)).obj K')) (a : K ⟶ K') :
    (compactSupportFor A (c.ofIsPullback (IsPullback.of_hasPullback f f))).map
        (((tensorFor A (pullback f f)).map ((pullFor A (pullback.fst f f)).map a)).app
          ((pullFor A (pullback.snd f f)).obj L)) ≫
      (exchangeCore A f c K' L hK' hL hP').hom =
        (exchangeCore A f c K L hK hL hP).hom ≫
          ((tensorFor A X).map
            ((pullFor A f).map ((compactSupportFor A c).map a))).app L := by sorry

end AlgebraicGeometry.ProEtale.FiniteTraceDiagonal
