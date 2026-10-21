/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T3
-/
module

public import Sheaf.AlgebraicGeometry.GeoCartierCanonicalClass

/-! # Naturality of the normalized Cartier reduction

Source: blueprint main-20261015, sk-lem-geo-cartier.proof.md.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale

/-- Pullback of the integral pole extension commutes with its normalized reduction
when the inverse-image divisor is Cartier.
Source: blueprint sk-lem-geo-cartier.proof.md, paragraph 6 and opening comparison
paragraph (blueprint: lem-sfb-cartier-reduction-pullback).
Proof: choose regular equations t for D. Their pullbacks are regular because the
inverse-image ideal is again Cartier. Sending u times t inverse to the pullback unit
and pulled-back inverse equation gives a map of pole extensions, independent of the
chosen equations. The finite-stalk formula makes closed exchange an isomorphism:
it is the identity on the constant stalk on D and the unique map between zero stalks
off D. Exact inverse image and naturality of the short exact triangle commute with
the extension boundary and its Kummer reduction. Flatness of the roots line and
tensor compatibility commute this equality with extension to A. Use the one fixed
roots-normalized finite-line transport for all schemes. Finally the comparison square
respects counits. Adjunction injectivity identifies its exchange with geoCartierExchange,
whose adjunct is inverse-image commutation followed by the pulled-back counit.
The resulting equality is an equality of derived morphisms by functoriality; stalks
were used only to identify the ordinary source exchange. Empty support and identity
base change give the zero and identity squares respectively. -/
theorem geoCartierCanonicalClass_pullback (A : Type (u + 1)) [CommRing A] [Finite A]
    (n : ℕ) (hn : 0 < n) (hA : (n : A) = 0) :
    ∃ t : Etale.OrdinaryFiniteTwistTransport A n hA,
      ∀ {D D' Z Z' : Scheme.{u}} (i : D ⟶ Z) (i' : D' ⟶ Z')
        [IsClosedImmersion i] [IsClosedImmersion i'] (g : Z' ⟶ Z) (gD : D' ⟶ D)
        (sq : IsPullback gD i' i g) (hI : i.ker.IsInvertible) (hI' : i'.ker.IsInvertible)
        (hZ : IsUnit (n : Γ(Z, ⊤))) (hZ' : IsUnit (n : Γ(Z', ⊤))),
        IsIso (geoCartierExchange A i i' g gD sq.toCommSq) ∧
        (Ext.mk₀ (geoCartierExchange A i i' g gD sq.toCommSq)).comp
            (geoCartierCanonicalClass A n hn hA i' hI' hZ') (zero_add 2) =
          ((geoCartierCanonicalClass A n hn hA i hI hZ).mapExactFunctor
            (upperStar (ModuleCat.{u + 1} A) g)).comp
            (Ext.mk₀ (geoCartierLinePullback A n hA t g hZ).hom) (add_zero 2) := by
  sorry

end AlgebraicGeometry.ProEtale
