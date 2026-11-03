/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GeneralFiniteScalarIdentification
public import WeilConjectures.AlgebraicGeometry.GeneralFiniteDiagonalReductionSource

/-! # Normalization of the live finite compact-support scalar comparison

Source: sk-thm-purity-transport proof, Step 1, exceptional-adjunction constituent;
sk-lem-sp-reduction, equation (10.15).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry.ProEtale

local instance (T : Scheme.{u}) : EssentiallySmall.{u + 1} T.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} _

/-- The actual compact-support scalar map agrees with the ordinary transported map.
This compares proper/open constructions, independently of exceptional maps, orientations,
or purity. Source: sk-thm-purity-transport proof, Step 1; sk-lem-sp-reduction (10.15).
(blueprint: lem-pur-general-side-compact-identification).

Proof: put L = f_A^! Rnu_*K, so exceptional A f K is literally nu_A^*L.
Write n_A,n_B for the site maps from comparison of ordinary compact support to
pro-etale compact support of comparison, delta for the chosen
scalar/site comparison, delta_live for its live derived presentation, and kappa
for the ordinary compact scalar map. Finite Tor amplitude of L puts its ordinary
scalar extension in D+, and the two site comparisons are invertible there.

First prove the live proper/open site square on comparison L:
S_live(n_A) followed by the live compact scalar map followed by Rf_!,B(delta_live,X)
equals delta_live,Y followed by comparison(kappa) followed by n_B.
For its proper constituent, transpose under derived pullback/direct image.
The normalized scalar/site/pullback cube identifies the two transposes: each is
the scalar/pullback comparison followed by comparison of the ordinary A-counit.
The geometric adjunction Hom bijection is injective, so the proper square follows.
For the open constituent, use the inverse open/scalar maps. Their adjuncts are
the inverse scalar/pullback comparisons followed by the scalar-extended open units.
The same cube, now at the open immersion, equates these adjuncts. Injectivity of
the open Hom bijection proves the open square. Paste the two squares; naturality
moves the proper scalar comparison past the open site comparison. The live maps
here are the specified proper mate and open conjugate, not arbitrary isomorphisms.

Substitute delta_live = sideScalarIdentification followed by delta, using scalar
normalization. Naturality of sideScalarIdentification moves S_live(n_A) to the
chosen scalar extension of n_A. Cancel the invertible n_A and delta_X factors.
The remaining compact map is conjugated by sideScalarIdentification and equals
scalar(inverse n_A) followed by delta_Y, comparison(kappa), n_B, and Rf_!,B of
inverse delta_X. Finally expand proCompactCoefficientMap at comparison L.
Naturality moves its ordinary origin unit next to the comparison counit, and the
triangle identity cancels them. This leaves exactly that five-factor composite.
The resulting equation is the displayed identity. -/
theorem sideCompactCoefficient_identification
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (φ : A →+* B) (f : X ⟶ Y) [HasCompactification f]
    [Functor.PreservesKFlatQuasiIso (sheafExtendScalars φ X)]
    [Functor.PreservesKFlatQuasiIso (sheafExtendScalars φ Y)]
    (K : Etale.FiniteSmoothPurity.proCategory A Y)
    (hG : Etale.DerivedCategory.boundedConstructibleFiniteTor A X
      ((Etale.rightDerivedUpperShriek A f).obj
        ((Etale.FiniteSmoothPurity.origin A Y).obj K))) :
    canonicalCompactReduction f φ K ≫
        (Etale.FiniteSmoothPurity.proCompact B f).map
          ((sideScalarIdentification φ X).hom.app
            ((Etale.FiniteSmoothPurity.exceptional A f).obj K)) =
      (sideScalarIdentification φ Y).hom.app
          ((Etale.FiniteSmoothPurity.proCompact A f).obj
            ((Etale.FiniteSmoothPurity.exceptional A f).obj K)) ≫
        Etale.FiniteSmoothPurity.proCompactCoefficientMap φ f
          ((Etale.FiniteSmoothPurity.exceptional A f).obj K) := by
  sorry

end AlgebraicGeometry.ProEtale
