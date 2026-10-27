/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q65
-/
module

public import Sheaf.SixFunctors.SelectedSchemeGaloisComparison
public import Sheaf.SecSmoothPurity.DirectImageScalarExchange
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Sheaf.SixFunctors.ScalarSixPullback
public import Sheaf.Paper.FiniteDiscreteCondensedRing
public import Sheaf.Paper.FiniteDiscreteSchemeRing
import Sheaf.Paper.IntegralFinitePullbackComposition
import Sheaf.AlgebraicGeometry.FrobeniusFactorization
import Sheaf.AlgebraicGeometry.AbsoluteFrobeniusCoefficientNaturality
import Sheaf.SixFunctors.SchemeFrobenius

/-!
# Coefficient naturality of the specified scheme--Galois comparison

Source: blueprint main-20261015, `thm-trf-finite-coefficient-map.proof.md`, final sentence,
and `prop-trf-scheme-galois-comparison.proof.md`, displayed construction of kappa.
(blueprint: lem-trf-scheme-galois-coefficient-change).

The constant-ring scalar extension and pullback comparison are the published universal
extension and tensor-unit-normalized mate. They express the ordinary constant-coefficient
transport of the condensed comparison. The comparison kappa is the selected normalized
multiplicative family, rather than an arbitrary natural isomorphism.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale

namespace WeilConjectures.FiniteFieldDatum

/-- The specified scheme--Galois comparison commutes with every finite coefficient map.
The annihilating integer is a unit in the characteristic-p field, equivalently prime to p.
This includes the zero ring, the empty scheme, non-flat coefficient maps and arbitrary
unbounded objects. At m = 1 it is the coefficient square for kappa itself.

Source: blueprint main-20261015, `thm-trf-finite-coefficient-map.proof.md`, final sentence;
`prop-trf-scheme-galois-comparison.proof.md`, both paragraphs.
(blueprint: lem-trf-scheme-galois-coefficient-change).

Proof:
1. Put H = F_X^(am). The Frobenius factorization and the inverse arithmetic/geometric
   Galois maps give Phi^m = g^m H = H g^m. This is an equality of scheme maps and
   does not require the Galois map to be k-linear.
2. By the specified construction, kappa_R at K is the canonical pullback compositor
   followed by the absolute-Frobenius trivialization at (g^m)^*K. The finite-discrete
   constant-ring identifications transport scalar-six-pullback (1) to these ordinary
   categories. Its composition law compares the compositor with coefficient change.
3. Apply lem-trf-absolute-frobenius-coefficient-naturality with exponent am at
   (g^m)^*K. Naturality of the B-trivialization at the g^m coefficient comparison
   moves that comparison past the trivialization.
4. Substitute the compositor identity from step 2 and the two identities from step 3
   into T(kappa_A) composed with c_Phi. Associativity gives c_g composed with kappa_B.
   All maps have target T((g^m)^*K). The calculation applies to every positive m,
   including 1, without flatness or Tor-amplitude assumptions. -/
theorem schemeGaloisComparison_coefficientChange
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (X₀ : Over (Spec (CommRingCat.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (A B : Type u) [CommRing A] [CommRing B] [Finite A] [Finite B]
    (hA : ∃ n : ℕ, IsUnit (n : D.k) ∧ ∀ a : A, n • a = 0)
    (hB : ∃ n : ℕ, IsUnit (n : D.k) ∧ ∀ b : B, n • b = 0)
    (φ : A →+* B) (m : ℕ) (hm : 1 ≤ m)
    (K : proEtaleDerivedCategory (D.geometricFiber X₀).left A) :
    (directImageScalarPullbackIso φ (D.schemeFrobeniusIterate X₀ m)).hom.app K ≫
        (directImageScalarExtension φ (D.geometricFiber X₀).left).map
          ((D.canonicalSchemeGaloisComparison X₀ A hA m hm).hom.app K) =
      (D.canonicalSchemeGaloisComparison X₀ B hB m hm).hom.app
          ((directImageScalarExtension φ (D.geometricFiber X₀).left).obj K) ≫
        (directImageScalarPullbackIso φ
          (HPow.hPow (α := End (D.geometricFiber X₀).left)
            (D.geometricGaloisFrobenius X₀) m)).hom.app K := by
  sorry

end WeilConjectures.FiniteFieldDatum
