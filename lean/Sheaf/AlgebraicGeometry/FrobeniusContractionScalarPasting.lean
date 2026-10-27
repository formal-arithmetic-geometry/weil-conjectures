/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q133
-/
module

public import Sheaf.AlgebraicGeometry.SchemeCharacteristic
public import WeilConjectures.AlgebraicGeometry.AbsoluteFrobenius
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Sheaf.SixFunctors.ScalarSixPullback
public import Sheaf.Paper.FiniteDiscreteCondensedRing
public import Sheaf.Paper.FiniteDiscreteSchemeRing
public import Sheaf.SecSmoothPurity.DirectImageScalarOperations
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingPullbackComparison
import Sheaf.Paper.IntegralFinitePullbackComposition
public import Sheaf.AlgebraicGeometry.AbsoluteFrobeniusSite
public import Sheaf.AlgebraicGeometry.AbsoluteFrobeniusCoefficientNaturality

/-!
# Frobenius contraction and scalar extension

Source: main-20261015 blueprint, `thm-trf-finite-coefficient-map.proof.md`, final sentence,
and `prop-trf-scheme-galois-comparison.proof.md`, displayed pullback contraction
(blueprint: lem-trf-frobenius-contraction-scalar-pasting).

The contraction is the canonical pullback compositor followed by the specified
absolute-Frobenius trivialization. All categories and scalar extensions are ordinary
and unbounded. The endomorphism need not be invertible, and exponent zero is included.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Contract the absolute-Frobenius factor in pullback along `v ∘ F^b` using the
canonical constant-coefficient compositor and the section-normalized trivialization.
Source: main-20261015 blueprint, `prop-trf-scheme-galois-comparison.proof.md`, displayed
construction of the comparison by composition and Frobenius trivialization
(blueprint: lem-trf-frobenius-contraction-scalar-pasting). -/
def frobeniusContraction (p : ℕ) (hp : p.Prime)
    (Y : Scheme.{u}) (hY : Y.IsCharacteristic p) (v : Y ⟶ Y)
    (R : Type u) [CommRing R] [Finite R] (b : ℕ) :
    proEtaleConstantRingDerivedPullback R (Y.iterateFrobenius hp (hY.2 ⊤) b ≫ v) ≅
      proEtaleConstantRingDerivedPullback R v :=
  (proEtaleConstantRingPullbackComposition (Y.iterateFrobenius hp (hY.2 ⊤) b) v R).symm ≪≫
    Functor.isoWhiskerLeft (proEtaleConstantRingDerivedPullback R v)
      (coefficientFrobeniusTrivialization p hp Y hY R b) ≪≫
    Functor.rightUnitor _

/-- Ordinary derived scalar extension respects contraction of an absolute-Frobenius
factor, for every scheme endomorphism and every nonnegative exponent.

Source: main-20261015 blueprint, `thm-trf-finite-coefficient-map.proof.md`, final
coefficient-naturality sentence, applied to the displayed compositor and trivialization
in `prop-trf-scheme-galois-comparison.proof.md`
(blueprint: lem-trf-frobenius-contraction-scalar-pasting).

Proof:
1. Apply the composition law in det-prop-scalar-six-pullback (1) with the ordered
   morphisms H = F^b and v. Invert its comparisons and transport through the finite
   discrete condensed and scheme constant-ring identifications, using the normalization
   of def-sp-constant-scalar-pullback-comparison. For the canonical compositor d this
   gives T(d_A) c_(vH) = c_(H,V_A K) P_B(c_v) d_B. The pullback order is P_R V_R.
2. Apply lem-trf-absolute-frobenius-coefficient-naturality at V_A K. It gives
   T(t_A) c_(H,V_A K) = t_B at T(V_A K), for the same normalized comparisons.
3. Naturality of t_B at c_v gives t_B P_B(c_v) = c_v t_B. Expand the contractions
   as t_R after d_R, apply functoriality of T, and substitute the preceding equalities.
   This is the asserted equality. The exponent-zero case retains the canonical
   identity-pullback unitors. No inverse to v, flatness, finite Tor amplitude,
   prime-to-p annihilator, boundedness, or constructibility is used. -/
theorem frobenius_contraction_scalar_pasting (p : ℕ) (hp : p.Prime)
    (Y : Scheme.{u}) (hY : Y.IsCharacteristic p) (v : Y ⟶ Y)
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B] (φ : A →+* B)
    (b : ℕ) (K : proEtaleDerivedCategory Y A) :
    (AlgebraicGeometry.ProEtale.directImageScalarPullbackIso φ
      (Y.iterateFrobenius hp (hY.2 ⊤) b ≫ v)).hom.app K ≫
        (AlgebraicGeometry.ProEtale.directImageScalarExtension φ Y).map
          ((frobeniusContraction p hp Y hY v A b).hom.app K) =
      (frobeniusContraction p hp Y hY v B b).hom.app
          ((AlgebraicGeometry.ProEtale.directImageScalarExtension φ Y).obj K) ≫
        (AlgebraicGeometry.ProEtale.directImageScalarPullbackIso φ v).hom.app K := by
  sorry

end AlgebraicGeometry.Scheme
