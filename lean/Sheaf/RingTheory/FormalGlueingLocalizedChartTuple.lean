/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Sheaf.RingTheory.FormalGlueingData
public import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
import Sheaf.Paper.FormalGlueingCanonicalMaps

/-!
# A compatible chart tuple after localization

Source: Stacks Project, Remark 05EL and Lemma 05EP, as used in Proposition 05ER.
-/

@[expose] public section

universe u v w

namespace FormalGlueing

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- The canonical localized chart tuple has compatibility differences vanishing after
localizing at the chart parameter. This only constructs a localized ambient tuple;
it does not clear denominators or produce an element of `h0`. The tuple is
specified by the inverse of the finite-product localization comparison, with
prime coordinate `(X.alpha i).symm (1 ⊗ x)` and chart coordinates
`X.alpha_overlap i j (x/1)`.
Source: Stacks Project, Remark 05EL, conditions (a) and (b), Lemma 05EP, and
Proposition 05ER, second paragraph
(blueprint: lem-weil-pbc-formal-glueing-localized-chart-tuple).

Proof:
Set `u = f i`. The prime coordinate is `(X.alpha i).symm (1 ⊗ x)` and the
`j` coordinate is `X.alpha_overlap i j (x/1)`. Localization commutes with the
finite product, so these coordinates determine an element of the localization
of the ambient product. Evaluate the square for
`(i,j)` on the prime coordinate and use the canonical swap and tensor comparison
fraction formulas. The comparison is injective by `compare_properties`; hence
equality after this comparison gives equality of the two terms in the localized
prime/chart difference.
Evaluate the cocycle for `(i,j,k)` on `(x/1)/1`, using the swap fraction formula:
the two terms in the localized overlap difference agree. Thus all the displayed
differences vanish. If `f i = 0`, all modules localized there are zero. An index
`i` excludes the empty index set; no nonzero ring or module hypothesis is needed. -/
theorem localized_chart_tuple_compatible {t : ℕ} (φ : R →+* S)
    (f : Fin t → R) (X : Data.{u, v, w} φ f) (i : Fin t)
    (x : piece (f i) (X.M i)) :
    letI : Algebra R S := φ.toAlgebra
    let A := ModuleCat.of R (restrict φ X.M' × ∀ j : Fin t, piece (f j) (X.M j))
    let p : ∀ j : Fin t, A →ₗ[R] piece (f j) (X.M j) :=
      fun j ↦ (LinearMap.proj j).comp (LinearMap.snd R _ _)
    let a := fun j : Fin t ↦
      (((X.alpha j).toLinearMap.comp
        (LocalizedModule.mkLinearMap _ (restrict φ X.M'))).comp
          (LinearMap.fst R _ _) -
        (TensorProduct.mk R S (piece (f j) (X.M j)) 1).comp (p j))
    let b := fun j k : Fin t ↦
      (((X.alpha_overlap j k).toLinearMap.comp
        (LocalizedModule.mkLinearMap _ (piece (f j) (X.M j)))).comp (p j) -
        (LocalizedModule.mkLinearMap _ (piece (f k) (X.M k))).comp (p k))
    let T := Submonoid.powers (f i)
    let ell₀ := LocalizedModule.mkLinearMap T (restrict φ X.M')
    let ell₁ : (∀ j, piece (f j) (X.M j)) →ₗ[R]
        (∀ j, LocalizedModule T (piece (f j) (X.M j))) :=
      LinearMap.pi fun j ↦ (LocalizedModule.mkLinearMap T _).comp (LinearMap.proj j)
    let e := IsLocalizedModule.linearEquiv T (ell₀.prodMap ell₁)
      (LocalizedModule.mkLinearMap T A)
    let z := e ((X.alpha i).symm (TensorProduct.tmul R (1 : S) x),
      fun j ↦ X.alpha_overlap i j (LocalizedModule.mk x 1))
    (∀ j, localMap (f i) (a j) z = 0) ∧
      (∀ j k, localMap (f i) (b j k) z = 0) := by sorry

end FormalGlueing
