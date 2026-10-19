module

public import Sheaf.AlgebraicGeometry.ReducedNormalization
public import Sheaf.RingTheory.ExcellentRing
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.Sober
import Sheaf.AlgebraicGeometry.ComponentwiseNormalizationAffineCharts
import Sheaf.AlgebraicGeometry.ExcellentSchemeAffineCover
import Sheaf.RingTheory.IsExcellentFiniteTypeLocalization
import WeilConjectures.RingTheory.JapaneseDomain
import WeilConjectures.RingTheory.NagataRing
import Sheaf.RingTheory.QuasiExcellentNagata

/-!
# Finite normalization over a dense open of an excellent scheme

Source: literature/stacks-project/morphisms.tex, Tags 035S, 035Q, and 0BAJ;
excellence via More on Algebra Tags 07QV and 07QU
(blueprint: lem-per-excellent-normalization-preparation).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The componentwise normalization of a reduced Noetherian excellent scheme is finite and
surjective, has excellent Noetherian normal source, and is an isomorphism on a dense open
containing all generic points.
Source: literature/stacks-project/morphisms.tex, Tags 035S, 035Q, and 0BAJ;
excellence via More on Algebra Tags 07QV and 07QU
(blueprint: lem-per-excellent-normalization-preparation).

Proof: The empty scheme is handled by the empty normalization and empty open. On affine
charts, componentwise normalization is the product of integral closures of the domains
obtained from the finitely many minimal primes. Excellence gives the Nagata property, so
these integral closures are finite; this proves finiteness. Integral lying-over proves
surjectivity, and integral closures in the component fraction fields are normal domains,
so affine stalks of the normalization are integrally closed domains. Finite type stability
of excellence and a finite affine cover prove that the source remains excellent and
Noetherian. Around each generic point, choose a domain affine neighbourhood and invert a
product of denominators of finite module generators; the normalization then becomes the
identity after localization. The resulting principal opens glue to a dense open containing
every generic point, and the restricted map is an isomorphism.
-/
theorem excellent_normalization_preparation
    (X : Scheme.{u}) [IsReduced X] [IsLocallyNoetherian X] [CompactSpace X]
    (hExcellent : ∀ U : X.affineOpens, IsExcellent Γ(X, U)) :
    IsFinite X.fromReducedNormalization ∧
      Surjective X.fromReducedNormalization ∧
      IsLocallyNoetherian X.reducedNormalization ∧
      CompactSpace X.reducedNormalization ∧
      (∀ V : X.reducedNormalization.affineOpens,
        IsExcellent Γ(X.reducedNormalization, V)) ∧
      (∀ x : X.reducedNormalization,
        IsDomain (X.reducedNormalization.presheaf.stalk x) ∧
          IsIntegrallyClosed (X.reducedNormalization.presheaf.stalk x)) ∧
      ∃ U : X.Opens,
        Dense (U : Set X) ∧
          (∀ Z : irreducibleComponents X, ∀ x : X,
            IsGenericPoint x Z.1 → x ∈ U) ∧
          IsIso (X.fromReducedNormalization ∣_ U) := by
  sorry

end AlgebraicGeometry
