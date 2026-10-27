module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
import WeilConjectures.AlgebraicGeometry.Morphisms.ProperQuasiFinite
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import WeilConjectures.RingTheory.RegularRingNormal
import Mathlib.RingTheory.LocalProperties.IntegrallyClosed
import Mathlib.RingTheory.IntegralClosure.GoingDown
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Unramified.Basic
import WeilConjectures.AlgebraicGeometry.Morphisms.FormallyUnramifiedStalkNeighbourhood
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.Etale.Kaehler
import Sheaf.AlgebraicGeometry.EtaleAtPrimeFlatUnramifiedCriterion
import Sheaf.AlgebraicGeometry.LocalQuasiFiniteBranchPurity

/-! # Codimension-one purity for a finite normalization

Source: Stacks Project, Fundamental Groups of Schemes, Tag 0BMB, Lemma `purity`,
applied to the finite normalization in a finite separable extension of the fraction field
(blueprint: lem-per-finite-normalization-codimension-one-purity).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace AlgebraicGeometry

/-- A finite normalization over a regular Noetherian domain is finite etale if the
relative local differentials vanish above every height-one prime of the base.
Source: Stacks Project, Tag 0BMB, Lemma `purity`, finite-normalization application
(blueprint: lem-per-finite-normalization-codimension-one-purity).

Proof plan:
1. Module finiteness makes the spectrum map finite and quasi-finite
   (`def-weil-finite-integral-morphism`, `pqf-lem-finite-qf`). The finite-algebra
   Noetherian lemma makes the source Noetherian. Integral closure in the finite extension
   is a normal domain with fraction field L, and its prime localizations are normal
   (`lem-weil-pbc-integral-closure-finite-extension-normal`,
   `lem-weil-pbc-localization-normal-domain`). Regularity makes A normal, hence integrally
   closed as a domain (`lem-weil-pbc-regular-ring-normal`,
   `lem-weil-pbc-normal-domain-of-local-normal`). Its prime localizations are regular local.
2. Integral incomparability contracts strict chains of primes in C to strict chains in A.
   Going down over the normal domain A lifts a chain ending at p backwards from any fixed
   prime q above p. Thus q and p have equal heights, and their local rings have equal
   dimensions (`lem-weil-pbc-going-down-normal-integral`,
   `lem-weil-pbc-integral-incomparability`,
   `lem-weil-pbc-localization-dimension-chains-below-prime`).
3. Every height-one prime of C contracts to a height-one prime of A. The assumed vanishing
   of relative local differentials gives formal unramifiedness by
   `lem-weil-pbc-formally-unramified-ring-iff-kahler-zero`. Since the map is locally of
   finite type, `lem-sbc-formally-unramified-stalk-neighbourhood` spreads this to a source
   neighbourhood, and `lem-weil-pbc-lft-formally-unramified-unramified` makes it unramified.
4. The algebra C is finitely presented over A by
   `lem-weil-pbc-finite-type-noetherian-finite-presentation`. At the generic point the
   local rings are L and K. The field extension is flat and has zero differentials
   (`lem-weil-pbc-module-over-field-flat`, `lem-trf-separable-field-differentials-vanish`).
   Differential localization identifies the generic differential module with Omega(L/A).
   Every A-derivation on L kills K, since D(a/b) = 0 for a,b in A and b nonzero;
   thus Omega(L/A) = Omega(L/K) = 0. Use
   `lem-weil-pbc-kahler-differentials-localization` and
   `lem-sc-etale-at-prime-flat-unramified-criterion` to obtain a generic etale neighbourhood.
5. At each nonzero prime q, the source local ring is normal, the target local ring is
   regular, the morphism is quasi-finite, their dimensions agree and are positive, and
   all height-one generalizations are unramified. Apply
   `lem-per-local-quasi-finite-branch-purity`. Together with step 4 this covers the source
   by etale neighbourhoods, so the map is etale. Its finiteness comes from step 1.
   If A is a field, height comparison leaves only the generic-point case of step 4.
-/
theorem finite_normalization_etale_of_codimension_one_differentials_vanish
    (A : Type u) [CommRing A] [IsDomain A] [IsRegularRing A]
    (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type u) [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Module.Finite A (integralClosure A L)]
    (hunram : ∀ (p : Ideal A) [p.IsPrime], p ≠ ⊥ →
      (∀ r : Ideal A, r.IsPrime → r < p → r = ⊥) →
      ∀ (q : Ideal (integralClosure A L)) [q.IsPrime]
        (hpq : p = q.comap (algebraMap A (integralClosure A L))),
        Subsingleton (@KaehlerDifferential (Localization.AtPrime p) (Localization.AtPrime q)
          _ _ (Localization.localRingHom p q
            (algebraMap A (integralClosure A L)) hpq).toAlgebra)) :
    IsFinite (Spec.map (CommRingCat.ofHom (algebraMap A (integralClosure A L)))) ∧
      Etale (Spec.map (CommRingCat.ofHom (algebraMap A (integralClosure A L)))) := by
  sorry

end AlgebraicGeometry
