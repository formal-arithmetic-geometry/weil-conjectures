module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.Away.Basic

import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import WeilConjectures.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints
import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTraitStalk
import WeilConjectures.RingTheory.LocalizationPrimeResidueFieldIso

/-! # Principal DVR neighbourhoods in an étale algebra over a DVR

Source: Stacks Project, More on Algebra, Tag 0AP2, lemma-Dedekind-etale-extension;
Models of Curves, Tag 0CDD, lemma-etale-local-at-worst-nodal, third proof paragraph.
(blueprint: lem-sfb-etale-dvr-principal-neighbourhood)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

universe u

namespace AlgebraicGeometry

/-- A prime over the closed point in an étale DVR algebra has a principal neighbourhood
whose ring is a DVR. Its maximal ideal is the extension of the chosen prime, and its
structural map from the original DVR is injective, local and étale.

Source: Stacks Project, More on Algebra, Tag 0AP2, lemma-Dedekind-etale-extension;
Models of Curves, Tag 0CDD, lemma-etale-local-at-worst-nodal, third proof paragraph.
(blueprint: lem-sfb-etale-dvr-principal-neighbourhood)

Proof:
1. The local PID definition (def-sc-discrete-valuation-ring) implies that Spec R has
   exactly the primes (0) and m_R: every nonzero prime principal ideal is maximal,
   by primality and cancellation in the domain.
2. Each fibre of Spec B over Spec R is affine (lem-weil-pbc-fibre-product-affine-spectra),
   hence quasi-compact (lem-weil-pbc-affine-scheme-qcqs), and discrete by
   lem-weil-pbc-etale-fibre-discrete-separable-points. It therefore has finitely many
   points. The fibre identification of def-pc-scheme-fibre and step 1 show Spec B is finite.
3. For each prime p not contained in q choose c_p in p outside q. Their finite product b
   lies outside q, and the primes not containing b are exactly those contained in q.
   The empty product is 1.
4. Localization prime correspondence (lem-weil-pbc-localization-prime-residue-field-iso)
   identifies all primes of C = B[1/b] with primes contained in q. Thus every prime of C
   is contained in qC. Maximal-ideal existence (lem-weil-pbc-proper-ideal-contained-in-maximal)
   shows C is local with unique maximal ideal qC.
5. The canonical map C to B_q is an isomorphism. For s outside q, its image in C lies
   outside qC, hence is a unit (lem-weil-pbc-local-ring-unit-criterion). This proves
   surjectivity by fractions. If x/b^n maps to zero, some s outside q annihilates x;
   multiplying by the inverse of its image in C proves injectivity. These fraction maps
   preserve the structural maps and the extended prime ideals, using
   def-weil-pbc-localization-at-prime and def-weil-ring-localization-away.
6. Choose a uniformizer of R and apply lem-sbc-etale-trait-stalk at the point q over m_R.
   Its stalk is a DVR and R maps injectively into it. The canonical affine-stalk
   identification (lem-weil-pbc-affine-open-stalk-localization), composed with step 5,
   transports this conclusion to C. The contraction of qC is q, whose contraction is
   m_R, giving localness of the composite R to C.
7. The map Spec C to Spec B is the principal-localization open immersion
   (lem-weil-pbc-principal-localization-open-immersion). Open immersions and composites
   of étale morphisms are étale (lem-weil-pbc-etale-composition-cancellation).
No module-finiteness, excellence, henselianity or completeness is used. -/
theorem exists_etale_dvr_principal_neighbourhood
    (R B : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing B]
    (φ : R →+* B) [Etale (Spec.map (CommRingCat.ofHom φ))]
    (q : Ideal B) [q.IsPrime] (hq : q.comap φ = IsLocalRing.maximalIdeal R) :
    ∃ (b : B), b ∉ q ∧
      ∃ (_ : IsDomain (Localization.Away b)) (_ : IsDiscreteValuationRing (Localization.Away b)),
        IsLocalRing.maximalIdeal (Localization.Away b) =
            q.map (algebraMap B (Localization.Away b)) ∧
          Function.Injective ((algebraMap B (Localization.Away b)).comp φ) ∧
          (IsLocalRing.maximalIdeal (Localization.Away b)).comap
              ((algebraMap B (Localization.Away b)).comp φ) = IsLocalRing.maximalIdeal R ∧
          Etale (Spec.map (CommRingCat.ofHom ((algebraMap B (Localization.Away b)).comp φ))) := by
  sorry

end AlgebraicGeometry
