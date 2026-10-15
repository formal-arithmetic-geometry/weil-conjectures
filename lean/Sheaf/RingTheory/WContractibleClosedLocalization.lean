/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NS
-/
module

public import Sheaf.RingTheory.IndPrincipalZariski
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Sheaf.RingTheory.LocalizationPrimeResidueFieldIso
import Sheaf.AlgebraicGeometry.Sites.WContractibleCoverSection

/-! # Closed localization of a w-contractible ring

Source: Stacks Project, Tags 096V, 0987 and 09AH
(blueprint: lem-weil-pbc-wcontractible-closed-localization).
-/

@[expose] public section

universe u v

open CategoryTheory AlgebraicGeometry

namespace IsLocalization

/-- The finite family of principal opens and the closed localization, indexed by `Option (Fin r)`.
The `none` member is `Spec B`. Source: Stacks Project, Tags 0987 and 09AH
(blueprint: lem-weil-pbc-wcontractible-closed-localization). -/
noncomputable def closedLocalizationFamily (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]
    {r : ℕ} (f : Fin r → R) : PreZeroHypercover (Spec (.of R)) where
  I₀ := Option (Fin r)
  X j := match j with
    | none => Spec (.of B)
    | some k => Spec (.of (Localization.Away (f k)))
  f j := match j with
    | none => Spec.map (CommRingCat.ofHom (algebraMap R B))
    | some k => Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (f k))))

/-- Closed localization and preservation of the retraction property called w-contractibility.
Source: Stacks Project, Tags 096V, 0987 and 09AH
(blueprint: lem-weil-pbc-wcontractible-closed-localization).

Proof: (1) Localization primes are primes disjoint from the denominator monoid. Such a prime
`p` is disjoint precisely when `p + I` is proper, equivalently when some prime `q` contains
both `p` and `I` (localization prime correspondence and existence of maximal ideals).
(2) Basic opens pull back to basic opens, and every denominator is invertible, so this
bijection is a homeomorphism onto its image with the subspace topology.
(3) The fraction map `a/s ↦ (a mod I)/(s mod I)` is surjective with kernel `IB`, inducing
the canonical quotient isomorphism, including when the quotient is zero.
(4) Localizations are flat and have invertible diagonal, hence are weakly etale. The
principal opens together with the localization image cover the spectrum, by the equality
of zero loci. The finite affine family therefore satisfies the full fpqc cover condition.
(5) Given a faithfully flat weakly etale map `B → D`, replace the `B` member by `D`;
its image is unchanged by faithful flatness. The w-contractible-cover-section lemma gives
a section of this finite cover over `R`.
(6) Restrict the section to `Spec B`. Points over `V(I)` must land in the `D` summand,
since each `f k` is in `I`. Every point specializes to one of these points, so the clopen
`D` summand contains the entire image. Restriction to that open summand gives `Spec B → Spec D`.
(7) Affine full faithfulness gives an `R`-map `D → B`. Its composite with `B → D` agrees
with the identity on `R` and hence on all fractions, so is a retraction. The same argument
covers the empty list, the unit ideal, and the zero ring. -/
theorem wcontractible_closed_localization (R B : Type u) [CommRing R] [CommRing B]
    [Algebra R B] (I : Ideal R)
    [IsLocalization ((IsUnit.submonoid (R ⧸ I)).comap (Ideal.Quotient.mk I)) B]
    (r : ℕ) (f : Fin r → R) (hf : ∀ k, f k ∈ I)
    (hV : PrimeSpectrum.zeroLocus (I : Set R) =
      PrimeSpectrum.zeroLocus (Set.range f)) :
    Topology.IsEmbedding (PrimeSpectrum.comap (algebraMap R B)) ∧
    Set.range (PrimeSpectrum.comap (algebraMap R B)) =
      {p | ∃ q : PrimeSpectrum R, I ≤ q.asIdeal ∧ p.asIdeal ≤ q.asIdeal} ∧
    (∃ e : (B ⧸ I.map (algebraMap R B)) ≃+* (R ⧸ I),
      ∀ a : R, e (Ideal.Quotient.mk _ (algebraMap R B a)) = Ideal.Quotient.mk I a) ∧
    (closedLocalizationFamily R B f).presieve₀ ∈ Scheme.proetalePrecoverage (Spec (.of R)) ∧
    ((∀ (D : Type (max u v)) [CommRing D] (g : R →+* D),
        g.FaithfullyFlat → g.WeaklyEtale → ∃ t : D →+* R, t.comp g = RingHom.id R) →
      ∀ (D : Type (max u v)) [CommRing D] (g : B →+* D),
        g.FaithfullyFlat → g.WeaklyEtale → ∃ t : D →+* B, t.comp g = RingHom.id B) := by
  sorry

end IsLocalization
