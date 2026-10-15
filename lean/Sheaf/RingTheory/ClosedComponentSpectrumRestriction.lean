/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NU
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.Topology.Connected.Clopen

import WeilConjectures.RingTheory.ProEtale.WContractible

/-!
# Restriction of an affine spectrum to a closed union of components

Source: Stacks Project, Tags 097C (`lemma-construct`), 04PL
(`lemma-closed-union-connected-components`), and 096T (`lemma-ind-zariski-implies`)
(blueprint: lem-weil-pbc-closed-component-spectrum-restriction).
-/

@[expose] public section

universe u

namespace PrimeSpectrum

/-- A closed union of connected components of `Spec A` is the spectrum of a quotient ring,
with the canonical maps on prime localizations isomorphisms.

Source: Stacks Project, Tags 097C (`lemma-construct`), 04PL
(`lemma-closed-union-connected-components`), and 096T (`lemma-ind-zariski-implies`)
(blueprint: lem-weil-pbc-closed-component-spectrum-restriction).

Proof plan:
1. Put `T = π(E)` in the connected-component quotient. Component saturation gives
   `π⁻¹(T) = E`, so the quotient topology makes `T` closed.
2. Take `B = WContractification.Restriction T`, the colimit of the localizations at the
   idempotents of clopen neighborhoods of `E`. The full spectrum is a neighborhood, and
   intersections direct the diagram. Use
   `lem-weil-pbc-restriction-algebraMap-surjective` for surjectivity of `A → B`.
3. Use `lem-weil-pbc-spec-quotient-homeomorphism-zero-locus` to identify the spectrum with
   the zero locus of the kernel. By `lem-weil-pbc-restriction-spectrum-range`, this is `E`.
4. The clopen-neighborhood diagram is small and filtered: the whole spectrum gives an object,
   intersections give common successors in reverse inclusion, and parallel arrows are equal.
   Each term `A_e` is a local isomorphism, using the neighborhood `g = 1` and `f = e`, since
   `(A_e)_1` is canonically `A_e` as an `A`-algebra.
5. Apply `lem-weil-pbc-ind-zariski-bijective-on-stalks` to this filtered presentation to
   obtain bijectivity of the induced map `A_{v⁻¹(q)} → B_q` for every prime `q`.
-/
theorem exists_closed_component_restriction (A : Type u) [CommRing A]
    (E : Set (PrimeSpectrum A)) (hE : IsClosed E)
    (hcomponents : ∀ x ∈ E, connectedComponent x ⊆ E) :
    ∃ (B : CommRingCat.{u}) (v : A →+* B), Function.Surjective v ∧
      ∃ h : PrimeSpectrum B ≃ₜ E,
        (∀ q : PrimeSpectrum B, (h q).val = PrimeSpectrum.comap v q) ∧
        ∀ q : PrimeSpectrum B, Function.Bijective
          (Localization.localRingHom (q.asIdeal.comap v) q.asIdeal v rfl) := by
  classical
  let T : Set (ConnectedComponents (PrimeSpectrum A)) := ConnectedComponents.mk '' E
  have hpre : ConnectedComponents.mk ⁻¹' T = E := by
    apply Set.Subset.antisymm
    · rintro x ⟨y, hy, hxy⟩
      exact hcomponents y hy (ConnectedComponents.coe_eq_coe'.mp hxy.symm)
    · exact Set.subset_preimage_image _ _
  have hT : IsClosed T := by
    apply ConnectedComponents.isQuotientMap_coe.isClosed_preimage.mp
    rwa [hpre]
  let B := WContractification.Restriction T
  have hsurj : Function.Surjective (algebraMap A B) :=
    WContractification.Restriction.algebraMap_surjective T
  have hrange : Set.range (PrimeSpectrum.comap (algebraMap A B)) = E :=
    (WContractification.Restriction.range_algebraMap_specComap hT).trans hpre
  have hemb := PrimeSpectrum.isEmbedding_comap_of_surjective B (algebraMap A B) hsurj
  let h : PrimeSpectrum B ≃ₜ E :=
    hemb.toHomeomorph.trans (Homeomorph.setCongr hrange)
  refine ⟨CommRingCat.of B, algebraMap A B, hsurj, h, fun _ ↦ rfl, ?_⟩
  intro q
  exact (Algebra.IndZariski.bijectiveOnStalks_algebraMap A B).localRingHom q.asIdeal

end PrimeSpectrum
