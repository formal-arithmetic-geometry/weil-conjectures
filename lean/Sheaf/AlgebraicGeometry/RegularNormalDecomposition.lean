/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.Topology.Irreducible
public import Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.AlgebraicGeometry.NoetherianComponents
import Mathlib.AlgebraicGeometry.Limits
import WeilConjectures.RingTheory.RegularRingNormal

/-!
# Regular schemes and the normal decomposition

Source: Weil conjectures blueprint, `sec-abelian-varieties/sk-def-av-jacobian`,
`rem-pc-regular-normal`; Stacks Project, Tags 0569, 02IT and 033M
(blueprint: rem-pc-regular-normal).

Normality is the normal-domain condition on every stalk. Regularity uses the affine-open
condition recorded by `def-weil-regular-scheme`. The coproduct assertion uses the canonical
open inclusions as the legs of a colimiting cofan, so it specifies a scheme decomposition.

The proof uses the source library's normal decomposition and identifies its pieces with the
irreducible components. Mathlib supplies the coproduct universal property of a disjoint open cover.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Regular schemes are normal; a Noetherian normal scheme is the finite disjoint union
of its clopen normal integral irreducible components; a nonempty connected Noetherian
regular scheme is irreducible.

Source: Weil conjectures blueprint, `rem-pc-regular-normal`; Stacks Project, Tags 0569,
02IT and 033M (blueprint: rem-pc-regular-normal).

Proof:
1. Choose an affine regular neighbourhood at each point (`def-weil-regular-scheme`).
   Its ring is normal by `lem-weil-pbc-regular-ring-normal`. The affine stalk localization
   of `lem-weil-pbc-affine-open-stalk-localization` is therefore a normal domain, by
   `def-weil-pbc-normal-ring`. This proves the first assertion, also for the empty scheme.
2. For a Noetherian normal scheme every stalk is reduced because it is a domain.
   By `def-pc-reduced-scheme` the scheme and every section ring are reduced. Choose affine
   Noetherian charts using `pqf-def-locnoeth`.
3. Every prime of a chart corresponds to a point by `lem-weil-pbc-affine-open-spec-points`;
   its localization is the normal stalk by `lem-weil-pbc-affine-open-stalk-localization`.
   The chart ring has finitely many minimal primes by
   `lem-weil-pbc-noetherian-finitely-many-minimal-primes`. Apply
   `lem-weil-pbc-reduced-normal-iff-integrally-closed-total-fractions` to decompose it
   as a finite product of normal domains.
4. By `lem-weil-pbc-finite-affine-coproduct-spectrum` each chart is a disjoint union
   of the spectra of these domains. The factors are clopen by
   `lem-weil-pbc-scheme-coproduct-family`, integral by
   `lem-weil-pbc-spec-domain-stalks-function-field`, and normal by
   `lem-weil-pbc-localization-normal-domain`. They are precisely the irreducible components
   of the chart: an irreducible subset cannot meet two disjoint clopen factors.
5. By `lem-sc-components-open-injection`, a global component meets each chart in a chart
   component or the empty set, so it is open; it is closed by
   `def-weil-irreducible-components`. If two components meet, their intersections with a
   chart through that point coincide, and the injectivity in the same lemma identifies
   the global components. Thus distinct components are disjoint.
6. The components cover by `lem-sc-irreducible-components-cover` and are finite by
   `lem-weil-pbc-noetherian-finitely-many-components`. Their open subschemes have the same
   stalks by `def-weil-open-immersion`, hence are normal and reduced. They are irreducible
   and nonempty, hence integral by `def-pc-integral-scheme`. Enumerate them by `Fin n`.
   Compatible maps from these opens glue uniquely by `lem-weil-pbc-scheme-morphism-gluing`;
   all overlaps are empty. This is the coproduct universal property in
   `lem-weil-pbc-scheme-coproduct-family`, with the actual inclusions as coprojections.
   The empty scheme has `n = 0`.
7. For the last assertion apply the first two assertions. Nonemptiness gives a component.
   If another existed, one component and the union of the others would disconnect the
   scheme. Thus its unique component is the whole space, which is irreducible by
   `def-weil-irreducible-components`. -/
theorem regular_normal_and_normal_decomposition (X : Scheme.{u}) :
    ((∀ x : X, ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧ IsRegularRing Γ(X, U)) →
      ∀ x : X, IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x)) ∧
    (IsNoetherian X →
      (∀ x : X, IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x)) →
      ∃ (n : ℕ) (U : Fin n → X.Opens),
        Set.range (fun i : Fin n ↦ (U i : Set X)) = irreducibleComponents X ∧
        (∀ i : Fin n, IsClosed (U i : Set X)) ∧
        (∀ i j : Fin n, i ≠ j → Disjoint (U i) (U j)) ∧
        (⨆ i : Fin n, U i) = ⊤ ∧
        (∀ i : Fin n, IsIntegral (U i).toScheme ∧
          ∀ x : (U i).toScheme,
            IsDomain ((U i).toScheme.presheaf.stalk x) ∧
              IsIntegrallyClosed ((U i).toScheme.presheaf.stalk x)) ∧
        Nonempty (IsColimit (Cofan.mk X (fun i : Fin n ↦ (U i).ι)))) ∧
    ((∀ x : X, ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧ IsRegularRing Γ(X, U)) →
      IsNoetherian X → Nonempty X → PreconnectedSpace X → IrreducibleSpace X) := by
  classical
  have hnormal
      (hreg : ∀ x : X, ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧
        IsRegularRing Γ(X, U)) (x : X) :
      IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x) := by
    obtain ⟨U, hx, hR⟩ := hreg x
    have := hR
    let := X.presheaf.algebra_section_stalk (⟨x, hx⟩ : (U : X.Opens))
    have := U.2.isLocalization_stalk ⟨x, hx⟩
    obtain ⟨hd, hc⟩ := IsRegularRing.isNormalRing Γ(X, U)
      (U.2.primeIdealOf ⟨x, hx⟩).asIdeal
    have := hd
    have := hc
    let e := (IsLocalization.algEquiv (U.2.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
      (Localization.AtPrime (U.2.primeIdealOf ⟨x, hx⟩).asIdeal)
      (X.presheaf.stalk x)).toRingEquiv
    exact ⟨e.symm.injective.isDomain e.symm.toRingHom, IsIntegrallyClosed.of_equiv e⟩
  refine ⟨hnormal, ?_, ?_⟩
  · intro hnoeth hn
    have := hnoeth
    obtain ⟨n, U, hcl, hdisj, hcover, hprop⟩ :=
      X.exists_isClopen_isIntegral_of_isIntegrallyClosed_stalk hn
    have hirr (i : Fin n) : IsIrreducible (U i : Set X) := by
      have := (hprop i).1
      simpa only [Set.image_univ, Scheme.Opens.range_ι] using
        (IrreducibleSpace.isIrreducible_univ (U i).toScheme).image (U i).ι
          (U i).ι.continuous.continuousOn
    have hmem (i : Fin n) : (U i : Set X) ∈ irreducibleComponents X := by
      refine ⟨hirr i, fun T hT hUT ↦ ?_⟩
      obtain ⟨x, hx⟩ := (hirr i).nonempty
      exact hT.2.isPreconnected.subset_isClopen (hcl i) ⟨x, hUT hx, hx⟩
    refine ⟨n, U, ?_, fun i ↦ (hcl i).isClosed, fun i j hij ↦ hdisj hij,
      hcover, ?_, ?_⟩
    · apply Set.Subset.antisymm
      · rintro _ ⟨i, rfl⟩
        exact hmem i
      · intro T hT
        obtain ⟨x, hx⟩ := hT.1.nonempty
        have hxcover : x ∈ ⨆ i, U i := by rw [hcover]; trivial
        obtain ⟨i, hxi⟩ := TopologicalSpace.Opens.mem_iSup.mp hxcover
        have hTU := hT.1.2.isPreconnected.subset_isClopen (hcl i) ⟨x, hx, hxi⟩
        exact ⟨i, Set.Subset.antisymm (hT.2 (hirr i) hTU) hTU⟩
    · intro i
      have := (hprop i).1
      exact ⟨inferInstance, fun x ↦ ⟨inferInstance, (hprop i).2 x⟩⟩
    · apply nonempty_isColimit_cofanMk_of
      · simpa using hcover
      · intro i j hij
        simpa using hdisj hij
  · intro hreg hnoeth hne hconn
    have := hnoeth
    have := hne
    have := hconn
    have : ConnectedSpace X := ⟨hne⟩
    exact irreducibleSpace_of_isDomain_stalk X (fun x ↦ (hnormal hreg x).1)

end AlgebraicGeometry
