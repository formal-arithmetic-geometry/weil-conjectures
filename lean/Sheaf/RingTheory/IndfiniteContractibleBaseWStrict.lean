/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NR
-/
module

public import WeilConjectures.RingTheory.ProEtale.WContractible
public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.RingTheory.FinitePresentation
public import Sheaf.Topology.SpectralSpace.ConnectedComponentsProfinite
import Sheaf.RingTheory.FiniteWContractible
import Sheaf.Topology.WLocalComponents
import Sheaf.Topology.FilteredSpectrumTopologicalLimit
import WeilConjectures.AlgebraicGeometry.FilteredColimitLocalizationAtPrime
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-!
# Ind-finite algebras over a w-contractible base

Source: Bhatt–Scholze, Lemma 2.1.9 and Example 2.2.2; Stacks Project, Tag 0986
(blueprint: lem-sfb-indfinite-contractible-base-wstrict).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

/-- A directed ring colimit of finite finitely presented algebras over a w-contractible
base is w-strictly local, preserves closed points over the base, and has the canonical
inverse-limit spaces of closed points and connected components.

Source: Bhatt–Scholze, Lemma 2.1.9 and Example 2.2.2; Stacks Project, Tag 0986
(blueprint: lem-sfb-indfinite-contractible-base-wstrict).

Proof for stage 3:
1. Apply `lem-ce-finite-finitely-presented-wcontractible` at every stage. By
`det-pe-wlocal-components` and `sk-def-pe-wlocal`, every stage has a closed closed-point
locus, unique closed specializations, and strictly henselian maximal localizations.
2. An A-module generating list for a later algebra also generates it over an earlier
algebra. Hence transition maps are finite, therefore integral by
`lem-weil-pbc-finite-algebra-is-integral`. Their spectrum maps preserve closed points by
`lem-weil-pbc-integral-maximal-contracts-maximal`, as do the structural maps to Spec A.
3. Use `lem-a1-filtered-spectrum-topological-limit` to identify the colimit spectrum
with compatible prime families, with their coordinate topology. Specialization is
coordinatewise inclusion of primes (`def-weil-affine-spectrum`).
4. For each compatible prime family, its unique closed specializations at the stages
are compatible, since integral maps preserve maximal ideals. The resulting prime is
maximal: every larger prime has the same maximal coordinates, hence equals it. Maximal
existence here is `lem-weil-pbc-proper-ideal-contained-in-maximal`.
5. Every maximal prime of the colimit therefore has maximal coordinates, and every
prime has exactly one maximal specialization. Its closed-point locus is the intersection
of the inverse images of the stage closed-point loci, hence is closed. Restrict the
prime-family homeomorphism to obtain the first canonical homeomorphism.
6. Apply the natural closed-point/component homeomorphisms of
`det-pe-wlocal-components` at the stages and limit. This gives the second homeomorphism
with the displayed coordinate formula, for the quotient topologies.
7. By `lem-weil-pbc-filtered-colimit-localization-at-prime`, localization at a maximal
ideal is the filtered colimit of the localizations at its maximal contractions.
The fraction transition maps are local by the numerator test. Apply
`lem-sfb-filtered-colimit-strictly-henselian-local` to get strict henselianity.
8. Choose a stage using nonemptiness. A closed point of the limit maps to a closed
point there, and then to a closed point of Spec A. Zero stages and the zero colimit
are allowed throughout; their maximal-localization conditions are vacuous. No step
asserts extremal disconnectedness of the limit component space. -/
theorem indfiniteContractibleBase_wStrict
    (A : Type u) [CommRing A] [IsWContractibleRing A]
    (D : Type u) [PartialOrder D] [Nonempty D]
    (hdir : Directed (· ≤ ·) (id : D → D))
    (F : D ⥤ CommAlgCat.{u} A)
    (hfinite : ∀ d : D, Module.Finite A (F.obj d))
    (hfp : ∀ d : D, Algebra.FinitePresentation A (F.obj d))
    (c : Cocone F)
    (hc : IsColimit ((forget₂ (CommAlgCat.{u} A) CommRingCat.{u}).mapCocone c)) :
    IsWStrictlyLocalRing c.pt ∧
      (∀ x : closedPoints (PrimeSpectrum c.pt),
        PrimeSpectrum.comap (algebraMap A c.pt) x.val ∈ closedPoints (PrimeSpectrum A)) ∧
      (∃ e : closedPoints (PrimeSpectrum c.pt) ≃ₜ
          {p : (d : D) → closedPoints (PrimeSpectrum (F.obj d)) //
            ∀ (i j : D) (hij : i ≤ j),
              PrimeSpectrum.comap (F.map (homOfLE hij)).hom.toRingHom (p j).val =
                (p i).val},
        ∀ (x : closedPoints (PrimeSpectrum c.pt)) (d : D),
          ((e x).val d).val = PrimeSpectrum.comap (c.ι.app d).hom.toRingHom x.val) ∧
      (∃ e : ConnectedComponents (PrimeSpectrum c.pt) ≃ₜ
          {p : (d : D) → ConnectedComponents (PrimeSpectrum (F.obj d)) //
            ∀ (i j : D) (hij : i ≤ j),
              (PrimeSpectrum.continuous_comap
                (F.map (homOfLE hij)).hom.toRingHom).connectedComponentsMap (p j) = p i},
        ∀ (x : ConnectedComponents (PrimeSpectrum c.pt)) (d : D),
          (e x).val d = (PrimeSpectrum.continuous_comap
            (c.ι.app d).hom.toRingHom).connectedComponentsMap x) := by
  sorry

end
