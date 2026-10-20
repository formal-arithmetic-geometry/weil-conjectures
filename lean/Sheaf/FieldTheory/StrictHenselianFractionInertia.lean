/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NZ
-/
module

public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import WeilConjectures.Mathlib.FieldTheory.IsSepClosed
public import Sheaf.RingTheory.GeneralizedHenselizationAtPrime
public import Sheaf.RingTheory.StrictHenselizationPresentationIn
public import Sheaf.AlgebraicGeometry.StrictHenselization
import Sheaf.TraceFormula.HenselizationPrimeIndEtale
import Sheaf.RingTheory.IndEtaleUniverseTransport
import WeilConjectures.RingTheory.EtaleColimitNormalLocalDomain
import Sheaf.RingTheory.HenselianFiniteEtaleEquivalence
import WeilConjectures.RingTheory.ReducedNormalIffIntegrallyClosedTotalFractions
import Sheaf.RingTheory.ValuationRingNormal
import Sheaf.RingTheory.HenselianFiniteGaloisLift
import Sheaf.RingTheory.StrictHenselizationFiniteLifts

/-!
# Strict-henselian fraction field and the residue inertia kernel

Source: Stacks Project, Tags 0BSD and 0BSW
(blueprint: lem-wf-strict-henselian-fraction-inertia).
-/

@[expose] public section
set_option autoImplicit false

universe u

open scoped IntermediateField
open AlgebraicGeometry CategoryTheory IsLocalRing

/-- Stacks Project, Tags 0BSD and 0BSW
(blueprint: lem-wf-strict-henselian-fraction-inertia).
The rings are characterized by the henselization universal property and the specified
pointed-etale colimit, whose pointings define `P.residueMap`. The existential structure
maps are compatible with these given algebras; restriction and reduction are specified
on elements. In particular `res` is their composite, not an arbitrary homomorphism.
Like the domain properties, locality of `R` is a conclusion (Stacks Tag 04GW), not a hypothesis.

Proof, following the ten steps of the DAG node:
1. The DVR is normal by `lem-weil-pbc-valuation-ring-normal`. Use
   `lem-trf-henselization-prime-ind-etale` and
   `lem-weil-pbc-etale-colimit-normal-local-domain` for its ordinary henselization.
   The normal-ring hypothesis follows from
   `lem-weil-pbc-reduced-normal-iff-integrally-closed-total-fractions`.
2. By `lem-wf-strict-henselization-finite-lifts`, replace the strict henselization
   by the filtered system of local finite-etale lifts of finite Galois residue fields.
   `lem-wf-henselian-finite-galois-lift` identifies their integral closures, degrees,
   and fraction-field Galois groups. Normality and injectivity pass to the colimit.
   The pointed affine spectrum construction identifies this colimit with the recorded
   scheme strict henselization, respecting the structure map and pointings.
3. Fractions occur at finite stages, so L/K is separable algebraic. Extend the resulting
   embedding into the separable closure by `lem-exc-etale-embedding-extension-sepclosed`,
   using `lem-weil-pbc-separable-closure-exists-galois` for the splitting hypothesis.
4. Every K-automorphism of Ω preserves the finite Galois fraction fields, their integral
   closures, and hence R and L. Restrict to R. Reduction preserves the maximal ideal
   and descends to its residue field. These operations respect composition.
5. Lift each residue automorphism uniquely to every finite-etale stage by
   `lem-weil-pbc-henselian-finite-etale-equivalence`. Full faithfulness makes these
   lifts compatible. Pass to R and L and extend to Ω by the embedding-extension lemma.
   The extension is onto since it permutes each finite set of conjugates. Thus res is onto.
6. A trivial residue action gives the identity on every finite-etale stage by full
   faithfulness. Conversely fixing L fixes R and its residue field. This identifies
   the kernel with the subgroup fixing L.
7. Apply `lem-exc-etale-galois-fixed-field-subgroup` to get Ω^I = L. The minimal
   polynomial over L divides the separable minimal polynomial over K, so Ω/L is
   separable algebraic; Ω is separably closed, hence a separable closure of L.
8. Pointwise stabilizers of finite subsets of Ω give the Krull neighbourhood bases.
   Intersecting the K-automorphism stabilizers with I gives exactly the L-automorphism
   stabilizers, proving the asserted topological identification.
9. Extend every K-embedding of L into Ω to an automorphism of Ω, as in step 5.
   Step 4 preserves L, so all conjugates lie in L; thus L/K is normal and Galois.
10. Restriction to L has kernel I and is onto. Restriction to R and extension to
    fractions are inverse. Reduction is onto by step 5 and injective by step 6.
    These give the three isomorphisms, with their displayed elementwise formulas.
-/
theorem strictHenselianFractionInertia
    {A H R κsep K Ω L : Type u}
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing H] [HenselianLocalRing H]
    [Algebra (Localization.AtPrime (maximalIdeal A)) H]
    [Algebra A H] [IsScalarTower A (Localization.AtPrime (maximalIdeal A)) H]
    (hH : Algebra.IsHenselizationAtPrime' A (maximalIdeal A) H)
    [CommRing R] [Algebra A R]
    [Field κsep] [Algebra (ResidueField A) κsep] [IsSepClosure (ResidueField A) κsep]
    [Algebra A κsep] [IsScalarTower A (ResidueField A) κsep]
    (P : Algebra.StrictHenselizationPresentationIn.{u, u} A κsep R)
    [Field K] [Algebra H K] [IsFractionRing H K]
    [Field L] [Algebra R L] [IsFractionRing R L]
    [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] :
    IsDomain H ∧ IsDomain R ∧
      Function.Injective (algebraMap A H) ∧
      ∃ _ : IsLocalRing R,
      Nonempty (R ≃+* Scheme.strictHenselizationRing
        (Spec.map (CommRingCat.ofHom
          ((algebraMap κsep (AlgebraicClosure κsep)).comp (algebraMap A κsep))))) ∧
      ∃ eκ : (Spec (.of R)).residueField (closedPoint R) ≃+* κsep,
        (∀ r : R,
          eκ (((Spec (.of R)).evaluation ⊤ (closedPoint R) trivial).hom
            ((Scheme.ΓSpecIso (.of R)).inv.hom r)) = P.residueMap r) ∧
        ∃ (_ : Algebra H R) (_ : Algebra H L) (_ : Algebra K L)
          (_ : Algebra L Ω) (_ : Algebra R Ω),
          IsScalarTower A H R ∧ IsScalarTower H R L ∧ IsScalarTower H K L ∧
          IsScalarTower K L Ω ∧ IsScalarTower R L Ω ∧
          IsLocalHom (algebraMap H R) ∧
          Function.Injective (algebraMap H R) ∧ Function.Injective (algebraMap R Ω) ∧
          IsGalois K L ∧ IsSepClosure L Ω ∧
          ∃ (act : Gal(Ω/K) →* (R ≃ₐ[H] R))
            (red : (R ≃ₐ[H] R) ≃* Gal(κsep/ResidueField A))
            (res : Gal(Ω/K) →* Gal(κsep/ResidueField A)),
            (∀ (σ : Gal(Ω/K)) (r : R), algebraMap R Ω (act σ r) = σ (algebraMap R Ω r)) ∧
            (∀ (τ : R ≃ₐ[H] R) (r : R), red τ (P.residueMap r) = P.residueMap (τ r)) ∧
            res = red.toMonoidHom.comp act ∧ Function.Surjective res ∧
            Set.range (algebraMap L Ω) = (IntermediateField.fixedField res.ker : Set Ω) ∧
            res.ker =
              (IntermediateField.adjoin K (Set.range (algebraMap L Ω))).fixingSubgroup ∧
            (∃ eI : res.ker ≃ₜ* Gal(Ω/L),
              ∀ (σ : res.ker) (a : Ω), eI σ a = σ.val a) ∧
            ∃ (q : (Gal(Ω/K) ⧸ res.ker) ≃* Gal(L/K))
              (s : Gal(L/K) ≃* (R ≃ₐ[H] R)),
              (∀ (σ : Gal(Ω/K)) (a : L),
                algebraMap L Ω (q (QuotientGroup.mk σ) a) = σ (algebraMap L Ω a)) ∧
              (∀ (τ : Gal(L/K)) (r : R), algebraMap R L (s τ r) = τ (algebraMap R L r)) := by
  sorry

end
