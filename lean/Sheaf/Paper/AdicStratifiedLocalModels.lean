/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P5
-/
module

public import Sheaf.Paper.AdicStratifiedPerfectData
import Sheaf.Paper.AdicLisseStratumModels
import WeilConjectures.ConstructibleSheaf.Refinement
import WeilConjectures.ConstructibleSheaf.OpenClosed
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-!
# Local perfect models from the residue stratification

Source: Bhatt--Scholze, Definition 6.5.1, Remark 6.3.2 and Proposition 6.6.11.
(blueprint: lem-sfb-adic-stratified-local-models).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open scoped ZeroObject
namespace AlgebraicGeometry.Scheme

private theorem common_cohomology_stratification
    (X : Scheme.{u}) (k : Type (u + 1)) [CommRing k]
    (C : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} k)) ℤ)
    (hc : ∀ q : ℤ, IsConstructibleSheaf (C.homology q)) (t : Finset ℤ) :
    ∃ s : LocallyClosedStratification X, ∀ q ∈ t, ∀ α : Fin s.n,
      IsFiniteLocallyConstantSheaf
        ((Etale.upperStar (ModuleCat.{u + 1} k) (s.immersion α)).obj (C.homology q)) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      exact ⟨Stratification.trivial X, by simp⟩
  | @insert q t hqt ih =>
      have := hc q
      obtain ⟨s, hs⟩ := IsConstructibleSheaf.exists_stratification
        (FA := fun M N : ModuleCat.{u + 1} k ↦ M →ₗ[k] N)
        (CA := fun M : ModuleCat.{u + 1} k ↦ M) (F := C.homology q)
      obtain ⟨r, hr⟩ := ih
      refine ⟨s.inter r, ?_⟩
      intro n hn α
      rcases Finset.mem_insert.mp hn with rfl | hn
      · exact (s.inter_refines_left r).isFiniteLocallyConstantSheaf_upperStar
          (C.homology n) hs α
      · exact (s.inter_refines_right r).isFiniteLocallyConstantSheaf_upperStar
          (C.homology n) (hr n hn) α

private theorem bounded_cohomology_stratification
    (X : Scheme.{u}) (k : Type (u + 1)) [CommRing k]
    (C : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} k)) ℤ)
    (a b : ℤ) (hb : ∀ q : ℤ, (q < a ∨ b < q) → IsZero (C.homology q))
    (hc : ∀ q : ℤ, IsConstructibleSheaf (C.homology q)) :
    ∃ s : LocallyClosedStratification X, ∀ q : ℤ, ∀ α : Fin s.n,
      IsFiniteLocallyConstantSheaf
        ((Etale.upperStar (ModuleCat.{u + 1} k) (s.immersion α)).obj (C.homology q)) := by
  classical
  obtain ⟨s, hs⟩ := common_cohomology_stratification X k C hc (Finset.Icc a b)
  refine ⟨s, fun q α ↦ ?_⟩
  by_cases hq : q ∈ Finset.Icc a b
  · exact hs q hq α
  · apply IsFiniteLocallyConstantSheaf.of_isZero
    exact (Etale.upperStar (ModuleCat.{u + 1} k) (s.immersion α)).map_isZero
      (hb q (by simpa only [Finset.mem_Icc, not_and_or, not_le] using hq))

/-- A complete complex with bounded constructible etale residue has finite immersed
strata with bounded finite-projective coefficient models. Perfectness of the
coefficient model is left to the caller, which has the explicit representative.

Source: Bhatt--Scholze, Proposition 6.6.11, forward direction and Lemma 6.6.8.
(blueprint: lem-sfb-adic-stratified-local-models).

Proof: Choose the bounded etale witness C. Refine the constructible stratifications
of its finitely many nonzero cohomology sheaves by fibre-product immersions. The
strata are Noetherian, since their constructible images are quasi-compact and
the immersions are locally quotients of open Noetherian affine charts. Restrict
completed coefficients to each stratum using immersion limit preservation. Slice
restriction preserves products, finite Koszul complexes and their Roos triangles;
therefore it preserves the completion unit. Comparison-pullback identifies the
restricted residue with the pullback of C restricted to the stratum. Transport
these objects through the equivalent coefficient-sized site models. Exact stalks
identify degree-zero tensor cohomology with tensor of vector spaces over A/I;
this preserves the bounded interval and gives the Tor test on all K-flat models.
Apply adicResidueLissePerfectLift on each stratum. Transport its covering sieve,
finite-projective complex, bounds and local isomorphism back to the original
sites. The normalized coefficient comparisons identify its termwise realization
with sfbCompletedModel restricted from X. The empty scheme uses the empty
stratification; no bound or coefficient finiteness assumption is added. -/
theorem sfb_adic_stratified_local_models
    (X : Scheme.{u}) [IsNoetherian X]
    (A : Type (u + 1)) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (hI : I.IsMaximal ∧ ∀ J : Ideal A, J.IsMaximal → J = I)
    [IsAdicComplete I A]
    (K : DerivedCategory (proEtaleRingModules X (adicLisseCompletedRing X I)))
    (hK : IsSfbAdicConstructible X I K) :
  letI := HasDerivedCategory.standard (ModuleCat.{u + 1} A)
  ∃ s : LocallyClosedStratification X,
    (∀ α : Fin s.n, Topology.IsConstructible (s.stratum α)) ∧
    ∀ α : Fin s.n, ∃ V : Sieve (⊤_ (s.domain α).ProEt),
      V ∈ ProEt.topology (s.domain α) (⊤_ (s.domain α).ProEt) ∧
        ∀ (U : (s.domain α).ProEt) (f : U ⟶ ⊤_ (s.domain α).ProEt), V f →
          ∃ (P : CochainComplex (ModuleCat.{u + 1} A) ℤ) (a b : ℤ),
            P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
            (∀ q : ℤ, Module.Projective A (P.X q) ∧ Module.Finite A (P.X q)) ∧
            Nonempty (sfbLocalRestriction (s.immersion α) (adicLisseCompletedRing X I) U K ≅
              sfbLocalRestriction (s.immersion α) (adicLisseCompletedRing X I) U
                (sfbCompletedModel X I P))  := by
  obtain ⟨hcomplete, C, ⟨a, b, hab, hb⟩, hc, he, ht⟩ := hK
  obtain ⟨s, hs⟩ := bounded_cohomology_stratification X (A ⧸ I ^ (0 + 1)) C a b hb hc
  refine ⟨s, s.isConstructible_stratum, ?_⟩
  intro α
  have : TopologicalSpace.NoetherianSpace (s.domain α) :=
    (s.immersion α).isEmbedding.noetherianSpace
  have : IsLocallyNoetherian (s.domain α) :=
    LocallyOfFiniteType.isLocallyNoetherian (s.immersion α)
  have : IsNoetherian (s.domain α) := {}
  exact sfb_adic_lisse_stratum_models X (s.domain α) (s.immersion α) A I hI K
    hcomplete C a b hb he (fun q ↦ hs q α)

end AlgebraicGeometry.Scheme
