/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P5
-/
module

public import Sheaf.Paper.AdicStratifiedPerfectData
import Sheaf.Paper.AdicResidueLissePerfectLift
import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
import Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization

/-! Transport of lisse perfect lifting to one immersed stratum. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ZeroObject
namespace AlgebraicGeometry.Scheme

/-- Perfect models on one immersed Noetherian stratum where the residue cohomology is lisse.
This statement assumes a specified residue representative, without assuming its global
constructibility or selecting a stratification.
Source: Bhatt--Scholze, Lemma 6.6.8 and Proposition 6.6.11, forward implication.
(blueprint: lem-sfb-adic-lisse-stratum-models).

Proof: Immersion inverse image preserves limits and is exact. Apply this to the completed
ring's quotient tower, identifying its pullback with the completed ring on S by its
projections. The same restriction preserves the products, finite Koszul complexes and cone
in the Roos model of the completion unit. Hence the restricted complex is locally complete.
Comparison-pullback coherence identifies its residue with the comparison pullback of the
restriction of C. Exact restriction identifies that complex's cohomology with the assumed
lisse finite cohomology, and retains the given bounds. Since A/I is a field, exact
conservative geometric stalks show that tensor with any residue module is exact; on every
K-flat representative its total tensor computes derived tensor, giving the required uniform
Tor test. Transport these constructions to the coefficient-sized site models and apply
adicResidueLissePerfectLift on S. Pull its covering sieve back through the site equivalence.
Its complexes already have bounded finite-projective terms; switch the order of the two
term properties. The inverse equivalence transports the local isomorphisms. The canonical
constant-section maps, immersion limit comparison and scalar-extension insertion identify
the transported termwise model with the restriction of sfbCompletedModel X I P. These
comparisons hold on finite free terms and their idempotent summands, hence on every finite
projective term and its differentials. This gives exactly the asserted slice isomorphism.
An empty stratum uses its empty covering sieve; no dimension or coefficient-set finiteness
assumption is made. -/
theorem sfb_adic_lisse_stratum_models
    (X S : Scheme.{u}) [IsNoetherian X] [IsNoetherian S]
    (i : S ⟶ X) [IsImmersion i]
    (A : Type (u + 1)) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (hI : I.IsMaximal ∧ ∀ J : Ideal A, J.IsMaximal → J = I)
    [IsAdicComplete I A]
    (K : DerivedCategory (proEtaleRingModules X (adicLisseCompletedRing X I)))
    (hcomplete : IsSfbAdicComplete X I K)
    (C : CochainComplex
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (A ⧸ I ^ (0 + 1)))) ℤ)
    (a b : ℤ) (hb : ∀ q : ℤ, (q < a ∨ b < q) → IsZero (C.homology q))
    (he : Nonempty (DerivedCategory.Q.obj (sfbResidueComplex X I K) ≅
      DerivedCategory.Q.obj
        (((ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (A ⧸ I ^ (0 + 1))) X).mapHomologicalComplex (.up ℤ)).obj C)))
    (hlisse : ∀ q : ℤ, IsFiniteLocallyConstantSheaf
      ((Etale.upperStar (ModuleCat.{u + 1} (A ⧸ I ^ (0 + 1))) i).obj (C.homology q))) :
  letI := HasDerivedCategory.standard (ModuleCat.{u + 1} A)
  ∃ V : Sieve (⊤_ S.ProEt), V ∈ ProEt.topology S (⊤_ S.ProEt) ∧
    ∀ (U : S.ProEt) (f : U ⟶ ⊤_ S.ProEt), V f →
      ∃ (P : CochainComplex (ModuleCat.{u + 1} A) ℤ) (c d : ℤ),
        P.IsStrictlyGE c ∧ P.IsStrictlyLE d ∧
        (∀ q : ℤ, Module.Projective A (P.X q) ∧ Module.Finite A (P.X q)) ∧
        Nonempty (sfbLocalRestriction i (adicLisseCompletedRing X I) U K ≅
          sfbLocalRestriction i (adicLisseCompletedRing X I) U
            (sfbCompletedModel X I P)) := by sorry

end AlgebraicGeometry.Scheme
