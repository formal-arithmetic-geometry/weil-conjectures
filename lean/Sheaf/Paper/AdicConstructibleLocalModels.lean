/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U2
-/
module

public import Sheaf.Paper.AdicStratifiedPerfectData


/-! # Perfect local models from an adic constructible residue

Source: Bhatt--Scholze, Proposition 6.6.11, forward implication.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open scoped ZeroObject

namespace AlgebraicGeometry.Scheme

/-- A complete object with bounded constructible etale residue admits finite stratified
perfect local models.
Source: Bhatt--Scholze, Proposition 6.6.11, forward implication, and Lemma 6.6.8
(blueprint: lem-sfb-adic-constructible-local-models).

Proof: Only finitely many residue cohomology sheaves are nonzero. Intersect their finite
constructible stratifications using the actual scheme fibre products. Pullback of the
chosen local trivializations makes every cohomology sheaf locally constant of finite
type on each refined stratum; zero cohomology imposes no extra refinement. Each stratum
is Noetherian, since its immersion is locally a quotient of a Noetherian affine chart
and its underlying subspace is quasi-compact. Transport the original ringed-module
complex to the equivalent small pro-etale site. Restriction of the completion unit to
immersions and slices preserves completeness, and comparison-pullback identifies the
residue with the pullback of the restricted etale complex. Over the residue field tensor
is exact, so the same bounded interval is a Tor interval after restriction. Apply
adicResidueLissePerfectLift on each stratum. Transport its covering sieve and its local
isomorphisms back through the small-site equivalence. Its bounded finite-projective
complex is perfect by the definition of IsPerfectRingComplex, witnessed by itself.
Composition of inverse images and their finite-projection coefficient comparisons gives
exactly sfbLocalRestriction and sfbCompletedModel. Assemble the finitely many strata.
For empty X the empty cover supplies the same assertion. -/
theorem adicConstructible_localModels (X : Scheme.{u}) [IsNoetherian X]
    (A : Type (u + 1)) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (hI : I.IsMaximal ∧ ∀ J : Ideal A, J.IsMaximal → J = I)
    [IsAdicComplete I A]
    (K : DerivedCategory (proEtaleRingModules X (adicLisseCompletedRing X I)))
    (hK : IsSfbAdicConstructible X I K) :
    ∃ s : Stratification X,
      (∀ α : Fin s.n, Topology.IsConstructible (s.stratum α)) ∧
      ∀ α : Fin s.n, ∃ V : Sieve (⊤_ (s.domain α).ProEt),
        V ∈ ProEt.topology (s.domain α) (⊤_ (s.domain α).ProEt) ∧
          ∀ (U : (s.domain α).ProEt) (f : U ⟶ ⊤_ (s.domain α).ProEt), V f →
            ∃ (P : CochainComplex (ModuleCat.{u + 1} A) ℤ) (a b : ℤ),
              P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
              (∀ q : ℤ, Module.Projective A (P.X q) ∧ Module.Finite A (P.X q)) ∧
              Nonempty
                (sfbLocalRestriction (s.immersion α) (adicLisseCompletedRing X I) U K ≅
                  sfbLocalRestriction (s.immersion α) (adicLisseCompletedRing X I) U
                    (sfbCompletedModel X I P)) := by
  sorry

end AlgebraicGeometry.Scheme
