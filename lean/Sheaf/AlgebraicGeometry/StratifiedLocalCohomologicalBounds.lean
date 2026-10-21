/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N7
-/
module

public import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Sheaf.AlgebraicGeometry.NoetherianStratumDetection
public import Sheaf.CategoryTheory.RingedDerivedRestrictionGeneral
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Sheaf.CategoryTheory.Sites.GeometricInverseImageExact

/-!
# Global cohomological bounds from finite stratified local bounds

Source: Bhatt--Scholze, The pro-etale topology for schemes, Proposition 6.6.11,
reverse implication (finite-stratum locality); Stacks Tags 04ZA, 0989, 04JC and 09AH.
Lemma 6.5.3 is contextual: the argument here concerns arbitrary ring sheaves.
(blueprint: lem-sfb-stratified-local-cohomological-bounds).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Local intervals on pro-etale covers of finitely many strata give a global interval.
The selected opens retain their labels in the original covering family. The lower
endpoint is a lower bound attained among the selected lower endpoints, and the upper
endpoint is an upper bound attained among the selected upper endpoints. These are
exactly the finite minimum and maximum; when there are no selected opens both are zero.
All restriction functors use the actual inverse-image ring, without scalar extension.

Source: Bhatt--Scholze, Proposition 6.6.11, reverse-implication locality argument;
Stacks Tags 04ZA, 0989, 04JC, 010N, 015F, 09AH and 09AB.
(blueprint: lem-sfb-stratified-local-cohomological-bounds).

Proof:
1. A finite affine cover by spectra of Noetherian rings makes X locally Noetherian
and quasi-compact. Every subset of a Noetherian space is quasi-compact. An immersion
is a homeomorphism onto its image, so every stratum is quasi-compact too.
2. Choose a finite affine open cover of each stratum. The pro-etale covering
condition over each affine supplies finitely many affine opens of covering members
whose images cover it. These are quasi-compact opens of the original members;
covering transitivity makes all their composites a covering of the stratum. There
are only finitely many strata, hence finitely many selected opens in total.
3. Inverse image over the actual inverse-image ring is exact. Its termwise functor
therefore commutes with cohomology, degree by degree, also for unbounded complexes.
Composition of inverse images identifies restriction to a selected open with the
further restriction from its original covering member. Thus its original interval
still bounds its cohomology.
4. Take the minimum of the finitely many selected lower bounds and the maximum of
the upper bounds. Every original lower bound is at most its upper bound, so the
minimum is at most the maximum. Outside this interval all selected restrictions
have zero cohomology. For an empty selected family put both endpoints equal to zero.
5. Apply finite-stratum detection to the underlying abelian sheaf of H^q(K).
Its inverse images on the selected covering opens vanish by steps 3 and 4, hence
it is zero. A module sheaf with zero underlying abelian sheaf is zero. This also
handles empty strata and the empty scheme via the empty-cover sheaf axiom. No
flatness of K, dimension bound, constancy or completeness of the ring is used. -/
theorem exists_global_bounds_of_stratified_local_bounds
    (X : Scheme.{u}) [IsNoetherian X] (S : FiniteLocallyClosedStratification X)
    (V : ∀ α : Fin S.n, Scheme.Cover.{w} proetalePrecoverage (S.domain α))
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (K : DerivedCategory (ringedSiteModules.{u + 1}
      ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)))
    (lower upper : ∀ α : Fin S.n, (V α).I₀ → ℤ)
    (hinterval : ∀ (α : Fin S.n) (j : (V α).I₀), lower α j ≤ upper α j)
    (hlocal : ∀ (α : Fin S.n) (j : (V α).I₀) (q : ℤ),
      q < lower α j ∨ upper α j < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj
        ((proEtaleAllRingDerivedInverseImage ((V α).f j ≫ S.immersion α)
          ((sheafCompose (ProEt.topology X)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)).obj K))) :
    ∃ (m : Fin S.n → ℕ) (label : ∀ α : Fin S.n, Fin (m α) → (V α).I₀)
      (W : ∀ (α : Fin S.n) (k : Fin (m α)), ((V α).X (label α k)).Opens),
      (∀ (α : Fin S.n) (k : Fin (m α)), IsCompact (W α k : Set ((V α).X (label α k)))) ∧
      (∀ α : Fin S.n,
        Presieve.ofArrows (fun k : Fin (m α) ↦ (W α k).toScheme)
          (fun k ↦ (W α k).ι ≫ (V α).f (label α k)) ∈ proetalePrecoverage (S.domain α)) ∧
      ∃ a b : ℤ, a ≤ b ∧
        (∀ (α : Fin S.n) (k : Fin (m α)), a ≤ lower α (label α k)) ∧
        (∀ (α : Fin S.n) (k : Fin (m α)), upper α (label α k) ≤ b) ∧
        ((∃ α : Fin S.n, Nonempty (Fin (m α))) →
          (∃ (α : Fin S.n) (k : Fin (m α)), a = lower α (label α k)) ∧
          (∃ (α : Fin S.n) (k : Fin (m α)), b = upper α (label α k))) ∧
        ((∀ α : Fin S.n, m α = 0) → a = 0 ∧ b = 0) ∧
        ∀ q : ℤ, q < a ∨ b < q →
          IsZero ((DerivedCategory.homologyFunctor _ q).obj K) := by
  sorry

end AlgebraicGeometry.Scheme
