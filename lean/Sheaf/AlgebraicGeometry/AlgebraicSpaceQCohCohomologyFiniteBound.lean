module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceSmallRingedModel
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated
public import WeilConjectures.Mathlib.CategoryTheory.Sites.GlobalSections
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.Algebra.Category.Grp.AB
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Uniform quasi-coherent cohomology bound for a qcqs algebraic space

Source: Stacks Project, Spaces Cohomology, Tag 072C, lemma-vanishing-quasi-separated
(blueprint: lem-sfb-space-qcoh-cohomology-finite-bound).

Cohomology is the right derived abelian global-sections functor on the existing small
ringed model of the small étale site. Restriction retains the original section universe.
Global sections are compatible families on this site; no final object is assumed.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- A qcqs algebraic space has one positive bound for cohomology of every quasi-coherent
module, with no finite-generation, dimension or Noetherian hypothesis.

Source: Stacks Project, Spaces Cohomology, Tag 072C, lemma-vanishing-quasi-separated
(blueprint: lem-sfb-space-qcoh-cohomology-finite-bound).

Proof:
1. Choose an affine surjective étale atlas U → X using
   lem-sfb-qc-space-affine-etale-atlas. The result lem-sfb-space-qc-etale-fibre-bound
   bounds its geometric fibres by an integer d ≥ 1, independent of the module.
2. By lem-sfb-etale-atlas-distinct-tuple-geometry, the ordered distinct (p+1)-tuple
   schemes W_p are quasi-compact and separated, and the atlas is separated. For p ≥ d
   they are empty: a geometric point would give too many distinct fibre points.
3. The alternating spectral sequence lem-sfb-space-alternating-sign-cohomology-spectral
   supplies the quotients Q_p and their maps to X. The result
   lem-sfb-free-finite-space-quotient-separated makes Q_p absolutely separated.
   Surjectivity of W_p → Q_p makes Q_p quasi-compact, using def-a1-space-point-topology.
   A closed diagonal is quasi-compact by def-weil-closed-immersion. Choose an affine
   atlas V_p → Q_p and a positive fibre bound d_p for each p < d using step 1's results.
4. For a quasi-coherent M, the coefficient on Q_p is its pullback tensored with the
   locally constant sign line. This is quasi-coherent: on the cover trivializing the
   sign line it is the restriction of M, so use def-trf-space-quasi-coherent-module.
   Apply lem-sfb-separated-space-atlas-cohomology-bound to obtain vanishing for q ≥ d_p.
   For p ≥ d the quotient is empty, and its abelian sheaves and cohomology are zero.
5. Set C = max(1, max_{p<d}(p+d_p)). Every E₁ entry of total degree n ≥ C vanishes,
   either because p ≥ d or because n-p ≥ d_p. Every later entry, being a subquotient,
   vanishes too. The finite abutment filtration in the alternating spectral sequence
   therefore has zero successive quotients and gives Hⁿ(X,M_ab)=0.
   Compute on the equivalent small ringed model of def-sfb-space-small-ringed-model;
   compatible global sections and injective resolutions are preserved by equivalence.
   Since C ≥ 1, all integer degrees in question are nonnegative, represented by toNat. -/
theorem exists_qcoh_cohomology_finite_bound
    {S : Scheme.{u}} (X : AlgebraicSpace S)
    [CompactSpace (Point X.obj.obj)] (hqs : X.IsAbsolutelyQuasiSeparated) :
    ∃ C : ℤ, 1 ≤ C ∧ ∀ (M : X.QCoh) (q : ℤ), C ≤ q →
      IsZero (((Sheaf.Γ X.smallEtaleModelTopology AddCommGrpCat.{u}).rightDerived
        q.toNat).obj ((SheafOfModules.toSheaf X.smallStructureRings).obj
          (X.smallModuleRestriction.obj M.obj))) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
