module
public import Sheaf.AlgebraicGeometry.PicardUniversalRankMatch
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Sheaf.AlgebraicGeometry.PerfectLowestCohomologyLocus
import Sheaf.AlgebraicGeometry.PerfectDirectImageBaseChange
@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
/-- Construction of a locally finitely presented immersion representing universal rank matching.
Source: Stacks Project, Tags 0BDP (rank-locus construction), 0B91 (perfect direct image
and arbitrary derived base change), and 0BDL (universal lowest-cohomology rank loci).
(blueprint: lem-sc-picard-universal-rank-match-locus-lfp-core)

Proof: Let X_r be the open-and-closed rank-r locus of E in X. Its image and the image
of its complement are open (flat local finite presentation) and closed (properness).
Let V be the open-and-closed image of X, and put S_r = V minus f(X minus X_r).
The S_r are pairwise disjoint open-and-closed subschemes; over S_r every fibre is
nonempty and E has constant rank r. A fibre with mixed ranks belongs to no S_r and
cannot satisfy the rank clause, even after extension of its residue field. The
complement of V has empty inverse image, and the condition there is rank zero.
Thus any test scheme satisfying the clause maps into the union of these components
and the empty-fibre component: apply the clause to residue fields at its points.
On S_r the perfect derived direct images of E and its dual commute with arbitrary
base change by Tag 0B91. All their base changes have no negative cohomology, so their
Tor amplitude locally begins in degree zero. Tag 0BDL, in degree zero and rank r,
gives two locally finitely presented immersions. Their fibre product represents
universal rank r for both ordinary pushforwards, by the derived base-change
comparison. The rank of pulled-back E is already r. Conversely the displayed rank
clause forces this same r on every nonempty fibre, so gives these two universal rank
conditions locally on every test scheme. Finite local freeness is local, and the
universal conditions in Tag 0BDL apply to all further base changes, including
nonreduced ones. The local representatives on amplitude charts agree uniquely on
overlaps, since immersions are monomorphisms, and these identifications satisfy the
cocycle identity. Glue them, and take their disjoint union over the S_r, together
with the empty-fibre component. This union is an immersion: locally in S it is one
of the componentwise immersions, or empty. To see the latter assertion near a mixed
fibre, use the intersection of the open images of two distinct rank loci; no S_r
meets that intersection. Local finite presentation is local on the target. The
empty-fibre component represents the vacuous pulled-back rank clause with both
pushforwards zero. Rank zero on nonempty fibres uses the zero perfect complexes;
empty test schemes satisfy the condition vacuously. This proves the claimed
universal property without a connected-fibre or structure-pushforward assumption.
-/
theorem exists_picardUniversalRankMatchLocus_finitePresentation_core
    {X S : Scheme.{u}}
    (f : X ⟶ S) [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    (E : X.Modules) [E.IsFiniteLocallyFree] :
    ∃ (W' : Scheme.{u}) (j' : W' ⟶ S),
      IsImmersion j' ∧ LocallyOfFinitePresentation j' ∧
      ∀ {T : Scheme.{u}} (g : T ⟶ S),
        (∃ h : T ⟶ W', h ≫ j' = g) ↔ PicardUniversalRankMatch f E g := by
  sorry
end AlgebraicGeometry.Scheme
