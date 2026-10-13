module
public import Sheaf.AlgebraicGeometry.PicardUniversalRankMatch
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Sheaf.AlgebraicGeometry.PicardUniversalSingleRankLocusFinitePresentation
import Sheaf.AlgebraicGeometry.PicardUniversalRankMatchSynchronization
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
  have : (Modules.dual E).IsFiniteLocallyFree := Modules.IsFiniteLocallyFree.dual E
  obtain ⟨W₁, j₁, hj₁, hfp₁, hW₁⟩ :=
    exists_picardUniversalSingleRankLocus_finitePresentation f E E
  obtain ⟨W₂, j₂, hj₂, hfp₂, hW₂⟩ :=
    exists_picardUniversalSingleRankLocus_finitePresentation f E (Modules.dual E)
  have : IsImmersion j₁ := hj₁
  have : IsImmersion j₂ := hj₂
  have : LocallyOfFinitePresentation j₁ := hfp₁
  have : LocallyOfFinitePresentation j₂ := hfp₂
  let j : pullback j₁ j₂ ⟶ S := pullback.fst j₁ j₂ ≫ j₁
  refine ⟨pullback j₁ j₂, j, inferInstance, inferInstance, ?_⟩
  intro T g
  have hmatch : PicardUniversalRankMatch f E g ↔
      PicardUniversalSingleRankMatch f E E g ∧
        PicardUniversalSingleRankMatch f E (Modules.dual E) g := by
    constructor
    · intro hR
      constructor
      · intro T' h t
        obtain ⟨U, ht, r, hE, _, hr⟩ := hR h t
        exact ⟨U, ht, r, hE, hr⟩
      · intro T' h t
        obtain ⟨U, ht, r, _, hd, hr⟩ := hR h t
        exact ⟨U, ht, r, hd, hr⟩
    · rintro ⟨hE, hd⟩
      exact picardUniversalRankMatch_of_singleRankMatch_without_unit f E g hE hd
  rw [hmatch]
  constructor
  · rintro ⟨h, hh⟩
    constructor
    · exact (hW₁ g).mp ⟨h ≫ pullback.fst j₁ j₂, by
        simpa only [Category.assoc] using hh⟩
    · exact (hW₂ g).mp ⟨h ≫ pullback.snd j₁ j₂, by
        rw [Category.assoc, ← pullback.condition]
        exact hh⟩
  · rintro ⟨h₁, h₂⟩
    obtain ⟨a, ha⟩ := (hW₁ g).mpr h₁
    obtain ⟨b, hb⟩ := (hW₂ g).mpr h₂
    refine ⟨pullback.lift a b (ha.trans hb.symm), ?_⟩
    dsimp only [j]
    rw [← Category.assoc, pullback.lift_fst, ha]
end AlgebraicGeometry.Scheme
