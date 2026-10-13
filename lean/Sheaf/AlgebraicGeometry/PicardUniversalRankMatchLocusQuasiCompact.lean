module
public import Sheaf.AlgebraicGeometry.PicardUniversalRankMatch
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Sheaf.AlgebraicGeometry.PicardUniversalRankMatchFiniteRanks
import Sheaf.AlgebraicGeometry.PicardUniversalRankMatchFixedRankRetrocompact
import WeilConjectures.ConstructibleSheaf.UniversalHomeomorphism
@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
/-- The representing immersion in Tag 0BDP is quasi-compact.
Source: Stacks Project, Tag 0BDP, rank decomposition and quasi-compactness paragraphs.
(blueprint: lem-sc-picard-universal-rank-match-locus-qc)
For each affine target open, finite rank coverage reduces the image of j to a finite
union of fixed-rank point loci. Their retrocompactness makes each intersection compact.
The universal property identifies the image of j with the universal rank clause tested
on residue-field morphisms: field-valued points lift along an immersion, and a lift
places its image point in the range. The proof below establishes both inclusions of the
finite-union identity. An immersion is a topological embedding, so compactness of the
image of the inverse image is equivalent to compactness of the inverse image itself.
Mathlib's affine-open criterion then gives quasi-compactness of j.
-/
theorem picardUniversalRankMatchLocus_quasiCompact {X S W : Scheme.{u}}
    (f : X ⟶ S) [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    (E : X.Modules) [E.IsFiniteLocallyFree] (j : W ⟶ S) (hj : IsImmersion j)
    (hchar : ∀ {T : Scheme.{u}} (g : T ⟶ S),
      (∃ h : T ⟶ W, h ≫ j = g) ↔ PicardUniversalRankMatch f E g) :
    QuasiCompact j := by
  classical
  have : IsImmersion j := hj
  have hrange (s : S) : s ∈ Set.range j ↔
      PicardUniversalRankMatch f E (S.fromSpecResidueField s) := by
    constructor
    · intro hs
      apply (hchar (S.fromSpecResidueField s)).mp
      apply exists_comp_eq_of_mem_range j (S.fromSpecResidueField s)
      convert hs using 1
      exact fromSpecResidueField_apply s _
    · intro hs
      obtain ⟨h, hh⟩ := (hchar (S.fromSpecResidueField s)).mpr hs
      refine ⟨h (IsLocalRing.closedPoint (S.residueField s)), ?_⟩
      have he := congrArg (fun k : Spec (S.residueField s) ⟶ S ↦
        k (IsLocalRing.closedPoint (S.residueField s))) hh
      simpa only [Hom.comp_apply, fromSpecResidueField_apply] using he
  apply quasiCompact_iff_forall_isAffineOpen.mpr
  intro U hU
  obtain ⟨R, hR⟩ := picardUniversalRankMatch_finiteRanks f E U hU
  let K (r : ℕ) : Set S :=
    {s : S | PicardUniversalRankMatch f E (S.fromSpecResidueField s) ∧
      SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((Modules.tensorPullback (pullback.fst f (S.fromSpecResidueField s))).obj E) r}
  have hK (r : ℕ) : IsCompact (K r ∩ (U : Set S)) :=
    picardUniversalRankMatch_fixedRank_retrocompact f E r hU.isCompact U.isOpen
  have heq : j '' (j ⁻¹ᵁ U : Set W) = ⋃ r ∈ (R : Set ℕ), K r ∩ (U : Set S) := by
    ext s
    constructor
    · rintro ⟨w, hw, rfl⟩
      have hs : PicardUniversalRankMatch f E (S.fromSpecResidueField (j w)) :=
        (hrange (j w)).mp ⟨w, rfl⟩
      obtain ⟨r, hr, hrank⟩ := hR (j w) hw hs
      exact Set.mem_iUnion.mpr ⟨r, Set.mem_iUnion.mpr ⟨hr, ⟨⟨hs, hrank⟩, hw⟩⟩⟩
    · intro hs
      obtain ⟨r, hs⟩ := Set.mem_iUnion.mp hs
      obtain ⟨_, hs, hU⟩ := Set.mem_iUnion.mp hs
      obtain ⟨w, hw⟩ := (hrange s).mpr hs.1
      refine ⟨w, ?_, hw⟩
      change j w ∈ U
      rwa [hw]
  apply j.isEmbedding.isCompact_iff.mpr
  rw [heq]
  exact R.finite_toSet.isCompact_biUnion fun r _ ↦ hK r
end AlgebraicGeometry.Scheme
