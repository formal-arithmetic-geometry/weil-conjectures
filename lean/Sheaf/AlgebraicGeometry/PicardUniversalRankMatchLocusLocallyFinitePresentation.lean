module
public import Sheaf.AlgebraicGeometry.PicardUniversalRankMatch
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusFinitePresentationIso
@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
set_option linter.style.haveILetI false in
/-- The representing immersion in Tag 0BDP is locally of finite presentation.
Source: Stacks Project, Tag 0BDP, rank decomposition and finite-presentation paragraphs.
(blueprint: lem-sc-picard-universal-rank-match-locus-lfp) -/
theorem picardUniversalRankMatchLocus_locallyOfFinitePresentation {X S W : Scheme.{u}}
    (f : X ⟶ S) [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    (E : X.Modules) [E.IsFiniteLocallyFree] (j : W ⟶ S) (hj : IsImmersion j)
    (hchar : ∀ {T : Scheme.{u}} (g : T ⟶ S),
      (∃ h : T ⟶ W, h ≫ j = g) ↔ PicardUniversalRankMatch f E g) :
    LocallyOfFinitePresentation j := by
  obtain ⟨W', j', e, hfp, he⟩ :=
    picardUniversalRankMatchLocus_exists_finitePresentation_iso f E j hj hchar
  haveI : LocallyOfFinitePresentation j' := hfp
  rw [← he]
  infer_instance
end AlgebraicGeometry.Scheme
