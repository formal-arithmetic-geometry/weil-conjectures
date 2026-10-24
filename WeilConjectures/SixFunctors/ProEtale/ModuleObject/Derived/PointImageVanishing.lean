/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.OverReduced
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.TopologicalInvariance

/-!

# Pullbacks along morphisms with image in a closed subscheme

Let `e : P ⟶ X` be a closed immersion of schemes over `Spec k` (for instance a rational point
`point k ⟶ X`, which is a closed immersion since `X` is separated) and `f : Y ⟶ X` a morphism
whose image lies set-theoretically in the image of `e`. If `Le^* M = 0` for some
`M : Dᵇc(X)⟦Λ⟧`, then `Lf^* M = 0`.

The morphism `f` itself need not factor through `e`, but its restriction `r ≫ f` to the reduction
`r : Y_red ⟶ Y` does, so `Lr^* Lf^* M ≅ Lg^* Le^* M = 0`. The reduction `r` is a finite
universal homeomorphism, so `Lr^*` is an equivalence by topological invariance
(`ProEtale.CondensedRing.isIso_unit_boundedConstructibleUpperStarLowerStarAdjunction`), whence
`Lf^* M = 0`.

## Main statements

- `ProEtale.CondensedRing.isZero_boundedConstructibleUpperStar_obj_of_range_subset`: for `e` a
  closed immersion and `range f ⊆ range e`, `Le^* M = 0` implies `Lf^* M = 0`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {k : Type u} [Field k]


/-- A morphism `f : Y ⟶ X` over `Spec k` whose image lies in the image of a closed immersion
`e : P ⟶ X` factors through `e` after restriction to the reduction `Y_red ⟶ Y`. -/
lemma exists_reducedι_comp_eq_of_range_subset {X Y P : Over (Spec (.of k))} (f : Y ⟶ X)
    (e : P ⟶ X) [IsClosedImmersion e.left]
    (hf : Set.range f.left.base ⊆ Set.range e.left.base) :
    ∃ g : Y.reduced ⟶ P, g ≫ e = Y.reducedι ≫ f := by
  set t := (Y.reducedι).left ≫ f.left
  have : Surjective (pullback.snd e.left t) := ⟨by
    rw [← Set.range_eq_univ, Scheme.Pullback.range_snd, Set.preimage_eq_univ_iff]
    exact (Set.range_comp_subset_range (Y.reducedι).left.base f.left.base).trans hf⟩
  have := isIso_of_isClosedImmersion_of_surjective (pullback.snd e.left t)
  have hl : (inv (pullback.snd e.left t) ≫ pullback.fst e.left t) ≫ e.left = t := by
    rw [Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]
  refine ⟨Over.homMk (inv (pullback.snd e.left t) ≫ pullback.fst e.left t) ?_,
    Over.OverMorphism.ext hl⟩
  rw [← Over.w e, ← Category.assoc, hl]
  simp [t, Over.reduced, Over.reducedι]

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  [IsFinitenessCoefficient ℓ Λ]

/-- Let `e : P ⟶ X` be a closed immersion (for instance a rational point) and `f : Y ⟶ X` a
morphism with image in the image of `e`. If `Le^* M = 0`, then `Lf^* M = 0`: the restriction of
`f` to the reduction `r : Y_red ⟶ Y` factors through `e`, and `Lr^*` is an equivalence by
topological invariance. -/
theorem isZero_boundedConstructibleUpperStar_obj_of_range_subset {X Y P : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]
    (f : Y ⟶ X) (e : P ⟶ X) [IsClosedImmersion e.left]
    (hf : Set.range f.left.base ⊆ Set.range e.left.base) (M : Dᵇc(X.left)⟦Λ⟧)
    (hM : IsZero ((boundedConstructibleUpperStar Λ ℓ e).obj M)) :
    IsZero ((boundedConstructibleUpperStar Λ ℓ f).obj M) := by
  obtain ⟨g, hg⟩ := exists_reducedι_comp_eq_of_range_subset f e hf
  set r := Y.reducedι
  have hr : IsZero ((boundedConstructibleUpperStar Λ ℓ r).obj
      ((boundedConstructibleUpperStar Λ ℓ f).obj M)) :=
    ((boundedConstructibleUpperStar Λ ℓ g).map_isZero hM).of_iso
      ((boundedConstructibleUpperStarComp Λ ℓ r f).symm.app M ≪≫ eqToIso (by rw [hg]) ≪≫
        (boundedConstructibleUpperStarComp Λ ℓ g e).app M)
  have := isIso_unit_boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ r
  exact ((boundedConstructibleLowerStar Λ ℓ r).map_isZero hr).of_iso
    (asIso ((boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ r).unit.app _))

end AlgebraicGeometry.ProEtale.CondensedRing
