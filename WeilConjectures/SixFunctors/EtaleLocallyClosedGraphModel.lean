/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition

/-! # The explicit locally closed graph model for étale compact support

The graph maps and the three constituent isomorphisms are explicit constructions. The
existence theorem supplies their properness and the specified endpoint comparison, without
choosing data from a postponed existence theorem.

## References

* [Stacks, Tag 0F7B](https://stacks.math.columbia.edu/tag/0F7B)
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

variable {X Y C U P : Scheme.{u}}
variable (a : X ⟶ U) (e : U ⟶ P) (π : P ⟶ Y) (j : X ⟶ C) (c : C ⟶ Y)
variable (h : (a ≫ e) ≫ π = j ≫ c)

/-- The map `v = (ea,j)` to `T = P ×_Y C`. -/
def locallyClosedGraphV : X ⟶ pullback π c :=
  pullback.lift (a ≫ e) j h

/-- The graph `s₁ = (v,1)` into `O₁ = T ×_C X`. -/
def locallyClosedGraphS₁ : X ⟶ pullback (pullback.snd π c) j :=
  pullback.lift (locallyClosedGraphV a e π j c h) (𝟙 X)
    (by simp [locallyClosedGraphV])

/-- The graph `s₂ = (v,a)` into `O₂ = T ×_P U`. -/
def locallyClosedGraphS₂ : X ⟶ pullback (pullback.fst π c) e :=
  pullback.lift (locallyClosedGraphV a e π j c h) a
    (by simp [locallyClosedGraphV])

/-- The common graph `s₁₂ = (s₁,s₂)` in `O₁₂ = O₁ ×_T O₂`. -/
def locallyClosedGraphS₁₂ :
    X ⟶ pullback (pullback.fst (pullback.snd π c) j)
      (pullback.fst (pullback.fst π c) e) :=
  pullback.lift (locallyClosedGraphS₁ a e π j c h) (locallyClosedGraphS₂ a e π j c h)
    (by simp [locallyClosedGraphS₁, locallyClosedGraphS₂])

variable (A : Type (u + 1)) [CommRing A] [Finite A]
variable [IsOpenImmersion j] [IsProper c] [IsProper a] [IsOpenImmersion e] [IsProper π]

/-- The specified `B₁`, inserting `Rq₁_* Rs₁_* = R(1_X)_*` and applying the Cartesian
proper/open interchange for `O₁ = T ×_C X`. -/
def locallyClosedGraphSide₁ :
    D((j)_!open[ModuleCat.{u + 1} A]) ⋙ R((c)_*[ModuleCat.{u + 1} A]) ≅
      R((locallyClosedGraphS₁ a e π j c h)_*[ModuleCat.{u + 1} A]) ⋙
        D((pullback.fst (pullback.snd π c) j)_!open[ModuleCat.{u + 1} A]) ⋙
          R((pullback.fst π c ≫ π)_*[ModuleCat.{u + 1} A]) :=
  (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight ((rightDerivedLowerStarIdIso A X).symm ≪≫
      (rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A)
        (locallyClosedGraphS₁ a e π j c h) (pullback.snd (pullback.snd π c) j)
        (𝟙 X) (by simp [locallyClosedGraphS₁])).symm) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (openImmersionLowerShriekLowerStarExchangeIso A
        (IsPullback.of_hasPullback (pullback.snd π c) j).flip) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A)
        (pullback.snd π c) c (pullback.fst π c ≫ π) pullback.condition.symm))

/-- The specified `B₂`, inserting `Rq₂_* Rs₂_* = Ra_*` and applying the Cartesian
proper/open interchange for `O₂ = T ×_P U`. -/
def locallyClosedGraphSide₂ :
    R((a)_*[ModuleCat.{u + 1} A]) ⋙ D((e)_!open[ModuleCat.{u + 1} A]) ⋙
      R((π)_*[ModuleCat.{u + 1} A]) ≅
    R((locallyClosedGraphS₂ a e π j c h)_*[ModuleCat.{u + 1} A]) ⋙
      D((pullback.fst (pullback.fst π c) e)_!open[ModuleCat.{u + 1} A]) ⋙
        R((pullback.fst π c ≫ π)_*[ModuleCat.{u + 1} A]) :=
  Functor.isoWhiskerRight (rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A)
      (locallyClosedGraphS₂ a e π j c h) (pullback.snd (pullback.fst π c) e) a
      (by simp [locallyClosedGraphS₂])).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (openImmersionLowerShriekLowerStarExchangeIso A
        (IsPullback.of_hasPullback (pullback.fst π c) e).flip) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A)
        (pullback.fst π c) π (pullback.fst π c ≫ π) rfl))

variable [IsProper (locallyClosedGraphS₁ a e π j c h)]
  [IsProper (locallyClosedGraphS₂ a e π j c h)]

/-- The specified `B₁₂`: invert the identity-top proper/open interchange over `O₁`,
compose the two open extensions, identify `b₁u₁ = b₂u₂`, split the open extensions over
`O₂`, and apply the identity-top interchange there. -/
def locallyClosedGraphMiddle :
    R((locallyClosedGraphS₁ a e π j c h)_*[ModuleCat.{u + 1} A]) ⋙
      D((pullback.fst (pullback.snd π c) j)_!open[ModuleCat.{u + 1} A]) ≅
    R((locallyClosedGraphS₂ a e π j c h)_*[ModuleCat.{u + 1} A]) ⋙
      D((pullback.fst (pullback.fst π c) e)_!open[ModuleCat.{u + 1} A]) :=
  Functor.isoWhiskerRight
      (rightDerivedLowerStarCompOpenImmersionLowerShriekIso A
        (locallyClosedGraphS₁₂ a e π j c h) _ (locallyClosedGraphS₁ a e π j c h)
        (by simp [locallyClosedGraphS₁₂])).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      ((mapDerivedCategoryOpenImmersionLowerShriekComp (ModuleCat.{u + 1} A) _ _).symm ≪≫
        mapDerivedCategoryOpenImmersionLowerShriekCongr (ModuleCat.{u + 1} A)
          pullback.condition ≪≫
        mapDerivedCategoryOpenImmersionLowerShriekComp (ModuleCat.{u + 1} A) _ _) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (rightDerivedLowerStarCompOpenImmersionLowerShriekIso A
        (locallyClosedGraphS₁₂ a e π j c h) _ (locallyClosedGraphS₂ a e π j c h)
        (by simp [locallyClosedGraphS₁₂])) _

/-- The explicit final comparison `B = B₂⁻¹ R(πp₁)_*(B₁₂) B₁`, including associators. -/
def locallyClosedGraphIso :
    D((j)_!open[ModuleCat.{u + 1} A]) ⋙ R((c)_*[ModuleCat.{u + 1} A]) ≅
      R((a)_*[ModuleCat.{u + 1} A]) ⋙ D((e)_!open[ModuleCat.{u + 1} A]) ⋙
        R((π)_*[ModuleCat.{u + 1} A]) :=
  locallyClosedGraphSide₁ a e π j c h A ≪≫ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (locallyClosedGraphMiddle a e π j c h A) _ ≪≫
    Functor.associator _ _ _ ≪≫ (locallyClosedGraphSide₂ a e π j c h A).symm

/-- The graph-model assertion, keeping the three properness witnesses and the comparison
with its specified normalization. These are the clauses of the graph-model theorem, not
an arbitrary choice of an endpoint isomorphism. -/
structure LocallyClosedGraphModel where
  [properS₁ : IsProper (locallyClosedGraphS₁ a e π j c h)]
  [properS₂ : IsProper (locallyClosedGraphS₂ a e π j c h)]
  properS₁₂ : IsProper (locallyClosedGraphS₁₂ a e π j c h)
  comparison : D((j)_!open[ModuleCat.{u + 1} A]) ⋙ R((c)_*[ModuleCat.{u + 1} A]) ≅
    R((a)_*[ModuleCat.{u + 1} A]) ⋙ D((e)_!open[ModuleCat.{u + 1} A]) ⋙
      R((π)_*[ModuleCat.{u + 1} A])
  comparison_eq : comparison = locallyClosedGraphIso a e π j c h A

/-- The proper-open-proper graph model and its explicitly normalized comparison exist
on ordinary unbounded small-étale module derived categories.
No tensor-compatibility assertion is made. -/
theorem etaleLocallyClosedGraphModel
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y C U P : Scheme.{u}} {f : X ⟶ Y}
    (a : X ⟶ U) (e : U ⟶ P) (π : P ⟶ Y) (j : X ⟶ C) (c : C ⟶ Y)
    [IsOpenImmersion j] [IsProper c] [IsProper a] [IsOpenImmersion e] [IsProper π]
    (h₁ : j ≫ c = f) (h₂ : a ≫ e ≫ π = f) :
    Nonempty (LocallyClosedGraphModel a e π j c
      ((Category.assoc a e π).trans (h₂.trans h₁.symm)) A) := by
  let h := (Category.assoc a e π).trans (h₂.trans h₁.symm)
  have : IsProper (locallyClosedGraphS₁ a e π j c h ≫
      pullback.snd (pullback.snd π c) j) := by
    simpa only [locallyClosedGraphS₁, pullback.lift_snd] using
      (inferInstance : IsProper (𝟙 X))
  have : IsProper (locallyClosedGraphS₁ a e π j c h) :=
    IsProper.of_comp _ (pullback.snd (pullback.snd π c) j)
  have : IsProper (locallyClosedGraphS₂ a e π j c h ≫
      pullback.snd (pullback.fst π c) e) := by
    simpa only [locallyClosedGraphS₂, pullback.lift_snd] using
      (inferInstance : IsProper a)
  have : IsProper (locallyClosedGraphS₂ a e π j c h) :=
    IsProper.of_comp _ (pullback.snd (pullback.fst π c) e)
  have : IsProper (locallyClosedGraphS₁₂ a e π j c h ≫
      pullback.fst (pullback.fst (pullback.snd π c) j)
        (pullback.fst (pullback.fst π c) e)) := by
    simpa only [locallyClosedGraphS₁₂, pullback.lift_fst] using
      (inferInstance : IsProper (locallyClosedGraphS₁ a e π j c h))
  have hs₁₂ : IsProper (locallyClosedGraphS₁₂ a e π j c h) :=
    IsProper.of_comp _ (pullback.fst (pullback.fst (pullback.snd π c) j)
      (pullback.fst (pullback.fst π c) e))
  exact ⟨{
    properS₁₂ := hs₁₂
    comparison := locallyClosedGraphIso a e π j c h A
    comparison_eq := rfl }⟩

end AlgebraicGeometry.Etale
