/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition
import WeilConjectures.AlgebraicGeometry.SingleComplexOpenStalkConjugacy

/-! # Restriction of the single-complex stalk condition to a source open

## References

* [Stacks Project, Tag 0DJ8](https://stacks.math.columbia.edu/tag/0DJ8)
* [Stacks Project, Tag 0DJ9](https://stacks.math.columbia.edu/tag/0DJ9)
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Restrict the canonical stalk condition and its coefficient map to a source open.
There is no affineness, quasi-coherence, quasi-compactness or boundedness assumption. -/
theorem singleComplexStalkCondition_open
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g)
    (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (φ : (derivedPullback g').obj K ⟶ K')
    (h_stalk : SingleComplexBaseChange.StalkCondition f f' g g' sq K K' φ)
    (U : X.Opens)
    (sqU : IsPullback (pullback.snd g' U.ι) (pullback.fst g' U.ι ≫ f') (U.ι ≫ f) g) :
    let φU :=
      ((Classical.choose (Classical.choose_spec (Classical.choose_spec
        (Classical.choose_spec exists_derivedPullbackComposition))))
        (pullback.snd g' U.ι) U.ι).hom.app K ≫
      eqToHom (congrArg (fun k ↦ (derivedPullback k).obj K)
        (pullback.condition (f := g') (g := U.ι)).symm) ≫
      ((Classical.choose (Classical.choose_spec (Classical.choose_spec
        (Classical.choose_spec exists_derivedPullbackComposition))))
        (pullback.fst g' U.ι) g').inv.app K ≫
      (derivedPullback (pullback.fst g' U.ι)).map φ
    SingleComplexBaseChange.StalkCondition (U.ι ≫ f) (pullback.fst g' U.ι ≫ f')
      g (pullback.snd g' U.ι) sqU ((derivedPullback U.ι).obj K)
      ((derivedPullback (pullback.fst g' U.ι)).obj K') φU := by
  let c := Classical.choice
    (SingleComplexBaseChange.nonempty_coordinates.{u, w} g' K K' φ)
  dsimp only [SingleComplexBaseChange.StalkCondition]
  intro d z i
  let e := Classical.choice
    (SingleComplexBaseChange.nonempty_stalkComparison_open_arrow_iso.{u, w}
      f f' g g' sq K K' φ c U sqU d z i)
  have h_original := h_stalk c (pullback.fst g' U.ι z) i
  let F := forget₂ (ModuleCat.{u} (X'.presheaf.stalk (pullback.fst g' U.ι z)))
    AddCommGrpCat.{u}
  let FU := forget₂ (ModuleCat.{u} ((pullback g' U.ι).presheaf.stalk z)) AddCommGrpCat.{u}
  have h_map : IsIso (F.map
      (SingleComplexBaseChange.stalkComparison f f' g g' sq c
        (pullback.fst g' U.ι z) i)) := inferInstance
  have h_restricted := (Arrow.isIso_iff_isIso_of_isIso e.hom).mp h_map
  exact isIso_of_reflects_iso _ FU

end AlgebraicGeometry
