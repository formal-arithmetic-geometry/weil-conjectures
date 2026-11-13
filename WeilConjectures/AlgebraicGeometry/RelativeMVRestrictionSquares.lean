/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RelativeMVMaps
import WeilConjectures.AlgebraicGeometry.RelativeMVRestrictionFirst
import WeilConjectures.AlgebraicGeometry.RelativeMVRestrictionSecond

/-! # Base change and the two restriction squares

## References

* [Stacks Project, Tag 08HY](https://stacks.math.columbia.edu/tag/08HY)
* [Stacks Project, Tag 08HZ](https://stacks.math.columbia.edu/tag/08HZ)
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry

/-- The canonical relative restriction units and differences commute with base change. -/
theorem relativeMV_restriction_squares
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (hpull : IsPullback g' f' f g)
    (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (φ : (derivedPullback g').obj K ⟶ K')
    (U V : X.Opens) :
    let a := relativeMVLocalArrow f f' g g' hpull K K' φ
    let aX := relativeMVGlobalArrow f f' g g' hpull K K' φ
    relativeMVSourceFirst f g U V K ≫ biprod.map (a U).hom (a V).hom =
      aX.hom ≫ relativeMVTargetFirst g' f' U V K' ∧
    relativeMVSourceSecond f g U V K ≫ (a (U ⊓ V)).hom =
      biprod.map (a U).hom (a V).hom ≫ relativeMVTargetSecond g' f' U V K' := by
  dsimp only
  constructor
  · dsimp only [relativeMVSourceFirst, relativeMVTargetFirst, relativeMVFirst, Functor.id_map]
    apply biprod.hom_ext
    · simp only [Category.assoc, biprod.map_fst, biprod.lift_fst_assoc]
      erw [biprod.lift_fst]
      exact relativeMV_restriction_unit f f' g g' hpull K K' φ U
    · simp only [Category.assoc, biprod.map_snd, biprod.lift_snd_assoc]
      erw [biprod.lift_snd]
      exact relativeMV_restriction_unit f f' g g' hpull K K' φ V
  · apply biprod.hom_ext'
    · simpa [relativeMVSourceSecond, relativeMVTargetSecond, relativeMVSecond,
        Category.assoc] using
        relativeMV_restriction_naturality f f' g g' hpull K K' φ (U ⊓ V) U inf_le_left
    · simpa [relativeMVSourceSecond, relativeMVTargetSecond, relativeMVSecond,
        Category.assoc] using congrArg Neg.neg
        (relativeMV_restriction_naturality f f' g g' hpull K K' φ (U ⊓ V) V inf_le_right)

end AlgebraicGeometry
