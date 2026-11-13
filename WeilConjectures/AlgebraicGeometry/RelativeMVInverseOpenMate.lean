/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RelativeMVInverseOpenIso
public import WeilConjectures.AlgebraicGeometry.RelativeMVExactOpenComparison
import WeilConjectures.AlgebraicGeometry.DerivedBaseChangeHorizontal
import WeilConjectures.AlgebraicGeometry.RelativeMVOpenCoefficientTransport
import WeilConjectures.AlgebraicGeometry.DerivedBaseChangeNaturality

/-! # Pasted mate identity for the explicit inverse-open comparison

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

/-- The two-stage exact-open base-change map becomes the local base-change mate
under the explicitly constructed source and target comparisons. This is an
identity of specified morphisms; no arbitrary family of comparison isomorphisms
is quantified over. -/
theorem relativeMVInverseOpenIso_mate
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (hpull : IsPullback g' f' f g)
    (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (φ : (derivedPullback g').obj K ⟶ K') (W : X.Opens) :
    mvBaseChangeOpenMap f f' g g' hpull.w K K' φ W ≫
        (relativeMVInverseOpenIso g' f' W K').hom =
      ((derivedPullback g).mapIso (relativeMVExactOpenIso f W K)).hom ≫
        (relativeMVLocalArrow f f' g g' hpull K K' φ W).hom := by
  let E := (schemeOpenRestriction X W).mapDerivedCategory.obj K
  let F := (derivedPullback W.ι).obj K
  let c := ((mvOpenRestrictionAdjunction X W).leftAdjointUniq
    (relativeMVAdj W.ι)).hom.app K
  let p := pullback.fst g' W.ι
  let v := pullback.snd g' W.ι
  let θ := (relativeMVComp v W.ι).hom.app K ≫
    eqToHom (congrArg (fun k ↦ (derivedPullback k).obj K)
      (pullback.condition (f := g') (g := W.ι)).symm) ≫
    (relativeMVComp p g').inv.app K ≫ (derivedPullback p).map φ
  have hc := relativeMV_open_coefficient_transport g' K K' φ W
  have hn := schemeDerivedBaseChangeMap_naturality f f' g g' hpull.w
    ((schemeDerivedDirectImage W.ι).map c)
  have hp := schemeDerivedBaseChange_horizontal W.ι f p f' g g' v hpull.w
    (pullback.condition (f := g') (g := W.ι)).symm F
  simp only [mvBaseChangeOpenMap, relativeMVInverseOpenIso, relativeMVExactOpenIso,
    relativeMVLocalArrow, Arrow.mk, Arrow.hom, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom]
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc]
  simp only [Category.assoc]
  rw [hc]
  change schemeDerivedBaseChangeMap f f' g g' hpull.w
      ((schemeDerivedDirectImage W.ι).obj E) ≫
    (schemeDerivedDirectImage f').map
      ((derivedPullback g').map ((schemeDerivedDirectImage W.ι).map c) ≫
        schemeDerivedBaseChangeMap W.ι p g' v
          (pullback.condition (f := g') (g := W.ι)).symm F ≫
        (schemeDerivedDirectImage p).map θ) ≫
      (relativeMVImageComp p f').hom.app ((derivedPullback p).obj K') =
    (derivedPullback g).map ((schemeDerivedDirectImage f).map
      ((schemeDerivedDirectImage W.ι).map c) ≫ (relativeMVImageComp W.ι f).hom.app F) ≫
      schemeDerivedBaseChangeMap (W.ι ≫ f) (p ≫ f') g v _ F ≫
        (schemeDerivedDirectImage (p ≫ f')).map θ
  rw [Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc]
  rw [← Category.assoc, ← hn]
  simp only [Category.assoc]
  erw [(relativeMVImageComp p f').hom.naturality θ]
  simp only [Functor.comp_map]
  have hpt := congrArg (fun t ↦ t ≫
    (schemeDerivedDirectImage (p ≫ f')).map θ) hp
  simp only [Category.assoc] at hpt
  erw [hpt]
  simp only [E, F, c, p, v, θ, Functor.map_comp, Category.assoc]

end AlgebraicGeometry
