/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SchemeDerivedBaseChangeMap
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
import WeilConjectures.AlgebraicGeometry.RelativeMVBoundaryCompletion
import WeilConjectures.AlgebraicGeometry.RelativeMVRestrictionSquares

/-! # Canonically identified relative Mayer--Vietoris triangles

## References

* [Stacks Project, Tag 0DJ9](https://stacks.math.columbia.edu/tag/0DJ9)
* [Stacks Project, Tag 08BV](https://stacks.math.columbia.edu/tag/08BV)
* [Stacks Project, Tag 08HZ](https://stacks.math.columbia.edu/tag/08HZ)
* [Stacks Project, Tag 08HY](https://stacks.math.columbia.edu/tag/08HY)
-/

@[expose] public section

universe um wm
open CategoryTheory CategoryTheory.Limits Pretriangulated
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry

/-- Construct the two relative Mayer--Vietoris triangles with their open terms
identified by the canonical composition comparisons, and construct the morphism
whose components are exactly the given global and local base-change composites.
No local isomorphism hypothesis or global isomorphism conclusion is assumed. -/
theorem relativeMV_canonicalTriangles
    [∀ Z : Scheme.{um},
      HasDerivedCategory.{wm} (SheafOfModules.{um} (moduleRings Z.toRingedSpace))]
    {X S X' S' : Scheme.{um}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (hpull : IsPullback g' f' f g)
    [IsAffine S] [IsAffine S'] [QuasiCompact f] [QuasiSeparated f]
    (K : schemeDerivedCategory X)
    (K' : schemeDerivedCategory X')
    (φ : (derivedPullback g').obj K ⟶ K')
    (U V : X.Opens) (hcover : U ⊔ V = ⊤)
 :
    let a : X.Opens → Arrow (schemeDerivedCategory S') := fun W ↦
      Arrow.mk (schemeDerivedBaseChangeMap (W.ι ≫ f)
      (pullback.fst g' W.ι ≫ f') g (pullback.snd g' W.ι)
      (by rw [← pullback.condition_assoc, Category.assoc, hpull.w, ← Category.assoc])
      ((derivedPullback W.ι).obj K) ≫
      (schemeDerivedDirectImage (pullback.fst g' W.ι ≫ f')).map
        (((Classical.choose (Classical.choose_spec (Classical.choose_spec
          (Classical.choose_spec exists_derivedPullbackComposition))))
          (pullback.snd g' W.ι) W.ι).hom.app K ≫
        eqToHom (congrArg (fun k => (derivedPullback k).obj K)
          (pullback.condition (f := g') (g := W.ι)).symm) ≫
        ((Classical.choose (Classical.choose_spec (Classical.choose_spec
          (Classical.choose_spec exists_derivedPullbackComposition))))
          (pullback.fst g' W.ι) g').inv.app K ≫
        (derivedPullback (pullback.fst g' W.ι)).map φ))
    let aX := Arrow.mk (schemeDerivedBaseChangeMap f f' g g' hpull.w K ≫
      (schemeDerivedDirectImage f').map φ)
    ∃ (d₁ : aX.left ⟶ (a U).left ⊞ (a V).left)
      (d₂ : (a U).left ⊞ (a V).left ⟶ (a (U ⊓ V)).left)
      (d₃ : (a (U ⊓ V)).left ⟶ aX.left⟦(1 : ℤ)⟧)
      (d₁' : aX.right ⟶ (a U).right ⊞ (a V).right)
      (d₂' : (a U).right ⊞ (a V).right ⟶ (a (U ⊓ V)).right)
      (d₃' : (a (U ⊓ V)).right ⟶ aX.right⟦(1 : ℤ)⟧),
      Triangle.mk d₁ d₂ d₃ ∈ distTriang (schemeDerivedCategory S') ∧
      Triangle.mk d₁' d₂' d₃' ∈ distTriang (schemeDerivedCategory S') ∧
      ∃ t : Triangle.mk d₁ d₂ d₃ ⟶ Triangle.mk d₁' d₂' d₃',
        t.hom₁ = aX.hom ∧
        t.hom₂ = biprod.map (a U).hom (a V).hom ∧
        t.hom₃ = (a (U ⊓ V)).hom := by
  classical
  let a := relativeMVLocalArrow f f' g g' hpull K K' φ
  let aX := relativeMVGlobalArrow f f' g g' hpull K K' φ
  have h := relativeMV_boundary_completion f f' g g' hpull K K' φ
    U V hcover
  let δ := Classical.choose h
  have h' := Classical.choose_spec h
  let δ' := Classical.choose h'
  have ht := Classical.choose_spec h'
  have hs := relativeMV_restriction_squares f f' g g' hpull K K' φ U V
  let t := Triangle.homMk
    (Triangle.mk (relativeMVSourceFirst f g U V K) (relativeMVSourceSecond f g U V K) δ)
    (Triangle.mk (relativeMVTargetFirst g' f' U V K')
      (relativeMVTargetSecond g' f' U V K') δ')
    aX.hom (biprod.map (a U).hom (a V).hom) (a (U ⊓ V)).hom hs.1 hs.2 ht.2.2
  exact ⟨relativeMVSourceFirst f g U V K, relativeMVSourceSecond f g U V K, δ,
    relativeMVTargetFirst g' f' U V K', relativeMVTargetSecond g' f' U V K', δ',
    ht.1, ht.2.1, t, rfl, rfl, rfl⟩

end AlgebraicGeometry
