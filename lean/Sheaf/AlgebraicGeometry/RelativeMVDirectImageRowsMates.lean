/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import WeilConjectures.AlgebraicGeometry.RelativeMVMaps
public import WeilConjectures.AlgebraicGeometry.MayerVietorisImageChainData

/-! # Resolved relative rows before the overlap mate -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits CochainComplex
namespace AlgebraicGeometry

/-- Mate identities for fixed resolved rows and vertex comparisons.
Source: Stacks Project, Cohomology of Sheaves, Tags 08BV, 08HZ, 08FE and 08HY.
(blueprint: lem-pc-relative-mv-direct-image-rows-mates).

Proof: compute the global component by transposing the chosen coefficient map;
compute the two open components by naturality of the open counit squares and
biproduct extensionality; and compute the overlap component on the intersection.
-/
theorem relativeMV_direct_image_rows_mates
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (hpull : IsPullback g' f' f g)
    (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (φ : (derivedPullback g').obj K ⟶ K')
    (U V : X.Opens)
    (P : ShortComplex (CochainComplex
        (SheafOfModules.{u} (moduleRings S.toRingedSpace)) ℤ))
    (P' : ShortComplex (CochainComplex
        (SheafOfModules.{u} (moduleRings S'.toRingedSpace)) ℤ))
    (m : P ⟶ P'.map
      ((RingedSpace.moduleDirectImage g.toLRSHom.toShHom).mapHomologicalComplex (.up ℤ)))
    (e₁ : (derivedPullback g).obj (DerivedCategory.Q.obj P.X₁) ≅
      (relativeMVGlobalArrow f f' g g' hpull K K' φ).left)
    (e₂ : (derivedPullback g).obj (DerivedCategory.Q.obj P.X₂) ≅
      (relativeMVLocalArrow f f' g g' hpull K K' φ U).left ⊞
        (relativeMVLocalArrow f f' g g' hpull K K' φ V).left)
    (e₃ : (derivedPullback g).obj (DerivedCategory.Q.obj P.X₃) ≅
      (relativeMVLocalArrow f f' g g' hpull K K' φ (U ⊓ V)).left)
    (e₁' : DerivedCategory.Q.obj P'.X₁ ≅
      (relativeMVGlobalArrow f f' g g' hpull K K' φ).right)
    (e₂' : DerivedCategory.Q.obj P'.X₂ ≅
      (relativeMVLocalArrow f f' g g' hpull K K' φ U).right ⊞
        (relativeMVLocalArrow f f' g g' hpull K K' φ V).right)
    (e₃' : DerivedCategory.Q.obj P'.X₃ ≅
      (relativeMVLocalArrow f f' g g' hpull K K' φ (U ⊓ V)).right)
    :
    let η := schemeMVDirectImageLocalization g
    let adj := relativeMVAdj g
    let a := relativeMVGlobalArrow f f' g g' hpull K K' φ
    let b := relativeMVLocalArrow f f' g g' hpull K K' φ
    (DerivedCategory.Q.map m.τ₁ ≫ η.app P'.X₁ =
      (adj.homEquiv _ _) (e₁.hom ≫ a.hom ≫ e₁'.inv)) →
    (DerivedCategory.Q.map m.τ₂ ≫ η.app P'.X₂ =
      (adj.homEquiv _ _) (e₂.hom ≫ biprod.map (b U).hom (b V).hom ≫ e₂'.inv)) →
    (DerivedCategory.Q.map m.τ₃ ≫ η.app P'.X₃ =
      (adj.homEquiv _ _) (e₃.hom ≫ (b (U ⊓ V)).hom ≫ e₃'.inv)) →
    (adj.homEquiv _ _).symm (DerivedCategory.Q.map m.τ₁ ≫ η.app P'.X₁) ≫ e₁'.hom =
      e₁.hom ≫ a.hom ∧
    (adj.homEquiv _ _).symm (DerivedCategory.Q.map m.τ₂ ≫ η.app P'.X₂) ≫ e₂'.hom =
      e₂.hom ≫ biprod.map (b U).hom (b V).hom ∧
    (adj.homEquiv _ _).symm (DerivedCategory.Q.map m.τ₃ ≫ η.app P'.X₃) =
      e₃.hom ≫ (b (U ⊓ V)).hom ≫ e₃'.inv := by
  dsimp only
  intro hα hβ hγ
  constructor
  · rw [hα, Equiv.symm_apply_apply]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  constructor
  · rw [hβ, Equiv.symm_apply_apply]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · rw [hγ, Equiv.symm_apply_apply]

end AlgebraicGeometry
