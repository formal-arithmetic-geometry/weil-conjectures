/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Sheaf.AlgebraicGeometry.RelativeMVMaps
import Sheaf.AlgebraicGeometry.RelativeMVHomotopyPullback
public import Sheaf.AlgebraicGeometry.MayerVietorisImageChainData

/-! # Resolved relative rows before the overlap mate -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits CochainComplex
namespace AlgebraicGeometry

/-- Resolved source and target short exact rows and their vertex comparisons,
before recording the three mate equations. Source: Stacks Project, Cohomology
of Sheaves, Tags 08BV, 08HZ, 08FE and 08HY.
(blueprint: lem-pc-relative-mv-direct-image-rows-core).
Proof: Choose injective-term K-injective representatives, form the restriction
Mayer--Vietoris rows, resolve the target image, and strictify the finite diagram.
The mapping-cocone row construction supplies the short exact source row; direct
image and restriction comparisons supply the target row and all six vertex
isomorphisms. Naturality of the localization and the chosen adjunction
equivalence records the three normalized equations hα, hβ, and hγ. -/
theorem relativeMV_direct_image_rows_core
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (hpull : IsPullback g' f' f g)
    (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (φ : (derivedPullback g').obj K ⟶ K')
    (U V : X.Opens) (hcover : U ⊔ V = ⊤) :
    let G := RingedSpace.moduleDirectImage g.toLRSHom.toShHom
    let F := G.mapHomologicalComplex (.up ℤ)
    let η := schemeMVDirectImageLocalization g
    let adj := relativeMVAdj g
    let a := relativeMVGlobalArrow f f' g g' hpull K K' φ
    let b := relativeMVLocalArrow f f' g g' hpull K K' φ
    ∃ (P : ShortComplex (CochainComplex
        (SheafOfModules.{u} (moduleRings S.toRingedSpace)) ℤ))
      (P' : ShortComplex (CochainComplex
        (SheafOfModules.{u} (moduleRings S'.toRingedSpace)) ℤ))
      (m : P ⟶ P'.map F)
      (e₁ : (derivedPullback g).obj (DerivedCategory.Q.obj P.X₁) ≅ a.left)
      (e₂ : (derivedPullback g).obj (DerivedCategory.Q.obj P.X₂) ≅
        (b U).left ⊞ (b V).left)
      (e₃ : (derivedPullback g).obj (DerivedCategory.Q.obj P.X₃) ≅ (b (U ⊓ V)).left)
      (e₁' : DerivedCategory.Q.obj P'.X₁ ≅ a.right)
      (e₂' : DerivedCategory.Q.obj P'.X₂ ≅ (b U).right ⊞ (b V).right)
      (e₃' : DerivedCategory.Q.obj P'.X₃ ≅ (b (U ⊓ V)).right)
      (hα : DerivedCategory.Q.map m.τ₁ ≫ η.app P'.X₁ =
        (adj.homEquiv _ _) (e₁.hom ≫ a.hom ≫ e₁'.inv))
      (hβ : DerivedCategory.Q.map m.τ₂ ≫ η.app P'.X₂ =
        (adj.homEquiv _ _) (e₂.hom ≫ biprod.map (b U).hom (b V).hom ≫ e₂'.inv))
      (hγ : DerivedCategory.Q.map m.τ₃ ≫ η.app P'.X₃ =
        (adj.homEquiv _ _) (e₃.hom ≫ (b (U ⊓ V)).hom ≫ e₃'.inv)),
      P.ShortExact ∧ P'.ShortExact := by sorry

end AlgebraicGeometry
