/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import WeilConjectures.AlgebraicGeometry.RelativeMVMaps
public import WeilConjectures.AlgebraicGeometry.MayerVietorisImageChainData
import Sheaf.AlgebraicGeometry.RelativeMVDirectImageRowsCore
import Sheaf.AlgebraicGeometry.RelativeMVDirectImageRowsMates

/-! # Resolved relative rows before the overlap mate -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits CochainComplex
namespace AlgebraicGeometry

/-- The resolved relative rows and the global and middle mate identities.
Source: Stacks Project, Cohomology of Sheaves, Tags 08BV, 08HZ, 08FE and 08HY;
the resolved-row construction before the overlap restriction calculation.
(blueprint: lem-pc-relative-mv-direct-image-rows-preoverlap).

Proof: choose injective-term K-injective representatives of the two coefficient
objects and resolve the direct image of the target representative. Form the
restriction Mayer--Vietoris rows, use sectionwise gluing and injective
flasqueness for short exactness, and take the homotopy pullback of the two
strict row maps. The global mate follows from the composite adjunction counit;
the middle mate follows by biproduct extensionality applied to the two open
components. The three normalized mate equations are then converted to the
displayed equations by the inverse and cancellation laws for the adjunction
equivalence. Empty and repeated opens reduce to the zero and split restriction
rows, respectively. -/
theorem relativeMV_direct_image_rows_preoverlap
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
      (e₃' : DerivedCategory.Q.obj P'.X₃ ≅ (b (U ⊓ V)).right),
      P.ShortExact ∧ P'.ShortExact ∧
      (adj.homEquiv _ _).symm (DerivedCategory.Q.map m.τ₁ ≫ η.app P'.X₁) ≫ e₁'.hom =
        e₁.hom ≫ a.hom ∧
      (adj.homEquiv _ _).symm (DerivedCategory.Q.map m.τ₂ ≫ η.app P'.X₂) ≫ e₂'.hom =
        e₂.hom ≫ biprod.map (b U).hom (b V).hom ∧
      (adj.homEquiv _ _).symm (DerivedCategory.Q.map m.τ₃ ≫ η.app P'.X₃) =
        e₃.hom ≫ (b (U ⊓ V)).hom ≫ e₃'.inv := by
  classical
  dsimp only
  obtain ⟨P, P', m, e₁, e₂, e₃, e₁', e₂', e₃', hα, hβ, hγ, hdata⟩ :=
    relativeMV_direct_image_rows_core f f' g g' hpull K K' φ U V hcover
  have hP := hdata.1
  have hP' := hdata.2
  have hm := relativeMV_direct_image_rows_mates f f' g g' hpull K K' φ U V
    P P' m e₁ e₂ e₃ e₁' e₂' e₃' hα hβ hγ
  rcases hm with ⟨h₁, h₂, h₃⟩
  exact ⟨P, P', m, e₁, e₂, e₃, e₁', e₂', e₃', hP, hP', h₁, h₂, h₃⟩

end AlgebraicGeometry
