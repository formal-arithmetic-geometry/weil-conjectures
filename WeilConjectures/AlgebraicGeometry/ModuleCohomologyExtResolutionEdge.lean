/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturality


public import WeilConjectures.AlgebraicGeometry.Cohomology.FlatCohomologyComparison
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturalityExtension
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtSectionDiagram

/-! # Edge compatibility for the resolution-normalized comparison

## References

* [Stacks, Tags 03FD, 01FB and 01F7]
-/

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules

private theorem common_section_diagram_cancel
    {A B C D E K : AddCommGrpCat.{u}}
    (aX : A ≅ B) (aY : C ≅ D) (bX : E ≅ B)
    (eX : A ⟶ E) (eY : C ⟶ K) (bY : K ≅ D)
    {L : AddCommGrpCat.{u}} (β : D ⟶ L) (μ : B ⟶ L) [IsIso μ]
    (hX : eX ≫ bX.hom = aX.hom) (hY : eY ≫ bY.hom = aY.hom)
    (edge : K ⟶ E) (h : bY.hom ≫ β = edge ≫ bX.hom ≫ μ) :
    (aY.hom ≫ β ≫ inv μ ≫ aX.inv) ≫ eX = eY ≫ edge := by
  rw [← cancel_mono bX.hom, Category.assoc, hX]
  rw [← cancel_mono μ]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, IsIso.inv_hom_id,
    Category.comp_id]
  rw [← h, ← Category.assoc, hY]

/-- The concrete resolution comparison intertwines the direct-image edge map.
This asserts an equality for the constructed `moduleCohomologyExtResolutionEquiv`,
not for arbitrary natural equivalences (Stacks, Tags 03FD, 01FB and 01F7). -/
theorem moduleCohomologyExtResolutionEquiv_edge
    {X Y : Scheme.{u}} (f : X ⟶ Y) (F : X.Modules) (p : ℕ)
    (x : (RingedSpace.moduleCohomology Y.toRingedSpace p).obj
      ((pushforward f).obj F)) :
    moduleCohomologyExtResolutionEquiv X F p (moduleCohomologyEdgeMap f F p x) =
      Sheaf.H.map (coeff f (𝟙 ((pushforward f).obj F))) p
        (Sheaf.H.mapFunctor (invImage f) (constIso f).symm
          ((SheafOfModules.toSheaf Y.ringCatSheaf).obj ((pushforward f).obj F)) p
          (moduleCohomologyExtResolutionEquiv Y ((pushforward f).obj F) p x)) := by
  let D := Classical.choice
    (moduleCohomologyFMapData_nonempty f ((pushforward f).obj F) F
      (𝟙 ((pushforward f).obj F)))
  let aX := ExtEdgeResolution.moduleResolutionIso X D.I p
  let aY := ExtEdgeResolution.moduleResolutionIso Y D.J p
  let bX := ExtEdgeResolution.abelianResolutionIso X D.I p
  let bY := ExtEdgeResolution.abelianResolutionIso Y D.J p
  let eX := AddCommGrpCat.ofHom
    (moduleCohomologyExtResolutionEquiv X F p).toAddMonoidHom
  let eY := AddCommGrpCat.ofHom
    (moduleCohomologyExtResolutionEquiv Y ((pushforward f).obj F) p).toAddMonoidHom
  let β := (HomologicalComplex.homologyFunctor AddCommGrpCat.{u}
    (ComplexShape.up ℕ) p).map
      (((ExtEdgeResolution.moduleSections Y).mapHomologicalComplex
        (ComplexShape.up ℕ)).map D.β)
  let μ := (HomologicalComplex.homologyFunctor AddCommGrpCat.{u}
    (ComplexShape.up ℕ) p).map (D.a.hom ≫
      ((ExtEdgeResolution.moduleSections Y).mapHomologicalComplex
        (ComplexShape.up ℕ)).map D.lambda)
  have : IsIso μ := D.invertible p
  have hX : eX ≫ bX.hom = aX.hom := by
    ext z
    exact ExtEdgeResolution.moduleCohomologyExtResolutionEquiv_normalization X D.I p z
  have hY : eY ≫ bY.hom = aY.hom := by
    ext z
    exact ExtEdgeResolution.moduleCohomologyExtResolutionEquiv_normalization Y D.J p z
  have h := common_section_diagram_cancel aX aY bX eX eY bY β μ hX hY
    (ExtEdgeResolution.abelianEdgeHom f F p)
    (ExtEdgeResolution.abelianEdge_section_diagram f F D p)
  have hm : D.map p = aY.hom ≫ β ≫ inv μ ≫ aX.inv := by
    simp only [ModuleCohomologyFMapData.map, aX, aY,
      ExtEdgeResolution.moduleResolutionIso, Iso.trans_hom, Iso.trans_inv,
      Iso.symm_hom, Iso.symm_inv, CategoryTheory.Functor.mapIso_hom,
      CategoryTheory.Functor.mapIso_inv,
      Category.assoc, β, μ]
  rw [← hm] at h
  exact congrArg (fun k ↦ k x) h

end AlgebraicGeometry.Scheme.Modules
