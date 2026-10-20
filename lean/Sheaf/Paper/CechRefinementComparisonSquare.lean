/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D4
-/
module

public import Sheaf.Paper.CechRefinementCochainMap
public import WeilConjectures.AlgebraicGeometry.ModuleCechComparison
import Sheaf.Paper.CechRefinementResolutionDiagram

/-! # The refinement comparison square

Source: Stacks Project, Tag 01FD.
-/

@[expose] public section

universe v
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

/-- Cancel the target resolution identification in the resolution formula. -/
private theorem resolution_map_postcompose {X Y : Scheme.{v}} {f : X ⟶ Y}
    {G : Y.Modules} {F : X.Modules} {φ : G ⟶ (pushforward f).obj F}
    [EnoughInjectives X.Modules] [EnoughInjectives Y.Modules]
    [(RingedSpace.globalSectionsFunctor X.toRingedSpace).Additive]
    [(RingedSpace.globalSectionsFunctor Y.toRingedSpace).Additive]
    (D : ModuleCohomologyFMapData f G F φ) (p : ℕ) :
    D.map p ≫ (forget₂ _ AddCommGrpCat).map
        (D.I.isoRightDerivedObj (RingedSpace.globalSectionsFunctor X.toRingedSpace) p).hom =
      (forget₂ _ AddCommGrpCat).map
          (D.J.isoRightDerivedObj (RingedSpace.globalSectionsFunctor Y.toRingedSpace) p).hom ≫
        (((RingedSpace.globalSectionsComplex D.J).sc p).mapHomologyIso
          (forget₂ _ AddCommGrpCat)).inv ≫
        HomologicalComplex.homologyMap
          (((RingedSpace.globalSectionsFunctor Y.toRingedSpace ⋙
            forget₂ _ AddCommGrpCat).mapHomologicalComplex (ComplexShape.up ℕ)).map D.β) p ≫
        inv (I := D.invertible p) (HomologicalComplex.homologyMap (D.a.hom ≫
          ((RingedSpace.globalSectionsFunctor Y.toRingedSpace ⋙
            forget₂ _ AddCommGrpCat).mapHomologicalComplex (ComplexShape.up ℕ)).map D.lambda) p) ≫
        (((RingedSpace.globalSectionsComplex D.I).sc p).mapHomologyIso
          (forget₂ _ AddCommGrpCat)).hom := by
  simp only [ModuleCohomologyFMapData.map, Category.assoc,
    ← Functor.map_comp, Iso.inv_hom_id]
  rfl

/-- Refinement pullback commutes with the canonical comparison for arbitrary covers.
Source: Stacks Project, Tag 01FD, proof of Lemma 20.15.1, specialized to the
adjunction unit F → f_* f^* F
(blueprint: lem-sc-cech-refinement-comparison-square).

Proof: resolve F by J on X and f^* F by I on X'. Resolve f_* I by J' and lift
J to J' over the unit and the augmentation. Form B = Cech(U,J), B' = Cech(U,J'),
B'' = Cech(U,f_* I), and A = Cech(U',I). The specified tuple formula defines
B'' → A. The augmentation pentagon commutes by the lift equation. The squares
with global sections commute by restriction naturality. Apply homology and invert
the global-sections comparison quasi-isomorphisms. The outer diagram is the stated
square: the horizontal maps are fixed by IsModuleCechComparison and the vertical
map on module cohomology is the resolution definition of moduleCohomologyPullback.
No comparison from Cech cohomology is inverted, and no acyclicity of the cover is
assumed. Empty index sets are allowed only when the covering equation forces the
scheme to be empty; the same zero-complex diagram proves that case. -/
theorem cechRefinement_comparison_square (X X' : Scheme.{v}) (f : X' ⟶ X)
    {ι ι' : Type v} (U : ι → X.Opens) (hU : iSup U = ⊤)
    (U' : ι' → X'.Opens) (hU' : iSup U' = ⊤)
    (refine : ι' → ι) (hrefine : ∀ i, U' i ≤ f ⁻¹ᵁ U (refine i))
    (F : X.Modules) [F.IsQuasicoherent] (p : ℕ)
    (cF : ((cechComplexFunctor U).obj F.presheafModuleCat).homology p ⟶
      (RingedSpace.moduleCohomology X.toRingedSpace p).obj F)
    (hcF : IsModuleCechComparison U F p cF)
    (cF' : ((cechComplexFunctor U').obj
        ((tensorPullback f).obj F).presheafModuleCat).homology p ⟶
      (RingedSpace.moduleCohomology X'.toRingedSpace p).obj ((tensorPullback f).obj F))
    (hcF' : IsModuleCechComparison U' ((tensorPullback f).obj F) p cF')
    (gamma : ((forget₂ (ModuleCat.{v} Γ(X, ⊤)) AddCommGrpCat.{v}).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj ((cechComplexFunctor U).obj F.presheafModuleCat) ⟶
      ((forget₂ (ModuleCat.{v} Γ(X', ⊤)) AddCommGrpCat.{v}).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj
          ((cechComplexFunctor U').obj ((tensorPullback f).obj F).presheafModuleCat))
    (hgamma : IsCechRefinementMap f U U' refine hrefine F gamma)
 :
    cechRefinementHomology gamma p ≫ (forget₂ _ AddCommGrpCat).map cF' =
      (forget₂ _ AddCommGrpCat).map cF ≫ moduleCohomologyPullback f F p := by
  let : EnoughInjectives X.Modules :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
  let : (RingedSpace.globalSectionsFunctor X.toRingedSpace).Additive :=
    RingedSpace.globalSectionsFunctor_additive X.toRingedSpace
  let : EnoughInjectives X'.Modules :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives X'.toRingedSpace).2
  let : (RingedSpace.globalSectionsFunctor X'.toRingedSpace).Additive :=
    RingedSpace.globalSectionsFunctor_additive X'.toRingedSpace
  generalize hD : Classical.choice (moduleCohomologyFMapData_nonempty f F
    ((tensorPullback f).obj F)
    ((Classical.choose (exists_tensorPullbackAdjunction f)).unit.app F)) = D
  obtain ⟨t, hβ, hα⟩ := exists_cechRefinement_resolution_diagram X X' f U hU U'
    refine hrefine F p gamma hgamma D
  have : IsIso (HomologicalComplex.homologyMap (moduleCechAlpha U' D.I) p) :=
    moduleCechAlpha_isIso U' hU' D.I p
  let e := (D.I.isoRightDerivedObj
    (RingedSpace.globalSectionsFunctor X'.toRingedSpace) p).hom ≫
      HomologicalComplex.homologyMap (moduleCechAlpha U' D.I) p
  apply (cancel_mono ((forget₂ (ModuleCat.{v} Γ(X', ⊤)) AddCommGrpCat).map e)).1
  have hc := congrArg ((forget₂ _ AddCommGrpCat).map) (hcF D.J)
  have hc' := congrArg ((forget₂ _ AddCommGrpCat).map) (hcF' D.I)
  dsimp only [e]
  simp only [Functor.map_comp, Category.assoc] at hc hc' ⊢
  apply (congrArg (fun k ↦ cechRefinementHomology gamma p ≫ k) hc').trans
  apply hβ.symm.trans
  have hs := congrArg (fun k ↦ k ≫ t) hc.symm
  simp only [Category.assoc] at hs
  apply hs.trans
  have ht := congrArg (fun k ↦ (forget₂ _ AddCommGrpCat).map cF ≫
    (forget₂ (ModuleCat.{v} Γ(X, ⊤)) AddCommGrpCat).map
      (D.J.isoRightDerivedObj
        (RingedSpace.globalSectionsFunctor X.toRingedSpace) p).hom ≫ k) hα
  simp only [Category.assoc] at ht
  apply ht.trans
  have hp : moduleCohomologyPullback f F p = D.map p :=
    congrArg (fun E ↦ E.map p) hD
  have hh := congrArg (fun k ↦ (forget₂ _ AddCommGrpCat).map cF ≫ k ≫
    (forget₂ (ModuleCat.{v} Γ(X', ⊤)) AddCommGrpCat).map
      (D.I.isoRightDerivedObj
        (RingedSpace.globalSectionsFunctor X'.toRingedSpace) p).hom ≫
    (forget₂ (ModuleCat.{v} Γ(X', ⊤)) AddCommGrpCat).map
      (HomologicalComplex.homologyMap (moduleCechAlpha U' D.I) p)) hp
  apply Eq.trans ?_ hh.symm
  have hr := congrArg (fun k ↦ (forget₂ _ AddCommGrpCat).map cF ≫ k ≫
    (forget₂ (ModuleCat.{v} Γ(X', ⊤)) AddCommGrpCat).map
      (HomologicalComplex.homologyMap (moduleCechAlpha U' D.I) p))
    (resolution_map_postcompose D p).symm
  simp only [Category.assoc] at hr
  exact hr

end
end AlgebraicGeometry.Scheme.Modules
