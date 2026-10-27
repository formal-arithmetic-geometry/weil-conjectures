/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SixFunctors.OpenTensorCochainData
public import Sheaf.SixFunctors.OpenTensorRepresentativeData

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe c v r u₁ u₂ v₁ v₂
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures.SemilinearSections
namespace WeilConjectures.CoefSupportOpenTensor

variable {C : Type c} [Category.{v} C] [EssentiallySmall.{max c v r} C]
  (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{max c v r})
  (A : SemilinearSections.Closed.{c, v, r} J R) (T : SemilinearSections.Models.{c, v, r} J R A)

variable {C' : Type c} [Category.{v} C'] [EssentiallySmall.{max c v r} C']
  (J' : GrothendieckTopology C') (R' : Sheaf J' CommRingCat.{max c v r})
  (A' : SemilinearSections.Closed.{c, v, r} J' R')
  (T' : SemilinearSections.Models.{c, v, r} J' R' A')
  (F : SemilinearSections.Mod.{c, v, max c v r} J' R' ⥤
    SemilinearSections.Mod.{c, v, max c v r} J R)
  (G : SemilinearSections.Mod.{c, v, max c v r} J R ⥤
    SemilinearSections.Mod.{c, v, max c v r} J' R')
  [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  (adj : F ⊣ G)
  (H : C ⥤ C')
  (sectionPull : ∀ (N : SemilinearSections.Mod.{c, v, max c v r} J R) (V : Cᵒᵖ),
    N.val.obj V → (G.obj N).val.obj (H.op.obj V))

def canonicalProjectionMate
    {E : Type u₁} {D : Type u₂} [Category.{v₁} E] [Category.{v₂} D]
    (S : E × E ⥤ E) (T : D × D ⥤ D)
    (F : D ⥤ E) (G : E ⥤ D) (adj : F ⊣ G)
    (μ : S ⋙ G ≅ (G.prod G) ⋙ T) :
    (𝟭 D).prod G ⋙ T ⋙ F ⟶ (F.prod (𝟭 E)) ⋙ S where
  app X := (adj.homEquiv _ _).symm
    (T.map (Prod.mkHom (adj.unit.app X.1) (𝟙 _)) ≫ μ.inv.app (F.obj X.1, X.2))
  naturality := by
    intro X Y f
    apply (adj.homEquiv _ _).injective
    change adj.homEquiv _ _ (F.map (T.map (Prod.mkHom f.1 (G.map f.2))) ≫ _) =
      adj.homEquiv _ _ (_ ≫ S.map (Prod.mkHom (F.map f.1) f.2))
    rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right]
    dsimp only [Functor.prod_obj, Functor.comp_obj, Functor.id_obj]
    simp only [Equiv.apply_symm_apply]
    have hμ := μ.inv.naturality (Prod.mkHom (F.map f.1) f.2)
    change T.map (Prod.mkHom (G.map (F.map f.1)) (G.map f.2)) ≫
      μ.inv.app (F.obj Y.1, Y.2) =
      μ.inv.app (F.obj X.1, X.2) ≫ G.map (S.map (Prod.mkHom (F.map f.1) f.2)) at hμ
    rw [Category.assoc, ← hμ]
    simp only [← Category.assoc, ← T.map_comp]
    congr 2
    apply Prod.hom_ext
    · exact adj.unit.naturality f.1
    · simp


/-- The canonical adjunction-transpose projection identity on resolving pairs.
This is the chain calculation with the mate fixed by the adjunction; it omits
any arbitrary natural transformation and is strictly simpler than the final
resolving-pair theorem. Source: Stacks 0GL1, 07A4 and 06YS--06YT.
(blueprint: lem-sf-open-tensor-projection-mate-canonical).
Proof: compute the adjunct on each signed total summand from the ordinary inverse,
the restriction comparison, and the two summand formulas, then localize. -/
theorem openTensorProjection_mate_canonical
    (D : OpenTensorCochainData.{c, v, r} J R J' R' F G adj H sectionPull)
    (restriction : A.tensor ⋙ G.mapDerivedCategory ≅
      (G.mapDerivedCategory.prod G.mapDerivedCategory) ⋙ A'.tensor)
    (restrictionModel : TensorComparisonModel.{c, v, r} J J' R R' G A A' T T' restriction)
    (hordinary : restrictionModel.ordinary = D.pullTensor)
    (ambientModel : RingedDerivedTensorComparison.{c, v, r, (max c v r) + 1} J R A)
    (openModel : RingedDerivedTensorComparison.{c, v, r, (max c v r) + 1} J' R' A')
    (C : CochainComplex (SemilinearSections.Mod.{c, v, max c v r} J' R') ℤ)
    (P : CochainComplex (SemilinearSections.Mod.{c, v, max c v r} J R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P)
    (flatP : flatTerms.{c, v, r} J R P) :
      DerivedCategory.Q.map (D.chain C P).hom ≫
        F.mapDerivedCategoryFactors.inv.app ((totalTensor.{c, v, r} J' R').obj
          (C, (G.mapHomologicalComplex (.up ℤ)).obj P)) ≫
        F.mapDerivedCategory.map ((openModel C ((G.mapHomologicalComplex (.up ℤ)).obj P)
          (Or.inr (restrictionModel.kflat P hP flatP))).hom) ≫
        F.mapDerivedCategory.map (A'.tensor.map
          (Prod.mkHom (𝟙 _) (G.mapDerivedCategoryFactors.inv.app P))) ≫
        (canonicalProjectionMate A.tensor A'.tensor F.mapDerivedCategory
          G.mapDerivedCategory
          (SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction adj)
          restriction).app (DerivedCategory.Q.obj C, DerivedCategory.Q.obj P) =
    (ambientModel ((F.mapHomologicalComplex (.up ℤ)).obj C) P (Or.inr hP)).hom ≫
        A.tensor.map (Prod.mkHom (F.mapDerivedCategoryFactors.inv.app C) (𝟙 _)) := by
  sorry

end WeilConjectures.CoefSupportOpenTensor
