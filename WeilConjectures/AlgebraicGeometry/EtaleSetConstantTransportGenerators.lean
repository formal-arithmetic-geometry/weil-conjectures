/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSetConstantPullbackComparison
public import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits
import WeilConjectures.AlgebraicGeometry.EtaleSetConstantPullbackUnitGenerators
import WeilConjectures.AlgebraicGeometry.EtaleSetConstantPullbackComposition

/-! # Composition transport on constant generators

## References

* Stacks Project, Tags 03CB, 03CC, 03P5 and 0A3H
-/

@[expose] public section

universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Maps out of constant sheaves transport compatibly with the chosen composition
comparison on every constant generator (Stacks, Tags 03CB, 03CC, 03P5, 0A3H). -/
theorem etaleSetConstantTransportGenerators
    (S P U V : Scheme.{u}) (s : P ⟶ S) (h : U ⟶ P) (v : V ⟶ U)
    (F : Sheaf S.smallEtaleTopology (Type (u + 1))) (A : Type (u + 1))
    (τ : (constantSheaf P.smallEtaleTopology (Type (u + 1))).obj A ⟶
      (Scheme.etaleSetPullback s).obj F) (W : U.Etale) (e : A) :
    (((Classical.choose etaleSetInverseImageCompositionUnits.2.2)
      S U V (h ≫ s) v).hom.app F).hom.app
      (op ((MorphismProperty.Over.pullback @Etale ⊤ v).obj W))
      (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (MorphismProperty.Over.pullback @Etale ⊤ v) (Type (u + 1))
        (U.smallGrothendieckTopology @Etale)
        (V.smallGrothendieckTopology @Etale)).unit.app
          ((Scheme.etaleSetPullback (h ≫ s)).obj F)).hom.app (op W)
        (((etaleSetConstantPullbackComparison h).inv.app A ≫
          (Scheme.etaleSetPullback h).map τ ≫
          ((Classical.choose etaleSetInverseImageCompositionUnits.2.2)
            S P U s h).hom.app F).hom.app (op W)
          ((toSheafify U.smallEtaleTopology
            ((Functor.const U.Etaleᵒᵖ).obj A)).app (op W) e))) =
      (((etaleSetConstantPullbackComparison (v ≫ h)).inv.app A ≫
        (Scheme.etaleSetPullback (v ≫ h)).map τ ≫
        ((Classical.choose etaleSetInverseImageCompositionUnits.2.2)
          S P V s (v ≫ h)).hom.app F ≫
        eqToHom (congrArg
          (fun k : V ⟶ S ↦ (Scheme.etaleSetPullback k).obj F)
          (Category.assoc v h s))).hom.app
            (op ((MorphismProperty.Over.pullback @Etale ⊤ v).obj W)))
        ((toSheafify V.smallEtaleTopology
          ((Functor.const V.Etaleᵒᵖ).obj A)).app
            (op ((MorphismProperty.Over.pullback @Etale ⊤ v).obj W)) e)  := by
  let c := Classical.choose etaleSetInverseImageCompositionUnits.2.2
  let x := (etaleSetConstantPullbackComparison h).inv.app A ≫
    (Scheme.etaleSetPullback h).map τ ≫ (c S P U s h).hom.app F
  have hn := etaleSetInverseImageCompositionUnits.2.1 U V v
    ((constantSheaf U.smallEtaleTopology (Type (u + 1))).obj A)
    ((Scheme.etaleSetPullback (h ≫ s)).obj F) x W
    ((toSheafify U.smallEtaleTopology ((Functor.const U.Etaleᵒᵖ).obj A)).app (op W) e)
  rw [hn, etaleSetConstantPullbackUnitGenerators U V v A W e]
  have hc : (etaleSetConstantPullbackComparison v).inv.app A ≫
      (Scheme.etaleSetPullback v).map x ≫ (c S U V (h ≫ s) v).hom.app F =
      (etaleSetConstantPullbackComparison (v ≫ h)).inv.app A ≫
        (Scheme.etaleSetPullback (v ≫ h)).map τ ≫
        (c S P V s (v ≫ h)).hom.app F ≫
        eqToHom (congrArg (fun k : V ⟶ S ↦ (Scheme.etaleSetPullback k).obj F)
          (Category.assoc v h s)) := by
    dsimp only [x]
    simp only [Functor.map_comp, Category.assoc]
    rw [(Classical.choose_spec etaleSetInverseImageCompositionUnits.2.2).2.2
      S P U V s h v F]
    rw [← Category.assoc ((Scheme.etaleSetPullback v).map
      ((Scheme.etaleSetPullback h).map τ))]
    rw [show (Scheme.etaleSetPullback v).map ((Scheme.etaleSetPullback h).map τ) ≫
      (c P U V h v).hom.app ((Scheme.etaleSetPullback s).obj F) =
      (c P U V h v).hom.app _ ≫ (Scheme.etaleSetPullback (v ≫ h)).map τ from
        (c P U V h v).hom.naturality τ]
    simpa only [Category.assoc] using congrArg
      (fun q ↦ q ≫ (Scheme.etaleSetPullback (v ≫ h)).map τ ≫
        (c S P V s (v ≫ h)).hom.app F ≫
        eqToHom (congrArg (fun k : V ⟶ S ↦ (Scheme.etaleSetPullback k).obj F)
          (Category.assoc v h s)))
      (etaleSetConstantPullbackComposition P U V h v A)
  have he := ConcreteCategory.congr_hom (NatTrans.congr_app
    (congrArg (fun k ↦ k.hom) hc)
    (op ((MorphismProperty.Over.pullback @Etale ⊤ v).obj W)))
      ((toSheafify V.smallEtaleTopology ((Functor.const V.Etaleᵒᵖ).obj A)).app
        (op ((MorphismProperty.Over.pullback @Etale ⊤ v).obj W)) e)
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    ConcreteCategory.comp_apply] at he
  convert he using 1
  simp only [c, ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    ConcreteCategory.comp_apply]

end AlgebraicGeometry
