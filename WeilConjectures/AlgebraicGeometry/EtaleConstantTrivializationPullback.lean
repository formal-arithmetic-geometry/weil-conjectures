/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
import WeilConjectures.AlgebraicGeometry.EtaleSetConstantTransportIdentity
import WeilConjectures.AlgebraicGeometry.EtaleSetConstantTransportGenerators

/-! # Extending a constant trivialization by inverse image

## References

* Stacks Project, Tags 03CB, 03CC and 0A3H
-/

@[expose] public section

universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry

/-- A constant trivialization over P extends coherently to every scheme over P
(Stacks, Tags 03CB, 03CC and 0A3H). -/
theorem etaleConstantTrivializationPullback
    (S P : Scheme.{u}) (s : P ⟶ S)
    (E : Sheaf S.smallEtaleTopology (Type (u + 1)) ⥤ Type (u + 1))
    (β : Scheme.etaleSetPullback (𝟙 P ≫ s) ≅
      E ⋙ constantSheaf P.smallEtaleTopology (Type (u + 1))) :
    ∃ α : ∀ (U : Scheme.{u}) (h : U ⟶ P),
      Scheme.etaleSetPullback (h ≫ s) ≅
        E ⋙ constantSheaf U.smallEtaleTopology (Type (u + 1)),
      α P (𝟙 P) = β ∧
      ∀ (U V : Scheme.{u}) (h : U ⟶ P) (v : V ⟶ U)
        (F : Sheaf S.smallEtaleTopology (Type (u + 1)))
        (W : U.Etale) (e : E.obj F),
        (((Classical.choose etaleSetInverseImageCompositionUnits.2.2)
          S U V (h ≫ s) v).hom.app F).hom.app
          (op ((MorphismProperty.Over.pullback @Etale ⊤ v).obj W))
          (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
            (MorphismProperty.Over.pullback @Etale ⊤ v) (Type (u + 1))
            (U.smallGrothendieckTopology @Etale)
            (V.smallGrothendieckTopology @Etale)).unit.app
              ((Scheme.etaleSetPullback (h ≫ s)).obj F)).hom.app (op W)
            (((α U h).inv.app F).hom.app (op W)
              ((toSheafify U.smallEtaleTopology
                ((Functor.const U.Etaleᵒᵖ).obj
                  (E.obj F))).app (op W) e))) =
        (((α V (v ≫ h)).inv.app F ≫
          eqToHom (congrArg
            (fun k : V ⟶ S => (Scheme.etaleSetPullback k).obj F)
            (Category.assoc v h s))).hom.app
              (op ((MorphismProperty.Over.pullback @Etale ⊤ v).obj W)))
          ((toSheafify V.smallEtaleTopology
            ((Functor.const V.Etaleᵒᵖ).obj
              (E.obj F))).app
                (op ((MorphismProperty.Over.pullback @Etale ⊤ v).obj W)) e) := by
  let c := Classical.choose etaleSetInverseImageCompositionUnits.2.2
  let β' : Scheme.etaleSetPullback s ≅
      E ⋙ constantSheaf P.smallEtaleTopology (Type (u + 1)) :=
    (eqToIso (congrArg Scheme.etaleSetPullback (Category.id_comp s))).symm ≪≫ β
  let α : ∀ (U : Scheme.{u}) (h : U ⟶ P),
      Scheme.etaleSetPullback (h ≫ s) ≅
        E ⋙ constantSheaf U.smallEtaleTopology (Type (u + 1)) := fun U h ↦
    (c S P U s h).symm ≪≫
      Functor.isoWhiskerRight β' (Scheme.etaleSetPullback h) ≪≫
      Functor.associator E _ _ ≪≫
      Functor.isoWhiskerLeft E (etaleSetConstantPullbackComparison h)
  have hα (U : Scheme.{u}) (h : U ⟶ P)
      (F : Sheaf S.smallEtaleTopology (Type (u + 1))) :
      (α U h).inv.app F =
        (etaleSetConstantPullbackComparison h).inv.app (E.obj F) ≫
          (Scheme.etaleSetPullback h).map (β'.inv.app F) ≫ (c S P U s h).hom.app F := by
    simp [α]
  refine ⟨α, ?_, ?_⟩
  · apply Iso.ext_inv
    apply NatTrans.ext
    funext F
    have hi := etaleSetConstantTransportIdentity S P s F (E.obj F) (β'.inv.app F)
    rw [hα]
    simpa [β', c] using hi
  · intro U V h v F W e
    rw [hα, hα]
    exact etaleSetConstantTransportGenerators S P U V s h v F (E.obj F) (β'.inv.app F) W e


end AlgebraicGeometry
