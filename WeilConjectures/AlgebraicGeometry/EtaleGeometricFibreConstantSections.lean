/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleGeometricFibreInverseImageConstant
import all WeilConjectures.ConstructibleSheaf.ModuleConstantOfSetPullback

/-!
# Sections on a connected geometric fibre

## References

* Stacks Project, Tags 0A3H and 03P5
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry

/-- The inverse image over a geometric point is the constant sheaf of its stalk.
Its global sections on a nonempty connected scheme are exactly the constant sections,
and further pullback preserves their values, even on an empty or disconnected scheme
(Stacks, Tags 0A3H and 03P5). -/
theorem etaleGeometricFibreConstantSections
    (S : Scheme.{u}) (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) :
    ∃ α : ∀ (U : Scheme.{u}) (h : U ⟶ Spec (.of Ω)),
      Scheme.etaleSetPullback (h ≫ s) ≅
        (Scheme.pointSmallEtale s).sheafFiber ⋙
          constantSheaf U.smallEtaleTopology (Type (u + 1)),
      α = Classical.choose (etaleGeometricFibreInverseImageConstant S Ω s) ∧
      ∀ (U : Scheme.{u}) (h : U ⟶ Spec (.of Ω)) [ConnectedSpace U]
        (F : Sheaf S.smallEtaleTopology (Type (u + 1))),
        Function.Bijective (fun e : (Scheme.pointSmallEtale s).sheafFiber.obj F =>
          ((α U h).inv.app F).hom.app (op (Scheme.Etale.mk (𝟙 U)))
            ((toSheafify U.smallEtaleTopology
              ((Functor.const U.Etaleᵒᵖ).obj
                ((Scheme.pointSmallEtale s).sheafFiber.obj F))).app
                  (op (Scheme.Etale.mk (𝟙 U))) e)) ∧
        ∀ (V : Scheme.{u}) (v : V ⟶ U)
          (e : (Scheme.pointSmallEtale s).sheafFiber.obj F),
          (((Classical.choose etaleSetInverseImageCompositionUnits.2.2)
            S U V (h ≫ s) v).hom.app F).hom.app
            (op ((MorphismProperty.Over.pullback @Etale ⊤ v).obj
              (Scheme.Etale.mk (𝟙 U))))
            (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
              (MorphismProperty.Over.pullback @Etale ⊤ v) (Type (u + 1))
              (U.smallGrothendieckTopology @Etale)
              (V.smallGrothendieckTopology @Etale)).unit.app
                ((Scheme.etaleSetPullback (h ≫ s)).obj F)).hom.app
                  (op (Scheme.Etale.mk (𝟙 U)))
              (((α U h).inv.app F).hom.app (op (Scheme.Etale.mk (𝟙 U)))
                ((toSheafify U.smallEtaleTopology
                  ((Functor.const U.Etaleᵒᵖ).obj
                    ((Scheme.pointSmallEtale s).sheafFiber.obj F))).app
                      (op (Scheme.Etale.mk (𝟙 U))) e))) =
          (((α V (v ≫ h)).inv.app F ≫
            eqToHom (congrArg
              (fun k : V ⟶ S => (Scheme.etaleSetPullback k).obj F)
              (Category.assoc v h s))).hom.app
                (op ((MorphismProperty.Over.pullback @Etale ⊤ v).obj
                  (Scheme.Etale.mk (𝟙 U)))))
            ((toSheafify V.smallEtaleTopology
              ((Functor.const V.Etaleᵒᵖ).obj
                ((Scheme.pointSmallEtale s).sheafFiber.obj F))).app
                  (op ((MorphismProperty.Over.pullback @Etale ⊤ v).obj
                    (Scheme.Etale.mk (𝟙 U)))) e) := by
  classical
  let α := Classical.choose (etaleGeometricFibreInverseImageConstant S Ω s)
  have hα := Classical.choose_spec (etaleGeometricFibreInverseImageConstant S Ω s)
  refine ⟨α, rfl, ?_⟩
  intro U h _ F
  constructor
  · have hi : Function.Bijective
        (((α U h).inv.app F).hom.app (op (Scheme.Etale.mk (𝟙 U)))) := by
      exact (CategoryTheory.isIso_iff_bijective _).1 inferInstance
    exact hi.comp (Scheme.set_constant_sections_bijective U
      ((Scheme.pointSmallEtale s).sheafFiber.obj F))
  · intro V v e
    exact hα.2 U V h v F (Scheme.Etale.mk (𝟙 U)) e

end AlgebraicGeometry
