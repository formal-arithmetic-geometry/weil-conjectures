module

public import Sheaf.SixFunctors.IntegralDualizingRoosModel
import Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import Mathlib.Algebra.Category.ModuleCat.Colimits
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
set_option linter.style.longLine false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

private def sectionsHomEquiv
    (N : SheafOfModules (completedIntegralCoefficientSheafUnrestricted l E X)) :
    (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E X) ⟶ N) ≃+
      ((integralDualizingSections l E X).obj N) where
  toFun f := f.val.app (op (ProEt.mk (𝟙 X)))
    (1 : (completedIntegralCoefficientSheafUnrestricted l E X).obj.obj
      (op (ProEt.mk (𝟙 X))))
  invFun x := N.unitHomEquiv.symm (N.val.sectionsMk
    (fun U ↦ N.val.map ((ProEt.isTerminalMkId X).op.to U) x)
    (by
      intro U V f
      rw [← PresheafOfModules.map_comp_apply]
      exact N.val.congr_map_apply
        ((ProEt.isTerminalMkId X).op.hom_ext _ _) x))
  left_inv f := by
    apply N.unitHomEquiv.injective
    rw [Equiv.apply_symm_apply]
    apply PresheafOfModules.sections_ext
    intro U
    change N.val.map _ (f.val.app _
      (1 : (completedIntegralCoefficientSheafUnrestricted l E X).obj.obj
        (op (ProEt.mk (𝟙 X))))) = f.val.app U
      (1 : (completedIntegralCoefficientSheafUnrestricted l E X).obj.obj U)
    have hf := PresheafOfModules.naturality_apply f.val
      ((ProEt.isTerminalMkId X).op.to U)
      (1 : (completedIntegralCoefficientSheafUnrestricted l E X).obj.obj
        (op (ProEt.mk (𝟙 X))))
    change f.val.app U
        ((completedIntegralCoefficientSheafUnrestricted l E X).obj.map
          ((ProEt.isTerminalMkId X).op.to U) 1) =
      N.val.map ((ProEt.isTerminalMkId X).op.to U)
        (f.val.app (op (ProEt.mk (𝟙 X)))
          (1 : (completedIntegralCoefficientSheafUnrestricted l E X).obj.obj
            (op (ProEt.mk (𝟙 X))))) at hf
    rw [map_one] at hf
    exact hf.symm
  right_inv x := by
    change (N.unitHomEquiv (N.unitHomEquiv.symm _)).val _ = x
    rw [Equiv.apply_symm_apply]
    change N.val.map _ x = x
    have h : (ProEt.isTerminalMkId X).op.to (op (ProEt.mk (𝟙 X))) = 𝟙 _ :=
      (ProEt.isTerminalMkId X).op.hom_ext _ _
    rw [h]
    simp
  map_add' _ _ := rfl

private def sectionsHomIso :
    preadditiveCoyoneda.obj (op (SheafOfModules.unit
      (completedIntegralCoefficientSheafUnrestricted l E X))) ≅
    integralDualizingSections l E X ⋙
      forget₂ (ModuleCat.{u + 1} (integralDualizingCoefficients l E)) AddCommGrpCat :=
  NatIso.ofComponents (fun N ↦ (sectionsHomEquiv l E X N).toAddCommGrpIso)
    (by intro M N f; ext x; rfl)

/-- The zeroth cohomology of the global integral Hom object represents maps.
Source: Stacks Project, Tag 08JA, after the global-Hom comparison.
(blueprint: lem-coef-integral-dualizing-mapping-limit-hom-at-degree-zero)

The derived internal Hom followed by coefficient-point sections computes the
Hom set in degree zero. This is the degree-zero part of the global comparison,
proved by the normalized K-flat/K-injective Hom-complex construction. -/
theorem integralDualizing_global_homology_at_zero
    (M : sfIntegralConstructibleCategory l E X)
    (K : sfIntegralConstructibleCategory l E X) :
    Nonempty (((DerivedCategory.homologyFunctor
      (ModuleCat.{u + 1} (integralDualizingCoefficients l E)) 0).obj
      ((integralDualizingGlobalHom l E X M.obj).obj (Opposite.op K))) ≃+
      (K.obj ⟶ M.obj)) := by
  let R := completedIntegralCommRingSheafUnrestricted l E X
  let : IsGrothendieckAbelian.{u + 1} (scalarReductionSource l E X) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u + 1, u, u}
      (ProEt.topology X) R).1
  let : Abelian.HasKInjectiveResolutions (scalarReductionSource l E X) :=
    @Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian
      (scalarReductionSource l E X) inferInstance inferInstance
      (inferInstance : IsGrothendieckAbelian.{u + 1} (scalarReductionSource l E X))
  let : HasDerivedCategory.{u + 1}
      (ModuleCat.{u + 1} (integralDualizingCoefficients l E)) :=
    HasDerivedCategory.ofIsGrothendieckAbelian _
  let := HasDerivedCategory.standard AddCommGrpCat.{u + 1}
  let V := forget₂ (ModuleCat.{u + 1} (integralDualizingCoefficients l E)) AddCommGrpCat.{u + 1}
  let : PreservesColimitsOfSize.{0, 0} V :=
    ModuleCat.forget₂PreservesColimitsOfSize.{u + 1, u + 1, 0, 0}
      (R := integralDualizingCoefficients l E)
  let : PreservesFiniteColimits V := PreservesColimitsOfSize.preservesFiniteColimits V
  let F := integralDualizingSections l E X
  let Γ : scalarReductionSource l E X ⥤ AddCommGrpCat.{u + 1} :=
    preadditiveCoyoneda.obj (op (SheafOfModules.unit
    (completedIntegralCoefficientSheafUnrestricted l E X)))
  let b : F.rightDerivedFunctor ⋙ V.mapDerivedCategory ≅ Γ.rightDerivedFunctor :=
    (Functor.rightDerivedFunctorCompMapDerivedCategoryIso F V).symm ≪≫
      Functor.rightDerivedFunctorNatIso (sectionsHomIso l E X).symm
  let c : F.rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor
        (ModuleCat.{u + 1} (integralDualizingCoefficients l E)) 0 ⋙ V ≅
      Γ.rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} 0 :=
    Functor.isoWhiskerLeft F.rightDerivedFunctor
      (Functor.mapDerivedCategoryHomologyFunctorIso V 0) ≪≫
      Functor.isoWhiskerRight b (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} 0)
  let H := (Functor.curry.obj
    (derivedInternalHomOfUniverses.{u + 1, u, u} (ProEt.topology X) R)).obj (op K.obj)
  let t := Functor.isoWhiskerLeft H c
  obtain ⟨e, _⟩ := rhom_global_sectionsOfUniverses.{u + 1, u, u, u + 2}
    (ProEt.topology X) R
  exact ⟨(t.app M.obj).addCommGroupIsoToAddEquiv.trans (e (op K.obj, M.obj))⟩

end WeilConjectures
