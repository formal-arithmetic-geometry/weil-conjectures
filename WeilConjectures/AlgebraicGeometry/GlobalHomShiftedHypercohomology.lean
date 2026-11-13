/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.GlobalDerivedHom
public import WeilConjectures.Algebra.Homology.RingedSiteZerothHypercohomology
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
import WeilConjectures.Algebra.Homology.DerivedInternalHomShiftComparison

/-! # Shift and global-section comparison for internal derived Hom

## References

* Stacks Project, Tags 08JA and 0B6A.
-/

@[expose] public section

set_option autoImplicit false
universe u w wA
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry

private noncomputable def unitToGlobalEquiv (X : Scheme.{u})
    (M : SheafOfModules.{u} (moduleRings X.toRingedSpace)) :
    (SheafOfModules.unit (moduleRings X.toRingedSpace) ⟶ M) ≃+
      M.val.obj (op ⊤) where
  toFun f := f.val.app (op ⊤)
    (1 : (moduleRings X.toRingedSpace).obj.obj (op ⊤))
  invFun x := M.unitHomEquiv.symm (M.val.sectionsMk
    (fun U ↦ M.val.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op x)
    (by
      intro U V f
      rw [← PresheafOfModules.map_comp_apply]
      congr 1))
  left_inv f := by
    apply M.unitHomEquiv.injective
    apply PresheafOfModules.sections_ext
    intro U
    simp only [Equiv.apply_symm_apply, SheafOfModules.unitHomEquiv_apply_coe]
    exact (PresheafOfModules.sections_property (M.unitHomEquiv f)
      (homOfLE (show U.unop ≤ ⊤ from le_top)).op)
  right_inv x := by
    change (M.unitHomEquiv (M.unitHomEquiv.symm _)).val (op ⊤) = x
    simp only [Equiv.apply_symm_apply]
    change M.val.map (𝟙 (op ⊤)) x = x
    simp
  map_add' f g := by rfl

private noncomputable def globalSectionsUnitIso (X : Scheme.{u}) :
    RingedSpace.globalSectionsFunctor X.toRingedSpace ⋙
        forget₂ (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))
          AddCommGrpCat.{u} ≅
      preadditiveCoyoneda.obj (op (SheafOfModules.unit (moduleRings X.toRingedSpace))) :=
  NatIso.ofComponents (fun M ↦ (unitToGlobalEquiv X M).symm.toAddCommGrpIso) (by
    intro M N f
    ext x
    apply (unitToGlobalEquiv X N).injective
    change unitToGlobalEquiv X N
      ((unitToGlobalEquiv X N).symm (f.val.app (op ⊤) x)) =
        unitToGlobalEquiv X N ((unitToGlobalEquiv X M).symm x ≫ f)
    rw [AddEquiv.apply_symm_apply]
    change _ = f.val.app (op ⊤)
      (unitToGlobalEquiv X M ((unitToGlobalEquiv X M).symm x))
    rw [AddEquiv.apply_symm_apply])

private noncomputable def globalSectionsZeroIso (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wA}
      (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))] :
    schemeDerivedGlobalSections X ⋙ DerivedCategory.homologyFunctor
        (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤))) 0 ⋙
          forget₂ (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))
            AddCommGrpCat.{u} ≅
      ringedSiteZerothHypercohomology (Opens.grothendieckTopology X) X.sheaf := by
  let A := ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤))
  let G := RingedSpace.globalSectionsFunctor X.toRingedSpace
  let U := forget₂ A AddCommGrpCat.{u}
  letI := HasDerivedCategory.standard AddCommGrpCat.{u}
  letI : IsGrothendieckAbelian.{u}
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    SheafOfModules.isGrothendieckAbelian _
  exact Functor.isoWhiskerLeft G.rightDerivedFunctor
      (U.mapDerivedCategoryHomologyFunctorIso 0) ≪≫
    Functor.isoWhiskerRight (G.rightDerivedFunctorCompMapDerivedCategoryIso U).symm
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0) ≪≫
    Functor.isoWhiskerRight (Functor.rightDerivedFunctorNatIso (globalSectionsUnitIso X))
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0)

private noncomputable def globalSectionsShiftIso (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wA}
      (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))] (k : ℤ) :
    schemeDerivedGlobalSections X ⋙ DerivedCategory.homologyFunctor
        (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤))) k ⋙
          forget₂ (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))
            AddCommGrpCat.{u} ≅
      shiftFunctor (schemeDerivedCategory X) k ⋙
        ringedSiteZerothHypercohomology (Opens.grothendieckTopology X) X.sheaf := by
  let A := ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤))
  let G := RingedSpace.globalSectionsFunctor X.toRingedSpace
  let U := forget₂ A AddCommGrpCat.{u}
  letI : IsGrothendieckAbelian.{u}
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    SheafOfModules.isGrothendieckAbelian _
  exact Functor.isoWhiskerLeft G.rightDerivedFunctor
      (Functor.isoWhiskerRight ((DerivedCategory.homologyFunctor A 0).shiftIso k 0 k
        (by simp)).symm U) ≪≫
    Functor.isoWhiskerRight (G.rightDerivedFunctor.commShiftIso k).symm
      (DerivedCategory.homologyFunctor A 0 ⋙ U) ≪≫
    Functor.isoWhiskerLeft (shiftFunctor (schemeDerivedCategory X) k) (globalSectionsZeroIso X)

/-- Cohomology of module-valued global Hom agrees with zeroth additive-group-valued
hypercohomology of the internal Hom of shifted arguments. This comparison concerns
only cohomology, not the identification with derived morphisms
(Stacks, Tags 08JA and 0B6A). -/
theorem schemeGlobalHom_shiftedHypercohomology_equiv
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (R : Type u) [Ring R], HasDerivedCategory.{wA} (ModuleCat.{u} R)]
    (X : Scheme.{u}) :
    ∃ c : ∀ (P Q : schemeDerivedCategory X) (m n : ℤ),
      ((DerivedCategory.homologyFunctor
        (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤))) (n - m)).obj
          ((schemeGlobalDerivedHom X).obj (op P, Q))) ≃+
        ((ringedSiteZerothHypercohomology (Opens.grothendieckTopology X) X.sheaf).obj
          ((derivedInternalHom (Opens.grothendieckTopology X) X.sheaf).obj
            (op (P⟦m⟧), Q⟦n⟧))),
      ∀ (P Q Q' : schemeDerivedCategory X) (m n : ℤ) (q : Q ⟶ Q')
        (x : ((DerivedCategory.homologyFunctor
          (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤))) (n - m)).obj
            ((schemeGlobalDerivedHom X).obj (op P, Q)))),
        c P Q' m n
          (((DerivedCategory.homologyFunctor
            (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤))) (n - m)).map
              ((schemeGlobalDerivedHom X).map ((𝟙 P).op, q))) x) =
          (ringedSiteZerothHypercohomology (Opens.grothendieckTopology X) X.sheaf).map
            ((derivedInternalHom (Opens.grothendieckTopology X) X.sheaf).map
              ((𝟙 (P⟦m⟧)).op, q⟦n⟧')) (c P Q m n x) := by
  classical
  have comparison := @derivedInternalHom_shift_comparison.{u, w} X.Opens _
    (Opens.grothendieckTopology X) X.sheaf
    (inferInstanceAs (HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))))
  let e := comparison.choose
  have he := comparison.choose_spec
  let H := ringedSiteZerothHypercohomology (Opens.grothendieckTopology X) X.sheaf
  let F := derivedInternalHom (Opens.grothendieckTopology X) X.sheaf
  let a (P Q : schemeDerivedCategory X) (m n : ℤ) :=
    ((globalSectionsShiftIso.{u, w, wA} X (n - m)).app (F.obj (op P, Q))).addCommGroupIsoToAddEquiv
  let b (P Q : schemeDerivedCategory X) (m n : ℤ) :=
    (H.mapIso (e P Q m n)).addCommGroupIsoToAddEquiv
  refine ⟨fun P Q m n ↦ (a P Q m n).trans (b P Q m n), ?_⟩
  intro P Q Q' m n q x
  let f := F.map (X := (op P, Q)) (Y := (op P, Q')) ((𝟙 P).op, q)
  have ha := (globalSectionsShiftIso.{u, w, wA} X (n - m)).hom.naturality f
  have ha' := congrArg (fun z ↦ z x) ha
  have hb := congrArg H.map (he P Q Q' m n q)
  simp only [Functor.map_comp] at hb
  have hb' := congrArg (fun z ↦ z (a P Q m n x)) hb
  exact (congrArg (b P Q' m n) ha').trans hb'

end AlgebraicGeometry
