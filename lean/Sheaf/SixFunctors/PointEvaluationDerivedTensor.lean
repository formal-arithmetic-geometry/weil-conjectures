/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q66
-/
module
public import Sheaf.SixFunctors.PointEvaluationTensorData
public import Sheaf.SixFunctors.PointEvaluationScalarTensor

/-! Source: Stacks 0991, 03EL, 07A4
(blueprint: def-sf-point-evaluation-derived-compatibility). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] SheafOfModules.monoidalCategory
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.CochainPullback
open scoped TensorProduct ChangeOfRings
namespace AlgebraicGeometry.ProEtale.PointEvaluation
variable {k : Type u} [Field k]
  (B : Sheaf (Scheme.ProEt.topology (Spec (.of k))) CommRingCat.{u + 1})
/-- The ordinary module total tensor bifunctor, using Mathlib's signed totalization.
Source: Stacks 07A4 (blueprint: def-sf-point-evaluation-derived-compatibility). -/
abbrev moduleTotal := Functor.uncurry.obj
  ((curriedTensor (ModuleCat.{u + 1} (sectionRing k B))).map₂CochainComplex)

/-- The dependency's exact derived sections functor at fixed sizes.
Source: Stacks 07A4 (blueprint: def-sf-point-evaluation-derived-compatibility). -/
abbrev derivedSections
    [HasDerivedCategory.{u + 2} (ModuleSheaves B)]
    [HasDerivedCategory.{u + 2} (ModuleCat.{u + 1} (sectionRing k B))]
    [(pointModuleSections k B).Additive]
    [PreservesFiniteLimits (pointModuleSections k B)]
    [PreservesFiniteColimits (pointModuleSections k B)] :=
  Functor.mapDerivedCategory.{u + 2, u + 2, u + 1, u + 1, u + 2, u + 2}
    (C₁ := ModuleSheaves B) (C₂ := ModuleCat.{u + 1} (sectionRing k B))
    (pointModuleSections k B)

/-- Its specified localization comparison.
Source: Stacks 07A4 (blueprint: def-sf-point-evaluation-derived-compatibility). -/
abbrev derivedSectionsFactors
    [HasDerivedCategory.{u + 2} (ModuleSheaves B)]
    [HasDerivedCategory.{u + 2} (ModuleCat.{u + 1} (sectionRing k B))]
    [(pointModuleSections k B).Additive]
    [PreservesFiniteLimits (pointModuleSections k B)]
    [PreservesFiniteColimits (pointModuleSections k B)] :=
  Functor.mapDerivedCategoryFactors.{u + 2, u + 2, u + 1, u + 1, u + 2, u + 2}
    (C₁ := ModuleSheaves B) (C₂ := ModuleCat.{u + 1} (sectionRing k B))
    (pointModuleSections k B)

/-- The representative square characterizing the canonical derived comparison.
Both tensor presentations are arbitrary, so uniqueness includes independence of models.
Source: Stacks 07A4, 06YY (blueprint: def-sf-point-evaluation-derived-compatibility). -/
def DerivedCompatible (T : TensorModel B)
    [HasDerivedCategory.{u + 2} (ModuleSheaves B)]
    [HasDerivedCategory.{u + 2} (ModuleCat.{u + 1} (sectionRing k B))]
    [(pointModuleSections k B).Additive]
    [PreservesFiniteLimits (pointModuleSections k B)]
    [PreservesFiniteColimits (pointModuleSections k B)] : Prop :=
  (∀ (L : DerivedCategory (ModuleSheaves B) ⥤
        DerivedCategory (ModuleCat.{u + 1} (sectionRing k B)))
    (e : DerivedCategory.Q (C := ModuleSheaves B) ⋙ L ⟶ complexSections k B ⋙
      DerivedCategory.Q (C := ModuleCat.{u + 1} (sectionRing k B))),
    L.IsLeftDerivedFunctor e (HomologicalComplex.quasiIso (ModuleSheaves B) (.up ℤ)) →
    ∃ η : L ≅ (derivedSections B),
      e = Functor.whiskerLeft DerivedCategory.Q η.hom ≫
        (derivedSectionsFactors B).hom) ∧
  (∀ (S : DerivedCategory (ModuleSheaves B) × DerivedCategory (ModuleSheaves B) ⥤
      DerivedCategory (ModuleSheaves B))
    (rS : ((resolving B).ι.prod (resolving B).ι) ⋙
      SheafOfModules.KFlatTotalTensorModel.total B ⋙ DerivedCategory.Q ≅
      (((resolving B).ι ⋙ DerivedCategory.Q).prod
        ((resolving B).ι ⋙ DerivedCategory.Q)) ⋙ S)
    (U : DerivedCategory (ModuleCat.{u + 1} (sectionRing k B)) ×
      DerivedCategory (ModuleCat.{u + 1} (sectionRing k B)) ⥤
        DerivedCategory (ModuleCat.{u + 1} (sectionRing k B)))
    (r : ((moduleResolving B).ι.prod (moduleResolving B).ι) ⋙ moduleTotal B ⋙
      DerivedCategory.Q ≅
      (((moduleResolving B).ι ⋙ DerivedCategory.Q).prod
        ((moduleResolving B).ι ⋙ DerivedCategory.Q)) ⋙ U),
    ∃! α : S ⋙ (derivedSections B) ≅
        ((derivedSections B).prod
          (derivedSections B)) ⋙ U,
      ∀ (P Q : Complexes B) (hP : resolving B P) (hQ : resolving B Q),
        (derivedSections B).map
            (rS.hom.app (⟨P, hP⟩, ⟨Q, hQ⟩)) ≫
          α.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
          U.map (Prod.mkHom
            ((derivedSectionsFactors B).hom.app P)
            ((derivedSectionsFactors B).hom.app Q)) =
        (derivedSectionsFactors B).hom.app (totalObj B P Q) ≫
          DerivedCategory.Q.map (T.b P Q).hom ≫
          r.hom.app (⟨(complexSections k B).obj P, T.preserves_resolving P hP⟩,
            ⟨(complexSections k B).obj Q, T.preserves_resolving Q hQ⟩))


/-- The scalar comparison after localization, uniquely fixed by the balanced chain map.
This quantifies all derived presentations with their representative maps.
Source: Stacks 03EL, 07A4 (blueprint: def-sf-point-evaluation-derived-compatibility). -/
def ScalarDerivedCompatible
    {B' : Sheaf (Scheme.ProEt.topology (Spec (.of k))) CommRingCat.{u + 1}}
    (a : B ⟶ B') (T : TensorModel B) (T' : TensorModel B') (S : ScalarModel a T T')
    [HasDerivedCategory.{u + 2} (ModuleSheaves B)]
    [HasDerivedCategory.{u + 2} (ModuleSheaves B')]
    [HasDerivedCategory.{u + 2} (ModuleCat.{u + 1} (sectionRing k B))]
    [HasDerivedCategory.{u + 2} (ModuleCat.{u + 1} (sectionRing k B'))]
    [(pointModuleSections k B).Additive] [(pointModuleSections k B').Additive]
    [PreservesFiniteLimits (pointModuleSections k B)]
    [PreservesFiniteColimits (pointModuleSections k B)]
    [PreservesFiniteLimits (pointModuleSections k B')]
    [PreservesFiniteColimits (pointModuleSections k B')] : Prop :=
  ∀ (LS : DerivedCategory (ModuleSheaves B) ⥤ DerivedCategory (ModuleSheaves B'))
    (LM : DerivedCategory (ModuleCat.{u + 1} (sectionRing k B)) ⥤
      DerivedCategory (ModuleCat.{u + 1} (sectionRing k B')))
    (eS : (resolving B).ι ⋙ DerivedCategory.Q ⋙ LS ≅
      (resolving B).ι ⋙ extend.{u + 1, u + 1, u} a ⋙ DerivedCategory.Q)
    (eM : (moduleResolving B).ι ⋙ DerivedCategory.Q ⋙ LM ≅
      (moduleResolving B).ι ⋙ moduleExtend B a ⋙ DerivedCategory.Q),
    ∃! δ : LS ⋙ derivedSections B' ≅ derivedSections B ⋙ LM,
      ∀ (P : Complexes B) (hP : resolving B P),
        (derivedSections B').map (eS.hom.app ⟨P, hP⟩) ≫
            (derivedSectionsFactors B').hom.app ((extend.{u + 1, u + 1, u} a).obj P) ≫
            DerivedCategory.Q.map (S.κ.hom.app P) =
          δ.hom.app (DerivedCategory.Q.obj P) ≫
            LM.map ((derivedSectionsFactors B).hom.app P) ≫
            eM.hom.app ⟨(complexSections k B).obj P, T.preserves_resolving P hP⟩

end AlgebraicGeometry.ProEtale.PointEvaluation
