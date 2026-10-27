/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.Paper.CondensedQcqsPushforwardContinuity
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
import WeilConjectures.CategoryTheory.Sites.InjectiveModuleAbelianAcyclic
import WeilConjectures.CategoryTheory.Sites.CohomologyRightDerivedSections
import WeilConjectures.CategoryTheory.Abelian.RightDerived.Comp
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange
import WeilConjectures.SixFunctors.ProEtale.Comparison.CohomologicalDimension
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous

/-! # Derived sections of a module with a classical underlying abelian sheaf

This is the scalar-forgetting and classical-comparison assembly used in the finite
supported-image estimate. All derived categories and section functors are uncompleted.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

private theorem internal_injective_sections_acyclic
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (X : Scheme.{u})
    (I : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj R X))
    [Injective I] :
    (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1} ⋙
      (evaluation X.ProEtᵒᵖ Ab.{u + 1}).obj
        (Opposite.op (Scheme.ProEt.mk (𝟙 X)))).rightAcyclic I.X := by
  let J := Scheme.ProEt.topology X
  let S := InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
    J (condensedRingObj R X)
  let E₀ := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    J (condensedRingObj R X)
  let I₀ := E₀.functor.obj I
  have : Injective I₀ := (E₀.map_injective_iff I).mpr inferInstance
  let C' := ULiftHom.{u + 1} X.ProEt
  let down : C' ⥤ X.ProEt := ULiftHom.down
  let up : X.ProEt ⥤ C' := ULiftHom.up
  let J' := down.inducedTopology J
  have : down.IsEquivalence :=
    inferInstanceAs ((ULiftHom.equiv : X.ProEt ≌ C').inverse.IsEquivalence)
  have : up.IsEquivalence :=
    inferInstanceAs ((ULiftHom.equiv : X.ProEt ≌ C').functor.IsEquivalence)
  have : down.IsContinuous J' J := by dsimp [J', down]; infer_instance
  have : up.IsContinuous J J' :=
    inferInstanceAs ((ULiftHom.equiv : X.ProEt ≌ C').functor.IsContinuous J
      ((ULiftHom.equiv : X.ProEt ≌ C').inverse.inducedTopology J))
  have : (ULiftHom.equiv.symm : C' ≌ X.ProEt).functor.IsContinuous J' J :=
    inferInstanceAs (down.IsContinuous J' J)
  have : (ULiftHom.equiv.symm : C' ≌ X.ProEt).inverse.IsContinuous J J' :=
    inferInstanceAs (up.IsContinuous J J')
  let S' := (down.sheafPushforwardContinuous CommRingCat.{u + 1} J' J).obj S
  let A := (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S
  let A' := (sheafCompose J' (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S'
  let E : SheafOfModules.{u + 1} A ≌ SheafOfModules.{u + 1} A' :=
    SheafOfModules.pushforwardPushforwardEquivalence
      (ULiftHom.equiv.symm : C' ≌ X.ProEt) (𝟙 A') (𝟙 A)
      (by ext V x; change (A.obj.map (𝟙 _)).hom x = x; simp)
      (by ext V x; change (A'.obj.map (𝟙 _)).hom x = x; simp)
  let I' := E.functor.obj I₀
  have : Injective I' := (E.map_injective_iff I₀).mpr inferInstance
  have : (ULiftHom.equiv.symm : C' ≌ X.ProEt).inverse.IsDenseSubsite J J' := by
    exact inferInstanceAs ((ULiftHom.equiv : X.ProEt ≌ C').functor.IsDenseSubsite J
      ((ULiftHom.equiv : X.ProEt ≌ C').inverse.inducedTopology J))
  let B := ((ULiftHom.equiv.symm : C' ≌ X.ProEt).sheafCongr J' J Ab.{u + 1}).symm
  let T := B.functor
  have : T.Additive := by
    constructor
    intro M N f g
    ext V
    rfl
  let U := Scheme.ProEt.mk (𝟙 X)
  let F := sheafToPresheaf J Ab.{u + 1} ⋙
    (evaluation X.ProEtᵒᵖ Ab.{u + 1}).obj (Opposite.op U)
  let F' := sheafToPresheaf J' Ab.{u + 1} ⋙
    (evaluation C'ᵒᵖ Ab.{u + 1}).obj (Opposite.op (up.obj U))
  have hT (M : Sheaf J Ab.{u + 1}) [Injective M] : F'.rightAcyclic (T.obj M) := by
    have : Injective (T.obj M) := (B.map_injective_iff M).mpr inferInstance
    exact F'.rightAcyclic_of_injective _
  have eF : F ≅ T ⋙ F' := NatIso.ofComponents (fun _ ↦ Iso.refl _)
  let : HasExt.{u + 1} (Sheaf J' Ab.{u + 1}) := hasExt_of_enoughInjectives _
  intro n
  let : Subsingleton (Sheaf.H' ((SheafOfModules.toSheaf A').obj I') (n + 1)
      (up.obj U)) := injective_module_abelian_acyclic (up.obj U) I' (n + 1) (by omega)
  obtain ⟨d⟩ := Sheaf.nonempty_cohomologyPresheafFunctor_eval_iso_rightDerived
    J' (up.obj U) (n + 1)
  have hz' : IsZero (Sheaf.H' ((SheafOfModules.toSheaf A').obj I') (n + 1)
      (up.obj U)) := AddCommGrpCat.isZero_of_subsingleton _
  have hz : IsZero ((F'.rightDerived (n + 1)).obj
      ((SheafOfModules.toSheaf A').obj I')) :=
    hz'.of_iso
      (d.app ((SheafOfModules.toSheaf A').obj I')).symm
  have hobj : (SheafOfModules.toSheaf A').obj I' ≅ T.obj I.X :=
    ObjectProperty.isoMk _ (NatIso.ofComponents (fun _ ↦ Iso.refl _))
  exact (hz.of_iso ((F'.rightDerived (n + 1)).mapIso hobj).symm).of_iso
    (Functor.rightDerivedObjIsoOfIso eF (n + 1) I.X ≪≫
      Functor.compRightDerivedObjIso T F' hT (n + 1) I.X)

private def single_sections_forget_iso
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (X : Scheme.{u})
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj R X)) :
    (condensedModuleSections R X).rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj N) ≅
      (Sheaf.Γ (Scheme.ProEt.topology X) Ab.{u + 1}).rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj N.X) := by
  let T : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj R X) ⥤
      Sheaf (Scheme.ProEt.topology X) Ab.{u + 1} := Mod.forget (condensedRingObj R X)
  let F := sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1} ⋙
    (evaluation X.ProEtᵒᵖ Ab.{u + 1}).obj
      (Opposite.op (Scheme.ProEt.mk (𝟙 X)))
  let G := T ⋙ F
  let e : G ⋙ 𝟭 Ab.{u + 1} ≅ T ⋙ F := Functor.rightUnitor G
  have hi := Functor.isIso_rightDerivedFunctorPlusBaseChange_of_rightAcyclic e
    (fun I _ ↦ internal_injective_sections_acyclic R X I)
  let K := (DerivedCategory.Plus.singleFunctor _ 0).obj N
  let Q := DerivedCategory.Plus.ι (C := Ab.{u + 1})
  let c := Q.mapIso (asIso ((Functor.rightDerivedFunctorPlusBaseChange e.hom).app K))
  let d := Q.mapIso ((Functor.mapDerivedCategoryPlusIdIso Ab.{u + 1}).app
    (G.rightDerivedFunctorPlus.obj K))
  let f := Q.mapIso (F.rightDerivedFunctorPlus.mapIso
    ((T.mapDerivedCategoryPlusSingleFunctor 0).app N))
  let a : G.rightDerivedFunctor.obj ((DerivedCategory.singleFunctor _ 0).obj N) ≅
      F.rightDerivedFunctor.obj ((DerivedCategory.singleFunctor _ 0).obj N.X) :=
    (G.rightDerivedFunctorPlusCompatibility.app K).symm ≪≫ d.symm ≪≫ c ≪≫ f ≪≫
      F.rightDerivedFunctorPlusCompatibility.app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj N.X)
  let g : Sheaf.Γ (Scheme.ProEt.topology X) Ab.{u + 1} ≅ F :=
    Sheaf.ΓNatIsoSheafSections _ _ (Scheme.ProEt.isTerminalMkId X)
  exact a ≪≫ (Functor.rightDerivedFunctorNatIso g).symm.app _

/-- Classical underlying abelian sheaves have the same derived sections on both sites.
Source: Stacks Tags 03FD and 099V; Bhatt--Scholze Corollary 5.1.6.
(blueprint: lem-sfb-classical-internal-module-sections).

Proof: apply the section-action equivalence between internal modules and modules over
its reconstructed ring sheaf. This equivalence preserves the underlying abelian sheaf
and evaluation at the terminal object. The module/abelian evaluation comparison of
Tag 03FD identifies right derived evaluation of a module with evaluation of its
underlying abelian sheaf: forgotten injective modules are evaluation-acyclic, even
though they need not be injective abelian sheaves. Its bounded-below comparison with
the total right derived functor applies to a module placed in degree zero. Transport
along e. For G[0], the bounded-below classical comparison unit is invertible. Apply
etale derived sections to that unit and then the comparison Leray isomorphism. This
identifies etale derived sections of G[0] with pro-etale derived sections of its
comparison inverse image. Compose the isomorphisms in the indicated direction.
The coefficient ring may be zero, and X may be empty. No torsion hypothesis is needed.
-/
theorem classical_internal_module_sections
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (X : Scheme.{u})
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj R X))
    (G : Sheaf X.smallEtaleTopology Ab.{u + 1})
    (e : (comparisonUpperStar Ab.{u + 1} X).obj G ≅ N.X) :
    Nonempty
      ((condensedModuleSections R X).rightDerivedFunctor.obj
          ((DerivedCategory.singleFunctor _ 0).obj N) ≅
        (Etale.rightDerivedGlobalSections Ab.{u + 1} X).obj
          ((DerivedCategory.singleFunctor _ 0).obj G)) := by
  let L := comparisonUpperStar Ab.{u + 1} X
  let K := (DerivedCategory.singleFunctor _ 0).obj G
  have hK : DerivedCategory.TStructure.t.plus K := ⟨0, inferInstance⟩
  have hi := isIso_derivedComparisonAdjunction_unit_app Ab.{u + 1} X K hK
  let a := (Etale.rightDerivedGlobalSections Ab.{u + 1} X).mapIso
    (asIso ((derivedComparisonAdjunction Ab.{u + 1} X).unit.app K))
  let b := (comparisonLowerStarCompRightDerivedGlobalSectionsIso Ab.{u + 1} X).app
    (L.mapDerivedCategory.obj K)
  let c := L.mapDerivedCategorySingleFunctor 0 |>.app G
  exact ⟨single_sections_forget_iso R X N ≪≫
    (rightDerivedGlobalSections Ab.{u + 1} X).mapIso
      ((DerivedCategory.singleFunctor _ 0).mapIso e.symm ≪≫ c.symm) ≪≫ b.symm ≪≫ a.symm⟩

end AlgebraicGeometry.ProEtale
