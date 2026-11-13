/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek

import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
import WeilConjectures.AlgebraicGeometry.EtaleSectionsFilteredColimit
import WeilConjectures.AlgebraicGeometry.EtaleFilteredInjectiveAcyclic
import WeilConjectures.AlgebraicGeometry.EtaleModuleCohomologyForget
import WeilConjectures.CategoryTheory.Abelian.RightDerived.FilteredColimitSuccessor

/-!
# Filtered colimits of etale cohomology

Source: Stacks Project, Tags 03Q5, 0739 and 03FD.

The image cocone has legs induced by the original coprojections. Its colimit property
expresses that the canonical comparison map is an isomorphism, rather than merely asserting
an unspecified isomorphism between the two cohomology objects.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

private noncomputable def cohomologySingleIsoRightDerived (Y : Scheme.{u}) (q : ℕ) :
    DerivedCategory.singleFunctor (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) 0 ⋙
      Etale.cohomology AddCommGrpCat.{u + 1} Y (q : ℤ) ≅
      (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerived q := by
  let Γ := Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{u + 1}
  let H := DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} (q : ℤ)
  exact Functor.isoWhiskerLeft
      (DerivedCategory.Plus.singleFunctor (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) 0)
      (Functor.isoWhiskerRight Γ.rightDerivedFunctorPlusCompatibility.symm H) ≪≫
    Γ.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso q

private theorem abelianSectionsColimit (Y : Scheme.{u}) [CompactSpace Y]
    [QuasiSeparatedSpace Y] {I : Type u} [SmallCategory I] [IsFiltered I]
    {F : I ⥤ Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}} {c : Cocone F}
    (hc : IsColimit c) :
    Nonempty (IsColimit ((Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{u + 1}).mapCocone c)) := by
  let R := ULift.{u + 1} ℤ
  let U := ModuleCat.restrictScalars (ULift.ringEquiv (R := ℤ)).symm.toRingHom ⋙
    forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}
  let e := U.asEquivalence
  let S := sheafCompose Y.smallEtaleTopology U
  have : S.EssSurj := ⟨fun P ↦ by
    let Q := (sheafCompose Y.smallEtaleTopology e.inverse).obj P
    refine ⟨Q, ⟨?_⟩⟩
    exact ObjectProperty.isoMk _
      (Functor.isoWhiskerLeft P.obj e.counitIso)⟩
  have : S.IsEquivalence := {}
  let T := S.asEquivalence.inverse
  let G := F ⋙ T
  let d := T.mapCocone c
  have hd : IsColimit d := isColimitOfPreserves T hc
  let V : Y.Etale := Etale.mk (𝟙 Y)
  have : CompactSpace V.left := inferInstanceAs (CompactSpace Y)
  have : QuasiSeparatedSpace V.left := inferInstanceAs (QuasiSeparatedSpace Y)
  let E := (sheafSections Y.smallEtaleTopology (ModuleCat.{u + 1} R)).obj (Opposite.op V)
  have hbij := AlgebraicGeometry.etale_sections_filtered_colimit Y R V I G d hd
  have hE : IsColimit (E.mapCocone d) := by
    exact (colimit.isColimit (G ⋙ E)).ofPointIso (t := E.mapCocone d)
      (i := (ConcreteCategory.isIso_iff_bijective _).2 hbij)
  let Eab := (sheafSections Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
    (Opposite.op V)
  have hEU := isColimitOfPreserves U hE
  change IsColimit ((T ⋙ S ⋙ Eab).mapCocone c) at hEU
  have hAb := IsColimit.mapCoconeEquiv
    (Functor.isoWhiskerRight S.asEquivalence.counitIso Eab) hEU
  have hV : IsTerminal V := MorphismProperty.Over.mkIdTerminal @Etale Y
  exact ⟨IsColimit.mapCoconeEquiv
    (Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology AddCommGrpCat.{u + 1} hV).symm hAb⟩

/-- On a quasi-compact quasi-separated scheme, etale cohomology of abelian sheaves commutes
with filtered colimits, with no torsion hypothesis. (Stacks, Tags 03Q5 and 0739) -/
theorem etaleCohomology_isColimit_of_isFiltered (Y : Scheme.{u}) [CompactSpace Y]
    [QuasiSeparatedSpace Y] {I : Type u} [SmallCategory I] [IsFiltered I]
    {F : I ⥤ Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}} {c : Cocone F}
    (hc : IsColimit c) (q : ℕ) :
    Nonempty (IsColimit
      ((DerivedCategory.singleFunctor (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) 0 ⋙
        Etale.cohomology AddCommGrpCat.{u + 1} Y (q : ℤ)).mapCocone c)) :=
  by
    let Γ := Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{u + 1}
    have : HasFilteredColimitsOfSize.{u, u}
        (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
      hasFilteredColimitsOfSize_of_univLE.{u, u, u + 1, u + 1}
    have : AB5OfSize.{u, u} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
      AB5OfSize_of_univLE.{u, u, u + 1, u + 1} _
    have : HasFilteredColimitsOfSize.{u, u} AddCommGrpCat.{u + 1} :=
      hasFilteredColimitsOfSize_of_univLE.{u, u, u + 1, u + 1}
    have : AB5OfSize.{u, u} AddCommGrpCat.{u + 1} :=
      AB5OfSize_of_univLE.{u, u, u + 1, u + 1} _
    have hpres (n : ℕ) : PreservesColimitsOfShape I (Γ.rightDerived n) := by
      induction n with
      | zero =>
        have hΓ : PreservesColimitsOfShape I Γ :=
          ⟨fun {G} ↦ ⟨fun {d} hd ↦ abelianSectionsColimit Y hd⟩⟩
        exact preservesColimitsOfShape_of_natIso Γ.rightDerivedZeroIsoSelf.symm
      | succ n ih =>
        have := ih
        exact Γ.preservesColimitsOfShape_rightDerived_succ I n
          (fun J hJ ↦ isZero_rightDerived_globalSections_colimit_of_injective Y I J hJ n)
    have := hpres q
    exact ⟨IsColimit.mapCoconeEquiv (cohomologySingleIsoRightDerived Y q).symm
      (isColimitOfPreserves (Γ.rightDerived q) hc)⟩

/-- The same canonical comparison is an isomorphism for etale sheaves of modules over a
fixed constant commutative ring. (Stacks, Tags 03FD, 03CO and 03Q5) -/
theorem etaleModuleCohomology_isColimit_of_isFiltered (Y : Scheme.{u}) [CompactSpace Y]
    [QuasiSeparatedSpace Y] (Λ : Type (u + 1)) [CommRing Λ]
    {I : Type u} [SmallCategory I] [IsFiltered I]
    {F : I ⥤ Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)} {c : Cocone F}
    (hc : IsColimit c) (q : ℕ) :
    Nonempty (IsColimit
      ((DerivedCategory.singleFunctor (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0 ⋙
        Etale.cohomology (ModuleCat.{u + 1} Λ) Y (q : ℤ)).mapCocone c)) :=
  by
    let U := forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}
    let S := sheafCompose Y.smallEtaleTopology U
    have : S.IsLeftAdjoint := moduleSheafForgetIsLeftAdjoint Y Λ
    have : ReflectsColimitsOfShape I U := reflectsColimitsOfShape_of_reflectsIsomorphisms
    let H := DerivedCategory.singleFunctor
      (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0 ⋙
      Etale.cohomology (ModuleCat.{u + 1} Λ) Y (q : ℤ)
    obtain ⟨e⟩ := nonempty_etaleModuleCohomology_forgetIso Y Λ q
    have hAb := (etaleCohomology_isColimit_of_isFiltered Y
      (isColimitOfPreserves S hc) q).some
    have hU : IsColimit ((H ⋙ U).mapCocone c) :=
      IsColimit.mapCoconeEquiv e.symm hAb
    exact ⟨isColimitOfReflects U hU⟩


end AlgebraicGeometry.Scheme
