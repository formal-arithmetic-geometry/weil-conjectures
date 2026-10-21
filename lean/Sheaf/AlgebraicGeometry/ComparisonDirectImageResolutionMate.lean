/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate
public import Sheaf.Paper.ComparisonGlobalResolutionModel
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison


/-!
# The restriction transpose on direct-image resolutions

Source: blueprint main-20261015, prop-pur-gm-relative-kummer.proof.md, opening
paragraph; Stacks Project Tags 099R, 0B65 and 0FND
(blueprint: lem-pur-comparison-direct-image-resolution-mate).

The helpers specify the actual chain maps and the augmentation-normalized resolution
identifications. The statement includes the chain identity, the fixed derived mate,
its derived transpose, and evaluation on arbitrary terminal sections in every degree.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u vC vD uC uD

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

variable (Λ : Type (u + 1)) [CommRing Λ] {U V : Scheme.{u}} (f : U ⟶ V)
variable (I : CochainComplex.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
variable (J : CochainComplex.Plus (Sheaf (Scheme.ProEt.topology U) (ModuleCat.{u + 1} Λ)))
variable (t : ((comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapHomologicalComplex
  (.up ℤ)).obj I.obj ⟶ J.obj)

/-- The chain adjunct `h` of the supplied comparison resolution map.
Source: Stacks Tags 099R and 0B65; blueprint resolution refinement
(blueprint: lem-pur-comparison-direct-image-resolution-mate). -/
noncomputable def comparisonResolutionAdjunct :
    I.obj ⟶ ((comparisonLowerStar (ModuleCat.{u + 1} Λ) U).mapHomologicalComplex
      (.up ℤ)).obj J.obj :=
  ((comparisonAdjunction (ModuleCat.{u + 1} Λ) U).mapHomologicalComplex
    (.up ℤ)).homEquiv I.obj J.obj t

/-- The chain map `k = δ⁻¹ ∘ u_* h`, using the restriction identity on both sites.
Source: Stacks Tags 099R and 0B65; blueprint resolution refinement
(blueprint: lem-pur-comparison-direct-image-resolution-mate). -/
noncomputable def comparisonResolutionRestriction :
    ((Etale.lowerStar (ModuleCat.{u + 1} Λ) f).mapHomologicalComplex (.up ℤ)).obj I.obj ⟶
      ((comparisonLowerStar (ModuleCat.{u + 1} Λ) V).mapHomologicalComplex (.up ℤ)).obj
        (((lowerStar (ModuleCat.{u + 1} Λ) f).mapHomologicalComplex (.up ℤ)).obj J.obj) :=
  ((Etale.lowerStar (ModuleCat.{u + 1} Λ) f).mapHomologicalComplex (.up ℤ)).map
      (comparisonResolutionAdjunct Λ I J t) ≫
    (NatTrans.mapHomologicalComplex
      (lowerStarCompComparisonLowerStarIso f (ModuleCat.{u + 1} Λ)).inv (.up ℤ)).app J.obj

/-- The chain transpose `d` of the specified restriction map `k`.
Source: Stacks Tags 099R and 0B65; blueprint resolution refinement
(blueprint: lem-pur-comparison-direct-image-resolution-mate). -/
noncomputable def comparisonResolutionTranspose :
    ((comparisonUpperStar (ModuleCat.{u + 1} Λ) V).mapHomologicalComplex (.up ℤ)).obj
        (((Etale.lowerStar (ModuleCat.{u + 1} Λ) f).mapHomologicalComplex (.up ℤ)).obj
          I.obj) ⟶
      ((lowerStar (ModuleCat.{u + 1} Λ) f).mapHomologicalComplex (.up ℤ)).obj J.obj :=
  (((comparisonAdjunction (ModuleCat.{u + 1} Λ) V).mapHomologicalComplex
    (.up ℤ)).homEquiv _ _).symm (comparisonResolutionRestriction Λ f I J t)

/-- The canonical resolution identification, using the derived comparison on `I` followed
by the inverse derived image of the augmentation. No replacement is chosen here.
Source: Stacks Tags 070K and 0FND; blueprint resolution refinement
(blueprint: lem-pur-comparison-direct-image-resolution-mate). -/
noncomputable def comparisonResolutionIso
    {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory C]
    {D : Type uD} [Category.{vD} D] [Abelian D] [HasDerivedCategory D]
    [EnoughInjectives C] (G : C ⥤ D) [G.Additive]
    (K L : CochainComplex.Plus C) [∀ n : ℤ, Injective (L.obj.X n)]
    (i : K.obj ⟶ L.obj) [QuasiIso i] :
    DerivedCategory.Plus.Q.obj (G.mapCochainComplexPlus.obj L) ≅
      G.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj K) :=
  haveI : IsIso (DerivedCategory.Plus.Q.map
      (ObjectProperty.homMk (X := K) (Y := L) i)) :=
    Localization.inverts DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso C)
    ((HomotopyCategory.Plus.quotient C).map (ObjectProperty.homMk (X := K) (Y := L) i))
    ((HomotopyCategory.quotient_map_mem_quasiIso_iff i).2
      ((HomologicalComplex.mem_quasiIso_iff i).2 inferInstance))
  asIso (G.rightDerivedFunctorPlusUnit.app ((HomotopyCategory.Plus.quotient C).obj L)) ≪≫
    G.rightDerivedFunctorPlus.mapIso
      (asIso (DerivedCategory.Plus.Q.map (ObjectProperty.homMk i))).symm


/-- The canonical identification `QC ≅ Ru_et,* K` induced by `i`.
Source: Stacks Tags 070K and 0FND; blueprint resolution refinement
(blueprint: lem-pur-comparison-direct-image-resolution-mate). -/
noncomputable def comparisonResolutionEtaleIso
    (K : CochainComplex.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    [∀ n : ℤ, Injective (I.obj.X n)] (i : K.obj ⟶ I.obj) [QuasiIso i] :
    DerivedCategory.Plus.Q.obj
        ((Etale.lowerStar (ModuleCat.{u + 1} Λ) f).mapCochainComplexPlus.obj I) ≅
      (Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) f).obj
        (DerivedCategory.Plus.Q.obj K) :=
  comparisonResolutionIso (Etale.lowerStar (ModuleCat.{u + 1} Λ) f) K I i

/-- The canonical identification `QD ≅ Ru_proet,* A_U K` induced by `t ∘ A_U(i)`.
The final factor is the specified exact-localization identification for `A_U`.
Source: Stacks Tags 070K and 0FND; blueprint resolution refinement
(blueprint: lem-pur-comparison-direct-image-resolution-mate). -/
noncomputable def comparisonResolutionProEtaleIso
    (K : CochainComplex.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    [∀ n : ℤ, Injective (J.obj.X n)] (i : K.obj ⟶ I.obj) [QuasiIso i] [QuasiIso t] :
    DerivedCategory.Plus.Q.obj
        ((lowerStar (ModuleCat.{u + 1} Λ) f).mapCochainComplexPlus.obj J) ≅
      (lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctorPlus.obj
        ((comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapDerivedCategoryPlus.obj
          (DerivedCategory.Plus.Q.obj K)) :=
  comparisonResolutionIso (lowerStar (ModuleCat.{u + 1} Λ) f)
      ((comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapCochainComplexPlus.obj K) J
      (((comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapHomologicalComplex
        (.up ℤ)).map i ≫ t) ≪≫
    (lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctorPlus.mapIso
      ((comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapDerivedCategoryPlusFactorsh.app
        ((HomotopyCategory.Plus.quotient _).obj K)).symm

/-- The localized chain map transported through precisely the two resolution
identifications of the statement. Its direction is `A_V Ru_et,* K → Ru_proet,* A_U K`.
Source: Stacks Tags 099R and 0FND; blueprint resolution refinement
(blueprint: lem-pur-comparison-direct-image-resolution-mate). -/
noncomputable def comparisonResolutionDerivedMap
    (K : CochainComplex.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    [∀ n : ℤ, Injective (I.obj.X n)] [∀ n : ℤ, Injective (J.obj.X n)]
    (i : K.obj ⟶ I.obj) [QuasiIso i] [QuasiIso t] :
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) V).mapDerivedCategoryPlus.obj
        ((Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) f).obj
          (DerivedCategory.Plus.Q.obj K)) ⟶
      (lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctorPlus.obj
        ((comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapDerivedCategoryPlus.obj
          (DerivedCategory.Plus.Q.obj K)) :=
  (comparisonUpperStar (ModuleCat.{u + 1} Λ) V).mapDerivedCategoryPlus.map
      (comparisonResolutionEtaleIso Λ f I K i).inv ≫
    ((comparisonUpperStar (ModuleCat.{u + 1} Λ) V).mapDerivedCategoryPlusFactorsh.hom.app
      ((HomotopyCategory.Plus.quotient _).obj
        ((Etale.lowerStar (ModuleCat.{u + 1} Λ) f).mapCochainComplexPlus.obj I))) ≫
    DerivedCategory.Plus.Q.map (ObjectProperty.homMk
      (X := (comparisonUpperStar (ModuleCat.{u + 1} Λ) V).mapCochainComplexPlus.obj
        ((Etale.lowerStar (ModuleCat.{u + 1} Λ) f).mapCochainComplexPlus.obj I))
      (Y := (lowerStar (ModuleCat.{u + 1} Λ) f).mapCochainComplexPlus.obj J)
      (comparisonResolutionTranspose Λ f I J t)) ≫
    (comparisonResolutionProEtaleIso Λ f I J t K i).hom


private theorem resolution_underived_counit {U V : Scheme.{u}} (f : U ⟶ V)
    (K : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) f).inv.app
        ((Etale.lowerStar (ModuleCat.{u + 1} Λ) f).obj K) ≫
      (ProEtale.upperStar (ModuleCat.{u + 1} Λ) f).map
        ((lowerStarComparisonUpperStarBaseChange f (ModuleCat.{u + 1} Λ)).app K) ≫
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).counit.app
        ((comparisonUpperStar (ModuleCat.{u + 1} Λ) U).obj K) =
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) U).map
      ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).counit.app K) := by
  have h := mateEquiv_counit_symm
    (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f)
    (lowerStarComparisonUpperStarBaseChange f (ModuleCat.{u + 1} Λ)) K
  have hi := iterated_mateEquiv_conjugateEquiv_symm
    (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f)
    (comparisonAdjunction (ModuleCat.{u + 1} Λ) V)
    (comparisonAdjunction (ModuleCat.{u + 1} Λ) U)
    (lowerStarCompComparisonLowerStarIso f (ModuleCat.{u + 1} Λ)).inv
  unfold lowerStarComparisonUpperStarBaseChange at h
  rw [hi] at h
  change _ = (comparisonUpperStarCompUpperStarIso
    (ModuleCat.{u + 1} Λ) f).hom.app _ ≫ _ at h
  simpa only [lowerStarComparisonUpperStarBaseChange, Category.assoc,
    Iso.inv_hom_id_app_assoc] using
    congrArg (fun t ↦ (comparisonUpperStarCompUpperStarIso
      (ModuleCat.{u + 1} Λ) f).inv.app ((Etale.lowerStar
        (ModuleCat.{u + 1} Λ) f).obj K) ≫ t) h


private theorem transpose_f (n : ℤ) :
    (comparisonResolutionTranspose Λ f I J t).f n =
      (lowerStarComparisonUpperStarBaseChange f (ModuleCat.{u + 1} Λ)).app (I.obj.X n) ≫
        (lowerStar (ModuleCat.{u + 1} Λ) f).map (t.f n) := by
  have he := congrArg (fun q ↦ q.f n)
    ((((comparisonAdjunction (ModuleCat.{u + 1} Λ) V).mapHomologicalComplex
      (.up ℤ)).homEquiv _ _).apply_symm_apply
        (comparisonResolutionRestriction Λ f I J t))
  have hu := unit_mateEquiv_symm
    (comparisonAdjunction (ModuleCat.{u + 1} Λ) U)
    (comparisonAdjunction (ModuleCat.{u + 1} Λ) V)
    (lowerStarCompComparisonLowerStarIso f (ModuleCat.{u + 1} Λ)).inv (I.obj.X n)
  apply ((comparisonAdjunction (ModuleCat.{u + 1} Λ) V).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  dsimp only [Functor.mapHomologicalComplex_obj_X] at *
  erw [← Category.assoc, ← hu]
  change (comparisonAdjunction (ModuleCat.{u + 1} Λ) V).unit.app _ ≫
    (comparisonLowerStar (ModuleCat.{u + 1} Λ) V).map
      ((comparisonResolutionTranspose Λ f I J t).f n) = _ at he
  dsimp only [Functor.mapHomologicalComplex_obj_X] at he
  erw [he]
  change (Etale.lowerStar (ModuleCat.{u + 1} Λ) f).map
      ((comparisonAdjunction (ModuleCat.{u + 1} Λ) U).unit.app _ ≫
        (comparisonLowerStar (ModuleCat.{u + 1} Λ) U).map (t.f n)) ≫ _ = _
  rw [Functor.map_comp, Category.assoc, Category.assoc]
  congr 1
  exact (lowerStarCompComparisonLowerStarIso f (ModuleCat.{u + 1} Λ)).inv.naturality
    (t.f n)

private theorem transpose_eq :
    comparisonResolutionTranspose Λ f I J t =
      (NatTrans.mapHomologicalComplex
        (lowerStarComparisonUpperStarBaseChange f (ModuleCat.{u + 1} Λ)) (.up ℤ)).app I.obj ≫
        ((lowerStar (ModuleCat.{u + 1} Λ) f).mapHomologicalComplex (.up ℤ)).map t := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact transpose_f Λ f I J t n

/-- Chain identity for the restriction transpose.
Source: Stacks Tags 099R and 0B65 (blueprint: lem-pur-comparison-direct-image-resolution-mate). -/
private theorem comparison_resolution_chain_identity :
    (NatTrans.mapHomologicalComplex
      (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) f).inv (.up ℤ)).app
        (((Etale.lowerStar (ModuleCat.{u + 1} Λ) f).mapHomologicalComplex (.up ℤ)).obj I.obj) ≫
      ((upperStar (ModuleCat.{u + 1} Λ) f).mapHomologicalComplex (.up ℤ)).map
        (comparisonResolutionTranspose Λ f I J t) ≫
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).mapHomologicalComplex
        (.up ℤ)).counit.app J.obj =
      ((comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapHomologicalComplex (.up ℤ)).map
        (((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).mapHomologicalComplex
           (.up ℤ)).counit.app I.obj) ≫ t := by
  apply HomologicalComplex.Hom.ext
  funext n
  simp only [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f,
    Functor.mapHomologicalComplex_map_f, Adjunction.mapHomologicalComplex_counit_app_f]
  dsimp only [Functor.mapHomologicalComplex_obj_X] at *
  rw [transpose_f, Functor.map_comp, Category.assoc]
  have hn := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).counit.naturality
    (t.f n)
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  dsimp only [Functor.mapHomologicalComplex_obj_X] at hn
  erw [hn]
  simpa only [Category.assoc] using
    congrArg (fun q ↦ q ≫ t.f n) (resolution_underived_counit Λ f (I.obj.X n))


section ResolutionBaseChange

variable {B B' C C' : Type*} [Category* B] [Category* B'] [Category* C] [Category* C']
  [Abelian B] [Abelian B'] [Abelian C] [Abelian C']
  [HasDerivedCategory B] [HasDerivedCategory B'] [HasDerivedCategory C]
  [HasDerivedCategory C'] [EnoughInjectives B] [EnoughInjectives B']
  (G : B ⥤ C) (G' : B' ⥤ C') (β : B ⥤ B') (γ : C ⥤ C')
  [G.Additive] [G'.Additive] [β.Additive] [γ.Additive]
  [PreservesFiniteLimits β] [PreservesFiniteColimits β]
  [PreservesFiniteLimits γ] [PreservesFiniteColimits γ]

private theorem resolution_baseChange_fac (e : G ⋙ γ ⟶ β ⋙ G')
    (M : HomotopyCategory.Plus B) :
    γ.mapDerivedCategoryPlus.map (G.rightDerivedFunctorPlusUnit.app M) ≫
        (Functor.rightDerivedFunctorPlusBaseChange e).app (DerivedCategory.Plus.Qh.obj M) ≫
        G'.rightDerivedFunctorPlus.map (β.mapDerivedCategoryPlusFactorsh.hom.app M) =
      γ.mapDerivedCategoryPlusFactorsh.hom.app (G.mapHomotopyCategoryPlus.obj M) ≫
        DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus e).app M) ≫
        G'.rightDerivedFunctorPlusUnit.app (β.mapHomotopyCategoryPlus.obj M) := by
  have h := congr_app (Functor.rightDerivedFunctorPlusBaseChange_fac e) M
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.comp_id] at h
  erw [← Category.assoc, h]
  simp [Functor.rightDerivedFunctorPlusBaseChangeAux,
    Functor.mapHomotopyCategoryPlusCompIso_refl_hom_app,
    Functor.mapHomotopyCategoryPlusCompIso_refl_inv_app, ← Functor.map_comp]

private theorem quasiIso_plus_Q_isIso
    {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
    {K L : CochainComplex.Plus A} (i : K.obj ⟶ L.obj) [QuasiIso i] :
    IsIso (DerivedCategory.Plus.Q.map (ObjectProperty.homMk (X := K) (Y := L) i)) :=
  Localization.inverts DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso A)
    ((HomotopyCategory.Plus.quotient A).map (ObjectProperty.homMk i))
    ((HomotopyCategory.quotient_map_mem_quasiIso_iff i).2
      ((HomologicalComplex.mem_quasiIso_iff i).2 inferInstance))

private theorem baseChange_resolutions (e : G ⋙ γ ⟶ β ⋙ G')
    (K L : CochainComplex.Plus B) (N : CochainComplex.Plus B')
    [∀ n : ℤ, Injective (L.obj.X n)] [∀ n : ℤ, Injective (N.obj.X n)]
    (i : K.obj ⟶ L.obj) [QuasiIso i]
    (t : (β.mapHomologicalComplex (.up ℤ)).obj L.obj ⟶ N.obj) [QuasiIso t] :
    γ.mapDerivedCategoryPlus.map (comparisonResolutionIso G K L i).inv ≫
      γ.mapDerivedCategoryPlusFactorsh.hom.app
        ((HomotopyCategory.Plus.quotient _).obj (G.mapCochainComplexPlus.obj L)) ≫
      DerivedCategory.Plus.Q.map (ObjectProperty.homMk
        (X := γ.mapCochainComplexPlus.obj (G.mapCochainComplexPlus.obj L))
        (Y := G'.mapCochainComplexPlus.obj N)
        ((NatTrans.mapHomologicalComplex e (.up ℤ)).app L.obj ≫
          (G'.mapHomologicalComplex (.up ℤ)).map t)) ≫
      (comparisonResolutionIso G' (β.mapCochainComplexPlus.obj K) N
        ((β.mapHomologicalComplex (.up ℤ)).map i ≫ t)).hom ≫
      G'.rightDerivedFunctorPlus.map (β.mapDerivedCategoryPlusFactorsh.inv.app
        ((HomotopyCategory.Plus.quotient _).obj K)) =
      (Functor.rightDerivedFunctorPlusBaseChange e).app (DerivedCategory.Plus.Q.obj K) := by
  let M := (HomotopyCategory.Plus.quotient _).obj L
  let P := (HomotopyCategory.Plus.quotient _).obj N
  let a : (HomotopyCategory.Plus.quotient _).obj K ⟶ M :=
    (HomotopyCategory.Plus.quotient _).map (ObjectProperty.homMk i)
  let b : β.mapHomotopyCategoryPlus.obj M ⟶ P :=
    (HomotopyCategory.Plus.quotient _).map
      (ObjectProperty.homMk (X := β.mapCochainComplexPlus.obj L) (Y := N) t)
  have hd : (HomotopyCategory.Plus.quotient C').map
      (ObjectProperty.homMk
        (X := γ.mapCochainComplexPlus.obj (G.mapCochainComplexPlus.obj L))
        (Y := G'.mapCochainComplexPlus.obj N)
        ((NatTrans.mapHomologicalComplex e (.up ℤ)).app L.obj ≫
          (G'.mapHomologicalComplex (.up ℤ)).map t)) =
      (NatTrans.mapHomotopyCategoryPlus e).app M ≫ G'.mapHomotopyCategoryPlus.map b := by
    apply (HomotopyCategory.Plus.ι C').map_injective
    rw [Functor.map_comp, NatTrans.ι_map_mapHomotopyCategoryPlus_app]
    change (HomotopyCategory.quotient C' (.up ℤ)).map (_ ≫ _) =
      (HomotopyCategory.quotient C' (.up ℤ)).map _ ≫
        (HomotopyCategory.quotient C' (.up ℤ)).map _
    exact Functor.map_comp _ _ _
  let j : (β.mapCochainComplexPlus.obj K).obj ⟶ N.obj :=
    (β.mapHomologicalComplex (.up ℤ)).map i ≫ t
  have : QuasiIso j := inferInstance
  have := quasiIso_plus_Q_isIso i
  have := quasiIso_plus_Q_isIso (K := β.mapCochainComplexPlus.obj K) (L := N) j
  have hj : DerivedCategory.Plus.Qh.map (β.mapHomotopyCategoryPlus.map a) ≫
      DerivedCategory.Plus.Qh.map b =
      DerivedCategory.Plus.Q.map (ObjectProperty.homMk
        (X := β.mapCochainComplexPlus.obj K) (Y := N) j) := by
    rw [← Functor.map_comp]
    congr 1
  have hf := resolution_baseChange_fac G G' β γ e M
  have ht := G'.rightDerivedFunctorPlusUnit.naturality b
  have hi := (Functor.rightDerivedFunctorPlusBaseChange e).naturality
    (DerivedCategory.Plus.Q.map (ObjectProperty.homMk (X := K) (Y := L) i))
  have hβ := β.mapDerivedCategoryPlusFactorsh.hom.naturality a
  dsimp only [Functor.comp_map] at ht hi hβ
  simp only [comparisonResolutionIso, Iso.trans_inv, Iso.symm_inv, Iso.trans_hom,
    Functor.mapIso_inv, Functor.mapIso_hom, asIso_hom, asIso_inv,
    Functor.map_comp, Category.assoc]
  rw [show DerivedCategory.Plus.Q.map (ObjectProperty.homMk
      (X := γ.mapCochainComplexPlus.obj (G.mapCochainComplexPlus.obj L))
      (Y := G'.mapCochainComplexPlus.obj N)
      ((NatTrans.mapHomologicalComplex e (.up ℤ)).app L.obj ≫
        (G'.mapHomologicalComplex (.up ℤ)).map t)) =
      DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus e).app M) ≫
        DerivedCategory.Plus.Qh.map (G'.mapHomotopyCategoryPlus.map b) by
      exact (DerivedCategory.Plus.Qh.congr_map hd).trans
        (DerivedCategory.Plus.Qh.map_comp _ _)]
  simp only [Category.assoc]
  erw [reassoc_of% ht, ← reassoc_of% hf]
  have hu : γ.mapDerivedCategoryPlus.map
      (inv (G.rightDerivedFunctorPlusUnit.app M)) ≫
      γ.mapDerivedCategoryPlus.map (G.rightDerivedFunctorPlusUnit.app M) = 𝟙 _ := by
    rw [← Functor.map_comp, IsIso.inv_hom_id, CategoryTheory.Functor.map_id]
  erw [reassoc_of% hu]
  have hc : β.mapDerivedCategoryPlusFactorsh.hom.app M ≫
      DerivedCategory.Plus.Qh.map b ≫
      (asIso (DerivedCategory.Plus.Q.map (ObjectProperty.homMk
        (X := β.mapCochainComplexPlus.obj K) (Y := N) j))).symm.hom ≫
      β.mapDerivedCategoryPlusFactorsh.inv.app
        ((HomotopyCategory.Plus.quotient _).obj K) =
      inv (β.mapDerivedCategoryPlus.map
        (DerivedCategory.Plus.Q.map (ObjectProperty.homMk (X := K) (Y := L) i))) := by
    apply (cancel_epi (β.mapDerivedCategoryPlus.map
      (DerivedCategory.Plus.Q.map (ObjectProperty.homMk (X := K) (Y := L) i)))).1
    erw [reassoc_of% hβ, reassoc_of% hj]
    simp
    rfl
  rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp]
  erw [hc, reassoc_of% hi]
  rw [← Functor.map_comp, IsIso.hom_inv_id, CategoryTheory.Functor.map_id, Category.comp_id]


end ResolutionBaseChange

/-- Derived map identification for the resolution transpose.
Source: Stacks Tags 070K and 0FND (blueprint: lem-pur-comparison-direct-image-resolution-mate). -/
private theorem comparison_resolution_derived_map_eq
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [∀ n : ℤ, Injective (I.obj.X n)] [∀ n : ℤ, Injective (J.obj.X n)]
    (i : (comparisonResolutionSingle F).obj ⟶ I.obj) [QuasiIso i] [QuasiIso t] :
    comparisonResolutionDerivedMap Λ f I J t (comparisonResolutionSingle F) i =
      (fixedComparisonDirectImageMatePlus Λ f).app
        (DerivedCategory.Plus.Q.obj (comparisonResolutionSingle F)) := by
  unfold comparisonResolutionDerivedMap comparisonResolutionEtaleIso
    comparisonResolutionProEtaleIso
  rw [transpose_eq]
  simpa [fixedComparisonDirectImageMatePlus, Etale.rightDerivedLowerStarPlus,
    Category.assoc] using
    baseChange_resolutions
      (Etale.lowerStar (ModuleCat.{u + 1} Λ) f)
      (lowerStar (ModuleCat.{u + 1} Λ) f)
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) U)
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) V)
      (lowerStarComparisonUpperStarBaseChange f (ModuleCat.{u + 1} Λ))
      (comparisonResolutionSingle F) I J i t


/-- Derived transpose identification for the resolution transpose.
Source: Stacks Tags 070K and 0FND (blueprint: lem-pur-comparison-direct-image-resolution-mate). -/
private theorem comparison_resolution_derived_transpose
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [Finite Λ] [QuasiCompact f] [QuasiSeparated f]
    [∀ n : ℤ, Injective (I.obj.X n)] [∀ n : ℤ, Injective (J.obj.X n)]
    (i : (comparisonResolutionSingle F).obj ⟶ I.obj) [QuasiIso i] [QuasiIso t] :
    ((derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) f).homEquiv _ _).symm
        (comparisonResolutionDerivedMap Λ f I J t (comparisonResolutionSingle F) i) =
      (fixedComparisonPullbackPlus Λ f).inv.app
          ((Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) f).obj
            (DerivedCategory.Plus.Q.obj (comparisonResolutionSingle F))) ≫
        (comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapDerivedCategoryPlus.map
          ((Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) f).counit.app
             (DerivedCategory.Plus.Q.obj (comparisonResolutionSingle F))) := by
  rw [comparison_resolution_derived_map_eq, Adjunction.homEquiv_counit]
  apply (cancel_epi ((fixedComparisonPullbackPlus Λ f).hom.app _)).1
  simpa only [Category.assoc, Iso.hom_inv_id_app_assoc] using
    fixedComparisonDirectImageMatePlus_counit Λ f
      (DerivedCategory.Plus.Q.obj (comparisonResolutionSingle F))


/-- Terminal-section identities for the restriction and its transpose.
Source: Stacks Tag 099R (blueprint: lem-pur-comparison-direct-image-resolution-mate). -/
private theorem comparison_resolution_section_identities :
    ∀ (n : ℤ)
      (z : (((Etale.lowerStar (ModuleCat.{u + 1} Λ) f).obj (I.obj.X n)).obj.obj
        (op (⊤_ V.Etale)))),
      ((comparisonResolutionRestriction Λ f I J t).f n).hom.app (op (⊤_ V.Etale)) z =
        ((comparisonResolutionAdjunct Λ I J t).f n).hom.app
          (op (f.Etale.obj (⊤_ V.Etale))) z ∧
      ((comparisonResolutionTranspose Λ f I J t).f n).hom.app
          (op ((Scheme.toProEt V).obj (⊤_ V.Etale)))
          (((comparisonAdjunction (ModuleCat.{u + 1} Λ) V).unit.app
            ((Etale.lowerStar (ModuleCat.{u + 1} Λ) f).obj (I.obj.X n))).hom.app
              (op (⊤_ V.Etale)) z) =
        ((comparisonResolutionAdjunct Λ I J t).f n).hom.app
          (op (f.Etale.obj (⊤_ V.Etale))) z := by
  intro n z
  have hk : ((comparisonResolutionRestriction Λ f I J t).f n).hom.app
      (op (⊤_ V.Etale)) z =
    ((comparisonResolutionAdjunct Λ I J t).f n).hom.app
      (op (f.Etale.obj (⊤_ V.Etale))) z := by
    dsimp [comparisonResolutionRestriction, lowerStarCompComparisonLowerStarIso,
      toProEtCompOverPullbackIso]
    erw [(J.obj.X n).obj.map_id]
    rfl
  refine ⟨hk, ?_⟩
  have he := (((comparisonAdjunction (ModuleCat.{u + 1} Λ) V).mapHomologicalComplex
    (.up ℤ)).homEquiv _ _).apply_symm_apply
      (comparisonResolutionRestriction Λ f I J t)
  have hn := congrArg (fun q ↦ (q.f n).hom.app (op (⊤_ V.Etale)) z) he
  change _ = ((comparisonResolutionRestriction Λ f I J t).f n).hom.app
    (op (⊤_ V.Etale)) z at hn
  exact hn.trans hk


/-- The restriction transpose on the supplied resolutions is the specified derived mate,
with its ordinary counit identity and its evaluation on all terminal sections.
Source: blueprint main-20261015, prop-pur-gm-relative-kummer.proof.md, opening
paragraph (resolution refinement); Stacks Tags 099R, 0B65, 070K and 0FND
(blueprint: lem-pur-comparison-direct-image-resolution-mate).

Proof: (1) The restriction isomorphism δ is the identity on `G(W ×[V] U)`,
including restriction maps and the constant coefficient action.
(2) Compose the comparison and inverse-image adjunctions in the two orders.
The conjugate-unit equation for the canonical pullback comparison identifies the
resulting Hom bijections after precomposition with `a⁰`.
(3) The adjuncts of `t ∘ A_U(εe_I)` and `εp_J ∘ p(d)` are `u_* h` and `k`.
The equality defining `k` and injectivity of the composite Hom bijection give
the asserted chain identity. This uses the termwise adjunction-homotopy interface.
(4) Exactness of the three inverse images gives their termwise localization
comparisons. The augmentations `i` and `A_U(i) ≫ t` are quasi-isomorphisms;
the K-injective computation of the right derived functors identifies their values
with `QC` and `QD`. These are exactly `comparisonResolutionEtaleIso` and
`comparisonResolutionProEtaleIso`, not arbitrary isomorphisms.
(5) The general pre-derived adjunction representative formula, with the exact
left adjoint unreplaced, computes the two derived transposes using the inverses
of the augmentations followed by the ordinary counits.
(6) Localize the chain identity and use naturality of the pullback comparison.
Cancel the exact comparison image of the etale resolution identification to obtain
that the transpose is `A_U(εe_F) ∘ a⁻¹`. Uniqueness of the adjoint transpose
identifies this map with `fixedComparisonDirectImageMatePlus`, whose counit
normalization is the canonical-mate dependency.
(7) Evaluate δ on the terminal object: it is the identity. Then evaluate the
adjunction equation `η ≫ N_V(d) = k` on a section `z`. This gives both section
identities in every degree, without a cocycle condition. Neither comparison
inverse image is required to preserve injective objects. -/
theorem comparison_direct_image_resolution_mate [Finite Λ]
    [QuasiCompact f] [QuasiSeparated f]
    [I.obj.IsStrictlyGE 0] [J.obj.IsStrictlyGE 0]
    [∀ n : ℤ, Injective (I.obj.X n)] [∀ n : ℤ, Injective (J.obj.X n)]
    [I.obj.IsKInjective] [J.obj.IsKInjective]
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (i : (comparisonResolutionSingle F).obj ⟶ I.obj) [QuasiIso i] [QuasiIso t] :
    (NatTrans.mapHomologicalComplex
        (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) f).inv (.up ℤ)).app
        (((Etale.lowerStar (ModuleCat.{u + 1} Λ) f).mapHomologicalComplex (.up ℤ)).obj
          I.obj) ≫
      ((upperStar (ModuleCat.{u + 1} Λ) f).mapHomologicalComplex (.up ℤ)).map
        (comparisonResolutionTranspose Λ f I J t) ≫
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).mapHomologicalComplex
        (.up ℤ)).counit.app J.obj =
      ((comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapHomologicalComplex (.up ℤ)).map
        (((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).mapHomologicalComplex
           (.up ℤ)).counit.app I.obj) ≫ t ∧
    comparisonResolutionDerivedMap Λ f I J t (comparisonResolutionSingle F) i =
      (fixedComparisonDirectImageMatePlus Λ f).app
        (DerivedCategory.Plus.Q.obj (comparisonResolutionSingle F)) ∧
    ((derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) f).homEquiv _ _).symm
        (comparisonResolutionDerivedMap Λ f I J t (comparisonResolutionSingle F) i) =
      (fixedComparisonPullbackPlus Λ f).inv.app
          ((Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) f).obj
            (DerivedCategory.Plus.Q.obj (comparisonResolutionSingle F))) ≫
        (comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapDerivedCategoryPlus.map
          ((Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) f).counit.app
             (DerivedCategory.Plus.Q.obj (comparisonResolutionSingle F))) ∧
    ∀ (n : ℤ)
      (z : (((Etale.lowerStar (ModuleCat.{u + 1} Λ) f).obj (I.obj.X n)).obj.obj
        (op (⊤_ V.Etale)))),
      ((comparisonResolutionRestriction Λ f I J t).f n).hom.app (op (⊤_ V.Etale)) z =
        ((comparisonResolutionAdjunct Λ I J t).f n).hom.app
          (op (f.Etale.obj (⊤_ V.Etale))) z ∧
      ((comparisonResolutionTranspose Λ f I J t).f n).hom.app
          (op ((Scheme.toProEt V).obj (⊤_ V.Etale)))
          (((comparisonAdjunction (ModuleCat.{u + 1} Λ) V).unit.app
            ((Etale.lowerStar (ModuleCat.{u + 1} Λ) f).obj (I.obj.X n))).hom.app
              (op (⊤_ V.Etale)) z) =
        ((comparisonResolutionAdjunct Λ I J t).f n).hom.app
          (op (f.Etale.obj (⊤_ V.Etale))) z := by
  refine ⟨comparison_resolution_chain_identity Λ f I J t, ?_, ?_, ?_⟩
  · exact comparison_resolution_derived_map_eq Λ f I J t F i
  · exact comparison_resolution_derived_transpose Λ f I J t F i
  · exact comparison_resolution_section_identities Λ f I J t

end AlgebraicGeometry.ProEtale
