/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import WeilConjectures.CategoryTheory.Abelian.DerivedBottomComparison
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective

/-! # The bottom cohomology presheaf of a K-injective complex

Source: the derived truncation argument for the left exact inclusion of sheaves.
(blueprint: lem-pur-kinjective-bottom-presheaf-sheaf).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe uC vC uD vD wC wD
open CategoryTheory CategoryTheory.Limits

private def bottomHomologyIso
    {C : Type uC} [Category.{vC} C] [Abelian C]
    [EnoughInjectives C] [Abelian.HasKInjectiveResolutions C] [HasDerivedCategory.{wC} C]
    {D : Type uD} [Category.{vD} D] [Abelian D] [HasDerivedCategory.{wD} D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    (K : CochainComplex C ℤ) [K.IsKInjective] (d : ℤ)
    (hvan : ∀ q : ℤ, q < d → IsZero (K.homology q)) :
    ((F.mapHomologicalComplex (.up ℤ)).obj K).homology d ≅ F.obj (K.homology d) := by
  let : K.IsGE d := (CochainComplex.isGE_iff K d).mpr
    (fun q hq ↦ (K.exactAt_iff_isZero_homology q).mpr (hvan q hq))
  let : DerivedCategory.TStructure.t.IsGE (DerivedCategory.Q.obj K) d :=
    (DerivedCategory.isGE_Q_obj_iff K d).mpr inferInstance
  exact ((DerivedCategory.homologyFunctorFactors D d).app _).symm ≪≫
    (DerivedCategory.homologyFunctor D d).mapIso (F.rightDerivedFunctorObjQIso K).symm ≪≫
    (DerivedCategory.homologyFunctor D d).mapIso
      (F.rightDerivedFunctor.mapIso (asIso
        ((DerivedCategory.TStructure.t.truncGEπ d).app (DerivedCategory.Q.obj K)))) ≪≫
    (F.rightDerivedFunctorTruncatedBottomIso d).app (DerivedCategory.Q.obj K) ≪≫
    F.mapIso ((DerivedCategory.homologyFunctorFactors C d).app K)

private def pointwiseHomologyIso
    {T : Type*} [Category* T] {V : Type*} [Category* V] [Abelian V]
    (K : CochainComplex (T ⥤ V) ℤ) (d : ℤ) :
    K.asFunctor ⋙ HomologicalComplex.homologyFunctor V (.up ℤ) d ≅ K.homology d :=
  NatIso.ofComponents (fun t ↦ (K.sc d).mapHomologyIso ((evaluation T V).obj t))
    (fun {t t'} f ↦ by
      change ShortComplex.homologyMap
        ((K.sc d).mapNatTrans ((evaluation T V).map f)) ≫ _ = _
      rw [ShortComplex.homologyMap_mapNatTrans]
      simp
      rfl)

/-- The bottom cohomology presheaf of a K-injective sheaf complex is a sheaf.
Source: Stacks Project, Tag 05TC (2), the bottom edge for a left exact functor; the proof
uses the already constructed derived truncation comparison.
(blueprint: lem-pur-kinjective-bottom-presheaf-sheaf).

Proof: lower homology vanishing puts the complex in D≥d. The derived inclusion of
sheaves into presheaves agrees in degree d with inclusion of the degree-d homology
sheaf, by truncation and left exactness. K-injectivity computes that derived functor
termwise. Evaluation preserves homology, naturally in the site object, so pointwise
homology of the underlying complex is isomorphic to this underlying sheaf. Transport
the sheaf condition along that natural isomorphism. -/
theorem CategoryTheory.Presheaf.isSheaf_bottom_cohomology_of_isKInjective
    {T : Type uC} [Category.{vC} T] (J : GrothendieckTopology T)
    [HasSheafify J AddCommGrpCat.{uC}]
    [IsGrothendieckAbelian.{wC} (Sheaf J AddCommGrpCat.{uC})]
    (K : CochainComplex (Sheaf J AddCommGrpCat.{uC}) ℤ) [K.IsKInjective]
    (d : ℤ) (hvan : ∀ q : ℤ, q < d → IsZero (K.homology q)) :
    Presheaf.IsSheaf J
      ((((sheafToPresheaf J AddCommGrpCat.{uC}).mapHomologicalComplex (.up ℤ)).obj K).asFunctor
        ⋙ HomologicalComplex.homologyFunctor AddCommGrpCat.{uC} (.up ℤ) d) := by
  let := HasDerivedCategory.standard (Tᵒᵖ ⥤ AddCommGrpCat.{uC})
  let e := pointwiseHomologyIso
    (((sheafToPresheaf J AddCommGrpCat.{uC}).mapHomologicalComplex (.up ℤ)).obj K) d ≪≫
    bottomHomologyIso (sheafToPresheaf J AddCommGrpCat.{uC}) K d hvan
  exact (Presheaf.isSheaf_of_iso_iff e).mpr (K.homology d).property
