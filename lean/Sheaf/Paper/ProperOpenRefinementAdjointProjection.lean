/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q35
-/
module

public import Sheaf.Paper.UnboundedProperOpenInterchange
public import Sheaf.AlgebraicGeometry.OpenSectionClopen
public import WeilConjectures.AlgebraicGeometry.EtaleSheafClopenProduct
public import WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeModules
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Complement
import Sheaf.CategoryTheory.DerivedCategory.ExactRestrictionComposition
import Sheaf.AlgebraicGeometry.DerivedCounitKInjectiveTermwise
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact

/-!
# The adjoint of proper/open refinement is the component projection

Source: Stacks Project, Tag 0F7B, lemma-shriek-proper-and-open, with the clopen-section
calculation of the blueprint (blueprint: lem-asd-proper-open-refinement-adjoint-projection).

The sheaf projection and its descent are specified by their component and localization
formulas. In particular, the projection is characterized independently of the derived mate.
-/

@[expose] public noncomputable section

set_option autoImplicit false


set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u v w

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

attribute [local instance 2000] Abelian.toPreadditive


attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor

/-- The two normalized comparisons for the refinement square, retaining only the
normalizations used below. Source: Stacks Project, Tag 0F7B
(blueprint: lem-asd-proper-open-refinement-adjoint-projection). -/
structure ProperOpenRefinementData (A : Type (u + 1)) [CommRing A]
    {U V₁ V₂ : Scheme.{u}} (p : V₁ ⟶ V₂) (j₁ : U ⟶ V₁) (j₂ : U ⟶ V₂)
    [IsOpenImmersion j₁] [IsOpenImmersion j₂] (h : j₁ ≫ p = j₂) where
  sheafIso : (𝟙 U)_*[ModuleCat.{u + 1} A] ⋙ (j₂)_!open[ModuleCat.{u + 1} A] ≅
    (j₁)_!open[ModuleCat.{u + 1} A] ⋙ (p)_*[ModuleCat.{u + 1} A]
  derivedIso : R((𝟙 U)_*[ModuleCat.{u + 1} A]) ⋙ D((j₂)_!open[ModuleCat.{u + 1} A]) ≅
    D((j₁)_!open[ModuleCat.{u + 1} A]) ⋙ R((p)_*[ModuleCat.{u + 1} A])
  sheaf_fac : ∀ M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A),
    sheafIso.hom.app M ≫ (p)_*[ModuleCat.{u + 1} A].map
        ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) j₁).app M) ≫
      (lowerStarComp (ModuleCat.{u + 1} A) j₁ p).hom.app M =
    (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) j₂).app
        ((𝟙 U)_*[ModuleCat.{u + 1} A].obj M) ≫
      (lowerStarComp (ModuleCat.{u + 1} A) (𝟙 U) j₂ (j₁ ≫ p)
        (h.trans (Category.id_comp j₂).symm)).hom.app M
  derived_fac : ∀ (J : CochainComplex
      (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) [J.IsKInjective]
      (I : CochainComplex (Sheaf V₁.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
      [I.IsKInjective]
      (ρ : ((j₁)_!open[ModuleCat.{u + 1} A].mapHomologicalComplex (.up ℤ)).obj J ⟶ I)
      [QuasiIso ρ],
    D((j₂)_!open[ModuleCat.{u + 1} A]).map
        (((𝟙 U)_*[ModuleCat.{u + 1} A]).rightDerivedFunctorObjQIso J).hom ≫
      ((j₂)_!open[ModuleCat.{u + 1} A]).mapDerivedCategoryFactors.hom.app
        (((𝟙 U)_*[ModuleCat.{u + 1} A].mapHomologicalComplex (.up ℤ)).obj J) ≫
      DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex sheafIso.hom (.up ℤ)).app J) ≫
      DerivedCategory.Q.map
        (((p)_*[ModuleCat.{u + 1} A].mapHomologicalComplex (.up ℤ)).map ρ) =
    derivedIso.hom.app (DerivedCategory.Q.obj J) ≫
      R((p)_*[ModuleCat.{u + 1} A]).map
        (((j₁)_!open[ModuleCat.{u + 1} A]).mapDerivedCategoryFactors.hom.app J ≫
          DerivedCategory.Q.map ρ) ≫
      (((p)_*[ModuleCat.{u + 1} A]).rightDerivedFunctorObjQIso I).hom

/-- Extract the normalized comparisons without retaining the other interchange clauses.
Source: Stacks Project, Tag 0F7B
(blueprint: lem-asd-proper-open-refinement-adjoint-projection).
Proof: specialize the sheaf and representative normalizations of proper/open interchange
at the square (j₁, identity, p, j₂). -/
theorem nonempty_properOpenRefinementData (A : Type (u + 1)) [CommRing A] [Finite A]
    {U V₁ V₂ : Scheme.{u}} [IsNoetherian U] [IsNoetherian V₁] [IsNoetherian V₂]
    (p : V₁ ⟶ V₂) [IsProper p] (j₁ : U ⟶ V₁) (j₂ : U ⟶ V₂)
    [IsOpenImmersion j₁] [IsOpenImmersion j₂] (h : j₁ ≫ p = j₂) :
    Nonempty (ProperOpenRefinementData A p j₁ j₂ h) := by
  obtain ⟨θ, Γ, hθ, hΓ, _⟩ := unboundedProperOpenInterchange A
  let sq : CommSq j₁ (𝟙 U) p j₂ := ⟨h.trans (Category.id_comp j₂).symm⟩
  exact ⟨⟨θ j₁ (𝟙 U) p j₂ sq, Γ j₁ (𝟙 U) p j₂ sq,
    hθ j₁ (𝟙 U) p j₂ sq, hΓ j₁ (𝟙 U) p j₂ sq⟩⟩

/-- The normalized comparison data; both isomorphisms are fixed by their normalization
formulas. Source: Stacks Project, Tag 0F7B
(blueprint: lem-asd-proper-open-refinement-adjoint-projection). -/
def properOpenRefinementData (A : Type (u + 1)) [CommRing A] [Finite A]
    {U V₁ V₂ : Scheme.{u}} [IsNoetherian U] [IsNoetherian V₁] [IsNoetherian V₂]
    (p : V₁ ⟶ V₂) [IsProper p] (j₁ : U ⟶ V₁) (j₂ : U ⟶ V₂)
    [IsOpenImmersion j₁] [IsOpenImmersion j₂] (h : j₁ ≫ p = j₂) :
    ProperOpenRefinementData A p j₁ j₂ h :=
  Classical.choice (nonempty_properOpenRefinementData A p j₁ j₂ h)

attribute [local irreducible] properOpenRefinementData

/-- The comparison of Tag 0F7B for the refinement square, with the identity direct-image
compositor inserted. The selected witness has the K-injective normalization in
`unboundedProperOpenInterchange`; this is not a choice of an unnormalized isomorphism.
Source: Stacks Project, Tag 0F7B
(blueprint: lem-asd-proper-open-refinement-adjoint-projection). -/
def unboundedProperOpenRefinementComparison (A : Type (u + 1)) [CommRing A] [Finite A]
    {U V₁ V₂ : Scheme.{u}} [IsNoetherian U] [IsNoetherian V₁] [IsNoetherian V₂]
    (p : V₁ ⟶ V₂) [IsProper p] (j₁ : U ⟶ V₁) (j₂ : U ⟶ V₂)
    [IsOpenImmersion j₁] [IsOpenImmersion j₂] (h : j₁ ≫ p = j₂) :
    D((j₂)_!open[ModuleCat.{u + 1} A]) ≅
      D((j₁)_!open[ModuleCat.{u + 1} A]) ⋙ R((p)_*[ModuleCat.{u + 1} A]) :=
  (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight
      ((((𝟙 U)_*[ModuleCat.{u + 1} A]).rightDerivedFunctorIsoMapDerivedCategory ≪≫
        Functor.mapDerivedCategoryNatIso (lowerStarId (ModuleCat.{u + 1} A) U) ≪≫
        Functor.mapDerivedCategoryIdIso _).symm) _ ≪≫
    (properOpenRefinementData A p j₁ j₂ h).derivedIso

attribute [local irreducible] unboundedProperOpenRefinementComparison

@[irreducible]
private def refinementSheafComparison (A : Type (u + 1)) [CommRing A] [Finite A]
    {U V₁ V₂ : Scheme.{u}} [IsNoetherian U] [IsNoetherian V₁] [IsNoetherian V₂]
    (p : V₁ ⟶ V₂) [IsProper p] (j₁ : U ⟶ V₁) (j₂ : U ⟶ V₂)
    [IsOpenImmersion j₁] [IsOpenImmersion j₂] (h : j₁ ≫ p = j₂) :
    (j₂)_!open[ModuleCat.{u + 1} A] ≅
      (j₁)_!open[ModuleCat.{u + 1} A] ⋙ (p)_*[ModuleCat.{u + 1} A] :=
  (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight (lowerStarId (ModuleCat.{u + 1} A) U).symm _ ≪≫
    (properOpenRefinementData A p j₁ j₂ h).sheafIso

private theorem refinementSheafComparison_normalization
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U V₁ V₂ : Scheme.{u}} [IsNoetherian U] [IsNoetherian V₁] [IsNoetherian V₂]
    (p : V₁ ⟶ V₂) [IsProper p] (j₁ : U ⟶ V₁) (j₂ : U ⟶ V₂)
    [IsOpenImmersion j₁] [IsOpenImmersion j₂] (h : j₁ ≫ p = j₂)
    (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (refinementSheafComparison A p j₁ j₂ h).hom.app M ≫
      (p)_*[ModuleCat.{u + 1} A].map
        ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) j₁).app M) ≫
      (lowerStarComp (ModuleCat.{u + 1} A) j₁ p j₂ h.symm).hom.app M =
    (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) j₂).app M := by
  subst j₂
  have hn := (properOpenRefinementData A p j₁ (j₁ ≫ p) rfl).sheaf_fac M
  unfold refinementSheafComparison
  simp only [Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerRight_hom, NatTrans.comp_app, Functor.leftUnitor_inv_app,
    Functor.whiskerRight_app, Category.id_comp, Category.assoc]
  rw [lowerStarComp_id_left] at hn
  simp only [Iso.trans_hom, Functor.isoWhiskerRight_hom, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app] at hn
  rw [hn, ← NatTrans.naturality_assoc]
  erw [← Functor.map_comp_assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp, Category.comp_id]
  rfl

@[irreducible]
private def refinementSheafProjection (A : Type (u + 1)) [CommRing A] [Finite A]
    {U V₁ V₂ : Scheme.{u}} [IsNoetherian U] [IsNoetherian V₁] [IsNoetherian V₂]
    (p : V₁ ⟶ V₂) [IsProper p] (j₁ : U ⟶ V₁) (j₂ : U ⟶ V₂)
    [IsOpenImmersion j₁] [IsOpenImmersion j₂] (h : j₁ ≫ p = j₂) :
    (j₂)_!open[ModuleCat.{u + 1} A] ⋙ (p)^*[ModuleCat.{u + 1} A] ⟶
      (j₁)_!open[ModuleCat.{u + 1} A] :=
  Functor.whiskerRight (refinementSheafComparison A p j₁ j₂ h).hom
      (p)^*[ModuleCat.{u + 1} A] ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (j₁)_!open[ModuleCat.{u + 1} A]
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p).counit ≫
    (Functor.rightUnitor _).hom

private theorem refinementSheafProjection_open
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U V₁ V₂ : Scheme.{u}} [IsNoetherian U] [IsNoetherian V₁] [IsNoetherian V₂]
    (p : V₁ ⟶ V₂) [IsProper p] (j₁ : U ⟶ V₁) (j₂ : U ⟶ V₂)
    [IsOpenImmersion j₁] [IsOpenImmersion j₂] (h : j₁ ≫ p = j₂)
    (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (j₁)^*[ModuleCat.{u + 1} A].map
        ((refinementSheafProjection A p j₁ j₂ h).app M) =
      (upperStarComp (ModuleCat.{u + 1} A) j₁ p j₂ h.symm).inv.app
          ((j₂)_!open[ModuleCat.{u + 1} A].obj M) ≫
        inv ((openImmersionLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} A) j₂).unit.app M) ≫
        (openImmersionLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} A) j₁).unit.app M := by
  let t₁ := (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) j₁).app M
  let t₂ := (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) j₂).app M
  let e₁ := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) j₁).counit.app M
  let e₂ := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) j₂).counit.app M
  let a₁ := (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j₁).unit.app M
  let a₂ := (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j₂).unit.app M
  have ht₁ : (j₁)^*[ModuleCat.{u + 1} A].map t₁ ≫ e₁ = inv a₁ := by
    apply (cancel_epi a₁).mp
    simpa only [IsIso.hom_inv_id, t₁, e₁, a₁, Functor.id_obj, Category.assoc] using
      unit_map_openImmersionLowerShriekToLowerStar_app_counit (ModuleCat.{u + 1} A) j₁ M
  have ht₂ : (j₂)^*[ModuleCat.{u + 1} A].map t₂ ≫ e₂ = inv a₂ := by
    apply (cancel_epi a₂).mp
    simpa only [IsIso.hom_inv_id, t₂, e₂, a₂, Functor.id_obj, Category.assoc] using
      unit_map_openImmersionLowerShriekToLowerStar_app_counit (ModuleCat.{u + 1} A) j₂ M
  have he₁ : a₁ ≫ (j₁)^*[ModuleCat.{u + 1} A].map t₁ ≫ e₁ = 𝟙 M :=
    unit_map_openImmersionLowerShriekToLowerStar_app_counit _ j₁ M
  apply (cancel_mono (inv a₁)).mp
  simp only [Category.assoc]
  rw [← ht₁]
  erw [he₁, Category.comp_id]
  unfold refinementSheafProjection
  simp only [NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.whiskerLeft_app,
    Functor.rightUnitor_hom_app, Category.id_comp]
  erw [Category.comp_id]
  have hn := refinementSheafComparison_normalization A p j₁ j₂ h M
  have hn' := congrArg (fun f ↦ f ≫
    (lowerStarComp (ModuleCat.{u + 1} A) j₁ p j₂ h.symm).inv.app M) hn
  simp only [Category.assoc, Iso.hom_inv_id_app] at hn'
  erw [Category.comp_id] at hn'
  have hnat := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p).counit.naturality t₁
  dsimp only [Functor.comp_map, Functor.id_map] at hnat
  rw [← Functor.map_comp_assoc, Category.assoc, ← hnat, ← Category.assoc,
    ← Functor.map_comp, hn', Functor.map_comp, Functor.map_comp, Category.assoc]
  rw [Functor.map_comp, Category.assoc,
    ← upperStarComp_inv_app_counit_app (ModuleCat.{u + 1} A) j₁ p M j₂ h.symm]
  erw [(upperStarComp (ModuleCat.{u + 1} A) j₁ p j₂ h.symm).inv.naturality_assoc]
  rw [ht₂]

private theorem refinementSheafProjection_disjoint
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U V₁ V₂ : Scheme.{u}} [IsNoetherian U] [IsNoetherian V₁] [IsNoetherian V₂]
    (p : V₁ ⟶ V₂) [IsProper p] (j₁ : U ⟶ V₁) (j₂ : U ⟶ V₂)
    [IsOpenImmersion j₁] [IsOpenImmersion j₂] (h : j₁ ≫ p = j₂)
    (C : Scheme.{u}) (c : C ⟶ V₁) [IsOpenImmersion c]
    (hc : Disjoint (Set.range c) (Set.range j₁))
    (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (c)^*[ModuleCat.{u + 1} A].map
      ((refinementSheafProjection A p j₁ j₂ h).app M) = 0 := by
  have hz := isInitial_openImmersionRestriction_openImmersionLowerShriek
    (ModuleCat.{u + 1} A) j₁ c hc.symm M
  have hz' : IsZero ((openImmersionRestriction (ModuleCat.{u + 1} A) c).obj
      ((j₁)_!open[ModuleCat.{u + 1} A].obj M)) := hz.isZero
  exact (IsZero.of_iso hz'
    ((upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} A) c).app _)).eq_of_tgt _ _

private theorem exact_rightDerived_representative
    {C D : Type v} [Category.{w} C] [Category.{w} D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (J : CochainComplex C ℤ) [J.IsKInjective] :
    F.rightDerivedFunctorIsoMapDerivedCategory.hom.app (DerivedCategory.Q.obj J) ≫
        F.mapDerivedCategoryFactors.hom.app J =
      (F.rightDerivedFunctorObjQIso J).hom := by
  have hf := congr_app F.rightDerivedFunctorIsoMapDerivedCategory_hom_fac
    ((HomotopyCategory.quotient C (.up ℤ)).obj J)
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hf
  have hfactor : F.mapDerivedCategoryFactorsh.hom.app
      ((HomotopyCategory.quotient C (.up ℤ)).obj J) =
      F.mapDerivedCategoryFactors.hom.app J := by
    rw [Functor.mapDerivedCategoryFactorsh_hom_app]
    simp only [Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_inv,
      DerivedCategory.quotientCompQhIso, HomologicalComplexUpToQuasiIso.quotientCompQhIso,
      Quotient.lift.isLift_hom]
    repeat erw [CategoryTheory.Functor.map_id]
    repeat erw [Category.id_comp]
    repeat erw [Category.comp_id]
  have hf' := congrArg (fun z ↦ z ≫ F.mapDerivedCategoryFactors.hom.app J) hf
  rw [← hfactor, Category.assoc, Iso.inv_hom_id_app] at hf'
  rw [hfactor] at hf'
  apply (cancel_epi (F.rightDerivedFunctorUnit.app
    ((HomotopyCategory.quotient C (.up ℤ)).obj J))).mp
  erw [hf']
  simp only [Functor.rightDerivedFunctorObjQIso, Iso.trans_hom,
    Functor.mapIso_hom, Iso.symm_hom, asIso_inv,
    DerivedCategory.quotientCompQhIso, HomologicalComplexUpToQuasiIso.quotientCompQhIso]
  repeat erw [CategoryTheory.Functor.map_id]
  repeat erw [Category.id_comp]
  change 𝟙 _ = _ ≫ inv _ ≫ (𝟙 _)
  erw [IsIso.hom_inv_id_assoc]

private theorem refinement_identity_representative
    (A : Type (u + 1)) [CommRing A] (U : Scheme.{u})
    (J : CochainComplex (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    [J.IsKInjective] :
    ((((𝟙 U)_*[ModuleCat.{u + 1} A]).rightDerivedFunctorIsoMapDerivedCategory ≪≫
        Functor.mapDerivedCategoryNatIso (lowerStarId (ModuleCat.{u + 1} A) U) ≪≫
        Functor.mapDerivedCategoryIdIso _).hom.app (DerivedCategory.Q.obj J)) =
      (((𝟙 U)_*[ModuleCat.{u + 1} A]).rightDerivedFunctorObjQIso J).hom ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
          (lowerStarId (ModuleCat.{u + 1} A) U).hom (.up ℤ)).app J) := by
  simp only [Iso.trans_hom, NatTrans.comp_app]
  rw [Functor.mapDerivedCategoryIdIso_hom_app_Q_obj,
    Functor.mapDerivedCategoryNatIso_fac, ← Category.assoc,
    exact_rightDerived_representative]

private theorem refinement_comparison_representative
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U V₁ V₂ : Scheme.{u}} [IsNoetherian U] [IsNoetherian V₁] [IsNoetherian V₂]
    (p : V₁ ⟶ V₂) [IsProper p] (j₁ : U ⟶ V₁) (j₂ : U ⟶ V₂)
    [IsOpenImmersion j₁] [IsOpenImmersion j₂] (h : j₁ ≫ p = j₂)
    (J : CochainComplex (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    [J.IsKInjective]
    (I : CochainComplex (Sheaf V₁.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    [I.IsKInjective]
    (ρ : ((j₁)_!open[ModuleCat.{u + 1} A].mapHomologicalComplex (.up ℤ)).obj J ⟶ I)
    [QuasiIso ρ] :
    (unboundedProperOpenRefinementComparison A p j₁ j₂ h).hom.app
        (DerivedCategory.Q.obj J) ≫
      R((p)_*[ModuleCat.{u + 1} A]).map
        (((j₁)_!open[ModuleCat.{u + 1} A]).mapDerivedCategoryFactors.hom.app J ≫
          DerivedCategory.Q.map ρ) ≫
      (((p)_*[ModuleCat.{u + 1} A]).rightDerivedFunctorObjQIso I).hom =
    ((j₂)_!open[ModuleCat.{u + 1} A]).mapDerivedCategoryFactors.hom.app J ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
        (refinementSheafComparison A p j₁ j₂ h).hom (.up ℤ)).app J) ≫
      DerivedCategory.Q.map
        (((p)_*[ModuleCat.{u + 1} A].mapHomologicalComplex (.up ℤ)).map ρ) := by
  let α := (((𝟙 U)_*[ModuleCat.{u + 1} A]).rightDerivedFunctorIsoMapDerivedCategory ≪≫
    Functor.mapDerivedCategoryNatIso (lowerStarId (ModuleCat.{u + 1} A) U) ≪≫
    Functor.mapDerivedCategoryIdIso _)
  let t := (NatIso.mapHomologicalComplex (lowerStarId (ModuleCat.{u + 1} A) U) (.up ℤ))
  have hi : α.inv.app (DerivedCategory.Q.obj J) =
      DerivedCategory.Q.map (t.inv.app J) ≫
        (((𝟙 U)_*[ModuleCat.{u + 1} A]).rightDerivedFunctorObjQIso J).inv := by
    apply (cancel_mono (α.hom.app (DerivedCategory.Q.obj J))).mp
    rw [Iso.inv_hom_id_app]
    change _ = _ ≫
      ((((𝟙 U)_*[ModuleCat.{u + 1} A]).rightDerivedFunctorIsoMapDerivedCategory ≪≫
        Functor.mapDerivedCategoryNatIso (lowerStarId (ModuleCat.{u + 1} A) U) ≪≫
        Functor.mapDerivedCategoryIdIso _).hom.app (DerivedCategory.Q.obj J))
    rw [refinement_identity_representative]
    erw [Category.assoc, Iso.inv_hom_id_assoc]
    erw [← DerivedCategory.Q.map_comp]
    change 𝟙 _ = DerivedCategory.Q.map (t.inv.app J ≫ t.hom.app J)
    rw [Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  have hn := (properOpenRefinementData A p j₁ j₂ h).derived_fac J I ρ
  unfold unboundedProperOpenRefinementComparison
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
    NatTrans.comp_app, Functor.leftUnitor_inv_app, Functor.whiskerRight_app,
    Category.id_comp, Category.assoc]
  erw [← hn]
  change D((j₂)_!open[ModuleCat.{u + 1} A]).map (α.inv.app _) ≫ _ = _
  rw [hi, Functor.map_comp]
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp]
  erw [((j₂)_!open[ModuleCat.{u + 1} A]).mapDerivedCategoryFactors.hom.naturality_assoc]
  unfold refinementSheafComparison
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
    NatTrans.comp_app, NatTrans.mapHomologicalComplex_comp, Functor.map_comp, Category.assoc]
  have hu : (NatTrans.mapHomologicalComplex
      (Functor.leftUnitor (j₂)_!open[ModuleCat.{u + 1} A]).inv (.up ℤ)).app J = 𝟙 _ := by
    apply HomologicalComplex.hom_ext
    intro n
    rfl
  have ht : (((j₂)_!open[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).map
      (t.inv.app J) = (NatTrans.mapHomologicalComplex
        (Functor.whiskerRight (lowerStarId (ModuleCat.{u + 1} A) U).inv
          (j₂)_!open[ModuleCat.{u + 1} A]) (.up ℤ)).app J := by
    apply HomologicalComplex.hom_ext
    intro n
    rfl
  erw [hu, CategoryTheory.Functor.map_id, Category.id_comp, ← ht]
  rfl

private theorem counit_quotient_factors
    {C D : Type v} [Category.{w} C] [Category.{w} D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) (P : D ⥤ C) [F.Additive] [P.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (adj : F ⊣ P) (I : CochainComplex D ℤ) :
    F.mapDerivedCategory.map
        ((DerivedCategory.quotientCompQhIso C).inv.app
          ((P.mapHomologicalComplex (.up ℤ)).obj I)) ≫
      F.mapDerivedCategoryFactorsh.hom.app
        ((HomotopyCategory.quotient C (.up ℤ)).obj
          ((P.mapHomologicalComplex (.up ℤ)).obj I)) ≫
      DerivedCategory.Qh.map ((adj.mapHomotopyCategory (.up ℤ)).counit.app
        ((HomotopyCategory.quotient D (.up ℤ)).obj I)) ≫
      (DerivedCategory.quotientCompQhIso D).hom.app I =
    F.mapDerivedCategoryFactors.hom.app ((P.mapHomologicalComplex (.up ℤ)).obj I) ≫
      DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).counit.app I) := by
  simp only [Functor.mapDerivedCategoryFactorsh_hom_app,
    Adjunction.mapHomotopyCategory_counit_app_quotient,
    Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_inv,
    DerivedCategory.quotientCompQhIso, HomologicalComplexUpToQuasiIso.quotientCompQhIso,
    Quotient.lift.isLift_hom]
  repeat erw [CategoryTheory.Functor.map_id]
  repeat erw [Category.id_comp]
  repeat erw [Category.comp_id]
  rfl

private theorem refinement_counit_representative
    (A : Type (u + 1)) [CommRing A] {V₁ V₂ : Scheme.{u}} (p : V₁ ⟶ V₂)
    (I : CochainComplex (Sheaf V₁.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    [I.IsKInjective] :
    (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p).counit.app
        (DerivedCategory.Q.obj I) =
      D((p)^*[ModuleCat.{u + 1} A]).map
          (((p)_*[ModuleCat.{u + 1} A]).rightDerivedFunctorObjQIso I).hom ≫
        ((p)^*[ModuleCat.{u + 1} A]).mapDerivedCategoryFactors.hom.app
          ((((p)_*[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).obj I) ≫
        DerivedCategory.Q.map
          (((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p).mapHomologicalComplex
            (.up ℤ)).counit.app I) := by
  exact (derivedCounitKInjectiveTermwise A p I).trans
    (congrArg (fun t ↦ D((p)^*[ModuleCat.{u + 1} A]).map
      (((p)_*[ModuleCat.{u + 1} A]).rightDerivedFunctorObjQIso I).hom ≫ t)
      (counit_quotient_factors (p)^*[ModuleCat.{u + 1} A] (p)_*[ModuleCat.{u + 1} A]
        (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p) I))

private theorem exact_natTrans_descent
    {C₀ C₁ C₂ : Type v} [Category.{w} C₀] [Category.{w} C₁] [Category.{w} C₂]
    [Abelian C₀] [Abelian C₁] [Abelian C₂]
    [HasDerivedCategory C₀] [HasDerivedCategory C₁] [HasDerivedCategory C₂]
    (E : C₀ ⥤ C₁) (F : C₁ ⥤ C₂) (K : C₀ ⥤ C₂)
    [E.Additive] [F.Additive] [K.Additive]
    [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits K] [PreservesFiniteColimits K] (π : E ⋙ F ⟶ K) :
    ∃ δ : E.mapDerivedCategory ⋙ F.mapDerivedCategory ⟶ K.mapDerivedCategory,
      ∀ J : CochainComplex C₀ ℤ,
        F.mapDerivedCategory.map (E.mapDerivedCategoryFactors.hom.app J) ≫
          F.mapDerivedCategoryFactors.hom.app ((E.mapHomologicalComplex (.up ℤ)).obj J) ≫
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex π (.up ℤ)).app J) =
        δ.app (DerivedCategory.Q.obj J) ≫ K.mapDerivedCategoryFactors.hom.app J := by
  let η := Localization.liftNatTrans DerivedCategory.Q
    (HomologicalComplex.quasiIso C₀ (.up ℤ))
    ((E ⋙ F).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (K.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (E ⋙ F).mapDerivedCategory K.mapDerivedCategory
    (Functor.whiskerRight (NatTrans.mapHomologicalComplex π (.up ℤ)) DerivedCategory.Q)
  refine ⟨(Functor.mapDerivedCategoryCompIso E F).inv ≫ η, fun J => ?_⟩
  have hE : Localization.Lifting.iso DerivedCategory.Q
      (HomologicalComplex.quasiIso C₀ (.up ℤ))
      ((E ⋙ F).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
      (E ⋙ F).mapDerivedCategory = (E ⋙ F).mapDerivedCategoryFactors := rfl
  have hK : Localization.Lifting.iso DerivedCategory.Q
      (HomologicalComplex.quasiIso C₀ (.up ℤ))
      (K.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
      K.mapDerivedCategory = K.mapDerivedCategoryFactors := rfl
  have hη : η.app (DerivedCategory.Q.obj J) ≫ K.mapDerivedCategoryFactors.hom.app J =
      (E ⋙ F).mapDerivedCategoryFactors.hom.app J ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex π (.up ℤ)).app J) := by
    simp only [η, Localization.liftNatTrans_app, hE, hK,
      Functor.whiskerRight_app, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  dsimp only [NatTrans.comp_app]
  rw [Category.assoc, hη]
  have hf := Functor.mapDerivedCategoryCompIso_fac E F J
  have hcomp : (Functor.mapHomologicalComplexCompIso (Iso.refl (E ⋙ F))
      (.up ℤ)).hom.app J = 𝟙 _ := rfl
  erw [hcomp, CategoryTheory.Functor.map_id, Category.comp_id] at hf
  rw [← hf]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]

private theorem refinement_projection_complex
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U V₁ V₂ : Scheme.{u}} [IsNoetherian U] [IsNoetherian V₁] [IsNoetherian V₂]
    (p : V₁ ⟶ V₂) [IsProper p] (j₁ : U ⟶ V₁) (j₂ : U ⟶ V₂)
    [IsOpenImmersion j₁] [IsOpenImmersion j₂] (h : j₁ ≫ p = j₂)
    (J : CochainComplex (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    (NatTrans.mapHomologicalComplex (refinementSheafProjection A p j₁ j₂ h)
        (.up ℤ)).app J =
      (((p)^*[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).map
        ((NatTrans.mapHomologicalComplex (refinementSheafComparison A p j₁ j₂ h).hom
          (.up ℤ)).app J) ≫
        (((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p).mapHomologicalComplex
          (.up ℤ)).counit.app
          (((j₁)_!open[ModuleCat.{u + 1} A].mapHomologicalComplex (.up ℤ)).obj J)) := by
  apply HomologicalComplex.hom_ext
  intro n
  simp only [NatTrans.mapHomologicalComplex_app_f, HomologicalComplex.comp_f,
    Functor.mapHomologicalComplex_map_f, Adjunction.mapHomologicalComplex_counit_app_f,
    refinementSheafProjection, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app,
    Category.id_comp]
  erw [Category.comp_id]
  rfl

private theorem exact_counit_resolution
    {C D : Type v} [Category.{w} C] [Category.{w} D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) (P : D ⥤ C) [F.Additive] [P.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (adj : F ⊣ P)
    (X : CochainComplex C ℤ) (Y I : CochainComplex D ℤ)
    (t : X ⟶ (P.mapHomologicalComplex (.up ℤ)).obj Y) (ρ : Y ⟶ I) :
    F.mapDerivedCategory.map
        (DerivedCategory.Q.map t ≫ DerivedCategory.Q.map
          ((P.mapHomologicalComplex (.up ℤ)).map ρ)) ≫
      F.mapDerivedCategoryFactors.hom.app ((P.mapHomologicalComplex (.up ℤ)).obj I) ≫
      DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).counit.app I) =
    F.mapDerivedCategoryFactors.hom.app X ≫
      DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map t ≫
        (adj.mapHomologicalComplex (.up ℤ)).counit.app Y) ≫ DerivedCategory.Q.map ρ := by
  rw [Functor.map_comp, Category.assoc]
  erw [F.mapDerivedCategoryFactors.hom.naturality_assoc]
  simp only [Functor.comp_map]
  rw [← DerivedCategory.Q.map_comp]
  have hn := (adj.mapHomologicalComplex (.up ℤ)).counit.naturality ρ
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  rw [hn, Functor.map_comp]
  erw [F.mapDerivedCategoryFactors.hom.naturality_assoc]
  simp only [Functor.comp_map]
  rw [← DerivedCategory.Q.map_comp_assoc]

private theorem refinement_mate_representative
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U V₁ V₂ : Scheme.{u}} [IsNoetherian U] [IsNoetherian V₁] [IsNoetherian V₂]
    (p : V₁ ⟶ V₂) [IsProper p] (j₁ : U ⟶ V₁) (j₂ : U ⟶ V₂)
    [IsOpenImmersion j₁] [IsOpenImmersion j₂] (h : j₁ ≫ p = j₂)
    (J : CochainComplex (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    [J.IsKInjective]
    (I : CochainComplex (Sheaf V₁.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    [I.IsKInjective]
    (ρ : ((j₁)_!open[ModuleCat.{u + 1} A].mapHomologicalComplex (.up ℤ)).obj J ⟶ I)
    [QuasiIso ρ] :
    D((p)^*[ModuleCat.{u + 1} A]).map
        ((unboundedProperOpenRefinementComparison A p j₁ j₂ h).hom.app
          (DerivedCategory.Q.obj J)) ≫
      (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p).counit.app
        (D((j₁)_!open[ModuleCat.{u + 1} A]).obj (DerivedCategory.Q.obj J)) ≫
      ((j₁)_!open[ModuleCat.{u + 1} A]).mapDerivedCategoryFactors.hom.app J ≫
      DerivedCategory.Q.map ρ =
    D((p)^*[ModuleCat.{u + 1} A]).map
        (((j₂)_!open[ModuleCat.{u + 1} A]).mapDerivedCategoryFactors.hom.app J) ≫
      ((p)^*[ModuleCat.{u + 1} A]).mapDerivedCategoryFactors.hom.app
        (((j₂)_!open[ModuleCat.{u + 1} A].mapHomologicalComplex (.up ℤ)).obj J) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
        (refinementSheafProjection A p j₁ j₂ h) (.up ℤ)).app J) ≫
      DerivedCategory.Q.map ρ := by
  let F := (p)^*[ModuleCat.{u + 1} A]
  let P := (p)_*[ModuleCat.{u + 1} A]
  let K := (j₁)_!open[ModuleCat.{u + 1} A]
  let E := (j₂)_!open[ModuleCat.{u + 1} A]
  let ε := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p).mapHomologicalComplex
    (.up ℤ)
  have hε := (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p).counit.naturality
    (K.mapDerivedCategoryFactors.hom.app J ≫ DerivedCategory.Q.map ρ)
  dsimp only [Functor.comp_map, Functor.id_map] at hε
  erw [← hε,
    refinement_counit_representative A p I]
  erw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
  erw [Category.assoc _ _
    (((p)_*[ModuleCat.{u + 1} A]).rightDerivedFunctorObjQIso I).hom]
  erw [refinement_comparison_representative A p j₁ j₂ h J I ρ]
  erw [Functor.map_comp, Category.assoc]
  erw [exact_counit_resolution F P (upperStarLowerStarAdjunction
    (ModuleCat.{u + 1} A) p) _ _ I
    ((NatTrans.mapHomologicalComplex (refinementSheafComparison A p j₁ j₂ h).hom
      (.up ℤ)).app J) ρ]
  erw [← refinement_projection_complex A p j₁ j₂ h J]

private theorem exact_ext_on_kinjective_resolutions
    {C D : Type v} [Category.{w} C] [Category.{w} D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions D]
    (K : C ⥤ D) [K.Additive] [PreservesFiniteLimits K] [PreservesFiniteColimits K]
    {L : DerivedCategory C ⥤ DerivedCategory D} (α β : L ⟶ K.mapDerivedCategory)
    (h : ∀ (J : CochainComplex C ℤ) [J.IsKInjective]
      (I : CochainComplex D ℤ) [I.IsKInjective]
      (ρ : (K.mapHomologicalComplex (.up ℤ)).obj J ⟶ I) [QuasiIso ρ],
      α.app (DerivedCategory.Q.obj J) ≫ K.mapDerivedCategoryFactors.hom.app J ≫
          DerivedCategory.Q.map ρ =
        β.app (DerivedCategory.Q.obj J) ≫ K.mapDerivedCategoryFactors.hom.app J ≫
          DerivedCategory.Q.map ρ) : α = β := by
  apply NatTrans.ext
  funext X
  obtain ⟨J, hJ, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective X
  have heq : α.app (DerivedCategory.Q.obj J) = β.app (DerivedCategory.Q.obj J) := by
    obtain ⟨I, hI, ρ, _, hρ⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective
      ((K.mapHomologicalComplex (.up ℤ)).obj J)
    have hQρ : IsIso (DerivedCategory.Q.map ρ) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso _ ρ).2 hρ
    apply (cancel_mono (K.mapDerivedCategoryFactors.hom.app J)).mp
    apply (cancel_mono (DerivedCategory.Q.map ρ)).mp
    simpa only [Category.assoc] using h J I ρ
  apply (cancel_mono (K.mapDerivedCategory.map e.hom)).mp
  rw [← α.naturality, heq, β.naturality]

/-- The clopen-section projection is natural, descends degreewise to all unbounded
complexes, and is the adjoint of the specified proper/open comparison.
Source: Stacks Project, Tags 0F7B, 03S6, 01KT and 015F; explicit clopen calculation in
(blueprint: lem-asd-proper-open-refinement-adjoint-projection).

Proof:
1. Form W = V₁ ×[V₂] U. The lift (j₁,id) is an open section of W → U.
   The latter is proper by proper base change, hence separated. By open_section_clopen,
   W splits into the section and its complementary open. Open-extension base change
   identifies p* j₂! M with extension from W of the pullback of M. The finite clopen
   sheaf decomposition defines its projection: identity on the section and zero on
   the complement. It is natural in M. The first displayed formula expresses identity
   on the section using the inverse-image compositor and the two open units; the
   second expresses zero on every disjoint open, including the complementary component.
2. Exact inverse image and exact extension by zero preserve quasi-isomorphisms.
   Apply the projection degreewise and descend through localization. The third formula
   specifies this descent on every complex, without any bound.
3. Choose K-injective J on U and a K-injective resolution rho: j₁!J → I.
   The normalized comparison is j₂!J = p_*j₁!J → p_*I. The canonical derived
   counit at QI is represented by the ordinary counit p*p_*I → I
   (lem-asd-derived-counit-k-injective-termwise). Naturality along rho reduces its
   composite with the comparison to the ordinary counit composite at j₁!J.
   Proper-support composition identifies j₂!M = p_*j₁!M. Restricting to W gives
   q*q_*s_*M → s_*M for the section s and projection q, with qs = id. Under the
   clopen sheaf decomposition this is identity on s(U) and zero on its complement,
   precisely the projection of step 1, with the inverse base-change normalization.
   Outside W both maps vanish. Naturality and resolution independence give the final
   equality of natural transformations on the entire unbounded derived category. -/
theorem properOpenRefinement_adjoint_projection
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U V₁ V₂ : Scheme.{u}} [IsNoetherian U] [IsNoetherian V₁] [IsNoetherian V₂]
    (p : V₁ ⟶ V₂) [IsProper p] (j₁ : U ⟶ V₁) (j₂ : U ⟶ V₂)
    [IsOpenImmersion j₁] [IsOpenImmersion j₂] (h : j₁ ≫ p = j₂) :
    ∃ (π : (j₂)_!open[ModuleCat.{u + 1} A] ⋙ (p)^*[ModuleCat.{u + 1} A] ⟶
        (j₁)_!open[ModuleCat.{u + 1} A])
      (Dπ : D((j₂)_!open[ModuleCat.{u + 1} A]) ⋙ D((p)^*[ModuleCat.{u + 1} A]) ⟶
        D((j₁)_!open[ModuleCat.{u + 1} A])),
      (∀ M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A),
        (j₁)^*[ModuleCat.{u + 1} A].map (π.app M) =
          (upperStarComp (ModuleCat.{u + 1} A) j₁ p j₂ h.symm).inv.app
              ((j₂)_!open[ModuleCat.{u + 1} A].obj M) ≫
            inv ((openImmersionLowerShriekUpperStarAdjunction
              (ModuleCat.{u + 1} A) j₂).unit.app M) ≫
            (openImmersionLowerShriekUpperStarAdjunction
              (ModuleCat.{u + 1} A) j₁).unit.app M) ∧
      (∀ (C : Scheme.{u}) (c : C ⟶ V₁) [IsOpenImmersion c],
        Disjoint (Set.range c) (Set.range j₁) →
          ∀ M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A),
            (c)^*[ModuleCat.{u + 1} A].map (π.app M) = 0) ∧
      (∀ J : CochainComplex (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ,
        D((p)^*[ModuleCat.{u + 1} A]).map
            (((j₂)_!open[ModuleCat.{u + 1} A]).mapDerivedCategoryFactors.hom.app J) ≫
          ((p)^*[ModuleCat.{u + 1} A]).mapDerivedCategoryFactors.hom.app
            (((j₂)_!open[ModuleCat.{u + 1} A].mapHomologicalComplex (.up ℤ)).obj J) ≫
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex π (.up ℤ)).app J) =
        Dπ.app (DerivedCategory.Q.obj J) ≫
          ((j₁)_!open[ModuleCat.{u + 1} A]).mapDerivedCategoryFactors.hom.app J) ∧
      Functor.whiskerRight (unboundedProperOpenRefinementComparison A p j₁ j₂ h).hom
          D((p)^*[ModuleCat.{u + 1} A]) ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft D((j₁)_!open[ModuleCat.{u + 1} A])
          (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p).counit ≫
        (Functor.rightUnitor _).hom = Dπ := by
  classical
  obtain ⟨δ, hδ⟩ := exact_natTrans_descent
    (j₂)_!open[ModuleCat.{u + 1} A] (p)^*[ModuleCat.{u + 1} A]
    (j₁)_!open[ModuleCat.{u + 1} A] (refinementSheafProjection A p j₁ j₂ h)
  refine ⟨refinementSheafProjection A p j₁ j₂ h, δ,
    refinementSheafProjection_open A p j₁ j₂ h,
    refinementSheafProjection_disjoint A p j₁ j₂ h, hδ, ?_⟩
  apply exact_ext_on_kinjective_resolutions (j₁)_!open[ModuleCat.{u + 1} A]
  intro J _ I _ ρ _
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app]
  simp only [Category.id_comp, Category.assoc]
  erw [Category.id_comp, refinement_mate_representative A p j₁ j₂ h J I ρ]
  exact (reassoc_of% (hδ J)) (DerivedCategory.Q.map ρ)


end AlgebraicGeometry.Etale
