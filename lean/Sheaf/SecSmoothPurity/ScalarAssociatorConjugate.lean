/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E4
-/
module

public import Sheaf.SecSmoothPurity.ScalarExtensionFunctor
public import Sheaf.Paper.FourCorners
public import Mathlib.CategoryTheory.Adjunction.Mates
import all Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization
import all Sheaf.Paper.AdicCoefficientDatum

/-! The right conjugate of the prescribed scalar associator.
Source: Stacks Tags 06YY, 07A6 and 0D6D.
(blueprint: lem-sp-scalar-associator-conjugate) -/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale


open CategoryTheory.Limits CategoryTheory.Functor
open SheafOfModules.SuccessiveDerivedQuotient

private local instance proEtSmall (T : Scheme.{u}) : EssentiallySmall.{u + 1} T.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} _

attribute [local irreducible] completedAdicChange completedAdicDerivedChange
attribute [local irreducible] reductionChange reductionDerivedChange
attribute [local irreducible] HasDerivedCategory.standard
attribute [local irreducible] SheafOfModules.monoidalCategory

private noncomputable def publishedPresentation (T : Scheme.{u})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (a : R ⟶ S) :
    Presentation.{u + 1, u, u + 1, u + 2} a where
  ordinary := reductionChange T a
  obj_eq := reductionChange_obj_eq T a
  map_eq := reductionChange_map_eq T a
  additive := reductionChangeAdditive T a
  derived := reductionDerivedChange T a
  counit := reductionDerivedCounit T a
  universal := reductionDerivedUniversal T a

private theorem complexCounitApp
    {D E : Type*} [Category D] [Category E] [Abelian D] [Abelian E]
    [HasDerivedCategory D] [HasDerivedCategory E]
    (F : D ⥤ E) [F.Additive] (L : DerivedCategory D ⥤ DerivedCategory E)
    (ε : DerivedCategory.Qh ⋙ L ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (P : CochainComplex D ℤ) :
    reductionComplexCounit F L ε P = ε.app ((HomotopyCategory.quotient _ _).obj P) := by
  dsimp only [reductionComplexCounit, DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso,
    Quotient.lift.isLift_hom, Quotient.lift.isLift_inv,
    Functor.mapHomotopyCategoryFactors]
  erw [L.map_id, DerivedCategory.Qh.map_id, Category.comp_id, Category.id_comp]
  exact Category.comp_id _

private theorem quotientMap
    {D : Type*} [Category D] [Abelian D] [HasDerivedCategory D]
    {P Q : CochainComplex D ℤ} (f : P ⟶ Q) :
    DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map f) =
      DerivedCategory.Q.map f := by
  have h := DerivedCategory.quotientCompQhIso_hom_naturality f
  dsimp only [DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso, Quotient.lift.isLift_hom] at h
  erw [Category.comp_id, Category.id_comp] at h
  exact h

private theorem homComparisonUnit
    {D E : Type*} [Category D] [Category E] [Abelian D] [Abelian E]
    [HasDerivedCategory D] [HasDerivedCategory E]
    (F : D ⥤ E) (G : E ⥤ D) [F.Additive] [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (a : F ⊣ G) (L : DerivedCategory D ⥤ DerivedCategory E)
    (ε : DerivedCategory.Qh ⋙ L ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (d : L ⊣ G.mapDerivedCategory)
    (h : ∀ (H : HomotopyCategory D (.up ℤ))
      (K : HomotopyCategory E (.up ℤ))
      (f : (F.mapHomotopyCategory (.up ℤ)).obj H ⟶ K),
      d.homEquiv _ _ (ε.app H ≫ DerivedCategory.Qh.map f) =
        DerivedCategory.Qh.map ((a.mapHomotopyCategory (.up ℤ)).homEquiv H K f) ≫
          G.mapDerivedCategoryFactorsh.inv.app K)
    (P : CochainComplex D ℤ) :
    d.unit.app (DerivedCategory.Q.obj P) ≫
      G.mapDerivedCategory.map (reductionComplexCounit F L ε P) ≫
      G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) =
    DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex a.unit (.up ℤ)).app P) := by
  have hp := h ((HomotopyCategory.quotient _ _).obj P)
    ((F.mapHomotopyCategory (.up ℤ)).obj ((HomotopyCategory.quotient _ _).obj P)) (𝟙 _)
  erw [DerivedCategory.Qh.map_id, Category.comp_id] at hp
  simp only [Adjunction.homEquiv_unit] at hp
  erw [(G.mapHomotopyCategory (.up ℤ)).map_id, Category.comp_id] at hp
  have hp' := congrArg (fun f ↦ f ≫ G.mapDerivedCategoryFactorsh.hom.app _) hp
  simp only [Category.assoc, Iso.inv_hom_id_app] at hp'
  erw [Category.comp_id] at hp'
  change d.unit.app (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj P)) ≫
    G.mapDerivedCategory.map (ε.app ((HomotopyCategory.quotient _ _).obj P)) ≫
    G.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.quotient _ _).obj
      ((F.mapHomologicalComplex (.up ℤ)).obj P)) =
    DerivedCategory.Qh.map ((a.mapHomotopyCategory (.up ℤ)).unit.app
      ((HomotopyCategory.quotient _ _).obj P)) at hp'
  erw [Functor.mapDerivedCategoryFactorsh_hom_app,
    Adjunction.mapHomotopyCategory_unit_app_quotient] at hp'
  dsimp only [reductionComplexCounit, DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso,
    Quotient.lift.isLift_hom, Quotient.lift.isLift_inv,
    Functor.mapHomotopyCategoryFactors, CategoryTheory.Functor.map_id,
    Category.id_comp, Category.comp_id] at hp' ⊢
  erw [L.map_id, DerivedCategory.Qh.map_id, Category.comp_id, Category.id_comp]
  erw [G.mapDerivedCategory.map_id, DerivedCategory.Qh.map_id, Category.comp_id,
    Category.comp_id] at hp'
  erw [Category.comp_id]
  erw [Category.id_comp] at hp'
  erw [quotientMap] at hp'
  exact hp'

private theorem publishedTensor (T : Scheme.{u})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (a : R ⟶ S)
    (M : reductionModules T R) (U : T.ProEtᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U) :
    sectionTensor (publishedPresentation T a) M U s x = pbcTensorSection a M U s x := by
  dsimp only [sectionTensor, SheafOfModules.SuccessiveDerivedQuotient.pure,
    publishedPresentation, pbcTensorSection,
    completedAdicChangeTensor, completedAdicChange]
  with_unfolding_all rfl

private theorem publishedAdjData (T : Scheme.{u})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (a : R ⟶ S)
    (d : AdjData.{u + 1, u, u + 1, u + 2} (publishedPresentation T a)) :
    d.ordinary = pbcScalarAdjunction a ∧ d.derived = pbcDerivedScalarAdjunction a := by
  have ho : d.ordinary = pbcScalarAdjunction a := by
    apply (pbcScalarAdjunction_exists a).unique
    · intro M V x
      exact (d.ordinary_unit M V x).trans (publishedTensor T a M V 1 x)
    · exact (pbcScalarAdjunction_exists a).exists.choose_spec
  refine ⟨ho, ?_⟩
  apply (pbcDerivedScalarAdjunction_exists a).unique
  · intro P hp
    have h := homComparisonUnit (pbcExtend a) (pbcRestrict a)
      d.ordinary (pbcDerivedExtend a) (pbcExtensionCounit a)
      d.derived d.hom_comparison P
    rw [ho] at h
    exact h
  · exact (pbcDerivedScalarAdjunction_exists a).exists.choose_spec

private noncomputable def publishedData (T : Scheme.{u})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (a : R ⟶ S) :
    AdjData.{u + 1, u, u + 1, u + 2} (publishedPresentation T a) :=
  Classical.choice (adjData_exists (publishedPresentation T a))

private theorem publishedComp_exists (T : Scheme.{u})
    {R S V : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (a : R ⟶ S) (b : S ⟶ V) (c : R ⟶ V) (h : a ≫ b = c) :
    ∃! e : reductionDerivedChange T a ⋙ reductionDerivedChange T b ≅
        reductionDerivedChange T c,
      e = derivedComp (publishedPresentation T) (publishedData T) a b ≪≫
        eqToIso (congrArg (fun f ↦ reductionDerivedChange T f) h) := by
  exact ⟨_, rfl, fun _ he ↦ he⟩

-- Keep the comparison behind its proved equation: projecting a concrete composite
-- adjunction otherwise unfolds the complete chosen localization during kernel checking.
private noncomputable def publishedComp (T : Scheme.{u})
    {R S V : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (a : R ⟶ S) (b : S ⟶ V) (c : R ⟶ V) (h : a ≫ b = c) :
    reductionDerivedChange T a ⋙ reductionDerivedChange T b ≅
      reductionDerivedChange T c :=
  (publishedComp_exists T a b c h).exists.choose

private theorem publishedComp_eq (T : Scheme.{u})
    {R S V : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (a : R ⟶ S) (b : S ⟶ V) (c : R ⟶ V) (h : a ≫ b = c) :
    publishedComp T a b c h =
      derivedComp (publishedPresentation T) (publishedData T) a b ≪≫
        eqToIso (congrArg (fun f ↦ reductionDerivedChange T f) h) :=
  (publishedComp_exists T a b c h).exists.choose_spec

private theorem publishedRepresentative (T : Scheme.{u})
    {R S V : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (a : R ⟶ S) (b : S ⟶ V) (c : R ⟶ V) (h : a ≫ b = c)
    (P : CochainComplex (reductionModules T R) ℤ) :
    (publishedComp T a b c h).hom.app
        (DerivedCategory.Q.obj P) ≫ reductionScalarComplexCounit T c P =
      (reductionDerivedChange T b).map (reductionScalarComplexCounit T a P) ≫
        reductionScalarComplexCounit T b ((reductionChangeComplex T a).obj P) ≫
        DerivedCategory.Q.map (reductionBalance T a b c h P) := by
  rw [publishedComp_eq]
  subst c
  let e := ordinaryComp (publishedPresentation T)
    (fun a ↦ (publishedData T a).ordinary) a b
  have he : (Functor.mapHomologicalComplexCompIso e (.up ℤ)).hom.app P =
      reductionBalance T a b (a ≫ b) rfl P := by
    apply (reductionBalance_exists T a b (a ≫ b) rfl P).unique
    · refine ⟨by infer_instance, ?_⟩
      intro n U s r x
      have hh := ordinaryComp_hom (publishedPresentation T)
        (fun a ↦ (publishedData T a).ordinary)
        (fun a ↦ (publishedData T a).ordinary_unit) a b (P.X n) U x r s
      rw [mul_comm] at hh
      simp only [publishedTensor] at hh
      dsimp only [reductionTensorSection]
      with_unfolding_all exact hh
    · exact (reductionBalance_exists T a b (a ≫ b) rfl P).exists.choose_spec
  have hd := derivedComp_representative (publishedPresentation T) (publishedData T)
    a b ((HomotopyCategory.quotient _ _).obj P)
  simp only [Iso.trans_hom, eqToIso_refl, Iso.refl_hom,
    Category.comp_id, reductionScalarComplexCounit, complexCounitApp]
  erw [← he, ← quotientMap]
  change _ ≫ _ = _ ≫ _ ≫ DerivedCategory.Qh.map
    ((HomotopyCategory.quotient _ _).map
      ((mapHomologicalComplexCompIso e (.up ℤ)).hom.app P))
  exact hd


private noncomputable def normalizedScalarComp (T : Scheme.{u})
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) :
    scalarExtensionFunctor φ T ⋙ scalarExtensionFunctor ψ T ≅
      scalarExtensionFunctor (ψ.comp φ) T :=
  publishedComp T
    (proEtaleConstantRingMap (T := T) φ) (proEtaleConstantRingMap (T := T) ψ)
    (proEtaleConstantRingMap (T := T) (ψ.comp φ))
    (scalarExtensionFunctor_ringMap_comp φ ψ T)

private theorem normalizedScalarComp_eq (T : Scheme.{u})
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) :
    scalarExtensionFunctor_composition φ ψ T = normalizedScalarComp T φ ψ := by
  symm
  apply (scalarExtensionFunctor_composition_existsUnique φ ψ T).unique
  · intro P hp
    exact publishedRepresentative T
      (proEtaleConstantRingMap (T := T) φ) (proEtaleConstantRingMap (T := T) ψ)
      (proEtaleConstantRingMap (T := T) (ψ.comp φ))
      (scalarExtensionFunctor_ringMap_comp φ ψ T) P
  · exact (scalarExtensionFunctor_composition_existsUnique φ ψ T).exists.choose_spec

private theorem publishedRightComp (T : Scheme.{u})
    {R S V : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (a : R ⟶ S) (b : S ⟶ V) :
    rightComp a b = pbcDerivedRestrictComp a b (a ≫ b) rfl := by
  have hr : resComp a b = pbcRestrictComp a b (a ≫ b) rfl := by
    apply (pbcRestrictComp_exists a b (a ≫ b) rfl).unique
    · intro M U x
      rfl
    · exact (pbcRestrictComp_exists a b (a ≫ b) rfl).exists.choose_spec
  unfold rightComp pbcDerivedRestrictComp
  rw [hr]

private theorem publishedConjugate (T : Scheme.{u})
    {R S V : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (a : R ⟶ S) (b : S ⟶ V) (c : R ⟶ V) (h : a ≫ b = c) :
    conjugateEquiv
        ((proEtaleRingDerivedExtensionAdjunction a).comp
          (proEtaleRingDerivedExtensionAdjunction b))
        (proEtaleRingDerivedExtensionAdjunction c)
        (publishedComp T a b c h).inv =
      (pbcDerivedRestrictComp a b c h).hom := by
  change conjugateEquiv
    ((pbcDerivedScalarAdjunction a).comp (pbcDerivedScalarAdjunction b))
    (pbcDerivedScalarAdjunction c) (publishedComp T a b c h).inv = _
  rw [publishedComp_eq]
  subst c
  simp only [eqToIso_refl, Iso.trans_refl]
  have hd := derivedComp_eq (publishedPresentation T) (publishedData T) a b
  rw [hd]
  rw [(publishedAdjData T a (publishedData T a)).2,
    (publishedAdjData T b (publishedData T b)).2,
    (publishedAdjData T (a ≫ b) (publishedData T (a ≫ b))).2]
  rw [Adjunction.conjugateEquiv_leftAdjointCompIso_inv]
  rw [publishedRightComp T a b]

/-- The prescribed balanced scalar associator is conjugate to restriction composition.
Source: Stacks Tags 06YY, 07A6 and 0D6D; scalar extension blueprint clause (4).
(blueprint: lem-sp-scalar-associator-conjugate).

Proof: bundle the published ordinary tensor functor, its fixed object and map equations,
and its universal derived pair as a Presentation. Choose the normalized adjunction data
of successive derived quotient normalization. Ordinary tensor-unit uniqueness identifies
its ordinary adjunction with pbcScalarAdjunction. The Hom comparison, evaluated at the
identity and transported by mapDerivedCategoryFactorsh, gives its derived unit on every
cochain representative. Derived unit uniqueness then identifies its derived adjunction
with pbcDerivedScalarAdjunction. The ordinary composite comparison sends
s tensor (r tensor x) to s*b(r) tensor x, hence equals reductionBalance, by the latter's
uniqueness. The representative equation for the derived comparison therefore is precisely
the normalization defining scalarExtensionFunctor_composition. Its uniqueness identifies
those comparisons. Finally the composite adjunction comparison has right conjugate equal
to restriction composition. Both ordinary restriction comparisons are identity on sections,
so their uniqueness identifies them, and exact localization gives pbcDerivedRestrictComp.
No flatness or finiteness is required in this normalization argument. -/
theorem scalarAssociatorConjugate
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) (T : Scheme.{u}) :
    conjugateEquiv
      ((proEtaleRingDerivedExtensionAdjunction
        (proEtaleConstantRingMap (T := T) φ)).comp
        (proEtaleRingDerivedExtensionAdjunction (proEtaleConstantRingMap (T := T) ψ)))
      (proEtaleRingDerivedExtensionAdjunction
        (proEtaleConstantRingMap (T := T) (ψ.comp φ)))
      (scalarExtensionFunctor_composition φ ψ T).inv =
    (pbcDerivedRestrictComp _ _ _ (scalarExtensionFunctor_ringMap_comp φ ψ T)).hom := by
  rw [normalizedScalarComp_eq]
  exact publishedConjugate T
    (proEtaleConstantRingMap (T := T) φ) (proEtaleConstantRingMap (T := T) ψ)
    (proEtaleConstantRingMap (T := T) (ψ.comp φ))
    (scalarExtensionFunctor_ringMap_comp φ ψ T)

end AlgebraicGeometry.ProEtale
