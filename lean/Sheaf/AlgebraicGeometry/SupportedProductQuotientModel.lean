/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q106
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleSupportedExteriorProduct
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import WeilConjectures.CategoryTheory.Sites.ConstantSheafMonoidal
import WeilConjectures.SixFunctors.OpenClosed.ClosedImmersion
import WeilConjectures.SixFunctors.OpenClosed.Conservative
import WeilConjectures.SixFunctors.OpenClosed.Vanishing
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.ClosedImmersion
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal


/-!
# The quotient model of supported constant coefficients

Source: blueprint main-20261015, sec-smooth-purity/sk-prop-an,
`lem-pur-kunneth-supported.proof.md`, paragraph 4
(blueprint: lem-pur-supported-product-quotient-model).

The quotient is an actual cokernel. The comparison with closed pushforward is
normalized by its quotient map. The unbounded tensor comparison is the localization
of the signed total-complex comparison.

## Main definitions and statement

* `Etale.supportQuotient` and `ProEtale.supportQuotient`: the cokernel objects.
* `supportQuotientOrdinaryIso`: the uniquely generator-normalized comparison.
* `supportQuotientComparison`: its canonical unbounded derived extension.
* `SupportQuotientModel`: adjunction, generator and counit normalizations.
* `supported_product_quotient_model`: both topologies for the three closed pairs.
-/

@[expose] public section
set_option autoImplicit false
universe u v w v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits MonoidalCategory CategoryTheory.Abelian


/-- Localization of tensor by a sheaf in degree zero, followed by the canonical
single-factor collapse. Source: blueprint paragraph 4
(blueprint: lem-pur-supported-product-quotient-model). -/
@[irreducible]
noncomputable def supportSingleTensorLocalization
    {C : Type w} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C]
    [SymmetricCategory C] [HasDerivedCategory.{v} C] [Abelian.HasFunctorialFlatResolution C]
    [HasColimitsOfSize.{0, 0} C] (K : C) :
    DerivedCategory.Q ⋙ tensorLeft
        (DerivedCategory.Q.obj ((HomologicalComplex.single C (.up ℤ) 0).obj K)) ⟶
      (tensorLeft K).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q := by
  exact (Functor.LaxMonoidal.μNatTrans DerivedCategory.Q).app
      ((HomologicalComplex.single C (.up ℤ) 0).obj K) ≫
    Functor.whiskerRight
      (CochainComplex.map₂HomologicalComplexObjSingleIso (curriedTensor C) K).hom
      DerivedCategory.Q


/-- Constant-coefficient localization, with the exact-functor comparison on either side.
Source: blueprint paragraph 4 (blueprint: lem-pur-supported-product-quotient-model). -/
@[irreducible]
noncomputable def supportCoefficientTensorLocalization
    {B : Type*} [Category B] [Abelian B] [HasDerivedCategory B]
    {C : Type w} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C]
    [SymmetricCategory C] [HasDerivedCategory.{v} C] [Abelian.HasFunctorialFlatResolution C]
    [HasColimitsOfSize.{0, 0} C] (F : B ⥤ C) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (K : C) [PreservesFiniteLimits (F ⋙ tensorLeft K)]
    [PreservesFiniteColimits (F ⋙ tensorLeft K)] :
    DerivedCategory.Q ⋙ (F.mapDerivedCategory ⋙ tensorLeft
        (DerivedCategory.Q.obj ((HomologicalComplex.single C (.up ℤ) 0).obj K))) ⟶
      DerivedCategory.Q ⋙ (F ⋙ tensorLeft K).mapDerivedCategory :=
  Functor.whiskerRight F.mapDerivedCategoryFactors.hom
      (tensorLeft (DerivedCategory.Q.obj ((HomologicalComplex.single C (.up ℤ) 0).obj K))) ≫
    Functor.whiskerLeft (F.mapHomologicalComplex (.up ℤ))
      (supportSingleTensorLocalization K) ≫
    Functor.whiskerRight
      (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ tensorLeft K)) (.up ℤ)).inv
      DerivedCategory.Q ≫
    (F ⋙ tensorLeft K).mapDerivedCategoryFactors.inv

section
variable {B : Type u} [Category.{v} B] [Abelian B] [IsGrothendieckAbelian.{v} B]
  [MonoidalCategory B] [MonoidalPreadditive B] [MonoidalClosed B]
  [SymmetricCategory B] [HasDerivedCategory.{v} B] [Abelian.HasFunctorialFlatResolution B]
  [HasColimitsOfSize.{0, 0} B]
  {C : Type w} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C]
  [SymmetricCategory C] [HasDerivedCategory.{v} C] [Abelian.HasFunctorialFlatResolution C]
  [HasColimitsOfSize.{0, 0} C]
  (F : B ⥤ C) [F.Additive] [F.PreservesFlat]
  [PreservesColimitsOfShape ℤ F] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (K : C) [PreservesFiniteLimits (F ⋙ tensorLeft K)]
  [PreservesFiniteColimits (F ⋙ tensorLeft K)]

private theorem singleTensorIsIso (P : CochainComplex C ℤ)
    (hP : (HomologicalComplex.quasiIso C (.up ℤ)).kFlat P) :
    IsIso ((supportSingleTensorLocalization K).app P) := by
  have hk := (HomotopyCategory.kFlat_quotient_obj_iff P).2 hP
  have hi := DerivedMonoidal.isIso_counit_app_app_of_kFlat_right DerivedCategory.Qh
    (HomotopyCategory.quasiIso C (.up ℤ))
    ((HomotopyCategory.quotient C (.up ℤ)).obj
      ((HomologicalComplex.single C (.up ℤ) 0).obj K)) _ hk
  have : IsIso (Functor.LaxMonoidal.μ DerivedCategory.Qh
      ((HomotopyCategory.quotient C (.up ℤ)).obj
        ((HomologicalComplex.single C (.up ℤ) 0).obj K))
      ((HomotopyCategory.quotient C (.up ℤ)).obj P)) := hi
  have : IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q
      ((HomologicalComplex.single C (.up ℤ) 0).obj K) P) := by
    change IsIso ((_ ⊗ₘ _) ≫
      (Functor.LaxMonoidal.μ DerivedCategory.Qh _ _ ≫ DerivedCategory.Qh.map _) ≫ _)
    infer_instance
  unfold supportSingleTensorLocalization
  change IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q
    ((HomologicalComplex.single C (.up ℤ) 0).obj K) P ≫ _)
  infer_instance

private theorem coefficientTensorIsIso :
    IsIso (supportCoefficientTensorLocalization F K) := by
  have (V : CochainComplex B ℤ) :
      IsIso ((supportCoefficientTensorLocalization F K).app V) := by
    let Λ : Abelian.LeftResolution (ObjectProperty.flat.ι : _ ⥤ B) := Classical.arbitrary _
    let P := Λ.reduced.resolutionFunctor.obj V
    let s := Λ.reduced.resolutionNatTrans.app V
    have hs : QuasiIso s := inferInstance
    have hFP := F.kFlat_mapHomologicalComplex_obj_resolutionFunctor_obj Λ.reduced
      ObjectProperty.flat.essImage_ι_le V
    have hP : IsIso ((supportCoefficientTensorLocalization F K).app P) := by
      have := singleTensorIsIso K ((F.mapHomologicalComplex (.up ℤ)).obj P) hFP
      unfold supportCoefficientTensorLocalization
      dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
      infer_instance
    have h := (supportCoefficientTensorLocalization F K).naturality s
    have hcomp : IsIso
        ((supportCoefficientTensorLocalization F K).app P ≫
          (DerivedCategory.Q ⋙ (F ⋙ tensorLeft K).mapDerivedCategory).map s) := by
      dsimp only [Functor.comp_map]
      infer_instance
    rw [← h] at hcomp
    have : IsIso ((DerivedCategory.Q ⋙ (F.mapDerivedCategory ⋙ tensorLeft
        (DerivedCategory.Q.obj ((HomologicalComplex.single C (.up ℤ) 0).obj K)))).map s ≫
        (supportCoefficientTensorLocalization F K).app V) := hcomp
    have : IsIso ((DerivedCategory.Q ⋙ (F.mapDerivedCategory ⋙ tensorLeft
        (DerivedCategory.Q.obj ((HomologicalComplex.single C (.up ℤ) 0).obj K)))).map s) := by
      dsimp only [Functor.comp_map]
      infer_instance
    exact IsIso.of_isIso_comp_left
      ((DerivedCategory.Q ⋙ (F.mapDerivedCategory ⋙ tensorLeft
        (DerivedCategory.Q.obj ((HomologicalComplex.single C (.up ℤ) 0).obj K)))).map s) _
  exact NatIso.isIso_of_isIso_app _
end

section Lift
variable {C D E : Type*} [Category C] [Category D] [Category E]
  (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]
  (F G : C ⥤ E) (F' G' : D ⥤ E)
  [Localization.Lifting L W F F'] [Localization.Lifting L W G G']
private theorem liftComparisonIsIso (τ : F ⟶ G) [IsIso τ] :
    IsIso (Localization.liftNatTrans L W F G F' G' τ) :=
  (Localization.liftNatIso L W F G F' G' (asIso τ)).isIso_hom
end Lift

section
variable {C : Type u} {D : Type w} [Category.{v} C] [Category.{v} D]
  [Abelian C] [Abelian D] [MonoidalCategory C] [MonoidalPreadditive C]
  [MonoidalClosed C] [SymmetricCategory C]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [SymmetricCategory D]

omit [MonoidalClosed D] [SymmetricCategory D] in
private theorem cokernelTensorFactor (S : C ⥤ D) (T : D ⥤ C)
    (a : S ⊣ T) [S.Monoidal]
    {O U : C} (f : O ⟶ U) (M : C) (N : D)
    (g : U ⊗ M ⟶ T.obj N) (hz : IsZero (S.obj O)) :
    ∃ b : cokernel f ⊗ M ⟶ T.obj N,
      (cokernel.π f ▷ M) ≫ b = g := by
  have hz' : IsZero (S.obj (O ⊗ M)) :=
    ((tensorRight (S.obj M)).map_isZero hz).of_iso
      (Functor.Monoidal.μIso S O M).symm
  have hfg : (f ▷ M) ≫ g = 0 := by
    apply (a.homEquiv _ _).symm.injective
    exact hz'.eq_of_src _ _
  refine ⟨(PreservesCokernel.iso (tensorRight M) f).hom ≫
    cokernel.desc _ g hfg, ?_⟩
  change (tensorRight M).map (cokernel.π f) ≫ _ = _
  simp only [← Category.assoc, PreservesCokernel.π_iso_hom, cokernel.π_desc]

omit [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C]
  [SymmetricCategory C] [MonoidalCategory D] [MonoidalPreadditive D]
  [MonoidalClosed D] [SymmetricCategory D] in
private theorem mapCokernelPiIso (S : C ⥤ D) [S.Additive]
    [PreservesFiniteColimits S] {O U : C} (f : O ⟶ U) (hz : IsZero (S.obj O)) :
    IsIso (S.map (cokernel.π f)) := by
  exact CokernelCofork.IsColimit.isIso_π _
    (CokernelCofork.mapIsColimit _ (cokernelIsCokernel f) S) (hz.eq_of_src _ _)

omit [Abelian C] [Abelian D] [MonoidalPreadditive C] [MonoidalClosed C]
  [SymmetricCategory C] [MonoidalPreadditive D] [MonoidalClosed D] [SymmetricCategory D] in
private theorem mapWhiskerRightIso (S : C ⥤ D) [S.Monoidal]
    {U V : C} (f : U ⟶ V) (M : C) [IsIso (S.map f)] :
    IsIso (S.map (f ▷ M)) := by
  rw [Functor.Monoidal.map_whiskerRight]
  infer_instance
end

namespace CategoryTheory.Adjunction
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
  [HasKInjectiveResolutions D]
  {L B : C ⥤ D} {R : D ⥤ C} [L.Additive] [B.Additive] [R.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [PreservesFiniteLimits B] [PreservesFiniteColimits B]
omit [HasDerivedCategory C] [HasDerivedCategory D] [HasKInjectiveResolutions D]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [PreservesFiniteLimits B] [PreservesFiniteColimits B] in
private theorem homotopyCounitTransport (a : L ⊣ R) (e : L ≅ B)
    (K : HomotopyCategory D (.up ℤ)) :
    (NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app
        ((R.mapHomotopyCategory (.up ℤ)).obj K) ≫
      ((a.ofNatIsoLeft e).mapHomotopyCategory (.up ℤ)).counit.app K =
    (a.mapHomotopyCategory (.up ℤ)).counit.app K := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  rw [mapHomotopyCategory_counit_app_quotient,
    mapHomotopyCategory_counit_app_quotient]
  change (HomotopyCategory.quotient D (.up ℤ)).map
      ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app
        ((R.mapHomologicalComplex (.up ℤ)).obj K)) ≫ _ = _
  rw [← Functor.map_comp]
  congr 1
  ext n
  change e.hom.app _ ≫ e.inv.app _ ≫ a.counit.app _ = a.counit.app _
  simp

private theorem derivedCounitTransport (a : L ⊣ R) (e : L ≅ B) :
    Functor.whiskerLeft R.rightDerivedFunctor (Functor.mapDerivedCategoryNatIso e).hom ≫
      (a.ofNatIsoLeft e).mapDerivedCategoryRightDerivedAdjunction.counit =
    a.mapDerivedCategoryRightDerivedAdjunction.counit := by
  apply (R.rightDerivedFunctor ⋙ L.mapDerivedCategory).rightDerived_ext
    (Functor.whiskerRight R.rightDerivedFunctorUnit L.mapDerivedCategory ≫
      (Functor.associator _ _ _).hom)
    (HomotopyCategory.quasiIso D (.up ℤ))
  ext K
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app]
  simp only [Category.comp_id]
  change L.mapDerivedCategory.map (R.rightDerivedFunctorUnit.app K) ≫
      (Functor.mapDerivedCategoryNatIso e).hom.app _ ≫
      (a.ofNatIsoLeft e).mapDerivedCategoryRightDerivedAdjunction.counit.app _ =
    L.mapDerivedCategory.map (R.rightDerivedFunctorUnit.app K) ≫
      a.mapDerivedCategoryRightDerivedAdjunction.counit.app _
  rw [NatTrans.naturality_assoc]
  change _ ≫ (B.mapDerivedCategory.map (R.rightDerivedFunctorUnit.app K) ≫
    (((a.ofNatIsoLeft e).mapHomotopyCategory (.up ℤ)).derivedε
      (HomotopyCategory.quasiIso D (.up ℤ))
      B.mapDerivedCategoryFactorsh.hom R.rightDerivedFunctorUnit).app _) = _
  rw [derivedε_fac_app]
  dsimp only [Functor.comp_obj]
  rw [Functor.mapDerivedCategoryNatIso_fach_assoc e
    ((R.mapHomotopyCategory (.up ℤ)).obj K)]
  rw [← DerivedCategory.Qh.map_comp, homotopyCounitTransport]
  exact (derivedε_fac_app (a.mapHomotopyCategory (.up ℤ))
    (HomotopyCategory.quasiIso D (.up ℤ))
    L.mapDerivedCategoryFactorsh.hom R.rightDerivedFunctorUnit K).symm

private theorem derivedCounitTransportReverse (a : L ⊣ R) (e : B ≅ L)
    (K : DerivedCategory D) :
    (Functor.mapDerivedCategoryNatIso e).hom.app (R.rightDerivedFunctor.obj K) ≫
      a.mapDerivedCategoryRightDerivedAdjunction.counit.app K =
    (a.ofNatIsoLeft e.symm).mapDerivedCategoryRightDerivedAdjunction.counit.app K := by
  have h := congr_app (derivedCounitTransport a e.symm) K
  dsimp only [Functor.whiskerLeft_app, NatTrans.comp_app] at h
  rw [← h, ← Category.assoc]
  have hs : (Functor.mapDerivedCategoryNatIso e.symm).hom =
      (Functor.mapDerivedCategoryNatIso e).inv := rfl
  rw [hs, Iso.hom_inv_id_app, Category.id_comp]
end CategoryTheory.Adjunction


section Comparison
variable {C D : Type*} [Category C] [Category D]
  {L B : C ⥤ D} {R : D ⥤ C}
private theorem comparisonHom (a : L ⊣ R) (aB : B ⊣ R) (e : L ≅ B)
    (hc : ∀ F, e.hom.app (R.obj F) ≫ aB.counit.app F = a.counit.app F)
    (V : C) (F : D) (f : B.obj V ⟶ F) :
    a.homEquiv V F (e.hom.app V ≫ f) = aB.homEquiv V F f := by
  apply (a.homEquiv V F).symm.injective
  rw [Equiv.symm_apply_apply, Adjunction.homEquiv_symm_apply]
  change e.hom.app V ≫ f = L.map (aB.homEquiv V F f) ≫ a.counit.app F
  rw [← hc, ← Category.assoc, e.hom.naturality, Category.assoc]
  congr 1
  exact ((aB.homEquiv V F).symm_apply_apply f).symm

private theorem comparisonUnique (a : L ⊣ R) (aB : B ⊣ R) (e : L ≅ B)
    (hc : ∀ F, e.hom.app (R.obj F) ≫ aB.counit.app F = a.counit.app F)
    (b : L ≅ B) :
    (∀ V F (f : B.obj V ⟶ F),
      a.homEquiv V F (b.hom.app V ≫ f) = aB.homEquiv V F f) ↔ b = e := by
  constructor
  · intro hb
    apply Iso.ext
    ext V
    have h := (a.homEquiv V (B.obj V)).injective
      ((hb V (B.obj V) (𝟙 _)).trans
        (comparisonHom a aB e hc V (B.obj V) (𝟙 _)).symm)
    simpa only [Category.comp_id] using h
  · rintro rfl
    exact comparisonHom a aB b hc
end Comparison


namespace AlgebraicGeometry.Etale

/-- Cache the existing constant-coefficient sheafification interface at this site.
Source: blueprint small-site convention
(blueprint: lem-pur-supported-product-quotient-model). -/
noncomputable instance supportQuotientWeakSheafify
    (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :
    HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u + 1} A) :=
  (GrothendieckTopology.hasSheafify_smallEtaleTopology (ModuleCat.{u + 1} A) X).isRightAdjoint

variable (A : Type (u + 1)) [CommRing A]
  {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-- The inclusion of the constant module on the open complement into the constant
module on the ambient site, adjoint to the constant inverse-image identification.
Source: blueprint paragraph 4 (blueprint: lem-pur-supported-product-quotient-model). -/
noncomputable def supportQuotientOpenArrow :
    (openImmersionLowerShriek (ModuleCat.{u + 1} A) i.openComplement.ι).obj
      ((constantSheaf i.openComplement.toScheme.smallEtaleTopology
        (ModuleCat.{u + 1} A)).obj (𝟙_ (ModuleCat.{u + 1} A))) ⟶
    (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).obj (𝟙_ (ModuleCat.{u + 1} A)) :=
  ((openImmersionLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} A) i.openComplement.ι).homEquiv _ _).symm
      ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A)
        i.openComplement.ι).inv.app (𝟙_ (ModuleCat.{u + 1} A)))

/-- The rank-one support quotient, with real cokernel data.
Source: blueprint paragraph 4 (blueprint: lem-pur-supported-product-quotient-model). -/
noncomputable def supportQuotient :
    Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A) := cokernel (supportQuotientOpenArrow A i)

/-- The ordinary tensor functor Q tensor constant coefficients.
Source: blueprint paragraph 4 (blueprint: lem-pur-supported-product-quotient-model). -/
noncomputable def supportQuotientCoefficients :
    ModuleCat.{u + 1} A ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A) :=
  constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A) ⋙
    tensorLeft (supportQuotient A i)

/-- Its quotient-generator map, using the unit and the canonical constant tensor map.
Source: blueprint paragraph 4 (blueprint: lem-pur-supported-product-quotient-model). -/
noncomputable def supportQuotientGenerator (M : ModuleCat.{u + 1} A) :
    (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).obj M ⟶
      (supportQuotientCoefficients A i).obj M :=
  (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).map (λ_ M).inv ≫
    Functor.OplaxMonoidal.δ
      (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) (𝟙_ _) M ≫
      (cokernel.π (supportQuotientOpenArrow A i) ▷
        (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).obj M)


private theorem constTensorIso (M N : ModuleCat.{u + 1} A) :
    IsIso (supportedConstantTensor A X M N) := by
  have : IsIso (constantPresheafTensor A X M N) := by
    have (V : X.Etaleᵒᵖ) : IsIso ((constantPresheafTensor A X M N).app V) := by
      change IsIso (𝟙 _)
      infer_instance
    exact NatIso.isIso_of_isIso_app _
  unfold supportedConstantTensor
  infer_instance

private theorem generatorEpi (M : ModuleCat.{u + 1} A) :
    Epi (supportQuotientGenerator A i M) := by
  have := constTensorIso (X := X) A (𝟙_ _) M
  unfold supportQuotientGenerator
  have : Epi ((tensorRight ((constantSheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} A)).obj M)).map (cokernel.π (supportQuotientOpenArrow A i))) :=
    inferInstance
  change Epi (_ ≫ _ ≫ (tensorRight _).map (cokernel.π (supportQuotientOpenArrow A i)))
  infer_instance

private theorem constantTensor_eq (M N : ModuleCat.{u + 1} A) :
    supportedConstantTensor A X M N =
      Functor.OplaxMonoidal.δ
        (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) M N := rfl

private theorem generatorNaturality {M N : ModuleCat.{u + 1} A} (f : M ⟶ N) :
    (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).map f ≫
      supportQuotientGenerator A i N =
    supportQuotientGenerator A i M ≫ (supportQuotientCoefficients A i).map f := by
  let F := constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)
  change F.map f ≫ (F.map (λ_ N).inv ≫ supportedConstantTensor A X _ N ≫
      (cokernel.π (supportQuotientOpenArrow A i) ▷ F.obj N)) =
    (F.map (λ_ M).inv ≫ supportedConstantTensor A X _ M ≫
      (cokernel.π (supportQuotientOpenArrow A i) ▷ F.obj M)) ≫
      (supportQuotient A i ◁ F.map f)
  simp only [constantTensor_eq, ← Functor.map_comp_assoc, leftUnitor_inv_naturality]
  rw [Functor.map_comp]
  simp only [Category.assoc]
  rw [← Functor.OplaxMonoidal.δ_natural_right_assoc]
  dsimp only [supportQuotient]
  rw [MonoidalCategory.whisker_exchange]

private theorem ordinaryComponent (M : ModuleCat.{u + 1} A) :
    ∃ b : (supportQuotientCoefficients A i).obj M ≅ (supportedCoefficients A i).obj M,
      supportQuotientGenerator A i M ≫ b.hom = supportedCoefficientQuotient A i M := by
  let F := constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)
  let S := upperStar (ModuleCat.{u + 1} A) i
  let R := upperStar (ModuleCat.{u + 1} A) i.openComplement.ι
  have hdisj := disjoint_range_of_range_eq_compl _ _
    i.range_eq_compl_range_openComplement_ι
  have hz := isZero_upperStar_openImmersionLowerShriek_of_disjoint_range
    (ModuleCat.{u + 1} A) i.openComplement.ι i hdisj
    ((constantSheaf i.openComplement.toScheme.smallEtaleTopology
      (ModuleCat.{u + 1} A)).obj (𝟙_ _))
  have hδ := constTensorIso (X := X) A (𝟙_ _) M
  let e : F.obj M ≅ F.obj (𝟙_ _) ⊗ F.obj M :=
    F.mapIso (λ_ M).symm ≪≫ asIso (supportedConstantTensor A X (𝟙_ _) M)
  obtain ⟨b, hb⟩ := cokernelTensorFactor S (lowerStar (ModuleCat.{u + 1} A) i)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i)
    (supportQuotientOpenArrow A i) (F.obj M)
    ((constantSheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)).obj M)
    (e.inv ≫ supportedCoefficientQuotient A i M) hz
  have hnorm : supportQuotientGenerator A i M ≫ b = supportedCoefficientQuotient A i M := by
    change e.hom ≫ (cokernel.π (supportQuotientOpenArrow A i) ▷ F.obj M) ≫ b = _
    rw [hb, Iso.hom_inv_id_assoc]
  have hSπ : IsIso (S.map (cokernel.π (supportQuotientOpenArrow A i))) :=
    mapCokernelPiIso S _ hz
  have hSπM := mapWhiskerRightIso S
    (cokernel.π (supportQuotientOpenArrow A i)) (F.obj M)
  have hSgen : IsIso (S.map (supportQuotientGenerator A i M)) := by
    change IsIso (S.map (e.hom ≫ (cokernel.π (supportQuotientOpenArrow A i) ▷ F.obj M)))
    rw [Functor.map_comp]
    infer_instance
  have hSq : IsIso (S.map (supportedCoefficientQuotient A i M)) := by
    unfold supportedCoefficientQuotient
    rw [Adjunction.homEquiv_apply, Functor.map_comp]
    dsimp only [S]
    infer_instance
  have hSb : IsIso (S.map b) := by
    have : IsIso (S.map (supportQuotientGenerator A i M) ≫ S.map b) := by
      rw [← Functor.map_comp, hnorm]
      exact hSq
    exact IsIso.of_isIso_comp_left (S.map (supportQuotientGenerator A i M)) _
  have hRf : IsIso (R.map (supportQuotientOpenArrow A i)) := by
    unfold supportQuotientOpenArrow
    rw [Adjunction.homEquiv_symm_apply, Functor.map_comp]
    dsimp only [R]
    infer_instance
  have hzRQ : IsZero (R.obj (supportQuotient A i)) :=
    (isZero_cokernel_of_epi (R.map (supportQuotientOpenArrow A i))).of_iso
      (PreservesCokernel.iso R _)
  have hzRsrc : IsZero (R.obj ((supportQuotientCoefficients A i).obj M)) :=
    ((tensorRight (R.obj (F.obj M))).map_isZero hzRQ).of_iso
      (Functor.Monoidal.μIso R (supportQuotient A i) (F.obj M)).symm
  have hzRtgt : IsZero (R.obj ((supportedCoefficients A i).obj M)) :=
    isZero_upperStar_lowerStar_of_disjoint_range (ModuleCat.{u + 1} A)
      i.openComplement.ι i hdisj _
  have hRb : IsIso (R.map b) := ⟨0, hzRsrc.eq_of_src _ _, hzRtgt.eq_of_src _ _⟩
  have : IsIso b := isIso_of_isIso_upperStar_map (ModuleCat.{u + 1} A)
    i.openComplement.ι i i.range_eq_compl_range_openComplement_ι b hRb hSb
  exact ⟨asIso b, hnorm⟩

/-- The ordinary comparison is uniquely determined by the quotient generators.
Source: blueprint paragraph 4 (blueprint: lem-pur-supported-product-quotient-model).
Proof: tensor preserves the cokernel defining Q. Closed restriction kills the
open extension, so the closed-pushforward quotient factors through this tensor
cokernel. Closed restriction makes its generator and the normalized quotient
invertible; open restriction kills both sides. Joint detection of isomorphisms
makes each comparison invertible. The generator is epic, so its naturality and
the quotient's naturality imply naturality and uniqueness of the comparison.
No flatness of the coefficient module is assumed. -/
theorem supportQuotientOrdinary_existsUnique :
    ∃! b : supportQuotientCoefficients A i ≅ supportedCoefficients A i,
      ∀ M : ModuleCat.{u + 1} A,
        supportQuotientGenerator A i M ≫ b.hom.app M = supportedCoefficientQuotient A i M := by
  classical
  choose b hb using ordinaryComponent A i
  let q : constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A) ⟶
      supportedCoefficients A i :=
    Functor.whiskerLeft
      (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i).unit ≫
      Functor.whiskerRight
        (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) i).hom
        (lowerStar (ModuleCat.{u + 1} A) i)
  let e : supportQuotientCoefficients A i ≅ supportedCoefficients A i :=
    NatIso.ofComponents b (by
      intro M N f
      have := generatorEpi A i M
      apply (cancel_epi (supportQuotientGenerator A i M)).1
      rw [← Category.assoc, ← generatorNaturality, Category.assoc, hb,
        ← Category.assoc, hb]
      exact q.naturality f)
  refine ⟨e, hb, ?_⟩
  intro e' he'
  apply Iso.ext
  apply NatTrans.ext
  funext M
  have := generatorEpi A i M
  exact (cancel_epi (supportQuotientGenerator A i M)).1 ((he' M).trans (hb M).symm)

/-- The uniquely quotient-normalized ordinary comparison.
Source: blueprint paragraph 4 (blueprint: lem-pur-supported-product-quotient-model). -/
@[irreducible]
noncomputable def supportQuotientOrdinaryIso :
    supportQuotientCoefficients A i ≅ supportedCoefficients A i :=
  (supportQuotientOrdinary_existsUnique A i).choose

/-- Additivity uses the existing constant-sheaf and tensor functors.
Source: blueprint paragraph 4 (blueprint: lem-pur-supported-product-quotient-model). -/
noncomputable instance supportQuotientCoefficients_additive :
    (supportQuotientCoefficients A i).Additive :=
  Functor.additive_of_iso (supportQuotientOrdinaryIso A i).symm

/-- Exactness transported along the uniquely normalized ordinary comparison.
Source: blueprint paragraph 4 (blueprint: lem-pur-supported-product-quotient-model). -/
noncomputable instance supportQuotientCoefficients_preservesFiniteLimits :
    PreservesFiniteLimits (supportQuotientCoefficients A i) :=
  preservesFiniteLimits_of_natIso (supportQuotientOrdinaryIso A i).symm

/-- Exactness transported along the uniquely normalized ordinary comparison.
Source: blueprint paragraph 4 (blueprint: lem-pur-supported-product-quotient-model). -/
noncomputable instance supportQuotientCoefficients_preservesFiniteColimits :
    PreservesFiniteColimits (supportQuotientCoefficients A i) :=
  preservesFiniteColimits_of_natIso (supportQuotientOrdinaryIso A i).symm

/-- The unbounded functor E(V) = Q[0] tensor-derived constant V.
Source: blueprint paragraph 4 (blueprint: lem-pur-supported-product-quotient-model). -/
noncomputable def supportQuotientDerived :
    DerivedCategory (ModuleCat.{u + 1} A) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
  (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).mapDerivedCategory ⋙
    tensorLeft
      (DerivedCategory.Q.obj
        ((HomologicalComplex.single _ (.up ℤ) 0).obj (supportQuotient A i)))

attribute [local instance] supportQuotientCoefficients_preservesFiniteLimits

/-- The canonical comparison on an arbitrary complex: constant localization,
lax-monoidal localization of the signed tensor, and collapse of the degree-zero
first factor. Source: blueprint paragraph 4
(blueprint: lem-pur-supported-product-quotient-model). -/
@[irreducible]
noncomputable def supportQuotientLocalizationComplex :
    DerivedCategory.Q ⋙ supportQuotientDerived A i ⟶
      DerivedCategory.Q ⋙ (supportQuotientCoefficients A i).mapDerivedCategory :=
  letI : PreservesFiniteLimits (constantSheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} A) ⋙ tensorLeft (supportQuotient A i)) :=
    supportQuotientCoefficients_preservesFiniteLimits A i
  supportCoefficientTensorLocalization
    (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) (supportQuotient A i)

/-- The component of the specified comparison on complexes.
Source: blueprint paragraph 4 (blueprint: lem-pur-supported-product-quotient-model). -/
noncomputable def supportQuotientLocalizationComponent
    (P : CochainComplex (ModuleCat.{u + 1} A) ℤ) :
    (supportQuotientDerived A i).obj (DerivedCategory.Q.obj P) ⟶
      (supportQuotientCoefficients A i).mapDerivedCategory.obj (DerivedCategory.Q.obj P) :=
  (supportQuotientLocalizationComplex A i).app P

/-- Naturality of the explicit localization components.
Source: blueprint paragraph 4 (blueprint: lem-pur-supported-product-quotient-model).
Proof: naturality of the constant localization isomorphism, of the lax-monoidal
localization map, and of the single-factor total-complex collapse gives the three
successive commuting squares. Compose them and the inverse exact-localization
square. The tensor differential has the usual sign; the first factor is in degree
zero, so the collapse introduces no sign or exchange of factors. -/
theorem supportQuotientLocalization_naturality
    {P P' : CochainComplex (ModuleCat.{u + 1} A) ℤ} (f : P ⟶ P') :
    (supportQuotientDerived A i).map (DerivedCategory.Q.map f) ≫
        supportQuotientLocalizationComponent A i P' =
      supportQuotientLocalizationComponent A i P ≫
        (supportQuotientCoefficients A i).mapDerivedCategory.map (DerivedCategory.Q.map f) := by
  exact (supportQuotientLocalizationComplex A i).naturality f


/-- Descend the specified complex comparison; localization gives a unique map.
Source: blueprint paragraph 4 (blueprint: lem-pur-supported-product-quotient-model). -/
@[irreducible]
noncomputable def supportQuotientLocalization :
    supportQuotientDerived A i ⟶ (supportQuotientCoefficients A i).mapDerivedCategory :=
  Localization.liftNatTrans DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{u + 1} A) (.up ℤ))
    _ _ _ _ (supportQuotientLocalizationComplex A i)

/-- The tensor localization comparison is invertible without boundedness assumptions.
Source: blueprint paragraph 4 (blueprint: lem-pur-supported-product-quotient-model).
Proof: choose a flat-term K-flat module resolution P of V. Constant inverse image
is exact and preserves K-flatness and flat terms. The lax tensor localization map
is thus invertible using its second factor. The single-factor collapse and both
exact-localization comparisons are invertible. Every derived object has such a
representative and naturality transports invertibility along its quasi-isomorphism.
This also proves independence of the chosen resolution. -/
theorem supportQuotientLocalization_isIso : IsIso (supportQuotientLocalization A i) := by
  have : (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).PreservesFlat :=
    ⟨fun h ↦ GrothendieckTopology.flat_presheafToSheaf_obj
      (ModuleCat.{u + 1} A) X.smallEtaleTopology _ (fun _ ↦ h)⟩
  have : PreservesFiniteLimits (constantSheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} A) ⋙ tensorLeft (supportQuotient A i)) :=
    supportQuotientCoefficients_preservesFiniteLimits A i
  have : PreservesFiniteColimits (constantSheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} A) ⋙ tensorLeft (supportQuotient A i)) :=
    supportQuotientCoefficients_preservesFiniteColimits A i
  have : IsIso (supportQuotientLocalizationComplex A i) := by
    unfold supportQuotientLocalizationComplex
    exact coefficientTensorIsIso _ _
  unfold supportQuotientLocalization
  exact liftComparisonIsIso DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{u + 1} A) (.up ℤ)) _ _ _ _
    (supportQuotientLocalizationComplex A i)

/-- The natural comparison, explicitly derived from the ordinary quotient comparison.
Source: blueprint paragraph 4 (blueprint: lem-pur-supported-product-quotient-model). -/
@[irreducible]
noncomputable def supportQuotientComparison :
    supportQuotientDerived A i ≅ (supportedCoefficients A i).mapDerivedCategory :=
  @asIso _ _ _ _ (supportQuotientLocalization A i)
    (supportQuotientLocalization_isIso A i) ≪≫
      Functor.mapDerivedCategoryNatIso (supportQuotientOrdinaryIso A i)

/-- The quotient-support adjunction, with identity on the existing right adjoint.
Source: blueprint paragraph 4 (blueprint: lem-pur-supported-product-quotient-model). -/
@[irreducible]
noncomputable def supportQuotientDerivedAdjunction :
    supportQuotientDerived A i ⊣ supportedSectionsDerived A i :=
  (((supportedCoefficientAdjunction A i).ofNatIsoLeft
    (supportQuotientOrdinaryIso A i).symm).mapDerivedCategoryRightDerivedAdjunction).ofNatIsoLeft
      (@asIso _ _ _ _ (supportQuotientLocalization A i)
        (supportQuotientLocalization_isIso A i)).symm

end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.ProEtale

/-- Cache the existing constant-coefficient sheafification interface at this site.
Source: blueprint small-site convention
(blueprint: lem-pur-supported-product-quotient-model). -/
noncomputable instance supportQuotientWeakSheafify
    (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :
    HasWeakSheafify (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A) :=
  (GrothendieckTopology.hasSheafify_proEtTopology (ModuleCat.{u + 1} A) X).isRightAdjoint

variable (A : Type (u + 1)) [CommRing A] [Finite A]
  {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-- The inclusion of the constant module on the open complement into the constant
module on the ambient site, adjoint to the constant inverse-image identification.
Source: blueprint paragraph 4 (blueprint: lem-pur-supported-product-quotient-model). -/
noncomputable def supportQuotientOpenArrow :
    (openImmersionLowerShriek (ModuleCat.{u + 1} A) i.openComplement.ι).obj
      ((constantSheaf (Scheme.ProEt.topology i.openComplement.toScheme)
        (ModuleCat.{u + 1} A)).obj (𝟙_ (ModuleCat.{u + 1} A))) ⟶
    (constantSheaf (Scheme.ProEt.topology X)
        (ModuleCat.{u + 1} A)).obj (𝟙_ (ModuleCat.{u + 1} A)) :=
  ((openImmersionLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} A) i.openComplement.ι).homEquiv _ _).symm
      ((constantSheafCompUpperStarIso (ModuleCat.{u + 1} A)
        i.openComplement.ι).inv.app (𝟙_ (ModuleCat.{u + 1} A)))

/-- The rank-one support quotient, with real cokernel data.
Source: blueprint paragraph 4 (blueprint: lem-pur-supported-product-quotient-model). -/
noncomputable def supportQuotient :
    Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A) := cokernel (supportQuotientOpenArrow A i)

/-- The ordinary tensor functor Q tensor constant coefficients.
Source: blueprint paragraph 4 (blueprint: lem-pur-supported-product-quotient-model). -/
noncomputable def supportQuotientCoefficients :
    ModuleCat.{u + 1} A ⥤ Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A) :=
  constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A) ⋙
    tensorLeft (supportQuotient A i)

/-- Its quotient-generator map, using the unit and the canonical constant tensor map.
Source: blueprint paragraph 4 (blueprint: lem-pur-supported-product-quotient-model). -/
noncomputable def supportQuotientGenerator (M : ModuleCat.{u + 1} A) :
    (constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)).obj M ⟶
      (supportQuotientCoefficients A i).obj M :=
  (constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)).map (λ_ M).inv ≫
    Functor.OplaxMonoidal.δ
      (constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) (𝟙_ _) M ≫
      (cokernel.π (supportQuotientOpenArrow A i) ▷
        (constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)).obj M)

variable [IsLocallyNoetherian X]

omit [IsLocallyNoetherian X] in
private theorem constTensorIso (M N : ModuleCat.{u + 1} A) :
    IsIso (supportedConstantTensor A X M N) := by
  have : IsIso (constantPresheafTensor A X M N) := by
    have (V : (Scheme.ProEt X)ᵒᵖ) : IsIso ((constantPresheafTensor A X M N).app V) := by
      change IsIso (𝟙 _)
      infer_instance
    exact NatIso.isIso_of_isIso_app _
  unfold supportedConstantTensor
  infer_instance

omit [IsLocallyNoetherian X] in
private theorem generatorEpi (M : ModuleCat.{u + 1} A) :
    Epi (supportQuotientGenerator A i M) := by
  have := constTensorIso (X := X) A (𝟙_ _) M
  unfold supportQuotientGenerator
  have : Epi ((tensorRight ((constantSheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} A)).obj M)).map (cokernel.π (supportQuotientOpenArrow A i))) :=
    inferInstance
  change Epi (_ ≫ _ ≫ (tensorRight _).map (cokernel.π (supportQuotientOpenArrow A i)))
  infer_instance

omit [IsLocallyNoetherian X] in
private theorem constantTensor_eq (M N : ModuleCat.{u + 1} A) :
    supportedConstantTensor A X M N =
      Functor.OplaxMonoidal.δ
        (constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) M N := rfl

omit [IsLocallyNoetherian X] in
private theorem generatorNaturality {M N : ModuleCat.{u + 1} A} (f : M ⟶ N) :
    (constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)).map f ≫
      supportQuotientGenerator A i N =
    supportQuotientGenerator A i M ≫ (supportQuotientCoefficients A i).map f := by
  let F := constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)
  change F.map f ≫ (F.map (λ_ N).inv ≫ supportedConstantTensor A X _ N ≫
      (cokernel.π (supportQuotientOpenArrow A i) ▷ F.obj N)) =
    (F.map (λ_ M).inv ≫ supportedConstantTensor A X _ M ≫
      (cokernel.π (supportQuotientOpenArrow A i) ▷ F.obj M)) ≫
      (supportQuotient A i ◁ F.map f)
  simp only [constantTensor_eq, ← Functor.map_comp_assoc, leftUnitor_inv_naturality]
  rw [Functor.map_comp]
  simp only [Category.assoc]
  rw [← Functor.OplaxMonoidal.δ_natural_right_assoc]
  dsimp only [supportQuotient]
  rw [MonoidalCategory.whisker_exchange]

private theorem ordinaryComponent (M : ModuleCat.{u + 1} A) :
    ∃ b : (supportQuotientCoefficients A i).obj M ≅ (supportedCoefficients A i).obj M,
      supportQuotientGenerator A i M ≫ b.hom = supportedCoefficientQuotient A i M := by
  let F := constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)
  let S := upperStar (ModuleCat.{u + 1} A) i
  let R := upperStar (ModuleCat.{u + 1} A) i.openComplement.ι
  have hdisj := disjoint_range_of_range_eq_compl _ _
    i.range_eq_compl_range_openComplement_ι
  have hz : IsZero (S.obj ((openImmersionLowerShriek (ModuleCat.{u + 1} A)
      i.openComplement.ι).obj ((constantSheaf (Scheme.ProEt.topology
        i.openComplement.toScheme) (ModuleCat.{u + 1} A)).obj (𝟙_ _)))) := by
    refine IsInitial.isZero (IsInitial.ofUnique (h := fun H ↦ ?_))
    have hz' := isZero_upperStar_lowerStar_of_disjoint
      (ModuleCat.{u + 1} A) i i.openComplement.ι hdisj.symm H
    have : Unique (((constantSheaf (Scheme.ProEt.topology i.openComplement.toScheme)
        (ModuleCat.{u + 1} A)).obj (𝟙_ _)) ⟶ R.obj ((lowerStar
          (ModuleCat.{u + 1} A) i).obj H)) :=
      ⟨⟨hz'.isTerminal.from _⟩, fun _ ↦ hz'.isTerminal.hom_ext _ _⟩
    exact Equiv.unique
      (((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i).homEquiv _ H).trans
        ((openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A)
          i.openComplement.ι).homEquiv _ _))
  have hδ := constTensorIso (X := X) A (𝟙_ _) M
  let e : F.obj M ≅ F.obj (𝟙_ _) ⊗ F.obj M :=
    F.mapIso (λ_ M).symm ≪≫ asIso (supportedConstantTensor A X (𝟙_ _) M)
  obtain ⟨b, hb⟩ := cokernelTensorFactor S (lowerStar (ModuleCat.{u + 1} A) i)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i)
    (supportQuotientOpenArrow A i) (F.obj M)
    ((constantSheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} A)).obj M)
    (e.inv ≫ supportedCoefficientQuotient A i M) hz
  have hnorm : supportQuotientGenerator A i M ≫ b = supportedCoefficientQuotient A i M := by
    change e.hom ≫ (cokernel.π (supportQuotientOpenArrow A i) ▷ F.obj M) ≫ b = _
    rw [hb, Iso.hom_inv_id_assoc]
  have hSπ : IsIso (S.map (cokernel.π (supportQuotientOpenArrow A i))) :=
    mapCokernelPiIso S _ hz
  have hSπM := mapWhiskerRightIso S
    (cokernel.π (supportQuotientOpenArrow A i)) (F.obj M)
  have hSgen : IsIso (S.map (supportQuotientGenerator A i M)) := by
    change IsIso (S.map (e.hom ≫ (cokernel.π (supportQuotientOpenArrow A i) ▷ F.obj M)))
    rw [Functor.map_comp]
    infer_instance
  have : IsIso (S.map ((upperStarLowerStarAdjunction
      (ModuleCat.{u + 1} A) i).unit.app (F.obj M))) := by
    have h := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i).left_triangle_components
      (F.obj M)
    have : IsIso (S.map ((upperStarLowerStarAdjunction
        (ModuleCat.{u + 1} A) i).unit.app (F.obj M)) ≫
        (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i).counit.app (S.obj (F.obj M))) := by
      rw [h]
      exact IsIso.id _
    exact IsIso.of_isIso_comp_right _
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i).counit.app (S.obj (F.obj M)))
  have hSq : IsIso (S.map (supportedCoefficientQuotient A i M)) := by
    unfold supportedCoefficientQuotient
    rw [Adjunction.homEquiv_apply, Functor.map_comp]
    dsimp only [S]
    infer_instance
  have hSb : IsIso (S.map b) := by
    have : IsIso (S.map (supportQuotientGenerator A i M) ≫ S.map b) := by
      rw [← Functor.map_comp, hnorm]
      exact hSq
    exact IsIso.of_isIso_comp_left (S.map (supportQuotientGenerator A i M)) _
  have : IsIso ((openImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) i.openComplement.ι).unit) :=
    Adjunction.unit_isIso_of_L_fully_faithful _
  have : IsIso (R.map ((openImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) i.openComplement.ι).counit.app (F.obj (𝟙_ _)))) := by
    dsimp only [R]
    rw [← IsIso.inv_eq_of_hom_inv_id
      ((openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A)
        i.openComplement.ι).right_triangle_components (F.obj (𝟙_ _)))]
    infer_instance
  have hRf : IsIso (R.map (supportQuotientOpenArrow A i)) := by
    unfold supportQuotientOpenArrow
    rw [Adjunction.homEquiv_symm_apply, Functor.map_comp]
    dsimp only [R]
    infer_instance
  have hzRQ : IsZero (R.obj (supportQuotient A i)) :=
    (isZero_cokernel_of_epi (R.map (supportQuotientOpenArrow A i))).of_iso
      (PreservesCokernel.iso R _)
  have hzRsrc : IsZero (R.obj ((supportQuotientCoefficients A i).obj M)) :=
    ((tensorRight (R.obj (F.obj M))).map_isZero hzRQ).of_iso
      (Functor.Monoidal.μIso R (supportQuotient A i) (F.obj M)).symm
  have hzRtgt : IsZero (R.obj ((supportedCoefficients A i).obj M)) :=
    isZero_upperStar_lowerStar_of_disjoint (ModuleCat.{u + 1} A)
      i i.openComplement.ι hdisj.symm _
  have hRb : IsIso (R.map b) := ⟨0, hzRsrc.eq_of_src _ _, hzRtgt.eq_of_src _ _⟩
  have : IsIso b := isIso_of_isIso_upperStar_of_isCompl i i.openComplement.ι
    (by rw [i.range_eq_compl_range_openComplement_ι]; exact isCompl_compl.symm) b
  exact ⟨asIso b, hnorm⟩

/-- The ordinary comparison is uniquely determined by the quotient generators.
Source: blueprint paragraph 4 (blueprint: lem-pur-supported-product-quotient-model).
Proof: tensor preserves the cokernel defining Q. Closed restriction kills the
open extension, so the closed-pushforward quotient factors through this tensor
cokernel. Closed restriction makes its generator and the normalized quotient
invertible; open restriction kills both sides. Joint detection of isomorphisms
makes each comparison invertible. The generator is epic, so its naturality and
the quotient's naturality imply naturality and uniqueness of the comparison.
No flatness of the coefficient module is assumed. -/
theorem supportQuotientOrdinary_existsUnique :
    ∃! b : supportQuotientCoefficients A i ≅ supportedCoefficients A i,
      ∀ M : ModuleCat.{u + 1} A,
        supportQuotientGenerator A i M ≫ b.hom.app M = supportedCoefficientQuotient A i M := by
  classical
  choose b hb using ordinaryComponent A i
  let q : constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A) ⟶
      supportedCoefficients A i :=
    Functor.whiskerLeft
      (constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i).unit ≫
      Functor.whiskerRight
        (constantSheafCompUpperStarIso (ModuleCat.{u + 1} A) i).hom
        (lowerStar (ModuleCat.{u + 1} A) i)
  let e : supportQuotientCoefficients A i ≅ supportedCoefficients A i :=
    NatIso.ofComponents b (by
      intro M N f
      have := generatorEpi A i M
      apply (cancel_epi (supportQuotientGenerator A i M)).1
      rw [← Category.assoc, ← generatorNaturality, Category.assoc, hb,
        ← Category.assoc, hb]
      exact q.naturality f)
  refine ⟨e, hb, ?_⟩
  intro e' he'
  apply Iso.ext
  apply NatTrans.ext
  funext M
  have := generatorEpi A i M
  exact (cancel_epi (supportQuotientGenerator A i M)).1 ((he' M).trans (hb M).symm)

/-- The uniquely quotient-normalized ordinary comparison.
Source: blueprint paragraph 4 (blueprint: lem-pur-supported-product-quotient-model). -/
@[irreducible]
noncomputable def supportQuotientOrdinaryIso :
    supportQuotientCoefficients A i ≅ supportedCoefficients A i :=
  (supportQuotientOrdinary_existsUnique A i).choose

/-- Additivity uses the existing constant-sheaf and tensor functors.
Source: blueprint paragraph 4 (blueprint: lem-pur-supported-product-quotient-model). -/
noncomputable instance supportQuotientCoefficients_additive :
    (supportQuotientCoefficients A i).Additive :=
  Functor.additive_of_iso (supportQuotientOrdinaryIso A i).symm

/-- Exactness transported along the uniquely normalized ordinary comparison.
Source: blueprint paragraph 4 (blueprint: lem-pur-supported-product-quotient-model). -/
noncomputable instance supportQuotientCoefficients_preservesFiniteLimits :
    PreservesFiniteLimits (supportQuotientCoefficients A i) :=
  preservesFiniteLimits_of_natIso (supportQuotientOrdinaryIso A i).symm

/-- Exactness transported along the uniquely normalized ordinary comparison.
Source: blueprint paragraph 4 (blueprint: lem-pur-supported-product-quotient-model). -/
noncomputable instance supportQuotientCoefficients_preservesFiniteColimits :
    PreservesFiniteColimits (supportQuotientCoefficients A i) :=
  preservesFiniteColimits_of_natIso (supportQuotientOrdinaryIso A i).symm

/-- The unbounded functor E(V) = Q[0] tensor-derived constant V.
Source: blueprint paragraph 4 (blueprint: lem-pur-supported-product-quotient-model). -/
noncomputable def supportQuotientDerived :
    DerivedCategory (ModuleCat.{u + 1} A) ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) :=
  (constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)).mapDerivedCategory ⋙
    tensorLeft
      (DerivedCategory.Q.obj
        ((HomologicalComplex.single _ (.up ℤ) 0).obj (supportQuotient A i)))

attribute [local instance] supportQuotientCoefficients_preservesFiniteLimits

/-- The canonical comparison on an arbitrary complex: constant localization,
lax-monoidal localization of the signed tensor, and collapse of the degree-zero
first factor. Source: blueprint paragraph 4
(blueprint: lem-pur-supported-product-quotient-model). -/
@[irreducible]
noncomputable def supportQuotientLocalizationComplex :
    DerivedCategory.Q ⋙ supportQuotientDerived A i ⟶
      DerivedCategory.Q ⋙ (supportQuotientCoefficients A i).mapDerivedCategory :=
  letI : PreservesFiniteLimits (constantSheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} A) ⋙ tensorLeft (supportQuotient A i)) :=
    supportQuotientCoefficients_preservesFiniteLimits A i
  supportCoefficientTensorLocalization
    (constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) (supportQuotient A i)

/-- The component of the specified comparison on complexes.
Source: blueprint paragraph 4 (blueprint: lem-pur-supported-product-quotient-model). -/
noncomputable def supportQuotientLocalizationComponent
    (P : CochainComplex (ModuleCat.{u + 1} A) ℤ) :
    (supportQuotientDerived A i).obj (DerivedCategory.Q.obj P) ⟶
      (supportQuotientCoefficients A i).mapDerivedCategory.obj (DerivedCategory.Q.obj P) :=
  (supportQuotientLocalizationComplex A i).app P

/-- Naturality of the explicit localization components.
Source: blueprint paragraph 4 (blueprint: lem-pur-supported-product-quotient-model).
Proof: naturality of the constant localization isomorphism, of the lax-monoidal
localization map, and of the single-factor total-complex collapse gives the three
successive commuting squares. Compose them and the inverse exact-localization
square. The tensor differential has the usual sign; the first factor is in degree
zero, so the collapse introduces no sign or exchange of factors. -/
theorem supportQuotientLocalization_naturality
    {P P' : CochainComplex (ModuleCat.{u + 1} A) ℤ} (f : P ⟶ P') :
    (supportQuotientDerived A i).map (DerivedCategory.Q.map f) ≫
        supportQuotientLocalizationComponent A i P' =
      supportQuotientLocalizationComponent A i P ≫
        (supportQuotientCoefficients A i).mapDerivedCategory.map (DerivedCategory.Q.map f) := by
  exact (supportQuotientLocalizationComplex A i).naturality f


/-- Descend the specified complex comparison; localization gives a unique map.
Source: blueprint paragraph 4 (blueprint: lem-pur-supported-product-quotient-model). -/
@[irreducible]
noncomputable def supportQuotientLocalization :
    supportQuotientDerived A i ⟶ (supportQuotientCoefficients A i).mapDerivedCategory :=
  Localization.liftNatTrans DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{u + 1} A) (.up ℤ))
    _ _ _ _ (supportQuotientLocalizationComplex A i)

/-- The tensor localization comparison is invertible without boundedness assumptions.
Source: blueprint paragraph 4 (blueprint: lem-pur-supported-product-quotient-model).
Proof: choose a flat-term K-flat module resolution P of V. Constant inverse image
is exact and preserves K-flatness and flat terms. The lax tensor localization map
is thus invertible using its second factor. The single-factor collapse and both
exact-localization comparisons are invertible. Every derived object has such a
representative and naturality transports invertibility along its quasi-isomorphism.
This also proves independence of the chosen resolution. -/
theorem supportQuotientLocalization_isIso : IsIso (supportQuotientLocalization A i) := by
  have : (constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)).PreservesFlat :=
    ⟨fun h ↦ GrothendieckTopology.flat_presheafToSheaf_obj
      (ModuleCat.{u + 1} A) (Scheme.ProEt.topology X) _ (fun _ ↦ h)⟩
  have : PreservesFiniteLimits (constantSheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} A) ⋙ tensorLeft (supportQuotient A i)) :=
    supportQuotientCoefficients_preservesFiniteLimits A i
  have : PreservesFiniteColimits (constantSheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} A) ⋙ tensorLeft (supportQuotient A i)) :=
    supportQuotientCoefficients_preservesFiniteColimits A i
  have : IsIso (supportQuotientLocalizationComplex A i) := by
    unfold supportQuotientLocalizationComplex
    exact coefficientTensorIsIso _ _
  unfold supportQuotientLocalization
  exact liftComparisonIsIso DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{u + 1} A) (.up ℤ)) _ _ _ _
    (supportQuotientLocalizationComplex A i)

/-- The natural comparison, explicitly derived from the ordinary quotient comparison.
Source: blueprint paragraph 4 (blueprint: lem-pur-supported-product-quotient-model). -/
@[irreducible]
noncomputable def supportQuotientComparison :
    supportQuotientDerived A i ≅ (supportedCoefficients A i).mapDerivedCategory :=
  @asIso _ _ _ _ (supportQuotientLocalization A i)
    (supportQuotientLocalization_isIso A i) ≪≫
      Functor.mapDerivedCategoryNatIso (supportQuotientOrdinaryIso A i)

/-- The quotient-support adjunction, with identity on the existing right adjoint.
Source: blueprint paragraph 4 (blueprint: lem-pur-supported-product-quotient-model). -/
@[irreducible]
noncomputable def supportQuotientDerivedAdjunction :
    supportQuotientDerived A i ⊣ supportedSectionsDerived A i :=
  (((supportedCoefficientAdjunction A i).ofNatIsoLeft
    (supportQuotientOrdinaryIso A i).symm).mapDerivedCategoryRightDerivedAdjunction).ofNatIsoLeft
      (@asIso _ _ _ _ (supportQuotientLocalization A i)
        (supportQuotientLocalization_isIso A i)).symm

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.Etale

/-- All normalizations of the quotient model for a single closed pair. The
ordinary equality identifies the generator adjunction, the Hom equivalence fixes
identity on the common right adjoint, and the complex formula fixes the derived
extension, including its values on unbounded complexes.
Source: blueprint paragraph 4 (blueprint: lem-pur-supported-product-quotient-model). -/
def SupportQuotientModel (A : Type (u + 1)) [CommRing A]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] : Prop :=
  (∀ M : ModuleCat.{u + 1} A,
    supportQuotientGenerator A i M ≫ (supportQuotientOrdinaryIso A i).hom.app M =
      supportedCoefficientQuotient A i M) ∧
  (∀ (M : ModuleCat.{u + 1} A)
      (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
      (f : M ⟶ (supportedEtaleSections A X i.openComplement).obj F),
    supportQuotientGenerator A i M ≫
      (((supportedCoefficientAdjunction A i).ofNatIsoLeft
        (supportQuotientOrdinaryIso A i).symm).homEquiv M F).symm f =
    ((constantSheafΓAdj X.smallEtaleTopology (ModuleCat.{u + 1} A)).homEquiv M F).symm
      (f ≫ (supportedEtaleSectionsι A X i.openComplement).app F)) ∧
  (∀ b : supportQuotientDerived A i ≅ (supportedCoefficients A i).mapDerivedCategory,
    (∀ (V : DerivedCategory (ModuleCat.{u + 1} A))
        (F : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
        (f : (supportedCoefficients A i).mapDerivedCategory.obj V ⟶ F),
      (supportQuotientDerivedAdjunction A i).homEquiv V F (b.hom.app V ≫ f) =
        (supportedCoefficientDerivedAdjunction A i).homEquiv V F f) ↔
      b = supportQuotientComparison A i) ∧
  (∀ P : CochainComplex (ModuleCat.{u + 1} A) ℤ,
    (supportQuotientComparison A i).hom.app (DerivedCategory.Q.obj P) ≫
      (supportedCoefficients A i).mapDerivedCategoryFactors.hom.app P =
    supportQuotientLocalizationComponent A i P ≫
      (supportQuotientCoefficients A i).mapDerivedCategoryFactors.hom.app P ≫
      DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex (supportQuotientOrdinaryIso A i) (.up ℤ)).hom.app
          P)) ∧
  (∀ F : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)),
    (supportQuotientComparison A i).hom.app ((supportedSectionsDerived A i).obj F) ≫
      (supportedCoefficientDerivedAdjunction A i).counit.app F =
    (supportQuotientDerivedAdjunction A i).counit.app F)

end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.ProEtale

/-- All normalizations of the quotient model for a single closed pair. The
ordinary equality identifies the generator adjunction, the Hom equivalence fixes
identity on the common right adjoint, and the complex formula fixes the derived
extension, including its values on unbounded complexes.
Source: blueprint paragraph 4 (blueprint: lem-pur-supported-product-quotient-model). -/
def SupportQuotientModel (A : Type (u + 1)) [CommRing A]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    [Finite A] [IsLocallyNoetherian X] : Prop :=
  (∀ M : ModuleCat.{u + 1} A,
    supportQuotientGenerator A i M ≫ (supportQuotientOrdinaryIso A i).hom.app M =
      supportedCoefficientQuotient A i M) ∧
  (∀ (M : ModuleCat.{u + 1} A)
      (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))
      (f : M ⟶ (supportSections i A).obj F),
    supportQuotientGenerator A i M ≫
      (((supportedCoefficientAdjunction A i).ofNatIsoLeft
        (supportQuotientOrdinaryIso A i).symm).homEquiv M F).symm f =
    ((constantSheafΓAdj (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)).homEquiv M F).symm
      (f ≫ (supportedModuleSectionsι A i).app F)) ∧
  (∀ b : supportQuotientDerived A i ≅ (supportedCoefficients A i).mapDerivedCategory,
    (∀ (V : DerivedCategory (ModuleCat.{u + 1} A))
        (F : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
        (f : (supportedCoefficients A i).mapDerivedCategory.obj V ⟶ F),
      (supportQuotientDerivedAdjunction A i).homEquiv V F (b.hom.app V ≫ f) =
        (supportedCoefficientDerivedAdjunction A i).homEquiv V F f) ↔
      b = supportQuotientComparison A i) ∧
  (∀ P : CochainComplex (ModuleCat.{u + 1} A) ℤ,
    (supportQuotientComparison A i).hom.app (DerivedCategory.Q.obj P) ≫
      (supportedCoefficients A i).mapDerivedCategoryFactors.hom.app P =
    supportQuotientLocalizationComponent A i P ≫
      (supportQuotientCoefficients A i).mapDerivedCategoryFactors.hom.app P ≫
      DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex (supportQuotientOrdinaryIso A i) (.up ℤ)).hom.app
          P)) ∧
  (∀ F : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)),
    (supportQuotientComparison A i).hom.app ((supportedSectionsDerived A i).obj F) ≫
      (supportedCoefficientDerivedAdjunction A i).counit.app F =
    (supportQuotientDerivedAdjunction A i).counit.app F)

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.Etale
variable (A : Type (u + 1)) [CommRing A]
  {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
private theorem comparisonCounit
    (F : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (supportQuotientComparison A i).hom.app ((supportedSectionsDerived A i).obj F) ≫
      (supportedCoefficientDerivedAdjunction A i).counit.app F =
    (supportQuotientDerivedAdjunction A i).counit.app F := by
  unfold supportQuotientComparison supportQuotientDerivedAdjunction
  dsimp only [Iso.trans_hom, NatTrans.comp_app, Adjunction.ofNatIsoLeft_counit,
    Iso.symm_inv, Functor.whiskerLeft_app, asIso_hom]
  rw [Category.assoc]
  congr 1
  exact CategoryTheory.Adjunction.derivedCounitTransportReverse
    (supportedCoefficientAdjunction A i) (supportQuotientOrdinaryIso A i) F

private theorem quotientModel : SupportQuotientModel A i := by
  refine ⟨by
    unfold supportQuotientOrdinaryIso
    exact (supportQuotientOrdinary_existsUnique A i).choose_spec.1, ?_, ?_, ?_,
    comparisonCounit A i⟩
  · intro M F f
    rw [Adjunction.homEquiv_ofNatIsoLeft_symm_apply]
    change supportQuotientGenerator A i M ≫ (supportQuotientOrdinaryIso A i).hom.app M ≫
      ((supportedCoefficientAdjunction A i).homEquiv M F).symm f = _
    have h : supportQuotientGenerator A i M ≫
        (supportQuotientOrdinaryIso A i).hom.app M = supportedCoefficientQuotient A i M :=
      by
        unfold supportQuotientOrdinaryIso
        exact (supportQuotientOrdinary_existsUnique A i).choose_spec.1 M
    rw [← Category.assoc, h]
    exact (exists_unique_supportedCoefficientAdjunction A i).choose_spec.1 M F f
  · intro b
    exact comparisonUnique (supportQuotientDerivedAdjunction A i)
      (supportedCoefficientDerivedAdjunction A i) (supportQuotientComparison A i)
      (comparisonCounit A i) b
  · intro P
    unfold supportQuotientComparison
    dsimp only [Iso.trans_hom, NatTrans.comp_app, asIso_hom]
    rw [Category.assoc, Functor.mapDerivedCategoryNatIso_fac]
    congr 1
    simp [supportQuotientLocalization, Localization.liftNatTrans_app,
      Localization.Lifting.iso, supportQuotientLocalizationComponent]
end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.ProEtale
variable (A : Type (u + 1)) [CommRing A]
  {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [Finite A] [IsLocallyNoetherian X]
private theorem comparisonCounit
    (F : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))) :
    (supportQuotientComparison A i).hom.app ((supportedSectionsDerived A i).obj F) ≫
      (supportedCoefficientDerivedAdjunction A i).counit.app F =
    (supportQuotientDerivedAdjunction A i).counit.app F := by
  unfold supportQuotientComparison supportQuotientDerivedAdjunction
  dsimp only [Iso.trans_hom, NatTrans.comp_app, Adjunction.ofNatIsoLeft_counit,
    Iso.symm_inv, Functor.whiskerLeft_app, asIso_hom]
  rw [Category.assoc]
  congr 1
  exact CategoryTheory.Adjunction.derivedCounitTransportReverse
    (supportedCoefficientAdjunction A i) (supportQuotientOrdinaryIso A i) F

private theorem quotientModel : SupportQuotientModel A i := by
  refine ⟨by
    unfold supportQuotientOrdinaryIso
    exact (supportQuotientOrdinary_existsUnique A i).choose_spec.1, ?_, ?_, ?_,
    comparisonCounit A i⟩
  · intro M F f
    rw [Adjunction.homEquiv_ofNatIsoLeft_symm_apply]
    change supportQuotientGenerator A i M ≫ (supportQuotientOrdinaryIso A i).hom.app M ≫
      ((supportedCoefficientAdjunction A i).homEquiv M F).symm f = _
    have h : supportQuotientGenerator A i M ≫
        (supportQuotientOrdinaryIso A i).hom.app M = supportedCoefficientQuotient A i M :=
      by
        unfold supportQuotientOrdinaryIso
        exact (supportQuotientOrdinary_existsUnique A i).choose_spec.1 M
    rw [← Category.assoc, h]
    exact (exists_unique_supportedCoefficientAdjunction A i).choose_spec.1 M F f
  · intro b
    exact comparisonUnique (supportQuotientDerivedAdjunction A i)
      (supportedCoefficientDerivedAdjunction A i) (supportQuotientComparison A i)
      (comparisonCounit A i) b
  · intro P
    unfold supportQuotientComparison
    dsimp only [Iso.trans_hom, NatTrans.comp_app, asIso_hom]
    rw [Category.assoc, Functor.mapDerivedCategoryNatIso_fac]
    congr 1
    simp [supportQuotientLocalization, Localization.liftNatTrans_app,
      Localization.Lifting.iso, supportQuotientLocalizationComponent]
end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry

/-- The quotient support model for both topologies and all three closed pairs.
Source: blueprint main-20261015, sec-smooth-purity/sk-prop-an,
`lem-pur-kunneth-supported.proof.md`, paragraph 4
(blueprint: lem-pur-supported-product-quotient-model).

Proof: finite type over a field gives the local Noetherian hypotheses for the
three ambient schemes. For each closed pair, tensor the cokernel defining Q
with a constant coefficient module. Tensor preserves cokernels. The normalized
constant-to-closed-pushforward map kills the open term by disjoint-support
vanishing, so it factors through this tensor cokernel. Closed restriction makes
this factor an isomorphism, and open restriction makes both objects zero.
Joint conservativity of the two restrictions proves invertibility. Cancellation
of the tensor quotient epimorphism gives naturality and uniqueness for every
module, without a free presentation or a flatness hypothesis on that module.

Transport exactness from the existing closed-pushforward coefficient functor.
The constant-sheaf functor preserves flat objects by the sheafification flatness
lemma. Apply a functorial flat resolution to coefficient complexes: its constant
image is K-flat by the flat-preserving-functor resolution theorem. The derived
tensor localization map is invertible with this K-flat second factor. Exactness
and naturality transport invertibility along the resolution quasi-isomorphism,
and localization descends this natural isomorphism to the derived categories.
The single-factor total-complex collapse keeps the prescribed signed tensor map.

The generator identity gives the ordinary adjunction normalization. Transport
of a left adjoint along a natural isomorphism commutes with the homotopy and
right-derived adjunction constructions: check their counits after the homotopy
quotient using derived counit factorization, then use localization extensionality.
This identifies the specified derived counits and Hom bijections. Injectivity
of the adjunction Hom equivalence gives uniqueness with identity on the common
right adjoint. Apply these results to i, j and their product immersion. -/
theorem supported_product_quotient_model
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (k : Type u) [Field k] [IsAlgClosed k]
    {X Y Z W : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    [LocallyOfFiniteType g] [QuasiCompact g] [IsSeparated g]
    (i : Z ⟶ X) (j : W ⟶ Y) [IsClosedImmersion i] [IsClosedImmersion j] :
    (Etale.SupportQuotientModel A i ∧ @ProEtale.SupportQuotientModel A _ _ _ i _ _
      (LocallyOfFiniteType.isLocallyNoetherian f)) ∧
    (Etale.SupportQuotientModel A j ∧ @ProEtale.SupportQuotientModel A _ _ _ j _ _
      (LocallyOfFiniteType.isLocallyNoetherian g)) ∧
    (Etale.SupportQuotientModel A (Etale.supportedProductImmersion f g i j) ∧
      @ProEtale.SupportQuotientModel A _ _ _ (Etale.supportedProductImmersion f g i j) _ _
        (LocallyOfFiniteType.isLocallyNoetherian (pullback.fst f g ≫ f))) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian g
  have : IsLocallyNoetherian (pullback f g) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst f g ≫ f)
  exact ⟨⟨Etale.quotientModel A i, ProEtale.quotientModel A i⟩,
    ⟨Etale.quotientModel A j, ProEtale.quotientModel A j⟩,
    ⟨Etale.quotientModel A _, ProEtale.quotientModel A _⟩⟩

end AlgebraicGeometry
