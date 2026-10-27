/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q139
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import Sheaf.SecSmoothPurity.ScalarExtensionFunctor
public import Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all Sheaf.Paper.AdicCoefficientDatum
import all Sheaf.SecSmoothPurity.ScalarAssociatorConjugate
import all Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization
import Sheaf.Algebra.Category.ModuleCat.Sheaf.ScalarExtensionRingIso
import all Sheaf.CategoryTheory.ExactEquivalenceDerivedSquares

/-! # Constant-coefficient tower transport and scalar-associator normalization

Source: Stacks Project, sites-cohomology.tex, Tags 0D6D, 06YY, 06YS, 0G7E and 07A6;
sites.tex, Tag 0H7J; sites-modules.tex, lemma-adjoint-push-pull-modules.
(blueprint: lem-sp-proetale-coefficient-tower-normalization).

All constructions below specialize the recorded module operations and universal
left-derived presentations. Scalar-first tensors `c ⊗ (b ⊗ x)` encode the paper's
`(x ⊗ b) ⊗ c`. No coefficient map is assumed flat and no complex is bounded.
-/

@[expose] public noncomputable section
set_option autoImplicit false
-- Sequential checking avoids contention among the large derived-category specializations.
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe u uC vC r w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open AlgebraicGeometry.Scheme
open SheafOfModules.SuccessiveDerivedQuotient

namespace AlgebraicGeometry.ProEtale

/-- The published ordinary and derived scalar extension with its universal counit,
repackaged in the presentation type of successive normalization; no choices are made.
Source: Stacks 06YY and 07A6
(blueprint: lem-sp-proetale-coefficient-tower-normalization). -/
def coefficientTowerPresentation (T : Scheme.{u})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (a : R ⟶ S) :
    Presentation.{u + 1, u, u + 1, u + 2} a where
  ordinary := reductionChange T a
  obj_eq := (reductionChangeExistence T a).choose_spec.choose
  map_eq := (reductionChangeExistence T a).choose_spec.choose_spec.choose
  additive := reductionChangeAdditive T a
  derived := reductionDerivedChange T a
  counit := reductionDerivedCounit T a
  universal := reductionDerivedUniversal T a

/-- The existing normalization data specialized to the original small pro-etale site.
The internal smallness witness enlarges neither its object nor its morphism universe.
Source: Stacks 0D6D and 09A5
(blueprint: lem-sp-proetale-coefficient-tower-normalization). -/
def CoefficientTowerNormalizationData (T : Scheme.{u}) : Type (u + 2) :=
  letI : EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  Normalization.{u + 1, u, u + 1, u + 2} (C := T.ProEt)
    (J := ProEt.topology T) (fun a ↦ coefficientTowerPresentation T a)

/-- Access to the recorded balanced associator with every site universe fixed explicitly.
Source: Stacks 0D6D
(blueprint: lem-sp-proetale-coefficient-tower-normalization). -/
def coefficientTowerBalancedComparison (T : Scheme.{u})
    (ν : CoefficientTowerNormalizationData T)
    {R S V : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (a : R ⟶ S) (b : S ⟶ V) :
    reductionDerivedChange T a ⋙ reductionDerivedChange T b ≅
      reductionDerivedChange T (a ≫ b) :=
  @Normalization.derived.{u + 1, u, u + 1, u + 2} T.ProEt inferInstance
    (essentiallySmallSelf.{0, u, u + 1} _) (ProEt.topology T)
    inferInstance inferInstance inferInstance
    (fun R ↦ reductionModulesHasDerivedCategory T R)
    (fun a ↦ coefficientTowerPresentation T a) ν R S V a b

/-- Relabel the inverse-image coefficient action by the inverse of the specified `c`.
This is restriction of scalars, so the underlying sheaf and its sections are unchanged.
Source: Stacks 03D7 and the ring-isomorphism specialization of 06YY
(blueprint: lem-sp-proetale-coefficient-tower-normalization). -/
abbrev coefficientTowerRelabel {Z Y : Scheme.{u}} (q : Z ⟶ Y)
    (A : Type u) [CommRing A] :=
  SheafOfModules.restrictScalars ((sheafCompose (ProEt.topology Z)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (proEtaleConstantRingComparison q A).inv)

/-- Exact relabelling on unbounded derived categories, induced termwise by the
existing inverse-isomorphism restriction functor.
Source: Stacks 06YY, ring-isomorphism specialization
(blueprint: lem-sp-proetale-coefficient-tower-normalization). -/
def coefficientTowerDerivedRelabel {Z Y : Scheme.{u}} (q : Z ⟶ Y)
    (A : Type u) [CommRing A] :
    reductionDerivedCategory Z
        ((proEtaleSheafInverseImage q CommRingCat.{u + 1}).obj (proEtaleConstantRing Y A)) ⥤
      proEtaleDerivedCategory Z A :=
  @Functor.mapDerivedCategory _ _ _ _ _ _ _ _ (coefficientTowerRelabel q A) inferInstance
    (proEtaleRingRestrictScalars_preservesFiniteLimits (proEtaleConstantRingComparison q A).inv)
    (proEtaleRingRestrictScalars_preservesFiniteColimits (proEtaleConstantRingComparison q A).inv)

/-- The canonical localization factorization of coefficient relabelling.
Source: Stacks 06YY, ring-isomorphism specialization
(blueprint: lem-sp-proetale-coefficient-tower-normalization). -/
def coefficientTowerRelabelFactors {Z Y : Scheme.{u}} (q : Z ⟶ Y)
    (A : Type u) [CommRing A] :
    DerivedCategory.Q ⋙ coefficientTowerDerivedRelabel q A ≅
      (coefficientTowerRelabel q A).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
  @Functor.mapDerivedCategoryFactors _ _ _ _ _ _ _ _ (coefficientTowerRelabel q A)
    inferInstance
    (proEtaleRingRestrictScalars_preservesFiniteLimits (proEtaleConstantRingComparison q A).inv)
    (proEtaleRingRestrictScalars_preservesFiniteColimits (proEtaleConstantRingComparison q A).inv)

private theorem towerDerivedRelabel_eq {Z Y : Scheme.{u}} (q : Z ⟶ Y)
    (A : Type u) [CommRing A] :
    coefficientTowerDerivedRelabel q A = (coefficientTowerRelabel q A).mapDerivedCategory :=
  rfl

private theorem towerRelabelFactors_eq {Z Y : Scheme.{u}} (q : Z ⟶ Y)
    (A : Type u) [CommRing A] :
    coefficientTowerRelabelFactors q A =
      (coefficientTowerRelabel q A).mapDerivedCategoryFactors :=
  rfl

attribute [local irreducible] coefficientTowerDerivedRelabel coefficientTowerRelabelFactors

private noncomputable def towerRelabelEquivalenceRaw
    {C₀ : Type uC} [Category.{vC} C₀] {J : GrothendieckTopology C₀}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    {R S : Sheaf J CommRingCat.{r}} (c : R ≅ S) :
    SheafOfModules.SuccessiveDerivedQuotient.Modules R ≌
      SheafOfModules.SuccessiveDerivedQuotient.Modules S := by
  let rc := (sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).mapIso c
  let : (CategoryTheory.Equivalence.refl (C := C₀)).functor.IsContinuous J J := by
    change (𝟭 C₀).IsContinuous J J
    infer_instance
  let : (CategoryTheory.Equivalence.refl (C := C₀)).inverse.IsContinuous J J := by
    change (𝟭 C₀).IsContinuous J J
    infer_instance
  exact SheafOfModules.pushforwardPushforwardEquivalence
    (J := J) (K := J) (S := (sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj S)
    (R := (sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)
    (CategoryTheory.Equivalence.refl (C := C₀)) rc.inv rc.hom
    (by
      apply NatTrans.ext
      funext U
      dsimp [CategoryTheory.Equivalence.refl]
      erw [((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R).obj.map_id]
      exact congrArg (fun q ↦ q.hom.app U) rc.hom_inv_id.symm)
    (by
      apply NatTrans.ext
      funext U
      dsimp [CategoryTheory.Equivalence.refl]
      erw [((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj S).obj.map_id,
        Category.comp_id]
      exact congrArg (fun q ↦ q.hom.app U) rc.inv_hom_id)

private noncomputable def towerRelabelEquivalence
    {C₀ : Type uC} [Category.{vC} C₀] {J : GrothendieckTopology C₀}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    {R S : Sheaf J CommRingCat.{r}} (c : R ≅ S) :
    SheafOfModules.SuccessiveDerivedQuotient.Modules R ≌
      SheafOfModules.SuccessiveDerivedQuotient.Modules S :=
  (towerRelabelEquivalenceRaw c).changeFunctor
    (show (towerRelabelEquivalenceRaw c).functor ≅ restriction c.inv from Iso.refl _)

-- The generic helpers deliberately retain the site's smallness and localization data.
set_option linter.unusedSectionVars false

private local instance towerSmall (T : Scheme.{u}) : EssentiallySmall.{u + 1} T.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} _

attribute [local irreducible] completedAdicChange completedAdicDerivedChange
attribute [local irreducible] reductionChange reductionDerivedChange
attribute [local irreducible] reductionDerivedCounit reductionComplexCounit
attribute [local irreducible] HasDerivedCategory.standard
attribute [local irreducible] SheafOfModules.monoidalCategory

attribute [local irreducible] derivedComp ordinaryComp rightComp

-- Prefer the given sheafification data to searches through site equivalences.
private local instance towerWeakSheafify
    {C₀ : Type uC} [Category.{vC} C₀] {J : GrothendieckTopology C₀}
    [h : HasSheafify J AddCommGrpCat.{r}] : HasWeakSheafify J AddCommGrpCat.{r} :=
  h.isRightAdjoint

section
attribute [local instance] restriction_limits restriction_colimits

private theorem normalizationForPresentation
    {C₀ : Type uC} [Category.{vC} C₀] [EssentiallySmall.{r} C₀]
    {J : GrothendieckTopology C₀}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
    [hD : ∀ R : Sheaf J CommRingCat.{r}, HasDerivedCategory.{w} (Modules R)]
    (p : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S), Presentation.{uC, vC, r, w} a)
    (D : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S), AdjData.{uC, vC, r, w} (p a)) :
    ∃ ν : Normalization.{uC, vC, r, w} p, ∀ {R S V : Sheaf J CommRingCat.{r}}
      (a : R ⟶ S) (b : S ⟶ V),
      ν.derived a b = derivedComp p D a b ∧
      ν.ordinary a b = ordinaryComp p (fun a ↦ (D a).ordinary) a b := by
  let A := fun {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S) ↦
    (D a).ordinary
  refine ⟨{
    ordinary := ordinaryComp p A
    ordinary_hom := ordinaryComp_hom p A (fun a ↦ (D a).ordinary_unit)
    ordinary_inv := ordinaryComp_inv p A (fun a ↦ (D a).ordinary_unit)
    derived := derivedComp p D
    computed := fun a ↦ (D a).computed
    intermediate_computed := fun a b ↦ intermediate_computed a b (p a) (p b) (D b)
    representative := fun a b P _ _ ↦ derivedComp_representative p D a b
      ((HomotopyCategory.quotient _ _).obj P)
    ordinaryAdjunction := A
    ordinary_unit := fun a ↦ (D a).ordinary_unit
    right := fun a ↦ (restriction a).mapDerivedCategory
    right_factors := fun a ↦ (restriction a).mapDerivedCategoryFactorsh
    adjunction := fun a ↦ (D a).derived
    adjunction_normalization := fun a ↦ (D a).unit_normalization
    restrictionComp := fun a b ↦ resComp a b
    restrictionComp_sections := by intros; rfl
    rightComp := fun a b ↦ rightComp a b
    rightComp_normalization := fun a b H ↦ rightComp_normalization.{uC, vC, r, w} a b H
    unit_comp := derivedComp_unit p D
    associative := derivedComp_assoc p D
    coefficient_naturality := derivedComp_coefficient_naturality p D }, ?_⟩
  intro R S V a b
  exact ⟨rfl, rfl⟩

end

private theorem compEqToHom
    {D E : Type*} [Category D] [Category E] {F G H : D ⥤ E}
    (e : F ≅ G) (h : G = H) (X : D) :
    e.hom.app X ≫ eqToHom (congrArg (fun F ↦ F.obj X) h) =
      (e ≪≫ eqToIso h).hom.app X := by
  subst H
  simp

private theorem normalizationComp_transport
    {C₀ : Type uC} [Category.{vC} C₀] [EssentiallySmall.{r} C₀]
    {J : GrothendieckTopology C₀}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
    [hD : ∀ R : Sheaf J CommRingCat.{r}, HasDerivedCategory.{w} (Modules R)]
    (p : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S), Presentation.{uC, vC, r, w} a)
      (D : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S), AdjData.{uC, vC, r, w} (p a))
    (ν : Normalization p)
    (hν : ∀ {R S V : Sheaf J CommRingCat.{r}} (a : R ⟶ S) (b : S ⟶ V),
      ν.derived a b = derivedComp p D a b)
    {R S V : Sheaf J CommRingCat.{r}} (a : R ⟶ S) (b : S ⟶ V) (c : R ⟶ V)
    (h : a ≫ b = c) (e : (p a).derived ⋙ (p b).derived ≅ (p c).derived)
    (he : e = derivedComp p D a b ≪≫ eqToIso (congrArg (fun f ↦ (p f).derived) h))
    (X : DerivedCategory (Modules R)) :
    (ν.derived a b).hom.app X ≫
      eqToHom (congrArg (fun f ↦ (p f).derived.obj X) h) = e.hom.app X := by
  rw [hν]
  exact (compEqToHom (derivedComp p D a b)
    (congrArg (fun f ↦ (p f).derived) h) X).trans
      (congrArg (fun e ↦ e.hom.app X) he.symm)

attribute [local irreducible] publishedData

private theorem towerSquare
    {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {Z Y : Scheme.{u}} (q : Z ⟶ Y) :
    (proEtaleSheafInverseImage q CommRingCat.{u + 1}).map
        (proEtaleConstantRingMap (T := Y) φ) ≫ proEtaleCoefficientInverseImageMap q B =
      proEtaleCoefficientInverseImageMap q A ≫ proEtaleConstantRingMap (T := Z) φ := by
  let a := CommRingCat.ofHom (φ.ulift : ULift.{u + 1} A →+* ULift.{u + 1} B)
  have hr : proEtaleConstantRingMap (T := Y) φ ≫
        proEtaleCoefficientDirectImageMap q B =
      proEtaleCoefficientDirectImageMap q A ≫
        (proEtaleSheafDirectImage q CommRingCat.{u + 1}).map
          (proEtaleConstantRingMap (T := Z) φ) := by
    apply ((sheafificationAdjunction (ProEt.topology Y) CommRingCat.{u + 1}).homEquiv
      ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A))) _).injective
    change (sheafificationAdjunction (ProEt.topology Y) CommRingCat.{u + 1}).homEquiv
      _ _ ((presheafToSheaf _ _).map ((Functor.const Y.ProEtᵒᵖ).map a) ≫ _) = _
    rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
    unfold proEtaleCoefficientDirectImageMap proEtaleConstantDirectImageMap
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    apply NatTrans.ext
    funext U
    exact congrArg (fun f ↦ f.app ((proEtaleBaseChange q).op.obj U))
      (toSheafify_naturality (ProEt.topology Z) ((Functor.const Z.ProEtᵒᵖ).map a))
  change (proEtaleSheafInverseImage q CommRingCat.{u + 1}).map _ ≫
    ((proEtaleSheafAdjunction q CommRingCat.{u + 1}).homEquiv _ _).symm
      (proEtaleCoefficientDirectImageMap q B) =
    ((proEtaleSheafAdjunction q CommRingCat.{u + 1}).homEquiv _ _).symm
      (proEtaleCoefficientDirectImageMap q A) ≫ _
  rw [← Adjunction.homEquiv_naturality_left_symm,
    ← Adjunction.homEquiv_naturality_right_symm, hr]

open scoped ChangeOfRings

section TensorBridge
variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [HasSheafify J AddCommGrpCat.{r}] [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  {R S : Sheaf J CommRingCat.{r}}
open SheafOfModules
private noncomputable def towerExtensionPresheafIso (a : R ⟶ S) (M : Modules R) :
    changeOfRingsPresheaf a M ≅ changeOfRingsPresheafOfUniverses a M :=
  PresheafOfModules.isoMk (fun _ ↦ Iso.refl _) (by
      intro V W i
      apply ModuleCat.hom_ext
      ext t
      induction t using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | add z z' hz hz' => simp only [_root_.map_add, hz, hz']
      | tmul s x =>
        change changeOfRingsMap a M i (s ⊗ₜ[R.obj.obj V, (a.hom.app V).hom] x) =
          changeOfRingsMapOfUniverses a M i (s ⊗ₜ[R.obj.obj V, (a.hom.app V).hom] x)
        exact (Classical.choose_spec (exists_changeOfRingsMap a M i) s x).trans
          (changeOfRingsMap_tmulOfUniverses a M i s x).symm)

private noncomputable def towerExtensionIso (a : R ⟶ S) (M : Modules R) :
    changeOfRings a M ≅ changeOfRingsOfUniverses a M :=
  (PresheafOfModules.sheafification (𝟙 _)).mapIso (towerExtensionPresheafIso a M)

omit [EssentiallySmall.{r} C] in
private theorem towerExtensionIso_unit (a : R ⟶ S) (M : Modules R)
    (V : Cᵒᵖ) (x : M.val.obj V) :
    (towerExtensionIso a M).hom.val.app V
      (((PresheafOfModules.sheafificationAdjunction (𝟙 _)).unit.app
        (changeOfRingsPresheaf a M)).app V
          ((1 : S.obj.obj V) ⊗ₜ[R.obj.obj V, (a.hom.app V).hom] x)) =
      scalarExtensionRingIsoTmul.{uC, vC, r, r} a M V x 1 := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj S).obj)
  dsimp only [towerExtensionIso, Functor.mapIso_hom]
  have hn := adj.unit.naturality (towerExtensionPresheafIso a M).hom
  exact (congrArg (fun f ↦ f.app V
    ((1 : S.obj.obj V) ⊗ₜ[R.obj.obj V, (a.hom.app V).hom] x)) hn).symm

end TensorBridge

private theorem extensionIso_naturality
    {C₀ : Type uC} [Category.{vC} C₀] [EssentiallySmall.{r} C₀]
    {J : GrothendieckTopology C₀}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
    {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S)
    {M N : Modules R} (f : M ⟶ N) :
    SheafOfModules.changeOfRingsHom a M f ≫
        (towerExtensionIso a N).hom =
      (towerExtensionIso a M).hom ≫
        SheafOfModules.changeOfRingsHomOfUniverses a M f := by
  let sh := PresheafOfModules.sheafification
    (R := (sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj S)
    (𝟙 (S.obj ⋙ forget₂ CommRingCat RingCat))
  change sh.map _ ≫ sh.map _ = sh.map _ ≫ sh.map _
  rw [← sh.map_comp, ← sh.map_comp]
  congr 1

private theorem towerScalarIso_exists
    {C₀ : Type uC} [Category.{vC} C₀] [EssentiallySmall.{r} C₀]
    {J : GrothendieckTopology C₀}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
    {R S : Sheaf J CommRingCat.{r}} (c : R ≅ S) :
    ∃ θ : ∀ M : Modules R,
      SheafOfModules.changeOfRings c.hom M ≅ (restriction c.inv).obj M,
      (∀ (M : Modules R) (U : C₀ᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U),
        (θ M).hom.val.app U (pure c.hom M U s x) = c.inv.hom.app U s • x) ∧
      (∀ (M : Modules R) (U : C₀ᵒᵖ) (x : M.val.obj U),
        (θ M).inv.val.app U x = pure c.hom M U 1 x) ∧
      (∀ {M N : Modules R} (f : M ⟶ N),
        SheafOfModules.changeOfRingsHom c.hom M f ≫ (θ N).hom =
          (θ M).hom ≫ (restriction c.inv).map f) := by
  obtain ⟨θ, hh, hi, hn⟩ := SheafOfModules.exists_scalarExtensionRingIso.{uC, vC, r, r} c
  let e (M : Modules R) := towerExtensionIso c.hom M
  let t (M : Modules R) := e M ≪≫ θ M
  have hunit (M : Modules R) (U : C₀ᵒᵖ) (x : M.val.obj U) :
      (t M).hom.val.app U (pure c.hom M U 1 x) = x := by
    change (θ M).hom.val.app U ((e M).hom.val.app U (pure c.hom M U 1 x)) = x
    have he := towerExtensionIso_unit c.hom M U x
    change (e M).hom.val.app U (pure c.hom M U 1 x) =
      SheafOfModules.scalarExtensionRingIsoTmul.{uC, vC, r, r} c.hom M U x 1 at he
    exact (congrArg ((θ M).hom.val.app U) he).trans
      ((hh M U x 1).trans (by rw [map_one, one_smul]))
  refine ⟨t, ?_, ?_, ?_⟩
  · intro M U s x
    let η := (PresheafOfModules.sheafificationAdjunction.{r}
      (R := (sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj S) (𝟙 _)).unit.app
        (SheafOfModules.changeOfRingsPresheaf c.hom M)
    have hp : pure c.hom M U s x = s • pure c.hom M U 1 x := by
      change η.app U (s ⊗ₜ[R.obj.obj U, (c.hom.hom.app U).hom] x) =
        s • η.app U ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (c.hom.hom.app U).hom] x)
      rw [← (η.app U).hom.map_smul]
      congr 1
      change s ⊗ₜ[R.obj.obj U, (c.hom.hom.app U).hom] x =
        (s * 1) ⊗ₜ[R.obj.obj U, (c.hom.hom.app U).hom] x
      rw [mul_one]
    rw [hp, ((t M).hom.val.app U).hom.map_smul, hunit]
    rfl
  · intro M U x
    have h := congrArg ((t M).inv.val.app U) (hunit M U x)
    have he := congrArg (fun f ↦ f.val.app U (pure c.hom M U 1 x)) (t M).hom_inv_id
    exact h.symm.trans he
  · intro M N f
    dsimp only [t, Iso.trans_hom]
    rw [← Category.assoc, extensionIso_naturality, Category.assoc, hn M N f]
    exact (Category.assoc _ _ _).symm

/-- The tensor formulas determine each component, so this choice retains the normalized
comparison rather than selecting an arbitrary module isomorphism. -/
private noncomputable def towerScalarIso
    {C₀ : Type uC} [Category.{vC} C₀] [EssentiallySmall.{r} C₀]
    {J : GrothendieckTopology C₀}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
    {R S : Sheaf J CommRingCat.{r}} (c : R ≅ S) (M : Modules R) :
    SheafOfModules.changeOfRings c.hom M ≅ (restriction c.inv).obj M :=
  (towerScalarIso_exists c).choose M

private theorem towerScalarIso_hom
    {C₀ : Type uC} [Category.{vC} C₀] [EssentiallySmall.{r} C₀]
    {J : GrothendieckTopology C₀}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
    {R S : Sheaf J CommRingCat.{r}} (c : R ≅ S) (M : Modules R)
    (U : C₀ᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U) :
    (towerScalarIso c M).hom.val.app U (pure c.hom M U s x) = c.inv.hom.app U s • x :=
  (towerScalarIso_exists c).choose_spec.1 M U s x

private theorem towerScalarIso_inv
    {C₀ : Type uC} [Category.{vC} C₀] [EssentiallySmall.{r} C₀]
    {J : GrothendieckTopology C₀}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
    {R S : Sheaf J CommRingCat.{r}} (c : R ≅ S) (M : Modules R)
    (U : C₀ᵒᵖ) (x : M.val.obj U) :
    (towerScalarIso c M).inv.val.app U x = pure c.hom M U 1 x :=
  (towerScalarIso_exists c).choose_spec.2.1 M U x

private theorem towerScalarIso_naturality
    {C₀ : Type uC} [Category.{vC} C₀] [EssentiallySmall.{r} C₀]
    {J : GrothendieckTopology C₀}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
    {R S : Sheaf J CommRingCat.{r}} (c : R ≅ S) {M N : Modules R} (f : M ⟶ N) :
    SheafOfModules.changeOfRingsHom c.hom M f ≫ (towerScalarIso c N).hom =
      (towerScalarIso c M).hom ≫ (restriction c.inv).map f :=
  (towerScalarIso_exists c).choose_spec.2.2 f

private theorem towerGeometricTransport
    {C₀ : Type uC} [Category.{vC} C₀] [EssentiallySmall.{r} C₀]
    {J : GrothendieckTopology C₀}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
    {R S : Sheaf J CommRingCat.{r}} (c : R ≅ S)
    {E : Type*} [Category E] (F : E ⥤ Modules R) (G : E ⥤ Modules S)
    (ho : ∀ M, G.obj M = SheafOfModules.changeOfRings c.hom (F.obj M))
    (hm : ∀ {M N : E} (f : M ⟶ N),
      G.map f = eqToHom (ho M) ≫
        SheafOfModules.changeOfRingsHom c.hom (F.obj M) (F.map f) ≫
        eqToHom (ho N).symm) :
    ∃ e : G ≅ F ⋙ restriction c.inv,
      (∀ (M : E) (U : C₀ᵒᵖ) (s : S.obj.obj U) (x : (F.obj M).val.obj U),
        (e.hom.app M).val.app U
          ((eqToHom (ho M).symm).val.app U (pure c.hom (F.obj M) U s x)) =
            c.inv.hom.app U s • x) ∧
      (∀ (M : E) (U : C₀ᵒᵖ) (x : (F.obj M).val.obj U),
        (e.inv.app M).val.app U x =
          (eqToHom (ho M).symm).val.app U (pure c.hom (F.obj M) U 1 x)) := by
  let e : G ≅ F ⋙ restriction c.inv :=
    NatIso.ofComponents (fun M ↦ eqToIso (ho M) ≪≫ towerScalarIso c (F.obj M)) (by
      intro M N f
      dsimp only [Functor.comp_map, Iso.trans_hom, eqToIso.hom]
      rw [hm]
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      rw [towerScalarIso_naturality])
  refine ⟨e, ?_, ?_⟩
  · intro M U s x
    have he : eqToHom (ho M).symm ≫ e.hom.app M = (towerScalarIso c (F.obj M)).hom := by
      dsimp only [e, NatIso.ofComponents_hom_app, Iso.trans_hom, eqToIso.hom]
      simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    have hh := congrArg (fun f ↦ f.val.app U (pure c.hom (F.obj M) U s x)) he
    exact hh.trans (towerScalarIso_hom c (F.obj M) U s x)
  · intro M U x
    change ((towerScalarIso c (F.obj M)).inv ≫ eqToHom (ho M).symm).val.app U x = _
    change (eqToHom (ho M).symm).val.app U
      ((towerScalarIso c (F.obj M)).inv.val.app U x) = _
    rw [towerScalarIso_inv]

private noncomputable def presentationRingIso
    {C₀ : Type uC} [Category.{vC} C₀] [EssentiallySmall.{r} C₀]
    {J : GrothendieckTopology C₀}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
    [∀ R : Sheaf J CommRingCat.{r}, HasDerivedCategory.{w} (Modules R)]
    {R S : Sheaf J CommRingCat.{r}} (c : R ≅ S)
    (p : Presentation.{uC, vC, r, w} c.hom) :
    p.ordinary ≅ restriction c.inv :=
  NatIso.ofComponents (fun M ↦ eqToIso (p.obj_eq M) ≪≫ towerScalarIso c M) (by
    intro M N f
    dsimp only [Iso.trans_hom, eqToIso.hom]
    rw [p.map_eq]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [towerScalarIso_naturality])

private theorem presentationRingIso_app
    {C₀ : Type uC} [Category.{vC} C₀] [EssentiallySmall.{r} C₀]
    {J : GrothendieckTopology C₀}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
    [∀ R : Sheaf J CommRingCat.{r}, HasDerivedCategory.{w} (Modules R)]
    {R S : Sheaf J CommRingCat.{r}} (c : R ≅ S)
    (p : Presentation.{uC, vC, r, w} c.hom) (M : Modules R) :
    (presentationRingIso c p).app M = eqToIso (p.obj_eq M) ≪≫ towerScalarIso c M :=
  rfl

attribute [local irreducible] towerScalarIso presentationRingIso


section ScalarSquare
variable {C₀ : Type uC} [Category.{vC} C₀] [EssentiallySmall.{r} C₀]
  {J : GrothendieckTopology C₀}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
  [∀ R : Sheaf J CommRingCat.{r}, HasDerivedCategory.{w} (Modules R)]
  (p : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S), Presentation.{uC, vC, r, w} a)
  (ν : Normalization p)
  {R S R' S' : Sheaf J CommRingCat.{r}}
  (a : R ⟶ S) (a' : R' ⟶ S') (α : R ≅ R') (β : S ≅ S')
  (h : a ≫ β.hom = α.hom ≫ a')

private theorem presentationRingIso_hom
    {R S : Sheaf J CommRingCat.{r}} (c : R ≅ S)
    (M : Modules R) (U : C₀ᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U) :
    ((presentationRingIso c (p c.hom)).hom.app M).val.app U
      (sectionTensor (p c.hom) M U s x) = c.inv.hom.app U s • x := by
  change ((presentationRingIso c (p c.hom)).app M).hom.val.app U _ = _
  rw [presentationRingIso_app]
  dsimp only [Iso.trans_hom, eqToIso.hom]
  change (towerScalarIso c M).hom.val.app U
    ((eqToHom ((p c.hom).obj_eq M)).val.app U
      ((eqToHom ((p c.hom).obj_eq M).symm).val.app U (pure c.hom M U s x))) = _
  have hi := congrArg (fun f ↦ f.val.app U (pure c.hom M U s x))
    (eqToIso ((p c.hom).obj_eq M)).inv_hom_id
  change (eqToHom ((p c.hom).obj_eq M)).val.app U
    ((eqToHom ((p c.hom).obj_eq M).symm).val.app U _) = _ at hi
  rw [hi]
  exact towerScalarIso_hom c M U s x

private theorem presentationRingIso_inv
    {R S : Sheaf J CommRingCat.{r}} (c : R ≅ S)
    (M : Modules R) (U : C₀ᵒᵖ) (x : M.val.obj U) :
    ((presentationRingIso c (p c.hom)).inv.app M).val.app U x =
      sectionTensor (p c.hom) M U 1 x := by
  change ((presentationRingIso c (p c.hom)).app M).inv.val.app U _ = _
  rw [presentationRingIso_app]
  dsimp only [Iso.trans_inv, eqToIso.inv]
  change (eqToHom ((p c.hom).obj_eq M).symm).val.app U
    ((towerScalarIso c M).inv.val.app U x) = _
  rw [towerScalarIso_inv]
  rfl

private noncomputable def towerOrdinarySquare :
    (p a).ordinary ⋙ restriction β.inv ≅ restriction α.inv ⋙ (p a').ordinary :=
  isoWhiskerLeft (p a).ordinary (presentationRingIso β (p β.hom)).symm ≪≫
    ν.ordinary a β.hom ≪≫
    eqToIso (congrArg (fun f ↦ (p f).ordinary) h) ≪≫
    (ν.ordinary α.hom a').symm ≪≫
    isoWhiskerRight (presentationRingIso α (p α.hom)) (p a').ordinary

include ν in
private theorem sectionTensor_naturality
    {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S)
    {M N : Modules R} (f : M ⟶ N) (U : C₀ᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U) :
    ((p a).ordinary.map f).val.app U (sectionTensor (p a) M U s x) =
      sectionTensor (p a) N U s (f.val.app U x) := by
  have hu := congrArg (fun g ↦ g.val.app U x) ((ν.ordinaryAdjunction a).unit.naturality f).symm
  change ((p a).ordinary.map f).val.app U
    (((ν.ordinaryAdjunction a).unit.app M).val.app U x) =
      ((ν.ordinaryAdjunction a).unit.app N).val.app U (f.val.app U x) at hu
  simp only [ν.ordinary_unit] at hu
  rw [sectionTensor_smul_one (p a) M U s x,
    (((p a).ordinary.map f).val.app U).hom.map_smul, hu,
    ← sectionTensor_smul_one]

omit [EssentiallySmall.{r} C₀] in
private theorem sectionTensor_transport
    {R S : Sheaf J CommRingCat.{r}} {a b : R ⟶ S} (h : a = b)
    (M : Modules R) (U : C₀ᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U) :
    (eqToHom (congrArg (fun f ↦ (p f).ordinary.obj M) h)).val.app U
      (sectionTensor (p a) M U s x) = sectionTensor (p b) M U s x := by
  cases h
  rfl

private theorem towerOrdinarySquare_hom
    (M : Modules R) (U : C₀ᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U) :
    ((towerOrdinarySquare p ν a a' α β h).hom.app M).val.app U
      (sectionTensor (p a) M U s x) =
        sectionTensor (p a') ((restriction α.inv).obj M) U (β.hom.hom.app U s) x := by
  dsimp only [towerOrdinarySquare, Iso.trans_hom, NatTrans.comp_app,
    isoWhiskerLeft_hom, isoWhiskerRight_hom, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Iso.symm_hom, eqToIso.hom]
  rw [eqToHom_app]
  change ((p a').ordinary.map ((presentationRingIso α (p α.hom)).hom.app M)).val.app U
    (((ν.ordinary α.hom a').inv.app M).val.app U
      ((eqToHom (congrArg (fun f ↦ (p f).ordinary.obj M) h)).val.app U
        (((ν.ordinary a β.hom).hom.app M).val.app U
          (((presentationRingIso β (p β.hom)).inv.app ((p a).ordinary.obj M)).val.app U
            (sectionTensor (p a) M U s x))))) = _
  rw [presentationRingIso_inv, ν.ordinary_hom, mul_one,
    sectionTensor_transport p h, ν.ordinary_inv, sectionTensor_naturality p ν,
    presentationRingIso_hom, map_one, one_smul]

private theorem towerOrdinarySquare_inv
    (M : Modules R) (U : C₀ᵒᵖ) (t : S'.obj.obj U) (x : M.val.obj U) :
    ((towerOrdinarySquare p ν a a' α β h).inv.app M).val.app U
      (sectionTensor (p a') ((restriction α.inv).obj M) U t x) =
        sectionTensor (p a) M U (β.inv.hom.app U t) x := by
  apply (ConcreteCategory.bijective_of_isIso
    ((SheafOfModules.evaluation _ U).map
      ((towerOrdinarySquare p ν a a' α β h).hom.app M))).1
  have hi := congrArg (fun f ↦ f.val.app U
    (sectionTensor (p a') ((restriction α.inv).obj M) U t x))
      ((towerOrdinarySquare p ν a a' α β h).inv_hom_id_app M)
  change ((towerOrdinarySquare p ν a a' α β h).hom.app M).val.app U
    (((towerOrdinarySquare p ν a a' α β h).inv.app M).val.app U _) =
      sectionTensor (p a') ((restriction α.inv).obj M) U t x at hi
  change ((towerOrdinarySquare p ν a a' α β h).hom.app M).val.app U
    (((towerOrdinarySquare p ν a a' α β h).inv.app M).val.app U _) =
      ((towerOrdinarySquare p ν a a' α β h).hom.app M).val.app U _
  have hb : β.hom.hom.app U (β.inv.hom.app U t) = t :=
    ConcreteCategory.congr_hom (congrArg (fun f ↦ f.hom.app U) β.inv_hom_id) t
  erw [hi, towerOrdinarySquare_hom, hb]

end ScalarSquare

attribute [local irreducible] towerOrdinarySquare

section GenericTransport
variable {C₀ : Type uC} [Category.{vC} C₀] [EssentiallySmall.{r} C₀]
  {J : GrothendieckTopology C₀}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
  [hD : ∀ R : Sheaf J CommRingCat.{r}, HasDerivedCategory.{w} (Modules R)]
  (p : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S), Presentation.{uC, vC, r, w} a)
  {R S R' S' : Sheaf J CommRingCat.{r}}
  (a : R ⟶ S) (a' : R' ⟶ S') (α : R ≅ R') (β : S ≅ S')
  (h : a ≫ β.hom = α.hom ≫ a')
attribute [local instance] restriction_limits restriction_colimits

private theorem towerDerivedSquare (ν : Normalization p) :
    ∃ eD : (p a).derived ⋙ (restriction β.inv).mapDerivedCategory ≅
        (restriction α.inv).mapDerivedCategory ⋙ (p a').derived,
      ∀ P : CochainComplex (Modules R) ℤ,
        eD.hom.app (DerivedCategory.Q.obj P) ≫
            (p a').derived.map ((restriction α.inv).mapDerivedCategoryFactors.hom.app P) ≫
            reductionComplexCounit (p a').ordinary (p a').derived (p a').counit
              (((restriction α.inv).mapHomologicalComplex (.up ℤ)).obj P) =
          (restriction β.inv).mapDerivedCategory.map
            (reductionComplexCounit (p a).ordinary (p a).derived (p a).counit P) ≫
          (restriction β.inv).mapDerivedCategoryFactors.hom.app
            (((p a).ordinary.mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map
            ((NatIso.mapHomologicalComplex (towerOrdinarySquare p ν a a' α β h)
              (.up ℤ)).hom.app P) := by
  have := (p a).universal
  have := (p a').universal
  have := complexCounitNat_kan (p a).ordinary (p a).derived (p a).counit
  have := complexCounitNat_kan (p a').ordinary (p a').derived (p a').counit
  have := Functor.IsLeftDerivedFunctor.isRightKanExtension (p a).derived
    (complexCounitNat (p a).ordinary (p a).derived (p a).counit)
    (HomologicalComplex.quasiIso (Modules R) (.up ℤ))
  have := Functor.IsLeftDerivedFunctor.isRightKanExtension (p a').derived
    (complexCounitNat (p a').ordinary (p a').derived (p a').counit)
    (HomologicalComplex.quasiIso (Modules R') (.up ℤ))
  have : (towerRelabelEquivalence α).functor.Additive := by
    change (restriction α.inv).Additive
    infer_instance
  have : (towerRelabelEquivalence β).functor.Additive := by
    change (restriction β.inv).Additive
    infer_instance
  obtain ⟨eD, heD⟩ :=
    CategoryTheory.leftDerivedSquare (towerRelabelEquivalence α) (towerRelabelEquivalence β)
      (p a).ordinary (p a').ordinary (p a).derived (p a').derived
      (complexCounitNat (p a).ordinary (p a).derived (p a).counit)
      (complexCounitNat (p a').ordinary (p a').derived (p a').counit)
      (towerOrdinarySquare p ν a a' α β h)
  refine ⟨eD, fun P ↦ ?_⟩
  simpa only [towerRelabelEquivalence, CategoryTheory.Equivalence.changeFunctor,
    CategoryTheory.Equivalence.mapDerivedCategory, CategoryTheory.Equivalence.mk,
    complexCounitNat_app] using heD P

include h in
private theorem towerTransport
    (D : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S), AdjData.{uC, vC, r, w} (p a)) :
    ∃ e : (p a).ordinary ⋙ restriction β.inv ≅ restriction α.inv ⋙ (p a').ordinary,
      (∀ (M : Modules R) (U : C₀ᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U),
        (e.hom.app M).val.app U (sectionTensor (p a) M U s x) =
          sectionTensor (p a') ((restriction α.inv).obj M) U (β.hom.hom.app U s) x) ∧
      (∀ (M : Modules R) (U : C₀ᵒᵖ) (t : S'.obj.obj U) (x : M.val.obj U),
        (e.inv.app M).val.app U
            (sectionTensor (p a') ((restriction α.inv).obj M) U t x) =
          sectionTensor (p a) M U (β.inv.hom.app U t) x) ∧
    ∃ eD : (p a).derived ⋙ (restriction β.inv).mapDerivedCategory ≅
        (restriction α.inv).mapDerivedCategory ⋙ (p a').derived,
      ∀ P : CochainComplex (Modules R) ℤ,
        eD.hom.app (DerivedCategory.Q.obj P) ≫
            (p a').derived.map ((restriction α.inv).mapDerivedCategoryFactors.hom.app P) ≫
            reductionComplexCounit (p a').ordinary (p a').derived (p a').counit
              (((restriction α.inv).mapHomologicalComplex (.up ℤ)).obj P) =
          (restriction β.inv).mapDerivedCategory.map
            (reductionComplexCounit (p a).ordinary (p a).derived (p a).counit P) ≫
          (restriction β.inv).mapDerivedCategoryFactors.hom.app
            (((p a).ordinary.mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map
            ((NatIso.mapHomologicalComplex e
              (.up ℤ)).hom.app P) := by
  obtain ⟨ν, _⟩ := normalizationForPresentation p D
  refine ⟨towerOrdinarySquare p ν a a' α β h,
    towerOrdinarySquare_hom p ν a a' α β h,
    towerOrdinarySquare_inv p ν a a' α β h, ?_⟩
  exact towerDerivedSquare p a a' α β h ν

end GenericTransport

section PublishedTransport
attribute [local instance] reductionModulesHasDerivedCategory
attribute [local instance] restriction_limits restriction_colimits

private theorem publishedTensor_reduction (T : Scheme.{u})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (a : R ⟶ S)
    (M : reductionModules T R) (U : T.ProEtᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U) :
    sectionTensor (publishedPresentation T a) M U s x =
      reductionTensorSection T a M U s x := by
  exact publishedTensor T a M U s x

end PublishedTransport

attribute [local irreducible] reductionTensorSection pbcTensorSection
attribute [local irreducible] sectionTensor SheafOfModules.SuccessiveDerivedQuotient.pure

attribute [local irreducible] proEtaleModuleInverseImage
attribute [local irreducible] Functor.sheafPullbackConstruction.sheafPullback
attribute [local irreducible] constantSheaf

set_option linter.unusedSectionVars true

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The canonical geometric pullback is transported inverse image, with the explicit
balanced tensor formula and insertion-of-one inverse. The ring map defining the
pushforward action is exactly the adjoint constant-section map.
Source: sites-modules.tex, lemma-adjoint-push-pull-modules; Stacks 0H7J
(blueprint: lem-sp-proetale-coefficient-tower-normalization).

Proof: apply the constant-sheaf comparison to the specified adjoint map (proof Step 1).
Transport the action by c inverse. Balancing sends r tensor m to c inverse(r) m,
with inverse m to 1 tensor m; their composites are identities (Step 3).
The direct-image coefficient map is the adjoint of c, hence rho by adjunction.
Exactness of inverse image and ring relabelling gives the same identifications on
complexes and their unbounded derived categories. This also applies to the empty Z. -/
theorem coefficientTowerGeometricTransport
    (ℓ : ℕ) [Fact ℓ.Prime] (A : Type u) [CommRing A] [Finite A]
    (_hA : ∃ n : ℕ, ∀ a : A, (ℓ ^ n) • a = 0)
    {Z Y : Scheme.{u}} (q : Z ⟶ Y) :
    ∃ e : proEtaleConstantRingPullback A q ≅
        proEtaleModuleInverseImage q (proEtaleConstantRing Y A) ⋙ coefficientTowerRelabel q A,
      (∀ (M : proEtaleRingModules Y (proEtaleConstantRing Y A)) (U : Z.ProEtᵒᵖ)
        (r : (proEtaleConstantRing Z A).obj.obj U)
        (m : ((proEtaleModuleInverseImage q (proEtaleConstantRing Y A)).obj M).val.obj U),
        (e.hom.app M).val.app U
          (pure (proEtaleCoefficientInverseImageMap q A)
            ((proEtaleModuleInverseImage q (proEtaleConstantRing Y A)).obj M) U r m) =
          ((proEtaleConstantRingComparison q A).inv.hom.app U).hom r • m) ∧
      (∀ (M : proEtaleRingModules Y (proEtaleConstantRing Y A)) (U : Z.ProEtᵒᵖ)
        (m : ((proEtaleModuleInverseImage q (proEtaleConstantRing Y A)).obj M).val.obj U),
        (e.inv.app M).val.app U m =
          pure (proEtaleCoefficientInverseImageMap q A)
            ((proEtaleModuleInverseImage q (proEtaleConstantRing Y A)).obj M) U 1 m) ∧
      proEtaleRingDirectImageMap q (proEtaleConstantRing Y A) (proEtaleConstantRing Z A)
        (proEtaleConstantRingComparison q A) = proEtaleCoefficientDirectImageMap q A := by
  obtain ⟨e, hh, hi⟩ := towerGeometricTransport
    (proEtaleConstantRingComparison q A)
    (proEtaleModuleInverseImage q (proEtaleConstantRing Y A))
    (proEtaleConstantRingPullback A q) (fun _ ↦ rfl) (by
      intro M N f
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
      rfl)
  refine ⟨e, ?_, ?_, ?_⟩
  · intro M U r m
    exact hh M U r m
  · intro M U m
    exact hi M U m
  · unfold proEtaleRingDirectImageMap
    rw [← Adjunction.homEquiv_apply]
    simp only [proEtaleConstantRingComparison, asIso_hom]
    exact Equiv.apply_symm_apply _ _


/-- Scalar extension relabels along the actual constant-ring comparisons, with both
balanced tensor formulas. These compare functors on every module, hence commute
with restrictions, module maps and differentials of arbitrary complexes.
Source: Stacks 03EK and 06YY, ring-isomorphism specialization
(blueprint: lem-sp-proetale-coefficient-tower-normalization).

Proof: put a=c_A and b=c_B. Send s tensor m to b(s) tensor m and use b inverse
for the inverse. The coefficient square in proEtaleCoefficientTowerNormalization
sends the source balancing relation r m tensor s = m tensor phi(r)s to the target
relation a(r)m tensor b(s) = m tensor phi_Z(a(r))b(s). Multiplicativity gives
linearity and the two inverse equations. These equations commute with restrictions
and differentials (proof Step 4); relabelling preserves flatness and K-flatness tests
since inverse relabelling supplies every test module and complex. Thus the same
maps compute the canonical derived transport by 06YY, with the target action retained. -/
theorem coefficientTowerScalarTransport
    (ℓ : ℕ) [Fact ℓ.Prime]
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (_hA : ∃ n : ℕ, ∀ a : A, (ℓ ^ n) • a = 0)
    (_hB : ∃ n : ℕ, ∀ b : B, (ℓ ^ n) • b = 0)
    (φ : A →+* B) {Z Y : Scheme.{u}} (q : Z ⟶ Y) :
    ∃ e : reductionChange Z
          ((proEtaleSheafInverseImage q CommRingCat.{u + 1}).map
            (proEtaleConstantRingMap (T := Y) φ)) ⋙ coefficientTowerRelabel q B ≅
        coefficientTowerRelabel q A ⋙ reductionChange Z (proEtaleConstantRingMap (T := Z) φ),
      (∀ (M : proEtaleRingModules Z
          ((proEtaleSheafInverseImage q CommRingCat.{u + 1}).obj
            (proEtaleConstantRing Y A))) (U : Z.ProEtᵒᵖ)
        (s : ((proEtaleSheafInverseImage q CommRingCat.{u + 1}).obj
          (proEtaleConstantRing Y B)).obj.obj U) (m : M.val.obj U),
        (e.hom.app M).val.app U
          (reductionTensorSection Z
            ((proEtaleSheafInverseImage q CommRingCat.{u + 1}).map
              (proEtaleConstantRingMap (T := Y) φ)) M U s m) =
          reductionTensorSection Z (proEtaleConstantRingMap (T := Z) φ)
            ((coefficientTowerRelabel q A).obj M) U
            ((proEtaleCoefficientInverseImageMap q B).hom.app U s) m) ∧
      (∀ (M : proEtaleRingModules Z
          ((proEtaleSheafInverseImage q CommRingCat.{u + 1}).obj
            (proEtaleConstantRing Y A))) (U : Z.ProEtᵒᵖ)
        (t : (proEtaleConstantRing Z B).obj.obj U) (m : M.val.obj U),
        (e.inv.app M).val.app U
          (reductionTensorSection Z (proEtaleConstantRingMap (T := Z) φ)
            ((coefficientTowerRelabel q A).obj M) U t m) =
          reductionTensorSection Z
            ((proEtaleSheafInverseImage q CommRingCat.{u + 1}).map
              (proEtaleConstantRingMap (T := Y) φ)) M U
            ((proEtaleConstantRingComparison q B).inv.hom.app U t) m) ∧
      ∃ eD : reductionDerivedChange Z
            ((proEtaleSheafInverseImage q CommRingCat.{u + 1}).map
              (proEtaleConstantRingMap (T := Y) φ)) ⋙ coefficientTowerDerivedRelabel q B ≅
          coefficientTowerDerivedRelabel q A ⋙
            reductionDerivedChange Z (proEtaleConstantRingMap (T := Z) φ),
        ∀ P : CochainComplex (proEtaleRingModules Z
            ((proEtaleSheafInverseImage q CommRingCat.{u + 1}).obj
              (proEtaleConstantRing Y A))) ℤ,
          eD.hom.app (DerivedCategory.Q.obj P) ≫
              (reductionDerivedChange Z (proEtaleConstantRingMap (T := Z) φ)).map
                ((coefficientTowerRelabelFactors q A).hom.app P) ≫
              reductionScalarComplexCounit Z (proEtaleConstantRingMap (T := Z) φ)
                (((coefficientTowerRelabel q A).mapHomologicalComplex (.up ℤ)).obj P) =
            (coefficientTowerDerivedRelabel q B).map
              (reductionScalarComplexCounit Z
                ((proEtaleSheafInverseImage q CommRingCat.{u + 1}).map
                  (proEtaleConstantRingMap (T := Y) φ)) P) ≫
            (coefficientTowerRelabelFactors q B).hom.app
              ((reductionChangeComplex Z
                ((proEtaleSheafInverseImage q CommRingCat.{u + 1}).map
                  (proEtaleConstantRingMap (T := Y) φ))).obj P) ≫
            DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app P) := by
  let a := (proEtaleSheafInverseImage q CommRingCat.{u + 1}).map
    (proEtaleConstantRingMap (T := Y) φ)
  let a' := proEtaleConstantRingMap (T := Z) φ
  let α := proEtaleConstantRingComparison q A
  let β := proEtaleConstantRingComparison q B
  obtain ⟨e, hh, hi, hd⟩ := towerTransport
    (hD := fun R ↦ reductionModulesHasDerivedCategory Z R)
    (publishedPresentation Z) a a' α β (towerSquare φ q) (publishedData Z)
  refine ⟨e, ?_, ?_, ?_⟩
  · intro M U t x
    have hx := hh M U t x
    rw [publishedTensor_reduction, publishedTensor_reduction] at hx
    exact hx
  · intro M U t x
    have hx := hi M U t x
    rw [publishedTensor_reduction, publishedTensor_reduction] at hx
    exact hx
  · simpa only [towerDerivedRelabel_eq, towerRelabelFactors_eq, coefficientTowerRelabel,
      restriction, reductionChangeComplex, publishedPresentation, a, a', α, β] using hd

/-- The three actual constant-section maps are invertible and intertwine the two
coefficient maps. On each of the two sites, the balanced normalization of successive
derived quotient is the prescribed scalar associator, as a C-linear derived morphism.
Its normalization data include both pure-tensor formulas, K-flat computations,
unit compatibility, naturality in inputs and coefficient towers, and coherence.
Source: Stacks 0D6D, 0H7J, 06YY, 06YS, 0G7E and 07A6
(blueprint: lem-sp-proetale-coefficient-tower-normalization).

Proof:
1. Apply prop-weil-pbc-proetale-constant-ring-map to A, B and C. The comparison is
precisely the adjunct c of the constant-section rho, including for empty Z.
2. Both rho_B phi_Y and u_*(phi_Z) rho_A extend the same map on constant generators.
The constant-sheaf and sheafification universal properties identify them. Naturality
of the inverse-image adjunction gives the first square; repeat for psi and compose.
3. The geometric actions are transported by c inverse as stated in
coefficientTowerGeometricTransport, using def-weil-pbc-proetale-operations.
4. For scalar transport send s tensor m to c_B(s) tensor m and use its inverse.
The coefficient square makes the balancing relation agree. Relabelling preserves
all flatness and K-flat tests, so 06YY gives the same derived transport.
5. Resolve any unbounded input by a flat-term K-flat complex (lem-pc-kflat-resolution).
Its extension to B is again flat-term K-flat by lem-weil-pbc-ringed-topos-kflat-pullback.
Apply lem-sfb-successive-derived-quotient-normalization to the constant-ring tower:
the forward map sends c tensor (b tensor x) to psi(b)c tensor x; its inverse inserts 1.
6. Normalize the scalar/restriction adjunctions by their tensor units, using
lem-pur-sheaf-ring-derived-coefficient-adjunction. The unit_comp clause for tau and
lem-sp-scalar-associator-conjugate for alpha give the identical composite-unit
equation. Uniqueness in lem-weil-pbc-conjugate-iso-unit-equation identifies tau
with this particular alpha, on every object of the full unbounded derived category.
7. Balancing checks both inverse identities and C-linearity. A chain map acts only
on x, while a commuting coefficient tower sends psi(b)c to psi'(f_B(b))f_C(c).
Thus the comparisons are natural in both inputs and coefficient maps. Descent via
the canonical K-flat counits retains these equations, without flatness or finite
projective dimension of coefficient maps and without a boundedness assumption. -/
theorem proEtaleCoefficientTowerNormalization
    (ℓ : ℕ) [Fact ℓ.Prime]
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Finite A] [Finite B] [Finite C]
    (_hA : ∃ n : ℕ, ∀ a : A, (ℓ ^ n) • a = 0)
    (_hB : ∃ n : ℕ, ∀ b : B, (ℓ ^ n) • b = 0)
    (_hC : ∃ n : ℕ, ∀ c : C, (ℓ ^ n) • c = 0)
    (φ : A →+* B) (ψ : B →+* C) {Z Y : Scheme.{u}} (q : Z ⟶ Y) :
    IsIso (proEtaleCoefficientInverseImageMap q A) ∧
    IsIso (proEtaleCoefficientInverseImageMap q B) ∧
    IsIso (proEtaleCoefficientInverseImageMap q C) ∧
    (proEtaleSheafInverseImage q CommRingCat.{u + 1}).map
        (proEtaleConstantRingMap (T := Y) φ) ≫ proEtaleCoefficientInverseImageMap q B =
      proEtaleCoefficientInverseImageMap q A ≫ proEtaleConstantRingMap (T := Z) φ ∧
    (proEtaleSheafInverseImage q CommRingCat.{u + 1}).map
        (proEtaleConstantRingMap (T := Y) ψ) ≫ proEtaleCoefficientInverseImageMap q C =
      proEtaleCoefficientInverseImageMap q B ≫ proEtaleConstantRingMap (T := Z) ψ ∧
    (∀ T : Scheme.{u}, T = Y ∨ T = Z →
      ∃ ν : CoefficientTowerNormalizationData T,
        ∀ N : proEtaleDerivedCategory T A,
          (coefficientTowerBalancedComparison T ν (proEtaleConstantRingMap (T := T) φ)
              (proEtaleConstantRingMap (T := T) ψ)).hom.app N ≫
            eqToHom (congrArg (fun a : proEtaleConstantRing T A ⟶ proEtaleConstantRing T C ↦
                (reductionDerivedChange T a).obj N)
              (scalarExtensionFunctor_ringMap_comp φ ψ T)) =
          (scalarExtensionFunctor_composition φ ψ T).hom.app N) := by
  refine ⟨inferInstance, inferInstance, inferInstance, towerSquare φ q, towerSquare ψ q, ?_⟩
  intro T _
  obtain ⟨ν, hν⟩ := normalizationForPresentation
    (hD := fun R ↦ reductionModulesHasDerivedCategory T R)
    (publishedPresentation T) (publishedData T)
  refine ⟨ν, fun N ↦ ?_⟩
  have he := (normalizedScalarComp_eq T φ ψ).trans
    (publishedComp_eq T
      (proEtaleConstantRingMap (T := T) φ) (proEtaleConstantRingMap (T := T) ψ)
      (proEtaleConstantRingMap (T := T) (ψ.comp φ))
      (scalarExtensionFunctor_ringMap_comp φ ψ T))
  exact normalizationComp_transport (publishedPresentation T) (publishedData T) ν
    (fun a b ↦ (hν a b).1)
    (proEtaleConstantRingMap (T := T) φ) (proEtaleConstantRingMap (T := T) ψ)
    (proEtaleConstantRingMap (T := T) (ψ.comp φ))
    (scalarExtensionFunctor_ringMap_comp φ ψ T) (scalarExtensionFunctor_composition φ ψ T)
    he N

end AlgebraicGeometry.ProEtale
