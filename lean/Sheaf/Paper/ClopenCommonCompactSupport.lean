/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q61
-/
module

public import Sheaf.Paper.FiniteClopenDerivedDecomposition
public import Sheaf.Paper.ConstructibleExceptionalInverseImage
public import Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport
public import Sheaf.AlgebraicGeometry.ProEtaleOpenSquareExchange
public import WeilConjectures.Compactification.RefinementCategory
public import Sheaf.AlgebraicGeometry.SfOpenExceptionalBaseChange
public import Sheaf.AlgebraicGeometry.FiniteComparisonClassAdjunction
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import WeilConjectures.Compactification.NagataCompactification
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroAdjunction
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroExact
import Sheaf.Paper.ProEtaleConstructibleOrigin
import Sheaf.Paper.CompactificationCoherence
import Sheaf.AlgebraicGeometry.ProEtaleConstantOpenSquareExchange
import all Sheaf.Paper.FiniteClopenConstructibilityBounds
import Sheaf.Paper.ProEtaleConstantModuleConstructibility
import Sheaf.Paper.FiniteRingConstructibleDerivedOrigin
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Localization.Predicate
import Sheaf.Paper.ClopenProductAdjoints
import all Sheaf.AlgebraicGeometry.ProEtaleFiniteClopenTensorCalculus
import all Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated
import Sheaf.AlgebraicGeometry.IntrinsicDerivedOpenAdjunction

/-! # Common compactification and finite clopen compact-support summands

Source: main-20261015, sec-six-functors-basics/sk-def-purity-conv/
def-pur-section-invariant.md, finite-clopen compact-support supplement;
Stacks Tags 03DI, 03DJ and 04TS (blueprint: lem-pur-clopen-common-compact-support).

The insertion is represented by the existing exact extension by zero. Its diagonal
unit and vanishing off the diagonal identify it with zero insertion under the recorded
finite-clopen equivalence. Component compactifications are `c.precomp (j i).left`:
the ambient scheme and the proper map are literally those of c. No separatedness
of the target over the ground field is assumed.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology

attribute [local irreducible] AlgebraicGeometry.Scheme.sfIntrinsicDerivedEquivalence
  AlgebraicGeometry.Scheme.sfIntrinsicModuleEquivalence
  AlgebraicGeometry.Scheme.sfIntrinsicExtensionByZero
  AlgebraicGeometry.Scheme.sfIntrinsicPullback

-- Keep the published fixed-coefficient instances for the completed support objects.
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.ClopenMonoidalDescent.modulesAbelian
  AlgebraicGeometry.Scheme.ProEt.ClopenMonoidalDescent.hasDerived
  AlgebraicGeometry.Scheme.ProEt.ClopenMonoidalDescent.monoidal
  AlgebraicGeometry.Scheme.ProEt.ClopenMonoidalDescent.symmetric
  AlgebraicGeometry.Scheme.ProEt.ClopenScalar.derived
  AlgebraicGeometry.Scheme.ProEt.ClopenLocalization.modulesAbelian
  AlgebraicGeometry.Scheme.ProEt.ClopenLocalization.hasDerived
  AlgebraicGeometry.Scheme.ProEt.ClopenLocalization.sheafify
  AlgebraicGeometry.Scheme.ProEt.ClopenLocalization.locallyBijective

universe u w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting


/-- The specified comparison b is the descent of the ordinary unit-compatible open
extension comparison, followed by the single proper direct image. It is defined on
all unbounded complexes. Source: Stacks 03DI, 03DJ, 015F and blueprint compact-support
supplement, step 6 (blueprint: lem-pur-clopen-common-compact-support). -/
def clopenSupportComponentComparison (P : PurityFiniteSetting.{u})
    {X Y Z : Scheme.{u}} {g : X ⟶ Y} (c : Compactification g)
    (j : Z ⟶ X) [IsOpenImmersion j] :
    Scheme.sfIntrinsicDerivedOpen P.Ring j ⋙ Scheme.sfIntrinsicCompactSupport c P.Ring ≅
      Scheme.sfIntrinsicCompactSupport (c.precomp j) P.Ring :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Scheme.sfIntrinsicDerivedOpenComp P.Ring j c.i).symm
      (Scheme.proEtaleConstantDerivedDirectImage c.g P.Ring)

/-- The canonical comparison on a bounded-below etale representative, transported
through the published constant-ring realization. The middle map is the recorded
compactification comparison, not an arbitrarily chosen isomorphism.
Source: blueprint compact-support supplement, step 8; Stacks 09AK and 09AL
(blueprint: lem-pur-clopen-common-compact-support). -/
def clopenSupportEtaleComparison (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} {g : X ⟶ Y} [QuasiCompact g] (c d : Compactification g)
    (L : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))) :
    (Scheme.sfIntrinsicCompactSupport c P.Ring).obj
        ((Scheme.sfIntrinsicDerivedEquivalence X P.Ring).functor.obj
          (((AlgebraicGeometry.ProEtale.comparisonUpperStar
            (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory).obj L.obj)) ≅
      (Scheme.sfIntrinsicCompactSupport d P.Ring).obj
        ((Scheme.sfIntrinsicDerivedEquivalence X P.Ring).functor.obj
          (((AlgebraicGeometry.ProEtale.comparisonUpperStar
            (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory).obj L.obj)) :=
  (AlgebraicGeometry.ProEtale.sfIntrinsicCompactSupportComparison P.Ring c).app _ ≪≫
    (Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).functor.mapIso
      ((AlgebraicGeometry.ProEtale.fixedCompactSupportOriginIso P.Coefficient c d).app L) ≪≫
    ((AlgebraicGeometry.ProEtale.sfIntrinsicCompactSupportComparison P.Ring d).app _).symm

private theorem clopenLiftMapProjection
    {C : Type*} [Category C] [Preadditive C] {J : Type*}
    {f g : J → C} [HasBiproduct f] [HasBiproduct g]
    {Z : C} (p : ∀ i, Z ⟶ f i) (t : ∀ i, f i ⟶ g i) (i : J) :
    biproduct.lift p ≫ biproduct.map t ≫ biproduct.π g i = p i ≫ t i := by
  rw [biproduct.map_π, biproduct.lift_π_assoc]

private theorem clopenMapComposition
    {C : Type*} [Category C] [Preadditive C] {J : Type*}
    {f g h : J → C} [HasBiproduct f] [HasBiproduct g] [HasBiproduct h]
    (a : ∀ i, f i ⟶ g i) (b : ∀ i, g i ⟶ h i) (c : ∀ i, f i ⟶ h i)
    (hc : ∀ i, a i ≫ b i = c i) :
    biproduct.map c = biproduct.map a ≫ biproduct.map b := by
  apply biproduct.hom_ext
  intro i
  simp only [Category.assoc, biproduct.map_π, biproduct.map_π_assoc]
  rw [hc i]

private theorem clopenConstructibleIso (P : PurityFiniteSetting.{u})
    {T : Scheme.{u}} {K L : Scheme.proEtaleDerivedCategory T P.Ring}
    (e : K ≅ L)
    (h : Scheme.intrinsicFiniteTorsionConstructible P.coefficients.l P.extension
      P.level P.level_pos T K) :
    Scheme.intrinsicFiniteTorsionConstructible P.coefficients.l P.extension
      P.level P.level_pos T L := by
  constructor
  · apply h.1.subset
    intro q hq hz
    exact hq (hz.of_iso ((DerivedCategory.homologyFunctor _ q).mapIso e).symm)
  · intro q
    have hq := h.2 q
    rw [Scheme.proEtaleModuleRestriction_constructible_iff] at hq ⊢
    exact AlgebraicGeometry.ProEtale.isConstructible_of_iso
      ((Scheme.proEtaleModuleRestriction T P.Ring).mapIso
        ((DerivedCategory.homologyFunctor _ q).mapIso e)) hq

private theorem clopenExtendIso
    {A B C : Type*} [Category A] [Category B] [Category C]
    (F : A ⥤ B) [F.Full] (G H : B ⥤ C) (Q : ObjectProperty B)
    (hw : ∀ K : Q.FullSubcategory, ∃ M : A, Nonempty (F.obj M ≅ K.obj))
    (α : F ⋙ G ≅ F ⋙ H) :
    ∃! t : Q.ι ⋙ G ≅ Q.ι ⋙ H,
      ∀ (K : Q.FullSubcategory) (M : A) (e : F.obj M ≅ K.obj),
        t.app K = G.mapIso e.symm ≪≫ α.app M ≪≫ H.mapIso e := by
  classical
  choose M e using hw
  let e' (K : Q.FullSubcategory) : F.obj (M K) ≅ K.obj := (e K).some
  have hn {U V : A} (f : F.obj U ⟶ F.obj V) :
      G.map f ≫ α.hom.app V = α.hom.app U ≫ H.map f := by
    simpa only [Functor.comp_map, Functor.map_preimage] using
      α.hom.naturality (F.preimage f)
  let t : Q.ι ⋙ G ≅ Q.ι ⋙ H := NatIso.ofComponents
    (fun K ↦ G.mapIso (e' K).symm ≪≫ α.app (M K) ≪≫ H.mapIso (e' K)) (by
      intro K L f
      have h := congrArg
        (fun z ↦ G.map (e' K).inv ≫ z ≫ H.map (e' L).hom)
        (hn ((e' K).hom ≫ f.hom ≫ (e' L).inv))
      simpa only [Functor.map_comp, Category.assoc, Iso.map_inv_hom_id_assoc,
        Iso.map_inv_hom_id, Functor.map_id,
        Category.id_comp, Category.comp_id, Functor.comp_map, ObjectProperty.ι_map, Iso.app_hom,
        Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom] using h)
  have ht (K : Q.FullSubcategory) (N : A) (d : F.obj N ≅ K.obj) :
      t.app K = G.mapIso d.symm ≪≫ α.app N ≪≫ H.mapIso d := by
    apply Iso.ext
    have h := congrArg (fun z ↦ G.map d.inv ≫ z ≫ H.map (e' K).hom)
      (hn (d.hom ≫ (e' K).inv))
    simpa only [t, Iso.app_hom, NatIso.ofComponents_hom_app, Iso.trans_hom, Functor.mapIso_hom,
      Iso.symm_hom, Functor.map_comp, Category.assoc, Iso.map_inv_hom_id_assoc,
      Iso.map_inv_hom_id, Functor.map_id,
      Category.id_comp, Category.comp_id] using h
  refine ⟨t, ht, ?_⟩
  intro t' ht'
  apply Iso.ext
  apply NatTrans.ext
  funext K
  exact congrArg Iso.hom ((ht' K (M K) (e' K)).trans (ht K (M K) (e' K)).symm)

private theorem clopenOriginWitness (P : PurityFiniteSetting.{u})
    {T : Scheme.{u}} (K : Scheme.proEtaleDerivedCategory T P.Ring)
    (hK : Scheme.intrinsicFiniteTorsionConstructible P.coefficients.l P.extension
      P.level P.level_pos T K) :
    ∃ L : DerivedCategory.Plus
        (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)),
      Nonempty ((Scheme.sfIntrinsicDerivedEquivalence T P.Ring).functor.obj
        (((AlgebraicGeometry.ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} P.Coefficient) T).mapDerivedCategory).obj L.obj) ≅ K) := by
  classical
  have : (AlgebraicGeometry.ProEtale.finiteCoefficientIntrinsicRealization
      T P.Ring).Additive :=
    AlgebraicGeometry.ProEtale.finiteCoefficientIntrinsicRealization_additive T P.Ring
  have : PreservesFiniteLimits
      (AlgebraicGeometry.ProEtale.finiteCoefficientIntrinsicRealization T P.Ring) :=
    AlgebraicGeometry.ProEtale.finiteCoefficientIntrinsicRealization_preservesFiniteLimits
      T P.Ring
  have : PreservesFiniteColimits
      (AlgebraicGeometry.ProEtale.finiteCoefficientIntrinsicRealization T P.Ring) :=
    AlgebraicGeometry.ProEtale.finiteCoefficientIntrinsicRealization_preservesFiniteColimits
      T P.Ring
  obtain ⟨a, ha⟩ := hK.1.bddBelow
  obtain ⟨b, hb⟩ := hK.1.bddAbove
  have hv (q : ℤ) (hq : q < min a b ∨ max a b < q) :
      IsZero ((DerivedCategory.homologyFunctor _ q).obj K) := by
    by_contra hz
    rcases hq with hq | hq
    · exact (not_lt_of_ge ((min_le_left a b).trans (ha hz))) hq
    · exact (not_lt_of_ge ((hb hz).trans (le_max_right a b))) hq
  obtain ⟨L, ⟨e⟩⟩ := (Scheme.finiteRing_constructibleDerived_origin T P.Ring).2.2.1 K
    |>.mpr ⟨hK.2, min a b, max a b, min_le_max, hv⟩
  obtain ⟨c, d, hcd, hd⟩ := L.property.2
  have hplus : DerivedCategory.TStructure.t.plus L.obj :=
    ⟨c, (DerivedCategory.isGE_iff L.obj c).mpr (fun q hq ↦ hd q (Or.inl hq))⟩
  refine ⟨⟨L.obj, hplus⟩, ⟨?_⟩⟩
  unfold Scheme.sfIntrinsicDerivedEquivalence Scheme.sfIntrinsicModuleEquivalence
  exact ((Functor.mapDerivedCategoryCompIso
    (AlgebraicGeometry.ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) T)
    (AlgebraicGeometry.ProEtale.finiteCoefficientIntrinsicRealization T P.Ring)).app
      L.obj).symm ≪≫ e

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem derivedId_hom_Q {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] (K : CochainComplex C ℤ) :
    (Functor.mapDerivedCategoryIdIso C).hom.app (DerivedCategory.Q.obj K) =
      (𝟭 C).mapDerivedCategoryFactors.hom.app K := by
  have hf := congr_app (congrArg Iso.hom (Functor.mapDerivedCategoryIdIso_factorsh C))
    ((HomotopyCategory.quotient C (.up ℤ)).obj K)
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.rightUnitor_hom_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app,
    Functor.mapDerivedCategoryFactorsh_hom_app,
    Functor.mapHomotopyCategoryIdIso_hom_app] at hf
  have h₁ : ((𝟭 C).mapHomotopyCategoryFactors (.up ℤ)).inv.app K = 𝟙 _ := rfl
  have h₂ : (Functor.mapHomologicalComplexIdIso C (.up ℤ)).hom.app K = 𝟙 _ := rfl
  rw [h₁, h₂] at hf
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
    Category.comp_id, Category.comp_id] at hf
  have he : (DerivedCategory.quotientCompQhIso C).inv.app
      (((𝟭 C).mapHomologicalComplex (.up ℤ)).obj K) = 𝟙 _ := rfl
  rw [he] at hf
  erw [Category.id_comp, Category.comp_id, Category.comp_id] at hf
  exact hf

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem exactDerivedAdjunction_unit
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) (G : D ⥤ C) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (adj : F ⊣ G) :
    let : CatCommSq (F.mapHomologicalComplex (.up ℤ))
      DerivedCategory.Q DerivedCategory.Q F.mapDerivedCategory :=
        ⟨F.mapDerivedCategoryFactors.symm⟩
    let : CatCommSq (G.mapHomologicalComplex (.up ℤ))
      DerivedCategory.Q DerivedCategory.Q G.mapDerivedCategory :=
        ⟨G.mapDerivedCategoryFactors.symm⟩
    ((adj.mapHomologicalComplex (.up ℤ)).localization
      DerivedCategory.Q (HomologicalComplex.quasiIso _ (.up ℤ))
      DerivedCategory.Q (HomologicalComplex.quasiIso _ (.up ℤ))
      F.mapDerivedCategory G.mapDerivedCategory).unit =
    (Functor.mapDerivedCategoryIdIso C).inv ≫
      Localization.liftNatTrans DerivedCategory.Q (HomologicalComplex.quasiIso _ (.up ℤ))
        ((𝟭 C).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
        ((F ⋙ G).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
        (𝟭 C).mapDerivedCategory (F ⋙ G).mapDerivedCategory
        (Functor.whiskerRight (NatTrans.mapHomologicalComplex adj.unit (.up ℤ))
          DerivedCategory.Q) ≫ (Functor.mapDerivedCategoryCompIso F G).hom := by
  let : CatCommSq (F.mapHomologicalComplex (.up ℤ))
      DerivedCategory.Q DerivedCategory.Q F.mapDerivedCategory :=
    ⟨F.mapDerivedCategoryFactors.symm⟩
  let : CatCommSq (G.mapHomologicalComplex (.up ℤ))
      DerivedCategory.Q DerivedCategory.Q G.mapDerivedCategory :=
    ⟨G.mapDerivedCategoryFactors.symm⟩
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso _ (.up ℤ))
  intro K
  simp only [Adjunction.localization_unit_app, NatTrans.comp_app, Iso.symm_hom]
  apply (cancel_mono (G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
    G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K))).1
  have hc := Functor.mapDerivedCategoryCompIso_fac F G K
  have hid : DerivedCategory.Q.map
      ((Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).hom.app K) =
        𝟙 _ := by
    change DerivedCategory.Q.map (𝟙 _) = 𝟙 _
    exact CategoryTheory.Functor.map_id _ _
  rw [hid] at hc
  erw [Category.comp_id] at hc
  simp only [Category.assoc]
  erw [hc]
  simp only [Localization.liftNatTrans_app]
  change _ = (Functor.mapDerivedCategoryIdIso C).inv.app _ ≫
    ((𝟭 C).mapDerivedCategoryFactors.hom.app K ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex adj.unit (.up ℤ)).app K) ≫
      (F ⋙ G).mapDerivedCategoryFactors.inv.app K) ≫
      (F ⋙ G).mapDerivedCategoryFactors.hom.app K
  rw [← derivedId_hom_Q]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app]
  erw [← G.mapDerivedCategory.map_comp_assoc, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_app]
  rfl

private theorem derivedOpenAdjunction_unit (A : Type u) [CommRing A] [Finite A]
    {U Y : Scheme.{u}} (j : U ⟶ Y) [IsOpenImmersion j] :
    (Scheme.exceptionalOpenAdjunction j A).unit = Scheme.sfIntrinsicDerivedOpenUnit A j := by
  exact exactDerivedAdjunction_unit _ _ (Scheme.sfIntrinsicOpenAdjunction A j)


/-- The categorical part of finite clopen compact-support insertion.

Source: the finite clopen ringed-module gluing argument, Stacks Tags 03DI, 03DJ
and 04TS (blueprint: lem-pur-clopen-common-compact-support).

Proof plan: identify the ambient derived category with the finite product of the
component derived categories by exact restriction and finite derived localization.
For each coordinate, transport the standard coordinate insertion adjunctions
through that equivalence. The transported diagonal units are the specified open
units, the off-diagonal composites are zero, and the coordinate bicone is a
finite biproduct. Uniqueness of adjoints identifies the transported left
adjoints with the intrinsic open functors and transports the right adjoints and
their unit sum. This gives all four displayed categorical conclusions.
-/
private theorem clopenSupport_insertion_categorical
    (P : PurityFiniteSetting.{u})
    (X : Over (Spec (CommRingCat.of P.field.k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    {I : Type w} [Finite I]
    (Xi : I → Over (Spec (CommRingCat.of P.field.k)))
    (j : ∀ i, Xi i ⟶ X)
    [∀ i, IsOpenImmersion (j i).left] [∀ i, IsClosedImmersion (j i).left]
    (hd : ∀ i k, i ≠ k →
      Disjoint (Set.range (j i).left) (Set.range (j k).left))
    (hc : (⋃ i, Set.range (j i).left) = Set.univ) :
    ∃ (L : ∀ i, Scheme.sfIntrinsicDerivedOpen P.Ring (j i).left ⊣
        Scheme.sfIntrinsicDerivedPullback P.Ring (j i).left)
      (R : ∀ i, Scheme.sfIntrinsicDerivedPullback P.Ring (j i).left ⊣
        Scheme.sfIntrinsicDerivedOpen P.Ring (j i).left),
      (∀ i, (L i).unit = Scheme.sfIntrinsicDerivedOpenUnit P.Ring (j i).left) ∧
      (∀ i, IsIso (L i).unit) ∧
      (∀ i M, (L i).unit.app M ≫ (R i).counit.app M = 𝟙 M) ∧
      (∀ i k, i ≠ k → ∀ M : Scheme.proEtaleDerivedCategory
          (Xi i).left P.Ring,
        IsZero ((Scheme.sfIntrinsicDerivedPullback P.Ring (j k).left).obj
          ((Scheme.sfIntrinsicDerivedOpen P.Ring (j i).left).obj M))) ∧
      ∀ K, IsIso (biproduct.lift (fun i ↦ (R i).unit.app K)) := by
  classical
  let r := fun i ↦ Scheme.sfIntrinsicPullback P.Ring (j i).left
  let rd := fun i ↦ Scheme.sfIntrinsicDerivedPullback P.Ring (j i).left
  let D := fun i ↦ Scheme.proEtaleDerivedCategory (Xi i).left P.Ring
  obtain ⟨E₀, hE₀⟩ := ordinaryClopenEquivalence X.left (fun i ↦ (Xi i).left)
    (fun i ↦ (j i).left) hd hc P.Ring
  let E := E₀.changeFunctor (eqToIso hE₀ ≪≫
    (show Functor.pi' (fun i ↦ Scheme.proEtaleConstantRingPullback P.Ring (j i).left) ≅
      Functor.pi' r from NatIso.pi' (fun i ↦ Scheme.openSquarePullbackModel P.Ring (j i).left)))
  have hE : E.functor = Functor.pi' r := rfl
  have hr : JointlyReflectIsomorphisms r := by
    constructor
    intro M N f hf
    have : IsIso (E.functor.map f) := (isIso_pi_iff _).mpr hf
    exact isIso_of_reflects_iso f E.functor
  let := Scheme.ProEt.FiniteClopenTensor.piPreadditive
    (fun i ↦ Scheme.proEtaleRingModules (Xi i).left
      (Scheme.proEtaleConstantRing (Xi i).left P.Ring))
  have hA : E.functor.Additive := by
    constructor
    intro M N f g
    funext i
    exact (r i).map_add
  let := hA
  have hD := Scheme.ProEt.FiniteClopenTensor.derivedPi_isEquivalence r E.inverse
    (fun M N ↦ E.inverse.map_zero M N)
    (by simpa only [hE] using E.unitIso)
    (by simpa only [hE] using E.counitIso) hr
  let := hD
  let ED := (Functor.pi' rd).asEquivalence
  let := Scheme.ProEt.FiniteClopenTensor.piPreadditive D
  have hED : ED.functor.Additive := by
    constructor
    intro M N f g
    funext i
    exact (rd i).map_add
  let := hED
  let L := fun i ↦ Scheme.exceptionalOpenAdjunction (j i).left P.Ring
  obtain ⟨R, hu, hdiag, hoff, hsum⟩ := clopenProductAdjoints D ED
    (fun i ↦ Scheme.sfIntrinsicDerivedOpen P.Ring (j i).left) L
  have hnorm (i) : (L i).unit = Scheme.sfIntrinsicDerivedOpenUnit P.Ring (j i).left :=
    derivedOpenAdjunction_unit P.Ring (j i).left
  exact ⟨L, R, hnorm, hu, hdiag, hoff, hsum⟩



/-- The geometric part of finite clopen compact-support insertion.

Source: finite clopen constructibility bounds and exact open restriction,
Stacks Tags 005J and 09YD (blueprint: lem-pur-clopen-common-compact-support).

Proof plan: restriction of a triangulated exact complex functor preserves
cones, shifts, and distinguished triangles, hence each intrinsic open functor
is triangulated. Restricting a finite torsion constructibility stratification
to a clopen component and conversely taking the finite disjoint union of the
component stratifications gives the displayed implication. The fixed
coefficient, interval, and torsion bounds are preserved by the constant-ring
comparison and by exact derived open restriction.
-/
private theorem clopenSupport_insertion_open_properties
    (P : PurityFiniteSetting.{u})
    (X : Over (Spec (CommRingCat.of P.field.k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    {I : Type w} [Finite I]
    (Xi : I → Over (Spec (CommRingCat.of P.field.k)))
    (j : ∀ i, Xi i ⟶ X)
    [∀ i, IsOpenImmersion (j i).left] [∀ i, IsClosedImmersion (j i).left]
    (hd : ∀ i k, i ≠ k →
      Disjoint (Set.range (j i).left) (Set.range (j k).left))
    (hc : (⋃ i, Set.range (j i).left) = Set.univ) :
    (∀ i, (Scheme.sfIntrinsicDerivedOpen P.Ring (j i).left).IsTriangulated) ∧
    (∀ i (M : Scheme.proEtaleDerivedCategory (Xi i).left P.Ring),
      Scheme.intrinsicFiniteTorsionConstructible P.coefficients.l P.extension
        P.level P.level_pos (Xi i).left M →
      Scheme.intrinsicFiniteTorsionConstructible P.coefficients.l P.extension
        P.level P.level_pos X.left
          ((Scheme.sfIntrinsicDerivedOpen P.Ring (j i).left).obj M)) := by
  classical
  let : Finite (Padic.coefficientExtensionRing P.coefficients.l
      (↥P.extension) P.level) := P.ringFinite
  constructor
  · intro i
    infer_instance
  · intro i M hM
    obtain ⟨L, R, hunit, hiso, hdiag, hoff, hsum⟩ :=
      clopenSupport_insertion_categorical P X Xi j hd hc
    let : X.left.Over (Spec (CommRingCat.of P.field.k)) := ⟨X.hom⟩
    have : LocallyOfFiniteType (X.left ↘ Spec (CommRingCat.of P.field.k)) :=
      inferInstanceAs (LocallyOfFiniteType X.hom)
    have : QuasiCompact (X.left ↘ Spec (CommRingCat.of P.field.k)) :=
      inferInstanceAs (QuasiCompact X.hom)
    have H := finite_clopen_constructibility_bounds P X.left (fun k ↦ (Xi k).left)
      (fun k ↦ (j k).left) hd hc
    let K := (Scheme.sfIntrinsicDerivedOpen P.Ring (j i).left).obj M
    have hrest (k : I) :
        Scheme.intrinsicFiniteTorsionConstructible P.coefficients.l P.extension
          P.level P.level_pos (Xi k).left
          ((Scheme.proEtaleConstantRingDerivedPullback P.Ring (j k).left).obj K) := by
      let e := (Scheme.openSquareDerivedPullbackModel P.Ring (j k).left).app K
      by_cases hik : i = k
      · subst k
        have : IsIso ((L i).unit.app M) := by
          have := hiso i
          infer_instance
        let d := asIso ((L i).unit.app M) ≪≫ e.symm
        constructor
        · apply hM.1.subset
          intro q hq hz
          exact hq (hz.of_iso ((DerivedCategory.homologyFunctor _ q).mapIso d).symm)
        · intro q
          exact Scheme.constructibleProEtale_of_iso _ _
            ((DerivedCategory.homologyFunctor _ q).mapIso d) (hM.2 q)
      · have hz := (hoff i k hik M).of_iso e
        constructor
        · apply Set.finite_empty.subset
          intro q hq
          exact (hq ((DerivedCategory.homologyFunctor _ q).map_isZero hz)).elim
        · intro q
          exact Scheme.constructibleProEtale_of_isZero _ _ _
            ((DerivedCategory.homologyFunctor _ q).map_isZero hz)
    obtain ⟨a, ha⟩ := hM.1.bddBelow
    obtain ⟨b, hb⟩ := hM.1.bddAbove
    have hs : Scheme.proEtaleCohomologicalSupport K ⊆ Set.Icc (min a b) (max a b) := by
      apply (H.2.2.2.2.1 K _ _ min_le_max).mpr
      intro k q hq
      let e := (Scheme.openSquareDerivedPullbackModel P.Ring (j k).left).app K
      by_cases hik : i = k
      · subst k
        have : IsIso ((L i).unit.app M) := by
          have := hiso i
          infer_instance
        let d := asIso ((L i).unit.app M) ≪≫ e.symm
        have hqm : q ∈ Scheme.proEtaleCohomologicalSupport M := by
          intro hz
          exact hq (hz.of_iso ((DerivedCategory.homologyFunctor _ q).mapIso d).symm)
        exact ⟨(min_le_left a b).trans (ha hqm), (hb hqm).trans (le_max_right a b)⟩
      · exact (hq ((DerivedCategory.homologyFunctor _ q).map_isZero
          ((hoff i k hik M).of_iso e))).elim
    exact ⟨(Set.finite_Icc _ _).subset hs,
      (H.2.2.2.1 K).mpr (fun k q ↦ (hrest k).2 q)⟩


section CanonicalComparison
variable (P : PurityFiniteSetting.{u})
  {X Y : Scheme.{u}} {g : X ⟶ Y} [QuasiCompact g]

/-- Canonical compactification comparisons descend to the full bounded constructible
subcategory, uniquely normalized on every bounded-below etale representative and
every isomorphism from such a representative. This supplies the actual comparisons
used below, without asserting independence on arbitrary unbounded objects.
Source: blueprint compact-support supplement, step 8
(blueprint: lem-pur-clopen-common-compact-support).
Proof: constructible_proEtale_origin supplies an etale-origin witness for each
bounded constructible object. Compactification coherence supplies the canonical
comparison on these witnesses. Its naturality with respect to all ambient arrows
uses full faithfulness of etale comparison on bounded-below objects. Conjugate by
the chosen witness isomorphisms. Naturality makes the result independent of the
witness, and the full-subcategory inclusion gives the stated natural isomorphism.
Every object has a witness, so the displayed normalization also proves uniqueness. -/
theorem clopenSupportCanonicalComparison_existsUnique (c d : Compactification g) :
    ∃! t : (Scheme.intrinsicFiniteTorsionConstructible P.coefficients.l P.extension
          P.level P.level_pos X).ι ⋙ Scheme.sfIntrinsicCompactSupport c P.Ring ≅
        (Scheme.intrinsicFiniteTorsionConstructible P.coefficients.l P.extension
          P.level P.level_pos X).ι ⋙ Scheme.sfIntrinsicCompactSupport d P.Ring,
      ∀ (K : (Scheme.intrinsicFiniteTorsionConstructible P.coefficients.l P.extension
          P.level P.level_pos X).FullSubcategory)
        (L : DerivedCategory.Plus
          (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)))
        (e : (Scheme.sfIntrinsicDerivedEquivalence X P.Ring).functor.obj
          (((AlgebraicGeometry.ProEtale.comparisonUpperStar
            (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory).obj L.obj) ≅ K.obj),
        t.app K = (Scheme.sfIntrinsicCompactSupport c P.Ring).mapIso e.symm ≪≫
          P.clopenSupportEtaleComparison c d L ≪≫
            (Scheme.sfIntrinsicCompactSupport d P.Ring).mapIso e := by
  classical
  let ν := (AlgebraicGeometry.ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory
  let E := Scheme.sfIntrinsicDerivedEquivalence X P.Ring
  let F := DerivedCategory.Plus.ι ⋙ ν ⋙ E.functor
  have : F.Full := ⟨fun {L M} f ↦ by
    obtain ⟨k, hk⟩ :=
      (AlgebraicGeometry.ProEtale.bijective_comparisonUpperStar_mapDerivedCategory_map
        L.obj M.obj M.property).2 (E.functor.preimage f)
    exact ⟨ObjectProperty.homMk k, by
      change E.functor.map (ν.map k) = f
      exact (congrArg E.functor.map hk).trans (E.functor.map_preimage f)⟩⟩
  let α : F ⋙ Scheme.sfIntrinsicCompactSupport c P.Ring ≅
      F ⋙ Scheme.sfIntrinsicCompactSupport d P.Ring :=
    Functor.isoWhiskerLeft (DerivedCategory.Plus.ι ⋙ ν)
      (AlgebraicGeometry.ProEtale.sfIntrinsicCompactSupportComparison P.Ring c) ≪≫
    Functor.isoWhiskerRight
      (AlgebraicGeometry.ProEtale.fixedCompactSupportOriginIso P.Coefficient c d)
      (Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).functor ≪≫
    (Functor.isoWhiskerLeft (DerivedCategory.Plus.ι ⋙ ν)
      (AlgebraicGeometry.ProEtale.sfIntrinsicCompactSupportComparison P.Ring d)).symm
  exact clopenExtendIso F (Scheme.sfIntrinsicCompactSupport c P.Ring)
    (Scheme.sfIntrinsicCompactSupport d P.Ring) _
    (fun K ↦ clopenOriginWitness P K.obj K.property) α

/-- The uniquely etale-normalized compactification comparison on bounded
constructible inputs. Source: blueprint supplement, step 8
(blueprint: lem-pur-clopen-common-compact-support). -/
def clopenSupportCanonicalComparison (c d : Compactification g) :=
  (P.clopenSupportCanonicalComparison_existsUnique c d).exists.choose

private theorem clopenEtaleComparison_trans (c d e : Compactification g)
    (L : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))) :
    P.clopenSupportEtaleComparison c d L ≪≫ P.clopenSupportEtaleComparison d e L =
      P.clopenSupportEtaleComparison c e L := by
  have h := congrArg (fun t ↦ t.hom.app L)
    (show AlgebraicGeometry.ProEtale.fixedCompactSupportOriginIso P.Coefficient c d ≪≫
        AlgebraicGeometry.ProEtale.fixedCompactSupportOriginIso P.Coefficient d e =
        AlgebraicGeometry.ProEtale.fixedCompactSupportOriginIso P.Coefficient c e by
      ext M
      simp only [AlgebraicGeometry.ProEtale.fixedCompactSupportOriginIso,
        Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
        Functor.whiskerRight_app, Category.assoc, Iso.inv_hom_id_app_assoc,
        ← Functor.map_comp_assoc]
      rw [← AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationPlusιIso_trans
        P.Coefficient c d e]
      simp)
  apply Iso.ext
  simp only [clopenSupportEtaleComparison, Iso.trans_hom, Iso.app_hom, Iso.app_inv,
    Functor.mapIso_hom, Iso.symm_hom, ObjectProperty.ι_obj, Category.assoc,
    Iso.inv_hom_id_app_assoc,
    ← Functor.map_comp_assoc]
  simp only [Iso.trans_hom, NatTrans.comp_app] at h
  exact congrArg (fun f ↦
    (AlgebraicGeometry.ProEtale.sfIntrinsicCompactSupportComparison P.Ring c).hom.app _ ≫
      (Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).functor.map f ≫
      (AlgebraicGeometry.ProEtale.sfIntrinsicCompactSupportComparison P.Ring e).inv.app _) h

private theorem clopenEtaleComparison_refl (c : Compactification g)
    (L : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))) :
    P.clopenSupportEtaleComparison c c L = Iso.refl _ := by
  have h := clopenEtaleComparison_trans P c c c L
  apply Iso.ext
  have hh := congrArg Iso.hom h
  apply (cancel_mono (P.clopenSupportEtaleComparison c c L).hom).mp
  simpa only [Iso.trans_hom, Iso.refl_hom, Category.id_comp] using hh

/-- The compactification comparisons satisfy identities and composition; consequently
choosing any compactification represents the same bounded constructible functor.
Source: blueprint supplement, step 8
(blueprint: lem-pur-clopen-common-compact-support).
Proof: the identity and composite have the same normalization on all etale
representatives as the identity and composite canonical comparisons in
compactification_coherence. Apply uniqueness in
clopenSupportCanonicalComparison_existsUnique. -/
theorem clopenSupportCanonicalComparison_coherence (c d e : Compactification g) :
    P.clopenSupportCanonicalComparison c c = Iso.refl _ ∧
      P.clopenSupportCanonicalComparison c d ≪≫ P.clopenSupportCanonicalComparison d e =
        P.clopenSupportCanonicalComparison c e := by
  have hn (a b : Compactification g)
      (K : (Scheme.intrinsicFiniteTorsionConstructible P.coefficients.l P.extension
        P.level P.level_pos X).FullSubcategory)
      (L : DerivedCategory.Plus
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)))
      (k : (Scheme.sfIntrinsicDerivedEquivalence X P.Ring).functor.obj
        (((AlgebraicGeometry.ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory).obj L.obj) ≅ K.obj) :
      (P.clopenSupportCanonicalComparison a b).app K =
        (Scheme.sfIntrinsicCompactSupport a P.Ring).mapIso k.symm ≪≫
          P.clopenSupportEtaleComparison a b L ≪≫
          (Scheme.sfIntrinsicCompactSupport b P.Ring).mapIso k :=
    (P.clopenSupportCanonicalComparison_existsUnique a b).exists.choose_spec K L k
  constructor
  · apply (P.clopenSupportCanonicalComparison_existsUnique c c).unique (hn c c)
    intro K L e
    rw [clopenEtaleComparison_refl]
    apply Iso.ext
    simp only [Iso.refl_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.trans_hom,
      Category.id_comp, Iso.map_inv_hom_id]
    rfl
  · apply (P.clopenSupportCanonicalComparison_existsUnique c e).unique _ (hn c e)
    intro K L k
    change (P.clopenSupportCanonicalComparison c d).app K ≪≫
        (P.clopenSupportCanonicalComparison d e).app K = _
    rw [hn c d K L k, hn d e K L k]
    apply Iso.ext
    simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
      Category.assoc, Iso.map_hom_inv_id_assoc]
    have h := congrArg Iso.hom (clopenEtaleComparison_trans P c d e L)
    simp only [Iso.trans_hom] at h
    simpa only [Category.assoc] using congrArg
      (fun f ↦ (Scheme.sfIntrinsicCompactSupport c P.Ring).map k.inv ≫ f ≫
        (Scheme.sfIntrinsicCompactSupport e P.Ring).map k.hom) h

end CanonicalComparison

section Cover
variable (P : PurityFiniteSetting.{u})
  (X Y : Over (Spec (CommRingCat.of P.field.k)))
  [hftX : LocallyOfFiniteType X.hom] [hqcX : QuasiCompact X.hom]
  [hftY : LocallyOfFiniteType Y.hom] [hqcY : QuasiCompact Y.hom]
  (g : X ⟶ Y) [hgsep : IsSeparated g.left]
  [hgft : LocallyOfFiniteType g.left] [hgqc : QuasiCompact g.left]
  {I : Type w} [hfinite : Finite I]
  (Xi : I → Over (Spec (CommRingCat.of P.field.k))) (j : ∀ i, Xi i ⟶ X)
  [∀ i, IsOpenImmersion (j i).left] [hclosed : ∀ i, IsClosedImmersion (j i).left]
  (hdisjoint : ∀ i k, i ≠ k → Disjoint (Set.range (j i).left) (Set.range (j k).left))
  (hcover : (⋃ i, Set.range (j i).left) = Set.univ)

include hftX hqcX hfinite hclosed hdisjoint hcover

include hftY hqcY hgsep hgft hgqc in
/-- Existence and geometry of the common compactification, including every choice
with extra boundary components. Components use `c.precomp (j i).left`, whose proper
part is c.g by definition. The natural number bound is the stated nonnegative
integer bound, and is zero on an empty ambient scheme.
Source: blueprint finite-clopen supplement, steps 1--3; Stacks 01T6, 01OY, 01T5,
01T3 and 01QR (blueprint: lem-pur-clopen-common-compact-support).
Proof: the finite-type structure maps make X,Y Noetherian; Y is therefore qcqs.
NagataCompactification gives a compactification without requiring Y/k separated.
Each clopen component is Noetherian. Its inclusion is quasi-compact because its
intersection with an affine open is closed and compact, and an open immersion is
locally of finite type. Composition gives finite type for each component map and
its structure map. The diagonal of j is an isomorphism; the diagonal of j followed
by g is the base change of the closed diagonal of g, so both maps are separated.
For any c, its proper part is finite type, hence c.Z is finite type over k and
Noetherian. Apply exists_topologicalKrullDim_le; in the empty case use zero. -/
theorem clopenSupport_geometry :
    Nonempty (Compactification g.left) ∧ IsNoetherian X.left ∧ IsNoetherian Y.left ∧
    (∀ i, IsNoetherian (Xi i).left ∧ IsSeparated (j i).left ∧
      LocallyOfFiniteType (j i).left ∧ QuasiCompact (j i).left ∧
      IsSeparated ((j i).left ≫ g.left) ∧ LocallyOfFiniteType ((j i).left ≫ g.left) ∧
      QuasiCompact ((j i).left ≫ g.left)) ∧
    ∀ c : Compactification g.left, IsNoetherian c.Z ∧
      ∃ d : ℕ, topologicalKrullDim c.Z ≤ (d : WithBot ℕ∞) ∧ (IsEmpty c.Z → d = 0) := by
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : IsNoetherian X.left := ⟨⟩
  have : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  have : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  have : IsNoetherian Y.left := ⟨⟩
  refine ⟨⟨NagataCompactification g.left⟩, inferInstance, inferInstance, ?_, ?_⟩
  · intro i
    have : IsLocallyNoetherian (Xi i).left :=
      LocallyOfFiniteType.isLocallyNoetherian (j i).left
    have : CompactSpace (Xi i).left :=
      QuasiCompact.compactSpace_of_compactSpace (j i).left
    exact ⟨⟨⟩, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, inferInstance⟩
  · intro c
    have : IsLocallyNoetherian c.Z := LocallyOfFiniteType.isLocallyNoetherian c.g
    have : CompactSpace c.Z := QuasiCompact.compactSpace_of_compactSpace c.g
    refine ⟨⟨⟩, ?_⟩
    classical
    by_cases he : IsEmpty c.Z
    · let _ := he
      exact ⟨0, topologicalKrullDim_zero_of_discreteTopology c.Z,
        fun _ ↦ rfl⟩
    · obtain ⟨d, hd⟩ := exists_topologicalKrullDim_le (c.g ≫ Y.hom)
      exact ⟨d, hd, fun h ↦ (he h).elim⟩

/-- The existing exact extension by zero is zero insertion: restriction to its
own component has the specified invertible unit and restriction to every other
component is zero. Both derived adjunctions and the natural finite biproduct
splitting are retained, including all empty-index cases.
Source: Stacks 04TS, 03DI, 03DJ and blueprint finite-clopen supplement, steps 4--5
(blueprint: lem-pur-clopen-common-compact-support).
Proof: use finiteClopen_module_equivalence and finiteClopen_unbounded_decomposition.
In a product category maps to and from zero coordinates are unique, so insertion
is both adjoints to evaluation, with identity unit on its own coordinate. Kernels
and cokernels are componentwise. The ordinary left-adjoint uniqueness comparison
identifies insertion with sfIntrinsicExtensionByZero, preserving the restriction
unit. Exact termwise localization descends the comparison and its inverse.
The diagonal unit is sfIntrinsicDerivedOpenUnit and the other adjunction's counit
is its inverse. Off-diagonal restrictions vanish. The product inclusions and
projections give the displayed biproduct map; it is invertible because their
composites are the Kronecker identities and their finite sum is the identity.
Constructibility follows by inserting the component stratification and zeros;
bounded cohomology is componentwise. For an empty component its module category
is zero, and the same argument applies. -/
theorem clopenSupport_insertion :
    ∃ (L : ∀ i, Scheme.sfIntrinsicDerivedOpen P.Ring (j i).left ⊣
          Scheme.sfIntrinsicDerivedPullback P.Ring (j i).left)
      (R : ∀ i, Scheme.sfIntrinsicDerivedPullback P.Ring (j i).left ⊣
          Scheme.sfIntrinsicDerivedOpen P.Ring (j i).left),
      (∀ i, (L i).unit = Scheme.sfIntrinsicDerivedOpenUnit P.Ring (j i).left) ∧
      (∀ i, IsIso (L i).unit) ∧
      (∀ i (M : Scheme.proEtaleDerivedCategory (Xi i).left P.Ring),
        (L i).unit.app M ≫ (R i).counit.app M = 𝟙 M) ∧
      (∀ i k, i ≠ k → ∀ M : Scheme.proEtaleDerivedCategory (Xi i).left P.Ring,
        IsZero ((Scheme.sfIntrinsicDerivedPullback P.Ring (j k).left).obj
          ((Scheme.sfIntrinsicDerivedOpen P.Ring (j i).left).obj M))) ∧
      (∀ i, (Scheme.sfIntrinsicDerivedOpen P.Ring (j i).left).IsTriangulated) ∧
      (∀ i (M : Scheme.proEtaleDerivedCategory (Xi i).left P.Ring),
        Scheme.intrinsicFiniteTorsionConstructible P.coefficients.l P.extension
          P.level P.level_pos (Xi i).left M →
        Scheme.intrinsicFiniteTorsionConstructible P.coefficients.l P.extension
          P.level P.level_pos X.left
          ((Scheme.sfIntrinsicDerivedOpen P.Ring (j i).left).obj M)) ∧
      ∀ K : Scheme.proEtaleDerivedCategory X.left P.Ring,
        IsIso (biproduct.lift (fun i ↦ (R i).unit.app K)) := by
  obtain ⟨L, R, hunit, hiso, hdiag, hoff, hsum⟩ :=
    clopenSupport_insertion_categorical P X Xi j hdisjoint hcover
  obtain ⟨htri, hconstructible⟩ :=
    clopenSupport_insertion_open_properties P X Xi j hdisjoint hcover
  exact ⟨L, R, hunit, hiso, hdiag, hoff, htri, hconstructible, hsum⟩

/-- The specified finite-sum map: apply the common compact-support functor to
all decomposition projections, then the component comparison on each coordinate.
Source: blueprint finite-clopen supplement, steps 6--7
(blueprint: lem-pur-clopen-common-compact-support). -/
def clopenSupportSumMap (c : Compactification g.left)
    (R : ∀ i, Scheme.sfIntrinsicDerivedPullback P.Ring (j i).left ⊣
      Scheme.sfIntrinsicDerivedOpen P.Ring (j i).left)
    (K : Scheme.proEtaleDerivedCategory X.left P.Ring) :
    (Scheme.sfIntrinsicCompactSupport c P.Ring).obj K ⟶
      ⨁ (fun i ↦ (Scheme.sfIntrinsicCompactSupport (c.precomp (j i).left) P.Ring).obj
        ((Scheme.sfIntrinsicDerivedPullback P.Ring (j i).left).obj K)) :=
  biproduct.lift (fun i ↦
    (Scheme.sfIntrinsicCompactSupport c P.Ring).map ((R i).unit.app K) ≫
      (P.clopenSupportComponentComparison c (j i).left).hom.app
        ((Scheme.sfIntrinsicDerivedPullback P.Ring (j i).left).obj K))

/-- The finite-sum compact-support map is the image of the component decomposition,
followed by the specified b on each summand. The map is natural in K since its
components are the adjunction units and a natural isomorphism. No boundedness or
constructibility hypothesis is imposed on this unbounded candidate statement.
Source: blueprint finite-clopen supplement, steps 6--7; Stacks 03DI and 015F
(blueprint: lem-pur-clopen-common-compact-support).
Proof: a_! preserves finite sums by its ordinary left adjunction and exact descent.
Rp_* preserves finite products by the unbounded derived pullback adjunction,
therefore it preserves finite biproducts. Apply Rp_*a_! to the inclusion/projection
splitting in clopenSupport_insertion, then apply clopenSupportComponentComparison
on each summand. Its construction uses sfIntrinsicOpenComp, the unique ordinary
unit-compatible comparison, and sfIntrinsicDerivedOpenComp, its termwise descent.
For the empty index set every K is zero, and both functors preserve zero. -/
theorem clopenSupport_sum (c : Compactification g.left)
    (R : ∀ i, Scheme.sfIntrinsicDerivedPullback P.Ring (j i).left ⊣
      Scheme.sfIntrinsicDerivedOpen P.Ring (j i).left)
    (hR : ∀ K : Scheme.proEtaleDerivedCategory X.left P.Ring,
      IsIso (biproduct.lift (fun i ↦ (R i).unit.app K))) :
    (∀ K : Scheme.proEtaleDerivedCategory X.left P.Ring,
      IsIso (P.clopenSupportSumMap X Y g Xi j c R K)) ∧
    (IsEmpty I → ∀ K : Scheme.proEtaleDerivedCategory X.left P.Ring,
      IsZero K ∧ IsZero ((Scheme.sfIntrinsicCompactSupport c P.Ring).obj K)) := by
  classical
  let F := Scheme.sfIntrinsicCompactSupport c P.Ring
  have : F.Additive := inferInstanceAs
    (((Scheme.sfIntrinsicExtensionByZero c.i P.Ring).mapDerivedCategory) ⋙
      Scheme.proEtaleConstantDerivedDirectImage c.g P.Ring).Additive
  have hiso (K : Scheme.proEtaleDerivedCategory X.left P.Ring) :
      IsIso (P.clopenSupportSumMap X Y g Xi j c R K) := by
    have := hR K
    let e (i : I) := (P.clopenSupportComponentComparison c (j i).left).app
      ((Scheme.sfIntrinsicDerivedPullback P.Ring (j i).left).obj K)
    have heq : P.clopenSupportSumMap X Y g Xi j c R K =
        F.map (biproduct.lift (fun i ↦ (R i).unit.app K)) ≫
          (F.mapBiproduct _).hom ≫ (biproduct.mapIso e).hom := by
      rw [← Category.assoc, biproduct.map_lift_mapBiprod]
      simp only [biproduct.mapIso_hom, biproduct.lift_map]
      rfl
    rw [heq]
    infer_instance
  refine ⟨hiso, ?_⟩
  intro hempty K
  let _ := hempty
  have := hR K
  have hz : IsZero K := by
    apply (IsZero.iff_id_eq_zero K).mpr
    apply (cancel_mono (biproduct.lift (fun i ↦ (R i).unit.app K))).mp
    apply biproduct.hom_ext
    intro i
    exact isEmptyElim i
  exact ⟨hz, F.map_isZero hz⟩

/-- The actual derived finite-sum isomorphism, with forward map fixed to the
image of the decomposition projections followed by b on each component.
Source: blueprint finite-clopen supplement, steps 6--7
(blueprint: lem-pur-clopen-common-compact-support). -/
def clopenSupportSumIso (c : Compactification g.left)
    (R : ∀ i, Scheme.sfIntrinsicDerivedPullback P.Ring (j i).left ⊣
      Scheme.sfIntrinsicDerivedOpen P.Ring (j i).left)
    (hR : ∀ K : Scheme.proEtaleDerivedCategory X.left P.Ring,
      IsIso (biproduct.lift (fun i ↦ (R i).unit.app K)))
    (K : Scheme.proEtaleDerivedCategory X.left P.Ring) :
    (Scheme.sfIntrinsicCompactSupport c P.Ring).obj K ≅
      ⨁ (fun i ↦ (Scheme.sfIntrinsicCompactSupport (c.precomp (j i).left) P.Ring).obj
        ((Scheme.sfIntrinsicDerivedPullback P.Ring (j i).left).obj K)) :=
  letI := (P.clopenSupport_sum X Y g Xi j hdisjoint hcover c R hR).1 K
  asIso (P.clopenSupportSumMap X Y g Xi j c R K)

/-- Naturality of the specified derived finite-sum isomorphism.
Source: blueprint finite-clopen supplement, step 7
(blueprint: lem-pur-clopen-common-compact-support).
Proof: compose naturality of each right-adjunction unit with naturality of the
specified component comparison. The biproduct projection universal property
identifies the resulting maps. No choice of inverse enters this equation. -/
theorem clopenSupportSumMap_naturality (c : Compactification g.left)
    (R : ∀ i, Scheme.sfIntrinsicDerivedPullback P.Ring (j i).left ⊣
      Scheme.sfIntrinsicDerivedOpen P.Ring (j i).left)
    {K L : Scheme.proEtaleDerivedCategory X.left P.Ring} (f : K ⟶ L) :
    (Scheme.sfIntrinsicCompactSupport c P.Ring).map f ≫
        P.clopenSupportSumMap X Y g Xi j c R L =
      P.clopenSupportSumMap X Y g Xi j c R K ≫
        biproduct.map (fun i ↦
          (Scheme.sfIntrinsicCompactSupport (c.precomp (j i).left) P.Ring).map
            ((Scheme.sfIntrinsicDerivedPullback P.Ring (j i).left).map f)) := by
  apply biproduct.hom_ext
  intro i
  simp only [clopenSupportSumMap, Category.assoc, biproduct.lift_π,
    biproduct.map_π, biproduct.lift_π_assoc]
  rw [← Category.assoc, ← Functor.map_comp, ← (R i).unit_naturality]
  simp only [Functor.map_comp, Category.assoc]
  congr 1
  exact (P.clopenSupportComponentComparison c (j i).left).hom.naturality
    ((Scheme.sfIntrinsicDerivedPullback P.Ring (j i).left).map f)

/-- Restriction carries bounded constructible inputs to bounded constructible inputs.
Source: blueprint finite-clopen supplement, steps 4 and 8; Stacks 04TS
(blueprint: lem-pur-clopen-common-compact-support).
Proof: finiteClopen_finite_bounds computes cohomology and constructibility on
components. finiteClopen_finite_restriction_identification identifies its
restriction with the recorded intrinsic derived inverse image. -/
theorem clopenSupport_restriction_constructible (i : I)
    (K : Scheme.proEtaleDerivedCategory X.left P.Ring)
    (hK : Scheme.intrinsicFiniteTorsionConstructible P.coefficients.l P.extension
      P.level P.level_pos X.left K) :
    Scheme.intrinsicFiniteTorsionConstructible P.coefficients.l P.extension
      P.level P.level_pos (Xi i).left
      ((Scheme.sfIntrinsicDerivedPullback P.Ring (j i).left).obj K) := by
  let : X.left.Over (Spec (CommRingCat.of P.field.k)) := ⟨X.hom⟩
  have : LocallyOfFiniteType (X.left ↘ Spec (CommRingCat.of P.field.k)) := hftX
  have : QuasiCompact (X.left ↘ Spec (CommRingCat.of P.field.k)) := hqcX
  have H := finite_clopen_constructibility_bounds P X.left (fun k ↦ (Xi k).left)
    (fun k ↦ (j k).left) hdisjoint hcover
  have hb := H.2.2.2.2.1
  obtain ⟨a, ha⟩ := hK.1.bddBelow
  obtain ⟨b, hb'⟩ := hK.1.bddAbove
  have hs : Scheme.proEtaleCohomologicalSupport K ⊆ Set.Icc (min a b) (max a b) :=
    fun q hq ↦ ⟨(min_le_left a b).trans (ha hq),
      (hb' hq).trans (le_max_right a b)⟩
  apply clopenConstructibleIso P ((Scheme.openSquareDerivedPullbackModel
    P.Ring (j i).left).app K)
  exact ⟨(Set.finite_Icc _ _).subset ((hb K _ _ min_le_max).mp hs i),
    (H.2.2.2.1 K).mp hK.2 i⟩

/-- Lift the actual insertion to the full bounded constructible subcategories.
Source: blueprint finite-clopen supplement, steps 4 and 8
(blueprint: lem-pur-clopen-common-compact-support). -/
def clopenSupportConstructibleInsertion (i : I) :
    (Scheme.intrinsicFiniteTorsionConstructible P.coefficients.l P.extension
      P.level P.level_pos (Xi i).left).FullSubcategory ⥤
    (Scheme.intrinsicFiniteTorsionConstructible P.coefficients.l P.extension
      P.level P.level_pos X.left).FullSubcategory :=
  (Scheme.intrinsicFiniteTorsionConstructible P.coefficients.l P.extension
    P.level P.level_pos X.left).lift
      ((Scheme.intrinsicFiniteTorsionConstructible P.coefficients.l P.extension
        P.level P.level_pos (Xi i).left).ι ⋙ Scheme.sfIntrinsicDerivedOpen P.Ring (j i).left)
      (fun M ↦ (P.clopenSupport_insertion X Xi j hdisjoint hcover).choose_spec.choose_spec
        |>.2.2.2.2.2.1 i M.obj M.property)

/-- Compactification-independent b, represented using any chosen compactification
c0 for g and d0 for its component. It is precisely theta_g inverse, then b^c,
then theta_i, rather than an unspecified comparison. The chosen common c will
be shown immaterial. Source: blueprint finite-clopen supplement, step 8
(blueprint: lem-pur-clopen-common-compact-support). -/
def clopenSupportIndependentComponentComparison (c c0 : Compactification g.left) (i : I)
    (d0 : Compactification ((j i).left ≫ g.left)) :
    P.clopenSupportConstructibleInsertion X Xi j hdisjoint hcover i ⋙
        (Scheme.intrinsicFiniteTorsionConstructible P.coefficients.l P.extension
          P.level P.level_pos X.left).ι ⋙ Scheme.sfIntrinsicCompactSupport c0 P.Ring ≅
      (Scheme.intrinsicFiniteTorsionConstructible P.coefficients.l P.extension
        P.level P.level_pos (Xi i).left).ι ⋙ Scheme.sfIntrinsicCompactSupport d0 P.Ring :=
  Functor.isoWhiskerLeft
      (P.clopenSupportConstructibleInsertion X Xi j hdisjoint hcover i)
      (P.clopenSupportCanonicalComparison c c0).symm ≪≫
    Functor.isoWhiskerLeft
      (Scheme.intrinsicFiniteTorsionConstructible P.coefficients.l P.extension
        P.level P.level_pos (Xi i).left).ι
      (P.clopenSupportComponentComparison c (j i).left) ≪≫
    P.clopenSupportCanonicalComparison (c.precomp (j i).left) d0

/-- Agreement through canonical compactification comparisons on bounded
constructible inputs: the normalized conjugation is independent of the common
compactification used to compute it.
Source: blueprint finite-clopen supplement, step 8
(blueprint: lem-pur-clopen-common-compact-support).
Proof: all inserted inputs are bounded constructible by clopenSupport_insertion,
and hence have etale origins by constructible_proEtale_origin. On those origins,
open-extension composition is the unit-normalized ordinary comparison and
compactification comparisons are the canonical ones of compactification_coherence.
Their naturality and cocycle law identify the two conjugations. Full faithfulness
of comparison on bounded-below representatives descends that equation to the full
bounded constructible subcategory. The sum comparison is transported by the same
comparisons on each summand, so the finite-biproduct universal property identifies
it as the image of the original decomposition; empty sums are included. -/
theorem clopenSupport_independent (c d c0 : Compactification g.left) (i : I)
    (d0 : Compactification ((j i).left ≫ g.left)) :
    P.clopenSupportIndependentComponentComparison X Y g Xi j hdisjoint hcover c c0 i d0 =
      P.clopenSupportIndependentComponentComparison X Y g Xi j hdisjoint hcover d c0 i d0 := by
  sorry

/-- The sum comparison agrees through the canonical compactification comparisons.
Together with clopenSupport_independent this gives precisely theta_g inverse,
then the common-compactification sum, then the componentwise theta_i formula.
Source: blueprint finite-clopen supplement, step 8
(blueprint: lem-pur-clopen-common-compact-support).
Proof: clopenSupport_independent identifies each component comparison after
canonical compactification transport. Naturality of the canonical comparison
on X applies to each decomposition projection K -> E_i r_i K; these source and
target objects are constructible by the restriction and insertion assertions.
Project to each biproduct summand and compose these two equations. The universal
property of the finite biproduct proves the displayed equality, also when I is
empty. This identifies the sum computed by any common compactification. -/
theorem clopenSupportSumMap_compactification (c d : Compactification g.left)
    (R : ∀ i, Scheme.sfIntrinsicDerivedPullback P.Ring (j i).left ⊣
      Scheme.sfIntrinsicDerivedOpen P.Ring (j i).left)
    (K : (Scheme.intrinsicFiniteTorsionConstructible P.coefficients.l P.extension
      P.level P.level_pos X.left).FullSubcategory) :
    (P.clopenSupportCanonicalComparison c d).hom.app K ≫
        P.clopenSupportSumMap X Y g Xi j d R K.obj =
      P.clopenSupportSumMap X Y g Xi j c R K.obj ≫
        biproduct.map (fun i ↦
          (P.clopenSupportCanonicalComparison (c.precomp (j i).left)
            (d.precomp (j i).left)).hom.app
              ⟨(Scheme.sfIntrinsicDerivedPullback P.Ring (j i).left).obj K.obj,
                P.clopenSupport_restriction_constructible X Xi j hdisjoint hcover
                  i K.obj K.property⟩) := by
  apply biproduct.hom_ext
  intro i
  let M : (Scheme.intrinsicFiniteTorsionConstructible P.coefficients.l P.extension
      P.level P.level_pos (Xi i).left).FullSubcategory :=
    ⟨(Scheme.sfIntrinsicDerivedPullback P.Ring (j i).left).obj K.obj,
      P.clopenSupport_restriction_constructible X Xi j hdisjoint hcover
        i K.obj K.property⟩
  let N := (P.clopenSupportConstructibleInsertion X Xi j hdisjoint hcover i).obj M
  have h := congrArg (fun e ↦ e.hom.app M)
    (P.clopenSupport_independent X Y g Xi j hdisjoint hcover
      c d d i (d.precomp (j i).left))
  have hrefl := (P.clopenSupportCanonicalComparison_coherence d d d).1
  have hrefl' := (P.clopenSupportCanonicalComparison_coherence
    (d.precomp (j i).left) (d.precomp (j i).left) (d.precomp (j i).left)).1
  simp only [clopenSupportIndependentComponentComparison, Iso.trans_hom,
    Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, hrefl, hrefl', Iso.refl_hom, Iso.refl_inv, NatTrans.id_app,
    Category.comp_id] at h
  simp only [Functor.comp_obj, ObjectProperty.ι_obj, Category.id_comp] at h
  have hc : (P.clopenSupportCanonicalComparison c d).hom.app N ≫
      (P.clopenSupportComponentComparison d (j i).left).hom.app M.obj =
      (P.clopenSupportComponentComparison c (j i).left).hom.app M.obj ≫
        (P.clopenSupportCanonicalComparison (c.precomp (j i).left)
          (d.precomp (j i).left)).hom.app M := by
    rw [← h]
    exact (P.clopenSupportCanonicalComparison c d).hom_inv_id_app_assoc N _
  have hn := (P.clopenSupportCanonicalComparison c d).hom.naturality
    (ObjectProperty.homMk ((R i).unit.app K.obj) : K ⟶ N)
  simp only [Functor.comp_map, ObjectProperty.ι_map, ObjectProperty.homMk_hom] at hn
  simp only [clopenSupportSumMap, Category.assoc, biproduct.lift_π]
  rw [← Category.assoc, ← hn, Category.assoc, hc]
  simpa only [Category.assoc, M, Functor.comp_obj, ObjectProperty.ι_obj,
    Functor.id_obj] using (clopenLiftMapProjection
    (f := fun k ↦ (Scheme.sfIntrinsicCompactSupport (c.precomp (j k).left) P.Ring).obj
      ((Scheme.sfIntrinsicDerivedPullback P.Ring (j k).left).obj K.obj))
    (g := fun k ↦ (Scheme.sfIntrinsicCompactSupport (d.precomp (j k).left) P.Ring).obj
      ((Scheme.sfIntrinsicDerivedPullback P.Ring (j k).left).obj K.obj))
    (fun k ↦ (Scheme.sfIntrinsicCompactSupport c P.Ring).map ((R k).unit.app K.obj) ≫
      (P.clopenSupportComponentComparison c (j k).left).hom.app
        ((Scheme.sfIntrinsicDerivedPullback P.Ring (j k).left).obj K.obj))
    (fun k ↦ (P.clopenSupportCanonicalComparison (c.precomp (j k).left)
      (d.precomp (j k).left)).hom.app
        ⟨(Scheme.sfIntrinsicDerivedPullback P.Ring (j k).left).obj K.obj,
          P.clopenSupport_restriction_constructible X Xi j hdisjoint hcover
            k K.obj K.property⟩) i).symm

/-- The independent sum isomorphism is exactly theta_g inverse, the specified
common-compactification sum, and the biproduct of the component theta_i.
Here c0 and d0 represent the already compactification-independent functors.
Source: blueprint finite-clopen supplement, step 8
(blueprint: lem-pur-clopen-common-compact-support). -/
def clopenSupportIndependentSumComparison (c c0 : Compactification g.left)
    (d0 : ∀ i, Compactification ((j i).left ≫ g.left))
    (R : ∀ i, Scheme.sfIntrinsicDerivedPullback P.Ring (j i).left ⊣
      Scheme.sfIntrinsicDerivedOpen P.Ring (j i).left)
    (hR : ∀ K : Scheme.proEtaleDerivedCategory X.left P.Ring,
      IsIso (biproduct.lift (fun i ↦ (R i).unit.app K)))
    (K : (Scheme.intrinsicFiniteTorsionConstructible P.coefficients.l P.extension
      P.level P.level_pos X.left).FullSubcategory) :
    (Scheme.sfIntrinsicCompactSupport c0 P.Ring).obj K.obj ≅
      ⨁ (fun i ↦ (Scheme.sfIntrinsicCompactSupport (d0 i) P.Ring).obj
        ((Scheme.sfIntrinsicDerivedPullback P.Ring (j i).left).obj K.obj)) :=
  ((P.clopenSupportCanonicalComparison c c0).app K).symm ≪≫
    P.clopenSupportSumIso X Y g Xi j hdisjoint hcover c R hR K.obj ≪≫
      biproduct.mapIso (fun i ↦
        (P.clopenSupportCanonicalComparison (c.precomp (j i).left) (d0 i)).app
          ⟨(Scheme.sfIntrinsicDerivedPullback P.Ring (j i).left).obj K.obj,
            P.clopenSupport_restriction_constructible X Xi j hdisjoint hcover
              i K.obj K.property⟩)

/-- The independent finite-sum comparison does not depend on its auxiliary common
compactification. Its naturality is inherited from the specified sum map and the
canonical natural compactification comparisons.
Source: blueprint finite-clopen supplement, step 8
(blueprint: lem-pur-clopen-common-compact-support).
Proof: clopenSupportSumMap_compactification gives the commutative square for c,d.
Compose with the inverse comparison to c0 on the source and the componentwise
comparisons to d0 on the target. clopenSupportCanonicalComparison_coherence
cancels the intermediate comparisons. Equality of isomorphisms follows from
equality of their forward maps. The biproduct universal property includes the
empty family without a separate nonemptiness assumption. -/
theorem clopenSupportIndependentSumComparison_eq (c d c0 : Compactification g.left)
    (d0 : ∀ i, Compactification ((j i).left ≫ g.left))
    (R : ∀ i, Scheme.sfIntrinsicDerivedPullback P.Ring (j i).left ⊣
      Scheme.sfIntrinsicDerivedOpen P.Ring (j i).left)
    (hR : ∀ K : Scheme.proEtaleDerivedCategory X.left P.Ring,
      IsIso (biproduct.lift (fun i ↦ (R i).unit.app K)))
    (K : (Scheme.intrinsicFiniteTorsionConstructible P.coefficients.l P.extension
      P.level P.level_pos X.left).FullSubcategory) :
    P.clopenSupportIndependentSumComparison X Y g Xi j hdisjoint hcover c c0 d0 R hR K =
      P.clopenSupportIndependentSumComparison X Y g Xi j hdisjoint hcover d c0 d0 R hR K := by
  let M (i : I) : (Scheme.intrinsicFiniteTorsionConstructible P.coefficients.l P.extension
      P.level P.level_pos (Xi i).left).FullSubcategory :=
    ⟨(Scheme.sfIntrinsicDerivedPullback P.Ring (j i).left).obj K.obj,
      P.clopenSupport_restriction_constructible X Xi j hdisjoint hcover
        i K.obj K.property⟩
  have hθ := congrArg (fun e ↦ e.hom.app K)
    (P.clopenSupportCanonicalComparison_coherence c d c0).2
  simp only [Iso.trans_hom, NatTrans.comp_app] at hθ
  have hβ (i : I) := congrArg (fun e ↦ e.hom.app (M i))
    (P.clopenSupportCanonicalComparison_coherence
      (c.precomp (j i).left) (d.precomp (j i).left) (d0 i)).2
  simp only [Iso.trans_hom, NatTrans.comp_app] at hβ
  have hs := P.clopenSupportSumMap_compactification X Y g Xi j hdisjoint hcover c d R K
  apply Iso.ext
  dsimp only [clopenSupportIndependentSumComparison]
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_inv, biproduct.mapIso_hom,
    clopenSupportSumIso, asIso_hom, Iso.app_hom]
  apply (cancel_epi ((P.clopenSupportCanonicalComparison c c0).hom.app K)).mp
  simp only [Iso.hom_inv_id_app_assoc]
  rw [← hθ]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [← Category.assoc, hs]
  simp only [Category.assoc]
  congr 1
  exact clopenMapComposition
    (fun i ↦ (P.clopenSupportCanonicalComparison (c.precomp (j i).left)
      (d.precomp (j i).left)).hom.app (M i))
    (fun i ↦ (P.clopenSupportCanonicalComparison (d.precomp (j i).left)
      (d0 i)).hom.app (M i))
    (fun i ↦ (P.clopenSupportCanonicalComparison (c.precomp (j i).left)
      (d0 i)).hom.app (M i)) hβ


end Cover
end WeilConjectures.PurityFiniteSetting
