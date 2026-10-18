/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q11
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.RingedDerivedRestrictionGeneral
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.Algebra.Homology.LocalizedRestrictionAdjunction
import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import Sheaf.CategoryTheory.ConstantLeftModuleInverseImage
import Sheaf.CategoryTheory.RingedSiteModules

/-!
# Compatible slice section models from one injective complex

Source: Stacks Project, `sites-cohomology.tex`, Tag 03F3 and restriction-mapping equation;
`derived.tex`, Tags 05TI, 05TH, 05SA.
(blueprint: lem-pe-injective-complex-slice-section-model)
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u w i

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}

/-- The actual presheaf of left coefficient modules obtained by restricting scalars
along a map from a constant presheaf of rings. Objects, arrows and maps of sheaves are
unchanged as abelian groups. Source: Stacks, 03F3, sectionwise evaluation.
(blueprint: lem-pe-injective-complex-slice-section-model) -/
def coefficientSectionPresheaf (Λ : Type u) [Ring Λ] (R : Sheaf J RingCat.{u})
    (c : (Functor.const Cᵒᵖ).obj (RingCat.of Λ) ⟶ R.obj) :
    SheafOfModules.{u} R ⥤ Cᵒᵖ ⥤ ModuleCat.{u} Λ where
  obj M :=
    { obj := fun W ↦ ((PresheafOfModules.restrictScalars c).obj M.val).obj W
      map := fun {W V} a ↦ ModuleCat.ofHom
        (X := ((PresheafOfModules.restrictScalars c).obj M.val).obj W)
        (Y := ((PresheafOfModules.restrictScalars c).obj M.val).obj V)
        { toFun := ((PresheafOfModules.restrictScalars c).obj M.val).map a
          map_add' := map_add _
          map_smul' := fun r x ↦
            ((PresheafOfModules.restrictScalars c).obj M.val).map_smul a r x }
      map_id := fun W ↦ by
        ext x
        exact congrArg (fun f ↦ f x)
          (((PresheafOfModules.restrictScalars c).obj M.val).presheaf.map_id W)
      map_comp := fun a b ↦ by
        ext x
        exact congrArg (fun f ↦ f x)
          (((PresheafOfModules.restrictScalars c).obj M.val).presheaf.map_comp a b) }
  map f :=
    { app := fun W ↦ (ModuleCat.restrictScalars (c.app W).hom).map (f.val.app W)
      naturality := fun _ _ a ↦ by
        ext x
        exact PresheafOfModules.naturality_apply f.val a x }

/-- Sectionwise additivity of the actual scalar-restriction construction.
Source: Stacks, 03F3 (blueprint: lem-pe-injective-complex-slice-section-model). -/
instance coefficientSectionPresheaf_additive (Λ : Type u) [Ring Λ]
    (R : Sheaf J RingCat.{u})
    (c : (Functor.const Cᵒᵖ).obj (RingCat.of Λ) ⟶ R.obj) :
    (coefficientSectionPresheaf Λ R c).Additive where
  map_add := rfl

/-- Evaluation with the specified constant scalar action.
Source: Stacks, 03F3 (blueprint: lem-pe-injective-complex-slice-section-model). -/
def coefficientSectionEvaluation (Λ : Type u) [Ring Λ] (R : Sheaf J RingCat.{u})
    (c : (Functor.const Cᵒᵖ).obj (RingCat.of Λ) ⟶ R.obj) (W : Cᵒᵖ) :
    SheafOfModules.{u} R ⥤ ModuleCat.{u} Λ :=
  coefficientSectionPresheaf Λ R c ⋙ (evaluation Cᵒᵖ (ModuleCat Λ)).obj W

/-- Its additive structure is inherited from scalar restriction and evaluation.
Source: Stacks, 03F3 (blueprint: lem-pe-injective-complex-slice-section-model). -/
instance coefficientSectionEvaluation_additive (Λ : Type u) [Ring Λ]
    (R : Sheaf J RingCat.{u})
    (c : (Functor.const Cᵒᵖ).obj (RingCat.of Λ) ⟶ R.obj) (W : Cᵒᵖ) :
    (coefficientSectionEvaluation Λ R c W).Additive :=
  inferInstanceAs ((coefficientSectionPresheaf Λ R c ⋙
    (evaluation Cᵒᵖ (ModuleCat Λ)).obj W).Additive)

/-- The canonical coefficient map is the unit of ring sheafification.
Source: Stacks, constant sheaves and 03F3
(blueprint: lem-pe-injective-complex-slice-section-model). -/
abbrev constantCoefficientMap (J : GrothendieckTopology C) (Λ : Type u) [Ring Λ]
    [HasWeakSheafify J RingCat.{u}] :=
  toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))

variable (J : GrothendieckTopology C) (Λ : Type u) [Ring Λ]
  [HasWeakSheafify J RingCat.{u}]

/-- The existing module-sheaf category for the constant ring sheaf; a transparent alias.
Source: Stacks, 03F3 (blueprint: lem-pe-injective-complex-slice-section-model). -/
abbrev constantModuleSheaves :=
  SheafOfModules.{u} ((constantSheaf J RingCat.{u}).obj (RingCat.of Λ))

/-- Evaluation of constant-ring module sheaves, as a diagram of additive functors.
Source: Stacks, 03F3 (blueprint: lem-pe-injective-complex-slice-section-model). -/
def constantModuleEvaluation (W : Cᵒᵖ) : (constantModuleSheaves J Λ) ⥤ (ModuleCat.{u} Λ) :=
  coefficientSectionEvaluation Λ ((constantSheaf J RingCat.{u}).obj (RingCat.of Λ))
    (constantCoefficientMap J Λ) W

/-- The inherited additive structure of evaluation.
Source: Stacks, 03F3 (blueprint: lem-pe-injective-complex-slice-section-model). -/
instance constantModuleEvaluation_additive (W : Cᵒᵖ) :
    (constantModuleEvaluation J Λ W).Additive :=
  coefficientSectionEvaluation_additive _ _ _ _

/-- Degreewise sheaf restriction, as a transformation of evaluation functors.
Source: Stacks, the restriction-mapping equation after 03F3
(blueprint: lem-pe-injective-complex-slice-section-model). -/
def constantModuleRestriction {W V : Cᵒᵖ} (a : W ⟶ V) :
    constantModuleEvaluation J Λ W ⟶ constantModuleEvaluation J Λ V where
  app M := ((coefficientSectionPresheaf Λ ((constantSheaf J RingCat.{u}).obj (RingCat.of Λ))
    (constantCoefficientMap J Λ)).obj M).map a
  naturality _ _ f :=
    (((coefficientSectionPresheaf Λ ((constantSheaf J RingCat.{u}).obj (RingCat.of Λ))
      (constantCoefficientMap J Λ)).map f).naturality a).symm

variable [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Enough injectives follows from the recorded Grothendieck theorem.
Source: Stacks, 079H (blueprint: lem-pe-injective-complex-slice-section-model). -/
instance moduleSheavesEnoughInjectives : EnoughInjectives (constantModuleSheaves J Λ) :=
  letI := SheafOfModules.isGrothendieckAbelianOfUniverses.{u, u, u, u} J
    ((constantSheaf J RingCat.{u}).obj (RingCat.of Λ))
  inferInstance

/-- The literal evaluation complexes and their literal sheaf restriction maps.
Source: Stacks, restriction-mapping after 03F3
(blueprint: lem-pe-injective-complex-slice-section-model). -/
def constantModuleSectionDiagram (L : CochainComplex (constantModuleSheaves J Λ) ℤ) :
    Cᵒᵖ ⥤ CochainComplex (ModuleCat.{u} Λ) ℤ where
  obj W := ((constantModuleEvaluation J Λ W).mapHomologicalComplex (.up ℤ)).obj L
  map a := ((constantModuleRestriction J Λ a).mapHomologicalComplex (.up ℤ)).app L
  map_id W := by
    ext n x
    exact congrArg (fun f ↦ f x)
      (((coefficientSectionPresheaf Λ _ (constantCoefficientMap J Λ)).obj
        (L.X n)).map_id W)
  map_comp a b := by
    ext n x
    exact congrArg (fun f ↦ f x)
      (((coefficientSectionPresheaf Λ _ (constantCoefficientMap J Λ)).obj
        (L.X n)).map_comp a b)

variable [HasDerivedCategory.{w} (constantModuleSheaves J Λ)] [HasDerivedCategory.{w}
  (ModuleCat.{u} Λ)]

/-- The canonical bounded-below derived section functor, defined by deriving actual
Λ-linear evaluation. Its slice interpretation is part of the theorem below.
Source: Stacks, 03F3 and derived.tex 05TI
(blueprint: lem-pe-injective-complex-slice-section-model). -/
def constantModuleDerivedSections (W : Cᵒᵖ) :
    DerivedCategory.Plus (constantModuleSheaves J Λ) ⥤ DerivedCategory.Plus (ModuleCat.{u} Λ) :=
  (constantModuleEvaluation J Λ W).rightDerivedFunctorPlus

/-- Canonical derived section pullback is the transformation induced by ordinary
restriction through the localization universal property, with its unit normalization.
Source: Stacks, restriction-mapping after 03F3, and 05SA
(blueprint: lem-pe-injective-complex-slice-section-model). -/
def constantModuleDerivedRestriction {W V : Cᵒᵖ} (a : W ⟶ V) :
    constantModuleDerivedSections J Λ W ⟶ constantModuleDerivedSections J Λ V :=
  Functor.rightDerivedNatTrans
    (constantModuleEvaluation J Λ W).rightDerivedFunctorPlus
    (constantModuleEvaluation J Λ V).rightDerivedFunctorPlus
    (constantModuleEvaluation J Λ W).rightDerivedFunctorPlusUnit
    (constantModuleEvaluation J Λ V).rightDerivedFunctorPlusUnit
    (HomotopyCategory.Plus.quasiIso (constantModuleSheaves J Λ))
    (Functor.whiskerRight
      (NatTrans.mapHomotopyCategoryPlus (constantModuleRestriction J Λ a))
      DerivedCategory.Plus.Qh)

/-- The normalized comparison for a specified representative and derived identification.
Source: Stacks, 05TI and 05SA (blueprint: lem-pe-injective-complex-slice-section-model). -/
def constantModuleSectionComparison (L : CochainComplex.Plus (constantModuleSheaves J Λ))
    (K : DerivedCategory.Plus (constantModuleSheaves J Λ)) (e : DerivedCategory.Plus.Q.obj L ≅
      K) (W : Cᵒᵖ) :
    DerivedCategory.Plus.Q.obj
        ((constantModuleEvaluation J Λ W).mapCochainComplexPlus.obj L) ⟶
      (constantModuleDerivedSections J Λ W).obj K :=
  (constantModuleEvaluation J Λ W).rightDerivedFunctorPlusUnit.app
      ((HomotopyCategory.Plus.quotient (constantModuleSheaves J Λ)).obj L) ≫
    (constantModuleDerivedSections J Λ W).map e.hom

variable [∀ W : C, HasDerivedCategory.{w}
  (SheafOfModules.{u} (((constantSheaf J RingCat.{u}).obj (RingCat.of Λ)).over W))]

/-- Additivity of slice restriction.
Source: Stacks, 03F3 (blueprint: lem-pe-injective-complex-slice-section-model). -/
instance sliceRestrictionAdditive (W : C) :
    (SheafOfModules.overFunctor.{u}
      ((constantSheaf J RingCat.{u}).obj (RingCat.of Λ)) W).Additive :=
  (ringedOverFunctor_exactGeneral _ W).1

/-- Preservation of finite limits by slice restriction.
Source: Stacks, 03F3 (blueprint: lem-pe-injective-complex-slice-section-model). -/
instance sliceRestrictionFiniteLimits (W : C) :
    PreservesFiniteLimits (SheafOfModules.overFunctor.{u}
      ((constantSheaf J RingCat.{u}).obj (RingCat.of Λ)) W) :=
  (ringedOverFunctor_exactGeneral _ W).2.1

/-- Preservation of finite colimits by slice restriction.
Source: Stacks, 03F3 (blueprint: lem-pe-injective-complex-slice-section-model). -/
instance sliceRestrictionFiniteColimits (W : C) :
    PreservesFiniteColimits (SheafOfModules.overFunctor.{u}
      ((constantSheaf J RingCat.{u}).obj (RingCat.of Λ)) W) :=
  (ringedOverFunctor_exactGeneral _ W).2.2

/-- Exact restriction to the localized site, on bounded below derived categories.
This uses the recorded general-site restriction and its canonical factorization.
Source: Stacks, 03F3 (blueprint: lem-pe-injective-complex-slice-section-model). -/
def constantModuleSliceRestriction (W : C) :=
  (SheafOfModules.overFunctor.{u}
    ((constantSheaf J RingCat.{u}).obj (RingCat.of Λ)) W).mapDerivedCategoryPlus

/-- Actual evaluation at the terminal object of the localized site. The scalar map
is the restriction of the canonical unit from the constant presheaf, not an arbitrary
coefficient action. Source: Stacks, 03F3
(blueprint: lem-pe-injective-complex-slice-section-model). -/
def constantModuleSliceEvaluation (W : C) :
    SheafOfModules.{u}
      (((constantSheaf J RingCat.{u}).obj (RingCat.of Λ)).over W) ⥤ ModuleCat.{u} Λ :=
  coefficientSectionEvaluation Λ _
    (Functor.whiskerLeft (Over.forget W).op (constantCoefficientMap J Λ))
    (op (Over.mk (𝟙 W)))

/-- Additivity is inherited from actual evaluation and scalar restriction.
Source: Stacks, 03F3 (blueprint: lem-pe-injective-complex-slice-section-model). -/
instance constantModuleSliceEvaluation_additive (W : C) :
    (constantModuleSliceEvaluation J Λ W).Additive :=
  coefficientSectionEvaluation_additive _ _ _ _

/-- Enough injectives on every localized module site.
Source: Stacks, 03F3 (blueprint: lem-pe-injective-complex-slice-section-model). -/
instance sliceModuleEnoughInjectives (W : C) : EnoughInjectives
    (SheafOfModules.{u}
      (((constantSheaf J RingCat.{u}).obj (RingCat.of Λ)).over W)) :=
  letI := SheafOfModules.isGrothendieckAbelianOfUniverses.{u, u, u, u} (J.over W)
    (((constantSheaf J RingCat.{u}).obj (RingCat.of Λ)).over W)
  inferInstance

/-- Derived sections on the localized module site, defined by the right derived
functor of terminal evaluation. Source: Stacks, 03F3 and 05TI
(blueprint: lem-pe-injective-complex-slice-section-model). -/
def constantModuleSliceDerivedSections (W : C) :=
  (constantModuleSliceEvaluation J Λ W).rightDerivedFunctorPlus

/-- A single bounded-below injective complex computes the derived sections on every
slice, naturally with respect to both site arrows and changes of representatives.
All complexes, differentials and transition maps below are literal evaluations, and
all derived maps are normalized by the right-derived unit.

Source: Stacks, sites-cohomology.tex, Tag 03F3 and restriction-mapping equation;
derived.tex, Tags 05TI, 05TH and 05SA.
(blueprint: lem-pe-injective-complex-slice-section-model).

Proof:
1. Sectionwise restriction identifies repeated localization and evaluation at the
terminal slice object. The constant scalar map is the sheafification unit restricted
along the slice forgetful functor (def-pur-localized-ringed-site).
2. Restriction is exact (lem-pe-constant-left-module-inverse-image), and is right
adjoint to exact extension by zero (lem-pur-kinjective-restrict-localized-adjunction).
Thus it preserves injectives (lem-sp-right-adjoint-preserves-injectives).
3. Module-sheaf categories are Grothendieck (lem-weil-pbc-ring-sheaves-grothendieck)
and have enough injectives (lem-sp-grothendieck-enough-injectives); modules do too
(lem-weil-pbc-ring-modules-enough-injectives). Derive evaluation and compare the two
composite functors by the localization unit. Its injective computation gives the
invertibility assertion (lem-weil-pbc-right-derived-plus-injective).
4. The normalized derived restriction is the unique descent of ordinary restriction
followed by the derived unit; its defining equation gives the displayed square.
5. Naturality of the unit and of its unique descent gives naturality in chain maps
and the chosen identification e.
6. Functoriality of the actual sheaf restrictions gives a strict opposite diagram.
Evaluation preserves zero terms, so every object has the same lower bound. The
single complex of an injective sheaf computes its derived sections, and has zero
positive cohomology. This does not require injectivity after forgetting scalars. -/
theorem injectiveComplexSliceSectionModel
    [∀ W : C, HasWeakSheafify (J.over W) RingCat.{u}]
    (L : CochainComplex.Plus (constantModuleSheaves J Λ))
    (hInjective : ∀ n : ℤ, Injective (L.obj.X n))
    (K : DerivedCategory.Plus (constantModuleSheaves J Λ))
    (e : DerivedCategory.Plus.Q.obj L ≅ K) :
    (∀ W : C, ∃ c :
      (((constantSheaf J RingCat.{u}).obj (RingCat.of Λ)).over W) ≅
        (constantSheaf (J.over W) RingCat.{u}).obj (RingCat.of Λ),
      Functor.whiskerLeft (Over.forget W).op (constantCoefficientMap J Λ) ≫
          c.hom.hom = constantCoefficientMap (J.over W) Λ) ∧
    (∀ W : C,
      PreservesFiniteLimits (SheafOfModules.overFunctor.{u}
        ((constantSheaf J RingCat.{u}).obj (RingCat.of Λ)) W) ∧
      PreservesFiniteColimits (SheafOfModules.overFunctor.{u}
        ((constantSheaf J RingCat.{u}).obj (RingCat.of Λ)) W) ∧
      ∀ M : constantModuleSheaves J Λ, Injective M →
        Injective (M.over W)) ∧
    ∃ beta : ∀ W : C, constantModuleDerivedSections J Λ (op W) ≅
        constantModuleSliceRestriction J Λ W ⋙ constantModuleSliceDerivedSections J Λ W,
      (∀ (W : C) (M : CochainComplex.Plus (constantModuleSheaves J Λ)),
        (constantModuleEvaluation J Λ (op W)).rightDerivedFunctorPlusUnit.app
            ((HomotopyCategory.Plus.quotient _).obj M) ≫
          (beta W).hom.app (DerivedCategory.Plus.Q.obj M) =
        (constantModuleSliceEvaluation J Λ W).rightDerivedFunctorPlusUnit.app
            (((SheafOfModules.overFunctor _ W).mapHomotopyCategoryPlus).obj
              ((HomotopyCategory.Plus.quotient _).obj M)) ≫
          (constantModuleSliceDerivedSections J Λ W).map
            ((SheafOfModules.overFunctor _ W).mapDerivedCategoryPlusFactorsh.inv.app
              ((HomotopyCategory.Plus.quotient _).obj M))) ∧
      (∀ W : C, IsIso (constantModuleSectionComparison J Λ L K e (op W) ≫
        (beta W).hom.app K)) ∧
      (∀ {W' W : C} (a : W' ⟶ W),
        (constantModuleSectionComparison J Λ L K e (op W) ≫ (beta W).hom.app K) ≫
          ((beta W).inv.app K ≫ (constantModuleDerivedRestriction J Λ a.op).app K ≫
            (beta W').hom.app K) =
        DerivedCategory.Plus.Q.map
            (ObjectProperty.homMk
              (((constantModuleRestriction J Λ a.op).mapHomologicalComplex (.up ℤ)).app
                L.obj)) ≫
          (constantModuleSectionComparison J Λ L K e (op W') ≫ (beta W').hom.app K)) ∧
      (∀ (L' : CochainComplex.Plus (constantModuleSheaves J Λ))
        (K' : DerivedCategory.Plus (constantModuleSheaves J Λ))
        (e' : DerivedCategory.Plus.Q.obj L' ≅ K') (f : L ⟶ L') (k : K ⟶ K'),
        DerivedCategory.Plus.Q.map f ≫ e'.hom = e.hom ≫ k → ∀ W : C,
          (constantModuleSectionComparison J Λ L K e (op W) ≫ (beta W).hom.app K) ≫
            (constantModuleSliceRestriction J Λ W ⋙
              constantModuleSliceDerivedSections J Λ W).map k =
          DerivedCategory.Plus.Q.map
              ((constantModuleEvaluation J Λ (op W)).mapCochainComplexPlus.map f) ≫
            (constantModuleSectionComparison J Λ L' K' e' (op W) ≫
              (beta W).hom.app K')) ∧
      (∀ (I : Type i) [SmallCategory I] (D : I ⥤ C),
        ∃ N : ℤ, ∀ (j : Iᵒᵖ) (n : ℤ), n < N →
          IsZero (((D.op ⋙ constantModuleSectionDiagram J Λ L.obj).obj j).X n)) ∧
      (∀ (M : constantModuleSheaves J Λ), Injective M → ∀ (W : C) (n : ℤ), 0 < n →
        IsZero ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} Λ) n).obj
          ((constantModuleSliceDerivedSections J Λ W).obj
            ((constantModuleSliceRestriction J Λ W).obj
              ((DerivedCategory.Plus.singleFunctor _ 0).obj M))))) := by
  sorry

end CategoryTheory
