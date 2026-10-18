/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q41
-/
module

public import Sheaf.CategoryTheory.ConstantLeftModuleInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ChangeOfRings
public import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange
import WeilConjectures.CategoryTheory.RightDerivedPlusCube
import WeilConjectures.CategoryTheory.Abelian.RightDerived.LongExactSequence
import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import Sheaf.CategoryTheory.ModuleAbelianEvaluationComparison

/-! # Derived evaluation and forgetting constant left-module scalars

Source: Stacks Project, sites-cohomology.tex, Tag 03FD, and derived.tex, Tags 05TA and 015E
(blueprint: lem-pe-left-module-derived-evaluation-forget).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.LeftModuleDerivedEvaluation

open ConstantLeftModuleInverseImage

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  (Λ : Type u) [Ring Λ] [HasWeakSheafify J RingCat.{u}]

/-- Restrict the sectionwise action along the constant-ring sheafification unit.
Source: Stacks, 03FD (blueprint: lem-pe-left-module-derived-evaluation-forget). -/
abbrev constantPresheafModules : Modules J Λ ⥤
    PresheafOfModules.{u} ((Functor.const Cᵒᵖ).obj (RingCat.of Λ)) :=
  SheafOfModules.forget ((constantSheaf J RingCat.{u}).obj (RingCat.of Λ)) ⋙
    PresheafOfModules.restrictScalars
      (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ)))

/-- Evaluation with its constant left `Λ`-action, including for noncommutative `Λ`.
Source: Stacks, 03FD (blueprint: lem-pe-left-module-derived-evaluation-forget). -/
abbrev G (W : C) : Modules J Λ ⥤ ModuleCat.{u} Λ :=
  constantPresheafModules J Λ ⋙
    PresheafOfModules.evaluation ((Functor.const Cᵒᵖ).obj (RingCat.of Λ)) (op W)

/-- Evaluation on abelian sheaves.
Source: Stacks, 01FT/03FD (blueprint: lem-pe-left-module-derived-evaluation-forget). -/
abbrev G₀ (W : C) : Sheaf J AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} :=
  (sheafSections J AddCommGrpCat.{u}).obj (op W)

/-- The scalar-forgetting functor on left modules.
Source: Stacks, 03FD (blueprint: lem-pe-left-module-derived-evaluation-forget). -/
abbrev v : ModuleCat.{u} Λ ⥤ AddCommGrpCat.{u} :=
  forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}

/-- The literal identity between the two underlying abelian evaluation functors.
Source: Stacks, 03FD, first proof paragraph
(blueprint: lem-pe-left-module-derived-evaluation-forget). -/
def evaluationIdentity (W : C) : G J Λ W ⋙ v Λ ≅ V J Λ ⋙ G₀ J W :=
  Iso.refl _

/-- Restriction of evaluated left-module sections along an arrow in the site.
Source: Stacks, 03FD (blueprint: lem-pe-left-module-derived-evaluation-forget). -/
def restriction {W W' : C} (f : W' ⟶ W) : G J Λ W ⟶ G J Λ W' :=
  Functor.whiskerLeft (constantPresheafModules J Λ)
    (PresheafOfModules.restriction ((Functor.const Cᵒᵖ).obj (RingCat.of Λ)) f.op ≫
      Functor.whiskerLeft
        (PresheafOfModules.evaluation ((Functor.const Cᵒᵖ).obj (RingCat.of Λ)) (op W'))
        (ModuleCat.restrictScalarsId' (RingHom.id Λ) rfl).hom)

/-- Restriction of evaluated abelian sections along the same site arrow.
Source: Stacks, 03FD (blueprint: lem-pe-left-module-derived-evaluation-forget). -/
abbrev restriction₀ {W W' : C} (f : W' ⟶ W) : G₀ J W ⟶ G₀ J W' :=
  (sheafSections J AddCommGrpCat.{u}).map f.op

/-- Additivity inherited from Mathlib's presheaf scalar restriction and evaluation.
Source: Stacks, 03FD (blueprint: lem-pe-left-module-derived-evaluation-forget). -/
instance gAdditive (W : C) : (G J Λ W).Additive :=
  inferInstanceAs ((constantPresheafModules J Λ ⋙
    PresheafOfModules.evaluation ((Functor.const Cᵒᵖ).obj (RingCat.of Λ)) (op W)).Additive)

/-- Additivity inherited from the underlying presheaf evaluation.
Source: Stacks, 01FT (blueprint: lem-pe-left-module-derived-evaluation-forget). -/
instance g₀Additive (W : C) : (G₀ J W).Additive :=
  inferInstanceAs ((sheafToPresheaf J AddCommGrpCat.{u} ⋙
    (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op W)).Additive)

/-- Exactness of scalar forgetting, from the recorded colimit theorem.
Source: Stacks, 03DA/03DB (blueprint: lem-pe-left-module-derived-evaluation-forget). -/
instance vPreservesFiniteColimits : PreservesFiniteColimits (V J Λ) :=
  (moduleSheaves_colimits_forgetful
    ((constantSheaf J RingCat.{u}).obj (RingCat.of Λ))).2.2.1

variable [HasDerivedCategory.{w} (Modules J Λ)]
  [HasDerivedCategory.{w} (Sheaf J AddCommGrpCat.{u})]
  [HasDerivedCategory.{w} (ModuleCat.{u} Λ)] [HasDerivedCategory.{w} AddCommGrpCat.{u}]
  [EnoughInjectives (Modules J Λ)] [EnoughInjectives (Sheaf J AddCommGrpCat.{u})]

/-- The canonical derived square comparison, obtained from the underived identity.
Source: Stacks, 03FD/05TA (blueprint: lem-pe-left-module-derived-evaluation-forget). -/
def comparison (W : C) :
    (G J Λ W).rightDerivedFunctorPlus ⋙ (v Λ).mapDerivedCategoryPlus ⟶
      (V J Λ).mapDerivedCategoryPlus ⋙ (G₀ J W).rightDerivedFunctorPlus :=
  Functor.rightDerivedFunctorPlusBaseChange (evaluationIdentity J Λ W).hom

/-- Pull a section back as a map from the terminal constant sheaf. This is the
geometric adjunction's global-cohomology map before derivation.
Source: Stacks, 00YV/0736 (blueprint: lem-pe-left-module-derived-evaluation-forget). -/
def pullbackSection {D : Type u} [SmallCategory D] (K : GrothendieckTopology D)
    {L : Sheaf J (Type u) ⥤ Sheaf K (Type u)}
    (p : L.obj ((constantSheaf J (Type u)).obj PUnit.{u + 1}) ≅
      (constantSheaf K (Type u)).obj PUnit.{u + 1})
    {T : C} (hT : IsTerminal T) {S : D} (hS : IsTerminal S)
    (F : Sheaf J (Type u)) (x : F.obj.obj (op T)) : (L.obj F).obj.obj (op S) :=
  ((constantSheafAdj K (Type u) hS).homEquiv _ _
    (p.inv ≫ L.map ((constantSheafAdj J (Type u) hT).homEquiv _ _ |>.symm
      (TypeCat.ofHom (fun _ : PUnit.{u + 1} ↦ x))))) PUnit.unit

end CategoryTheory.LeftModuleDerivedEvaluation

namespace CategoryTheory.LeftModuleDerivedEvaluation

open ConstantLeftModuleInverseImage

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {Λ : Type u} [Ring Λ] [HasWeakSheafify J RingCat.{u}]
  [HasWeakSheafify K RingCat.{u}]
  {L : Sheaf J (Type u) ⥤ Sheaf K (Type u)}
  {R : Sheaf K (Type u) ⥤ Sheaf J (Type u)}
  {adj : L ⊣ R} {hL : PreservesFiniteLimits L}

/-- The abelian inverse image of a geometric morphism is additive and exact.
Source: Stacks, 00YV (2) (blueprint: lem-pe-left-module-derived-evaluation-forget).
Proof: `d.abelianAdj` makes the abelian inverse image a left adjoint, so it
preserves finite colimits. Forgetting abelian sheaves to set sheaves creates
finite limits and reflects isomorphisms. The isomorphism `d.abelianSetIso`
identifies this forgotten inverse image with set forgetting followed by `L`;
both preserve finite limits. Reflection of limits therefore gives preservation
of finite limits by the abelian inverse image itself. An exact functor between
abelian categories preserves the canonical binary biproduct addition on Hom,
and hence is additive. These are the canonical induced structures, not extra
hypotheses on the geometric morphism. -/
theorem abelianInverseExact
    (d : ConstantLeftModuleInverseImageLift J K Λ L R adj hL) :
    d.abelianInverse.Additive ∧ PreservesFiniteLimits d.abelianInverse ∧
      PreservesFiniteColimits d.abelianInverse := by
  sorry

/-- The module lift is additive, by the recorded inverse-image interface.
Source: Stacks, 00YV (6) (blueprint: lem-pe-left-module-derived-evaluation-forget). -/
instance moduleInverseAdditive (d : ConstantLeftModuleInverseImageLift J K Λ L R adj hL) :
    d.moduleFunctor.Additive := d.additive

/-- The module lift preserves finite limits.
Source: Stacks, 00YV (6) (blueprint: lem-pe-left-module-derived-evaluation-forget). -/
instance moduleInverseLimits (d : ConstantLeftModuleInverseImageLift J K Λ L R adj hL) :
    PreservesFiniteLimits d.moduleFunctor := d.preservesFiniteLimits

/-- The module lift preserves finite colimits.
Source: Stacks, 00YV (6) (blueprint: lem-pe-left-module-derived-evaluation-forget). -/
instance moduleInverseColimits (d : ConstantLeftModuleInverseImageLift J K Λ L R adj hL) :
    PreservesFiniteColimits d.moduleFunctor := d.preservesFiniteColimits

/-- Additivity of the abelian inverse image.
Source: Stacks, 00YV (2) (blueprint: lem-pe-left-module-derived-evaluation-forget). -/
instance abelianInverseAdditive (d : ConstantLeftModuleInverseImageLift J K Λ L R adj hL) :
    d.abelianInverse.Additive := (abelianInverseExact d).1

/-- Left exactness of the abelian inverse image.
Source: Stacks, 00YV (2) (blueprint: lem-pe-left-module-derived-evaluation-forget). -/
instance abelianInverseLimits (d : ConstantLeftModuleInverseImageLift J K Λ L R adj hL) :
    PreservesFiniteLimits d.abelianInverse := (abelianInverseExact d).2.1

/-- Right exactness of the abelian inverse image.
Source: Stacks, 00YV (2) (blueprint: lem-pe-left-module-derived-evaluation-forget). -/
instance abelianInverseColimits (d : ConstantLeftModuleInverseImageLift J K Λ L R adj hL) :
    PreservesFiniteColimits d.abelianInverse := (abelianInverseExact d).2.2

/-- The canonical global pullback maps, normalized on sections using the geometric
inverse image and its underlying-set comparisons. The normalization determines each
component on every element, so the maps are unique.
Source: Stacks, 00YV/0736 (blueprint: lem-pe-left-module-derived-evaluation-forget). -/
structure GlobalPullback
    (d : ConstantLeftModuleInverseImageLift J K Λ L R adj hL)
    {T : C} (hT : IsTerminal T) {S : D} (hS : IsTerminal S) where
  moduleMap : G J Λ T ⟶ d.moduleFunctor ⋙ G K Λ S
  abelianMap : G₀ J T ⟶ d.abelianInverse ⋙ G₀ K S
  module_normalization : ∀ (M : Modules J Λ) (x : (G J Λ T).obj M),
    moduleMap.app M x =
      (d.moduleSetIso.inv.app M).hom.app (op S)
        (pullbackSection J K d.pointIso hT hS ((W J Λ).obj M) x)
  abelian_normalization : ∀ (A : Sheaf J AddCommGrpCat.{u}) (x : (G₀ J T).obj A),
    abelianMap.app A x =
      (d.abelianSetIso.inv.app A).hom.app (op S)
        (pullbackSection J K d.pointIso hT hS ((U J).obj A) x)

variable [HasDerivedCategory.{w} (Modules J Λ)]
  [HasDerivedCategory.{w} (Modules K Λ)]
  [HasDerivedCategory.{w} (Sheaf J AddCommGrpCat.{u})]
  [HasDerivedCategory.{w} (Sheaf K AddCommGrpCat.{u})]
  [HasDerivedCategory.{w} (ModuleCat.{u} Λ)] [HasDerivedCategory.{w} AddCommGrpCat.{u}]
  [EnoughInjectives (Modules J Λ)] [EnoughInjectives (Modules K Λ)]
  [EnoughInjectives (Sheaf J AddCommGrpCat.{u})]
  [EnoughInjectives (Sheaf K AddCommGrpCat.{u})]

/-- The exact inverse-image scalar comparison on bounded-below derived categories.
Source: Stacks, 00YV/0736 (blueprint: lem-pe-left-module-derived-evaluation-forget). -/
def derivedUnderlying (d : ConstantLeftModuleInverseImageLift J K Λ L R adj hL) :
    d.moduleFunctor.mapDerivedCategoryPlus ⋙ (V K Λ).mapDerivedCategoryPlus ≅
      (V J Λ).mapDerivedCategoryPlus ⋙ d.abelianInverse.mapDerivedCategoryPlus :=
  (Functor.mapDerivedCategoryPlusCompIso d.moduleFunctor (V K Λ)).symm ≪≫
    Functor.mapDerivedCategoryPlusNatIso d.underlyingIso ≪≫
    Functor.mapDerivedCategoryPlusCompIso (V J Λ) d.abelianInverse

/-- Derive the normalized module global pullback, using the identity on coefficients.
Source: Stacks, 0736 (blueprint: lem-pe-left-module-derived-evaluation-forget). -/
def globalModulePullback
    {d : ConstantLeftModuleInverseImageLift J K Λ L R adj hL}
    {T : C} {hT : IsTerminal T} {S : D} {hS : IsTerminal S}
    (b : GlobalPullback d hT hS) :
    (G J Λ T).rightDerivedFunctorPlus ⟶
      d.moduleFunctor.mapDerivedCategoryPlus ⋙ (G K Λ S).rightDerivedFunctorPlus :=
  (Functor.rightUnitor _).inv ≫
    Functor.whiskerLeft _ (Functor.mapDerivedCategoryPlusIdIso (ModuleCat.{u} Λ)).inv ≫
    Functor.rightDerivedFunctorPlusBaseChange b.moduleMap

/-- Derive the normalized abelian global pullback, using the identity on coefficients.
Source: Stacks, 0736 (blueprint: lem-pe-left-module-derived-evaluation-forget). -/
def globalAbelianPullback
    {d : ConstantLeftModuleInverseImageLift J K Λ L R adj hL}
    {T : C} {hT : IsTerminal T} {S : D} {hS : IsTerminal S}
    (b : GlobalPullback d hT hS) :
    (G₀ J T).rightDerivedFunctorPlus ⟶
      d.abelianInverse.mapDerivedCategoryPlus ⋙ (G₀ K S).rightDerivedFunctorPlus :=
  (Functor.rightUnitor _).inv ≫
    Functor.whiskerLeft _ (Functor.mapDerivedCategoryPlusIdIso AddCommGrpCat.{u}).inv ≫
    Functor.rightDerivedFunctorPlusBaseChange b.abelianMap

end CategoryTheory.LeftModuleDerivedEvaluation

namespace CategoryTheory

open ConstantLeftModuleInverseImage LeftModuleDerivedEvaluation

/-- Forgetting constant left-module scalars commutes canonically with bounded-below
derived evaluation, its computation on injective complexes, object restriction,
geometric global pullback, and cohomology in every integer degree.

Source: Stacks Project, sites-cohomology.tex, Tag 03FD; derived.tex, 05TA (1) and 015E;
0736 for the adjunction-unit description of global pullback
(blueprint: lem-pe-left-module-derived-evaluation-forget).

Proof: (1) The forgetful functors `V` and `v` are exact by
lem-weil-pbc-module-sheaves-colimits-forgetful and the elementary module kernel/quotient
construction. Thus they descend termwise to derived categories and commute with cohomology.
The underived square is `evaluationIdentity`, the identity on sections and restrictions.
(2) The Tag-03FD module/abelian evaluation comparison
lem-weil-pbc-ringed-site-module-abelian-evaluation-comparison applied to an injective
module sheaf makes its forgotten sheaf evaluation-acyclic; no injectivity after forgetting
is used. (3) Choose a bounded-below injective representative using
lem-weil-pbc-dplus-injective-representative. Exact forgetting preserves its representing
quasi-isomorphism. Lemma-weil-pbc-leray-acyclicity, clause (3), applies to its acyclic
forgotten terms, so the abelian evaluation unit is invertible. The common evaluated
complex computes both sides. (4) The resulting morphism is precisely `comparison`,
namely the canonical derived square of the identity. Hence it is independent of the
representative and natural in the derived object. Apply lem-weil-pbc-right-derived-plus-cube
to the underived restriction square to obtain the displayed restriction equation.
(5) For geometric pullback, lem-pe-constant-left-module-inverse-image supplies the exact
module inverse image and the unit-compatible scalar comparison. Pulling maps from the
terminal constant sheaf back constructs the normalized global section maps. Their
underlying abelian square commutes by that unit compatibility. The same derived cube
lemma gives the global-pullback equation, including the exact inverse-image comparison.
(6) Apply homology in any integer degree; exactness of `v` supplies the displayed
homology comparison, which is invertible because `comparison` is invertible. -/
theorem leftModuleDerivedEvaluationForget
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (Λ : Type u) [Ring Λ] [HasWeakSheafify J RingCat.{u}]
    [HasDerivedCategory.{w} (Modules J Λ)]
    [HasDerivedCategory.{w} (Sheaf J AddCommGrpCat.{u})]
    [HasDerivedCategory.{w} (ModuleCat.{u} Λ)] [HasDerivedCategory.{w} AddCommGrpCat.{u}]
    [EnoughInjectives (Modules J Λ)] [EnoughInjectives (Sheaf J AddCommGrpCat.{u})] :
    (∀ W : C, IsIso (comparison J Λ W)) ∧
    (∀ (W : C) (A : CochainComplex.Plus (Modules J Λ)),
      (∀ i : ℤ, Injective (A.obj.X i)) →
        (∀ (i : ℤ) (q : ℕ), IsZero (((G₀ J W).rightDerived (q + 1)).obj
          ((V J Λ).obj (A.obj.X i)))) ∧
        IsIso ((G J Λ W).rightDerivedFunctorPlusUnit.app
          ((HomotopyCategory.Plus.quotient (Modules J Λ)).obj A)) ∧
        IsIso ((G₀ J W).rightDerivedFunctorPlusUnit.app
          ((V J Λ).mapHomotopyCategoryPlus.obj
            ((HomotopyCategory.Plus.quotient (Modules J Λ)).obj A)))) ∧
    (∀ (W W' : C) (f : W' ⟶ W) (X : DerivedCategory.Plus (Modules J Λ)),
      (v Λ).mapDerivedCategoryPlus.map
          ((Functor.rightDerivedFunctorPlusNatTrans (restriction J Λ f)).app X) ≫
        (comparison J Λ W').app X =
      (comparison J Λ W).app X ≫
        (Functor.rightDerivedFunctorPlusNatTrans (restriction₀ J f)).app
          ((V J Λ).mapDerivedCategoryPlus.obj X)) ∧
    (∀ {D : Type u} [SmallCategory D] (K : GrothendieckTopology D)
      [HasWeakSheafify K RingCat.{u}]
      [HasDerivedCategory.{w} (Modules K Λ)]
      [HasDerivedCategory.{w} (Sheaf K AddCommGrpCat.{u})]
      [EnoughInjectives (Modules K Λ)] [EnoughInjectives (Sheaf K AddCommGrpCat.{u})]
      (L : Sheaf J (Type u) ⥤ Sheaf K (Type u))
      (R : Sheaf K (Type u) ⥤ Sheaf J (Type u))
      (adj : L ⊣ R) (hL : PreservesFiniteLimits L)
      (d : ConstantLeftModuleInverseImageLift J K Λ L R adj hL)
      (T : C) (hT : IsTerminal T) (S : D) (hS : IsTerminal S),
      ∃ b : GlobalPullback d hT hS,
        ∀ X : DerivedCategory.Plus (Modules J Λ),
          (v Λ).mapDerivedCategoryPlus.map ((globalModulePullback b).app X) ≫
            (comparison K Λ S).app (d.moduleFunctor.mapDerivedCategoryPlus.obj X) ≫
            (G₀ K S).rightDerivedFunctorPlus.map ((derivedUnderlying d).hom.app X) =
          (comparison J Λ T).app X ≫
            (globalAbelianPullback b).app ((V J Λ).mapDerivedCategoryPlus.obj X)) ∧
    (∀ (W : C) (X : DerivedCategory.Plus (Modules J Λ)) (n : ℤ),
      IsIso (((v Λ).mapDerivedCategoryPlusHomologyFunctorIso n).hom.app
          ((G J Λ W).rightDerivedFunctorPlus.obj X) ≫
        (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} n).map
          ((comparison J Λ W).app X))) := by
  sorry

end CategoryTheory
