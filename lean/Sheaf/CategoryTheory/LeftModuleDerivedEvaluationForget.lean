/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q41 and P1
-/
module

public import Sheaf.CategoryTheory.ConstantLeftModuleInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ChangeOfRings
public import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange

import WeilConjectures.CategoryTheory.RightDerivedPlusCube
import WeilConjectures.CategoryTheory.Sites.InjectiveModuleAbelianAcyclic
import WeilConjectures.CategoryTheory.Sites.CohomologyRightDerivedSections

/-! # Derived evaluation and forgetting constant left-module scalars

Source: Stacks Project, sites-cohomology.tex, Tag 03FD, and derived.tex, Tags 05TA and 015E
(blueprint: lem-pe-left-module-derived-evaluation-forget).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

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
  have forget_preserves {E : Type u} [SmallCategory E] (T : GrothendieckTopology E) :
      PreservesLimitsOfSize.{0, 0} (U T) := by
    let : PreservesLimitsOfSize.{0, 0} (U T ⋙ sheafToPresheaf T (Type u)) :=
      show PreservesLimitsOfSize.{0, 0} (sheafToPresheaf T AddCommGrpCat.{u} ⋙
        (Functor.whiskeringRight _ _ _).obj (forget AddCommGrpCat.{u})) from
        inferInstance
    exact preservesLimits_of_reflects_of_preserves _ (sheafToPresheaf T (Type u))
  let : PreservesLimitsOfSize.{0, 0} (U J) := forget_preserves J
  let : PreservesFiniteLimits (U J ⋙ L) := comp_preservesFiniteLimits _ _
  let : PreservesLimitsOfSize.{0, 0} (U K) := forget_preserves K
  let : ReflectsLimitsOfSize.{0, 0} (U K) := reflectsLimits_of_reflectsIsomorphisms
  let : PreservesFiniteLimits (d.abelianInverse ⋙ U K) :=
    preservesFiniteLimits_of_natIso d.abelianSetIso.symm
  let : PreservesFiniteLimits d.abelianInverse :=
    preservesFiniteLimits_of_reflects_of_preserves d.abelianInverse (U K)
  let : PreservesColimitsOfSize.{0, 0} d.abelianInverse :=
    d.abelianAdj.leftAdjoint_preservesColimits
  let : PreservesFiniteColimits d.abelianInverse := inferInstance
  exact ⟨d.abelianInverse.additive_of_preserves_binary_products, inferInstance, inferInstance⟩

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
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

private theorem global_underlying
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (Λ : Type u) [Ring Λ] [HasWeakSheafify J RingCat.{u}]
    [HasWeakSheafify K RingCat.{u}]
    {L : Sheaf J (Type u) ⥤ Sheaf K (Type u)}
    {R : Sheaf K (Type u) ⥤ Sheaf J (Type u)}
    {adj : L ⊣ R} {hL : PreservesFiniteLimits L}
    (d : ConstantLeftModuleInverseImageLift J K Λ L R adj hL)
    {T : C} {S : D} (hT : IsTerminal T) (hS : IsTerminal S)
    (b : GlobalPullback d hT hS) (M : Modules J Λ) :
    (v Λ).map (b.moduleMap.app M) ≫ (G₀ K S).map (d.underlyingIso.hom.app M) =
      b.abelianMap.app ((V J Λ).obj M) := by
  ext x
  change (d.underlyingIso.hom.app M).hom.app (op S) (b.moduleMap.app M x) = _
  erw [b.module_normalization, b.abelian_normalization]
  have hi : d.moduleSetIso.inv.app M ≫ (U K).map (d.underlyingIso.hom.app M) =
      d.abelianSetIso.inv.app ((V J Λ).obj M) := by
    apply (cancel_mono (d.abelianSetIso.hom.app ((V J Λ).obj M))).1
    rw [Category.assoc, d.moduleSetIso_compatibility,
      Iso.inv_hom_id_app, Iso.inv_hom_id_app]
    rfl
  exact ConcreteCategory.congr_hom (congrArg (fun f ↦ f.hom.app (op S)) hi) _

private theorem derivedNatIso_refl (Λ : Type u) [Ring Λ]
    [HasDerivedCategory.{w} (ModuleCat.{u} Λ)] [HasDerivedCategory.{w} AddCommGrpCat.{u}] :
    Functor.mapDerivedCategoryPlusNatIso (Iso.refl (v Λ)) =
      Iso.refl (v Λ).mapDerivedCategoryPlus := by
  apply Iso.ext
  apply Localization.natTrans_ext DerivedCategory.Plus.Qh
    (HomotopyCategory.Plus.quasiIso (ModuleCat.{u} Λ))
  intro M
  apply (cancel_mono ((v Λ).mapDerivedCategoryPlusFactorsh.hom.app M)).mp
  rw [Functor.mapDerivedCategoryPlusNatIso_hom_app_factorsh]
  simp only [Iso.refl_hom, NatTrans.mapHomotopyCategoryPlus_id, NatTrans.id_app,
    Functor.map_id, Category.id_comp]
  erw [Category.comp_id]

section Sections
variable {C D : Type u} [SmallCategory C] [SmallCategory D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    {L : Sheaf J (Type u) ⥤ Sheaf K (Type u)}
    (p : L.obj ((constantSheaf J (Type u)).obj PUnit.{u + 1}) ≅
      (constantSheaf K (Type u)).obj PUnit.{u + 1})
    {T : C} {S : D} (hT : IsTerminal T) (hS : IsTerminal S)

private theorem pullback_natural {F F' : Sheaf J (Type u)} (f : F ⟶ F')
    (x : F.obj.obj (op T)) :
    (L.map f).hom.app (op S) (pullbackSection J K p hT hS F x) =
      pullbackSection J K p hT hS F' (f.hom.app (op T) x) := by
  have hs : ((constantSheafAdj J (Type u) hT).homEquiv _ _).symm
      (TypeCat.ofHom (fun _ : PUnit.{u + 1} ↦ f.hom.app (op T) x)) =
      ((constantSheafAdj J (Type u) hT).homEquiv _ _).symm
        (TypeCat.ofHom (fun _ : PUnit.{u + 1} ↦ x)) ≫ f := by
    rw [← Adjunction.homEquiv_naturality_right_symm]
    congr 1
  unfold pullbackSection
  rw [hs, Functor.map_comp, ← Category.assoc, Adjunction.homEquiv_naturality_right]
  rfl

private noncomputable def sectionAddition (A : Sheaf J AddCommGrpCat.{u}) :
    (U J).obj A ⨯ (U J).obj A ⟶ (U J).obj A :=
  CartesianMonoidalCategory.lift prod.fst prod.snd ≫
    ⟨{ app := fun Q ↦ TypeCat.ofHom
        (fun z ↦ (show A.obj.obj Q from z.1) + (show A.obj.obj Q from z.2))
       naturality := by
         intro Q Q' f
         ext z
         exact ((A.obj.map f).hom.map_add _ _).symm }⟩

private theorem sectionAddition_spec (A : Sheaf J AddCommGrpCat.{u}) :
    IsAddition J A (sectionAddition J A) := by
  intro Q x
  rfl

private noncomputable def pointMap (F : Sheaf J (Type u)) (x : F.obj.obj (op T)) :
    (constantSheaf J (Type u)).obj PUnit.{u + 1} ⟶ F :=
  ((constantSheafAdj J (Type u) hT).homEquiv _ _).symm
    (TypeCat.ofHom (fun _ : PUnit.{u + 1} ↦ x))

private theorem pointMap_natural {F F' : Sheaf J (Type u)} (f : F ⟶ F')
    (x : F.obj.obj (op T)) :
    pointMap J hT F x ≫ f = pointMap J hT F' (f.hom.app (op T) x) := by
  unfold pointMap
  rw [← Adjunction.homEquiv_naturality_right_symm]
  congr 1

private theorem pointMap_recover {F : Sheaf J (Type u)}
    (f : (constantSheaf J (Type u)).obj PUnit.{u + 1} ⟶ F) :
    pointMap J hT F (((constantSheafAdj J (Type u) hT).homEquiv _ _ f) PUnit.unit) = f := by
  apply ((constantSheafAdj J (Type u) hT).homEquiv _ _).injective
  rw [pointMap, Equiv.apply_symm_apply]
  ext t
  cases t
  rfl

private theorem pointMap_pullback (F : Sheaf J (Type u)) (x : F.obj.obj (op T)) :
    pointMap K hS (L.obj F) (pullbackSection J K p hT hS F x) =
      p.inv ≫ L.map (pointMap J hT F x) := by
  exact pointMap_recover K hS _

private theorem pointMap_add (A : Sheaf J AddCommGrpCat.{u})
    (x y : A.obj.obj (op T)) :
    pointMap J hT ((U J).obj A) (x + y) =
      prod.lift (pointMap J hT ((U J).obj A) x) (pointMap J hT ((U J).obj A) y) ≫
        sectionAddition J A := by
  apply ((constantSheafAdj J (Type u) hT).homEquiv _ _).injective
  rw [pointMap, Equiv.apply_symm_apply, Adjunction.homEquiv_naturality_right]
  ext t
  let f := prod.lift (pointMap J hT ((U J).obj A) x)
    (pointMap J hT ((U J).obj A) y)
  have hx := (constantSheafAdj J (Type u) hT).homEquiv_naturality_right f prod.fst
  have hy := (constantSheafAdj J (Type u) hT).homEquiv_naturality_right f prod.snd
  simp only [f, prod.lift_fst, prod.lift_snd, pointMap, Equiv.apply_symm_apply] at hx hy
  have hx' := ConcreteCategory.congr_hom hx t
  have hy' := ConcreteCategory.congr_hom hy t
  change x + y = (sectionAddition J A).hom.app (op T)
    (((constantSheafAdj J (Type u) hT).homEquiv _ _ f) t)
  rw [sectionAddition_spec]
  exact congrArg₂ (· + ·) hx' hy'

private theorem pointMap_injective (F : Sheaf J (Type u)) :
    Function.Injective (pointMap J hT F) := by
  intro x y h
  have hh := congrArg ((constantSheafAdj J (Type u) hT).homEquiv _ _) h
  simp only [pointMap, Equiv.apply_symm_apply] at hh
  exact ConcreteCategory.congr_hom hh PUnit.unit

private theorem pullback_point_pair [PreservesFiniteLimits L]
    (F : Sheaf J (Type u))
    (f g : (constantSheaf J (Type u)).obj PUnit.{u + 1} ⟶ F) :
    p.inv ≫ L.map (prod.lift f g) =
      prod.lift (p.inv ≫ L.map f) (p.inv ≫ L.map g) ≫ inv (prodComparison L F F) := by
  apply (cancel_mono (prodComparison L F F)).1
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  apply prod.hom_ext <;> simp [Category.assoc, ← Functor.map_comp]

end Sections

section Normalized
variable {C D : Type u} [SmallCategory C] [SmallCategory D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (Λ : Type u) [Ring Λ] [HasWeakSheafify J RingCat.{u}]
    [HasWeakSheafify K RingCat.{u}]
    {L : Sheaf J (Type u) ⥤ Sheaf K (Type u)}
    {R : Sheaf K (Type u) ⥤ Sheaf J (Type u)}
    {adj : L ⊣ R} {hL : PreservesFiniteLimits L}
    (d : ConstantLeftModuleInverseImageLift J K Λ L R adj hL)
    {T : C} {S : D} (hT : IsTerminal T) (hS : IsTerminal S)

private noncomputable def abelianSection (A : Sheaf J AddCommGrpCat.{u})
    (x : A.obj.obj (op T)) : (d.abelianInverse.obj A).obj.obj (op S) :=
  (d.abelianSetIso.inv.app A).hom.app (op S)
    (pullbackSection J K d.pointIso hT hS ((U J).obj A) x)

private theorem abelianSection_point (A : Sheaf J AddCommGrpCat.{u})
    (x : A.obj.obj (op T)) :
    pointMap K hS ((U K).obj (d.abelianInverse.obj A))
        (abelianSection J K Λ d hT hS A x) ≫ d.abelianSetIso.hom.app A =
      d.pointIso.inv ≫ L.map (pointMap J hT ((U J).obj A) x) := by
  dsimp only [abelianSection]
  erw [← pointMap_natural]
  erw [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  exact pointMap_pullback J K d.pointIso hT hS _ _

private theorem abelianSection_add (A : Sheaf J AddCommGrpCat.{u})
    (x y : A.obj.obj (op T)) :
    abelianSection J K Λ d hT hS A (x + y) =
      abelianSection J K Λ d hT hS A x + abelianSection J K Λ d hT hS A y := by
  let : PreservesFiniteLimits L := hL
  apply pointMap_injective K hS ((U K).obj (d.abelianInverse.obj A))
  apply (cancel_mono (d.abelianSetIso.hom.app A)).1
  erw [abelianSection_point, pointMap_add, pointMap_add]
  rw [Category.assoc, d.abelian_addition A _ _
    (sectionAddition_spec J A) (sectionAddition_spec K (d.abelianInverse.obj A))]
  rw [← Category.assoc, prod.lift_map]
  rw [abelianSection_point, abelianSection_point]
  rw [Functor.map_comp, ← Category.assoc, pullback_point_pair J K d.pointIso, Category.assoc]
  rfl

private theorem abelianSection_natural {A B : Sheaf J AddCommGrpCat.{u}} (f : A ⟶ B)
    (x : A.obj.obj (op T)) :
    (d.abelianInverse.map f).hom.app (op S) (abelianSection J K Λ d hT hS A x) =
      abelianSection J K Λ d hT hS B (f.hom.app (op T) x) := by
  have h := d.abelianSetIso.inv.naturality f
  have he := congrArg
    (fun k : L.obj ((U J).obj A) ⟶ (U K).obj (d.abelianInverse.obj B) ↦
      k.hom.app (op S) (pullbackSection J K d.pointIso hT hS ((U J).obj A) x)) h
  dsimp only [abelianSection]
  erw [← he]
  change (d.abelianSetIso.inv.app B).hom.app (op S)
      ((L.map ((U J).map f)).hom.app (op S)
        (pullbackSection J K d.pointIso hT hS ((U J).obj A) x)) = _
  erw [pullback_natural]
  rfl

private noncomputable def scalarMap (M : Modules J Λ) (r : Λ) :
    (V J Λ).obj M ⟶ (V J Λ).obj M :=
  ⟨{ app := fun Q ↦ AddCommGrpCat.ofHom
        (DistribSMul.toAddMonoidHom (M.val.obj Q)
          ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))).app Q r))
     naturality := by
       intro Q Q' f
       ext x
       have hm := M.val.map_smul f
         ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))).app Q r)
         (show M.val.obj Q from x)
       have hr := congrArg (fun k ↦ k r)
         ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))).naturality f)
       have hh := congrArg (fun t : ((constantSheaf J RingCat.{u}).obj
         (RingCat.of Λ)).obj.obj Q' ↦ t • (M.val.map f x : M.val.obj Q')) hr
       exact hh.trans hm.symm }⟩

private theorem scalarMap_spec (M : Modules J Λ) (r : Λ) :
    IsScalar J Λ M r (scalarMap J Λ M r) := by
  intro Q x
  rfl

private noncomputable def moduleSection (M : Modules J Λ)
    (x : (G J Λ T).obj M) : (G K Λ S).obj (d.moduleFunctor.obj M) :=
  (d.underlyingIso.inv.app M).hom.app (op S)
    (abelianSection J K Λ d hT hS ((V J Λ).obj M) x)

private theorem moduleSection_add (M : Modules J Λ) (x y : (G J Λ T).obj M) :
    moduleSection J K Λ d hT hS M (x + y) =
      moduleSection J K Λ d hT hS M x + moduleSection J K Λ d hT hS M y := by
  unfold moduleSection
  rw [abelianSection_add, map_add]

private theorem moduleSection_smul (M : Modules J Λ) (r : Λ)
    (x : (G J Λ T).obj M) :
    moduleSection J K Λ d hT hS M (r • x) =
      r • moduleSection J K Λ d hT hS M x := by
  have hs := d.scalar_compatibility M r (scalarMap J Λ M r)
    (scalarMap K Λ (d.moduleFunctor.obj M) r)
    (scalarMap_spec J Λ M r) (scalarMap_spec K Λ (d.moduleFunctor.obj M) r)
  have hi : (d.abelianInverse.map (scalarMap J Λ M r)) ≫ d.underlyingIso.inv.app M =
      d.underlyingIso.inv.app M ≫ scalarMap K Λ (d.moduleFunctor.obj M) r := by
    apply (cancel_epi (d.underlyingIso.hom.app M)).1
    rw [← Category.assoc, ← hs, Category.assoc, Iso.hom_inv_id_app]
    erw [Category.comp_id, Iso.hom_inv_id_app_assoc]
  have he := congrArg
    (fun f : d.abelianInverse.obj ((V J Λ).obj M) ⟶ (V K Λ).obj
        (d.moduleFunctor.obj M) ↦
      f.hom.app (op S) (abelianSection J K Λ d hT hS ((V J Λ).obj M) x)) hi
  have hn := abelianSection_natural J K Λ d hT hS (scalarMap J Λ M r) x
  unfold moduleSection
  change (d.underlyingIso.inv.app M).hom.app (op S)
      (abelianSection J K Λ d hT hS ((V J Λ).obj M)
        ((scalarMap J Λ M r).hom.app (op T) x)) = _
  rw [← hn]
  exact he

private theorem moduleSection_natural {M N : Modules J Λ} (f : M ⟶ N)
    (x : (G J Λ T).obj M) :
    (G K Λ S).map (d.moduleFunctor.map f) (moduleSection J K Λ d hT hS M x) =
      moduleSection J K Λ d hT hS N ((G J Λ T).map f x) := by
  have h := d.underlyingIso.inv.naturality f
  have he := congrArg
    (fun k : d.abelianInverse.obj ((V J Λ).obj M) ⟶
        (V K Λ).obj (d.moduleFunctor.obj N) ↦
      k.hom.app (op S) (abelianSection J K Λ d hT hS ((V J Λ).obj M) x)) h
  dsimp only [moduleSection]
  erw [← he]
  change (d.underlyingIso.inv.app N).hom.app (op S)
      ((d.abelianInverse.map ((V J Λ).map f)).hom.app (op S)
        (abelianSection J K Λ d hT hS ((V J Λ).obj M) x)) = _
  rw [abelianSection_natural]
  rfl

private theorem moduleSection_normalization (M : Modules J Λ)
    (x : (G J Λ T).obj M) :
    moduleSection J K Λ d hT hS M x =
      (d.moduleSetIso.inv.app M).hom.app (op S)
        (pullbackSection J K d.pointIso hT hS ((W J Λ).obj M) x) := by
  have hi : d.abelianSetIso.inv.app ((V J Λ).obj M) ≫
      (U K).map (d.underlyingIso.inv.app M) = d.moduleSetIso.inv.app M := by
    apply (cancel_mono (d.moduleSetIso.hom.app M)).1
    rw [← d.moduleSetIso_compatibility, Category.assoc, ← Functor.map_comp_assoc,
      Iso.inv_hom_id_app]
    erw [Functor.map_id, Category.id_comp, Iso.inv_hom_id_app]
    rw [d.moduleSetIso_compatibility, Iso.inv_hom_id_app]
    rfl
  exact congrArg (fun f : L.obj ((W J Λ).obj M) ⟶
      (W K Λ).obj (d.moduleFunctor.obj M) ↦
    f.hom.app (op S) (pullbackSection J K d.pointIso hT hS ((W J Λ).obj M) x)) hi

private noncomputable def normalizedGlobalPullback : GlobalPullback d hT hS where
  moduleMap :=
    { app := fun M ↦ ModuleCat.ofHom (X := (G J Λ T).obj M)
        (Y := (G K Λ S).obj (d.moduleFunctor.obj M))
        (show (G J Λ T).obj M →ₗ[Λ] (G K Λ S).obj (d.moduleFunctor.obj M) from
          { toFun := moduleSection J K Λ d hT hS M
            map_add' := moduleSection_add J K Λ d hT hS M
            map_smul' := moduleSection_smul J K Λ d hT hS M })
      naturality := by
        intro M N f
        ext x
        exact (moduleSection_natural J K Λ d hT hS f x).symm }
  abelianMap :=
    { app := fun A ↦ AddCommGrpCat.ofHom
        (AddMonoidHom.mk' (abelianSection J K Λ d hT hS A)
          (abelianSection_add J K Λ d hT hS A))
      naturality := by
        intro A B f
        ext x
        exact (abelianSection_natural J K Λ d hT hS f x).symm }
  module_normalization := moduleSection_normalization J K Λ d hT hS
  abelian_normalization := fun A x ↦ rfl

end Normalized


section Derived
variable {C D : Type u} [SmallCategory C] [SmallCategory D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (Λ : Type u) [Ring Λ] [HasWeakSheafify J RingCat.{u}]
    [HasWeakSheafify K RingCat.{u}]
    [HasDerivedCategory.{w} (Modules J Λ)] [HasDerivedCategory.{w} (Modules K Λ)]
    [HasDerivedCategory.{w} (Sheaf J AddCommGrpCat.{u})]
    [HasDerivedCategory.{w} (Sheaf K AddCommGrpCat.{u})]
    [HasDerivedCategory.{w} (ModuleCat.{u} Λ)] [HasDerivedCategory.{w} AddCommGrpCat.{u}]
    [EnoughInjectives (Modules J Λ)] [EnoughInjectives (Modules K Λ)]
    [EnoughInjectives (Sheaf J AddCommGrpCat.{u})]
    [EnoughInjectives (Sheaf K AddCommGrpCat.{u})]
    {L : Sheaf J (Type u) ⥤ Sheaf K (Type u)}
    {R : Sheaf K (Type u) ⥤ Sheaf J (Type u)}
    {adj : L ⊣ R} {hL : PreservesFiniteLimits L}
    (d : ConstantLeftModuleInverseImageLift J K Λ L R adj hL)
    {T : C} {S : D} (hT : IsTerminal T) (hS : IsTerminal S)
    (b : GlobalPullback d hT hS)

omit [HasDerivedCategory.{w} (Modules K Λ)]
  [HasDerivedCategory.{w} (Sheaf J AddCommGrpCat.{u})]
  [HasDerivedCategory.{w} (ModuleCat.{u} Λ)] [HasDerivedCategory.{w} AddCommGrpCat.{u}]
  [EnoughInjectives (Modules J Λ)] [EnoughInjectives (Modules K Λ)]
  [EnoughInjectives (Sheaf J AddCommGrpCat.{u})]
  [EnoughInjectives (Sheaf K AddCommGrpCat.{u})] in
private theorem underlying_natIso_symm :
    (Functor.mapDerivedCategoryPlusNatIso d.underlyingIso.symm).inv =
      (Functor.mapDerivedCategoryPlusNatIso d.underlyingIso).hom := by
  apply Localization.natTrans_ext DerivedCategory.Plus.Qh
    (HomotopyCategory.Plus.quasiIso (Modules J Λ))
  intro M
  apply (cancel_epi
    ((Functor.mapDerivedCategoryPlusNatIso d.underlyingIso.symm).hom.app
      (DerivedCategory.Plus.Qh.obj M))).mp
  apply (cancel_mono
    ((V J Λ ⋙ d.abelianInverse).mapDerivedCategoryPlusFactorsh.hom.app M)).mp
  rw [Iso.hom_inv_id_app, Category.id_comp]
  rw [Category.assoc, Functor.mapDerivedCategoryPlusNatIso_hom_app_factorsh]
  rw [← Category.assoc, Functor.mapDerivedCategoryPlusNatIso_hom_app_factorsh]
  simp only [Category.assoc, ← Functor.map_comp, ← NatTrans.comp_app,
    ← NatTrans.mapHomotopyCategoryPlus_comp, Iso.symm_hom, Iso.inv_hom_id,
    NatTrans.mapHomotopyCategoryPlus_id, NatTrans.id_app, Functor.map_id]
  erw [Category.comp_id]

private theorem global_cube (X : DerivedCategory.Plus (Modules J Λ)) :
    let c : v Λ ⋙ 𝟭 AddCommGrpCat.{u} ≅ 𝟭 (ModuleCat.{u} Λ) ⋙ v Λ :=
      (v Λ).rightUnitor ≪≫ (v Λ).leftUnitor.symm
    let dc := (Functor.mapDerivedCategoryPlusCompIso (v Λ) (𝟭 AddCommGrpCat.{u})).symm ≪≫
      Functor.mapDerivedCategoryPlusNatIso c ≪≫
      Functor.mapDerivedCategoryPlusCompIso (𝟭 (ModuleCat.{u} Λ)) (v Λ)
    (v Λ).mapDerivedCategoryPlus.map
        ((Functor.rightDerivedFunctorPlusBaseChange
          (G := G J Λ T) (G' := G K Λ S)
          (β := d.moduleFunctor) (γ := 𝟭 (ModuleCat.{u} Λ)) b.moduleMap).app X) ≫
      (comparison K Λ S).app (d.moduleFunctor.mapDerivedCategoryPlus.obj X) ≫
      (G₀ K S).rightDerivedFunctorPlus.map ((derivedUnderlying d).hom.app X) =
    dc.inv.app ((G J Λ T).rightDerivedFunctorPlus.obj X) ≫
      (𝟭 AddCommGrpCat.{u}).mapDerivedCategoryPlus.map ((comparison J Λ T).app X) ≫
      (Functor.rightDerivedFunctorPlusBaseChange
        (G := G₀ J T) (G' := G₀ K S)
        (β := d.abelianInverse) (γ := 𝟭 AddCommGrpCat.{u}) b.abelianMap).app
        ((V J Λ).mapDerivedCategoryPlus.obj X) := by
  let : PreservesFiniteLimits L := hL
  have h := Functor.rightDerivedFunctorPlusBaseChange_cube
    (G J Λ T) (G K Λ S) (G₀ J T) (G₀ K S)
    d.moduleFunctor (𝟭 (ModuleCat.{u} Λ)) d.abelianInverse (𝟭 AddCommGrpCat.{u})
    (V J Λ) (v Λ) (V K Λ) (v Λ)
    b.moduleMap b.abelianMap (evaluationIdentity J Λ T).hom
    (evaluationIdentity K Λ S).hom
    ((v Λ).rightUnitor ≪≫ (v Λ).leftUnitor.symm) d.underlyingIso.symm
    (by
      intro M
      dsimp only [Iso.symm_inv, Iso.trans_inv, Functor.leftUnitor_hom_app,
        Functor.rightUnitor_inv_app, NatTrans.comp_app, Functor.id_map,
        evaluationIdentity, Iso.refl_hom, NatTrans.id_app]
      erw [Category.id_comp, Category.id_comp, Category.id_comp]
      exact global_underlying J K Λ d hT hS b M) X
  simpa only [derivedUnderlying, Iso.symm_inv, Iso.symm_hom, Iso.trans_inv,
    Iso.trans_hom, comparison, underlying_natIso_symm, Category.assoc] using h

private theorem global_derived (X : DerivedCategory.Plus (Modules J Λ)) :
    (v Λ).mapDerivedCategoryPlus.map ((globalModulePullback b).app X) ≫
      (comparison K Λ S).app (d.moduleFunctor.mapDerivedCategoryPlus.obj X) ≫
      (G₀ K S).rightDerivedFunctorPlus.map ((derivedUnderlying d).hom.app X) =
    (comparison J Λ T).app X ≫
      (globalAbelianPullback b).app ((V J Λ).mapDerivedCategoryPlus.obj X) := by
  let c : v Λ ⋙ 𝟭 AddCommGrpCat.{u} ≅ 𝟭 (ModuleCat.{u} Λ) ⋙ v Λ :=
    (v Λ).rightUnitor ≪≫ (v Λ).leftUnitor.symm
  have hc : c = Iso.refl (v Λ) := by
    apply Iso.ext
    ext M
    rfl
  have h := global_cube J K Λ d hT hS b X
  dsimp only at h
  rw [show ((v Λ).rightUnitor ≪≫ (v Λ).leftUnitor.symm) = Iso.refl (v Λ) from hc,
    derivedNatIso_refl] at h
  simp only [globalModulePullback, globalAbelianPullback, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.rightUnitor_inv_app, Category.id_comp,
    Functor.map_comp, Category.assoc]
  rw [h]
  let M := (G J Λ T).rightDerivedFunctorPlus.obj X
  have hL := congr_app (Functor.mapDerivedCategoryPlusCompIso_id_comp (v Λ)) M
  have hLi : (Functor.mapDerivedCategoryPlusCompIso (𝟭 (ModuleCat.{u} Λ))
      (v Λ)).inv.app M = (v Λ).mapDerivedCategoryPlus.map
        ((Functor.mapDerivedCategoryPlusIdIso (ModuleCat.{u} Λ)).hom.app M) := by
    apply (cancel_epi
      ((Functor.mapDerivedCategoryPlusCompIso (𝟭 (ModuleCat.{u} Λ))
        (v Λ)).hom.app M)).mp
    exact (Iso.hom_inv_id_app _ M).trans hL.symm
  have hR := congr_app (Functor.mapDerivedCategoryPlusCompIso_comp_id (v Λ)) M
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, NatTrans.id_app] at hR
  have hRh : (Functor.mapDerivedCategoryPlusCompIso (v Λ)
      (𝟭 AddCommGrpCat.{u})).hom.app M =
      (Functor.mapDerivedCategoryPlusIdIso AddCommGrpCat.{u}).inv.app
        ((v Λ).mapDerivedCategoryPlus.obj M) := by
    apply (cancel_mono
      ((Functor.mapDerivedCategoryPlusIdIso AddCommGrpCat.{u}).hom.app
        ((v Λ).mapDerivedCategoryPlus.obj M))).mp
    exact hR.trans (Iso.inv_hom_id_app
      (Functor.mapDerivedCategoryPlusIdIso AddCommGrpCat.{u})
      ((v Λ).mapDerivedCategoryPlus.obj M)).symm
  simp only [Iso.trans_inv, Iso.symm_inv, Iso.refl_inv, NatTrans.comp_app, NatTrans.id_app]
  erw [Category.comp_id]
  rw [hLi, hRh]
  simp only [Category.assoc]
  erw [← Functor.map_comp_assoc, Iso.inv_hom_id_app, Functor.map_id, Category.id_comp]
  have hn := (Functor.mapDerivedCategoryPlusIdIso AddCommGrpCat.{u}).inv.naturality
    ((comparison J Λ T).app X)
  simpa only [Functor.id_map, Category.assoc] using ((reassoc_of% hn) _).symm

end Derived

end CategoryTheory

namespace CategoryTheory.LeftModuleDerivedEvaluation
open ConstantLeftModuleInverseImage

private theorem forgottenInjectiveAcyclic
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (Λ : Type u) [Ring Λ] [HasWeakSheafify J RingCat.{u}]
    [EnoughInjectives (Sheaf J AddCommGrpCat.{u})] (W : C)
    (I : Modules J Λ) [Injective I] :
    (G₀ J W).rightAcyclic ((V J Λ).obj I) := by
  let : HasExt.{u} (Sheaf J AddCommGrpCat.{u}) := hasExt_of_enoughInjectives _
  intro n
  let : Subsingleton (Sheaf.H' ((V J Λ).obj I) (n + 1) W) :=
    injective_module_abelian_acyclic W I (n + 1) (Nat.succ_pos n)
  obtain ⟨e⟩ := Sheaf.nonempty_cohomologyPresheafFunctor_eval_iso_rightDerived J W (n + 1)
  exact (AddCommGrpCat.isZero_of_subsingleton
    (Sheaf.H' ((V J Λ).obj I) (n + 1) W)).of_iso (e.app ((V J Λ).obj I)).symm

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
  have hi (W : C) : IsIso (comparison J Λ W) := by
    let : PreservesFiniteLimits (G₀ J W) := inferInstanceAs
      (PreservesFiniteLimits (sheafToPresheaf J AddCommGrpCat.{u} ⋙
        (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op W)))
    apply Functor.isIso_rightDerivedFunctorPlusBaseChange_of_rightAcyclic
      (G := G J Λ W) (G' := G₀ J W) (β := V J Λ) (γ := v Λ)
      (evaluationIdentity J Λ W)
    intro I hI
    exact forgottenInjectiveAcyclic J Λ W I
  refine ⟨hi, ?_, ?_, ?_, ?_⟩
  · intro W A hA
    let : ∀ i : ℤ, Injective (A.obj.X i) := hA
    refine ⟨fun i q ↦ forgottenInjectiveAcyclic J Λ W (A.obj.X i) q, ?_, ?_⟩
    · have (i : ℤ) : Injective
          (((HomotopyCategory.Plus.quotient (Modules J Λ)).obj A).obj.as.X i) := hA i
      infer_instance
    · let : PreservesFiniteLimits (G₀ J W) := inferInstanceAs
        (PreservesFiniteLimits (sheafToPresheaf J AddCommGrpCat.{u} ⋙
          (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op W)))
      exact (G₀ J W).isIso_rightDerivedFunctorPlusUnit_app_of_rightAcyclic
        ((V J Λ).mapCochainComplexPlus.obj A)
        (fun i ↦ forgottenInjectiveAcyclic J Λ W (A.obj.X i))
  · intro W W' f X
    let α := Functor.whiskerRight
      (Functor.rightDerivedFunctorPlusNatTrans (restriction J Λ f))
      (v Λ).mapDerivedCategoryPlus ≫ comparison J Λ W'
    let β := comparison J Λ W ≫ Functor.whiskerLeft (V J Λ).mapDerivedCategoryPlus
      (Functor.rightDerivedFunctorPlusNatTrans (restriction₀ J f))
    have heq : α = β := by
      apply Functor.rightDerived_ext
        ((G J Λ W).rightDerivedFunctorPlus ⋙ (v Λ).mapDerivedCategoryPlus)
        (Functor.whiskerRight (G J Λ W).rightDerivedFunctorPlusUnit
          (v Λ).mapDerivedCategoryPlus ≫ (Functor.associator _ _ _).hom)
        (HomotopyCategory.Plus.quasiIso (Modules J Λ))
      apply NatTrans.ext
      funext M
      simp only [α, β, NatTrans.comp_app, Functor.whiskerRight_app,
        Functor.whiskerLeft_app, Functor.associator_hom_app, Category.id_comp, Category.assoc]
      rw [← Functor.map_comp_assoc, Functor.rightDerivedFunctorPlusNatTrans_app]
      rw [Functor.map_comp, Category.assoc]
      have hw := congr_app (Functor.rightDerivedFunctorPlusBaseChange_fac
        (evaluationIdentity J Λ W).hom) M
      have hw' := congr_app (Functor.rightDerivedFunctorPlusBaseChange_fac
        (evaluationIdentity J Λ W').hom) M
      simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
        Functor.associator_hom_app, Category.comp_id] at hw hw'
      change (v Λ).mapDerivedCategoryPlus.map
          ((G J Λ W).rightDerivedFunctorPlusUnit.app M) ≫
        (comparison J Λ W).app (DerivedCategory.Plus.Qh.obj M) = _ at hw
      change (v Λ).mapDerivedCategoryPlus.map
          ((G J Λ W').rightDerivedFunctorPlusUnit.app M) ≫
        (comparison J Λ W').app (DerivedCategory.Plus.Qh.obj M) = _ at hw'
      rw [hw', reassoc_of% hw]
      simp only [Functor.rightDerivedFunctorPlusBaseChangeAux, NatTrans.comp_app,
        Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
        Functor.associator_inv_app, Category.id_comp, Category.comp_id, Category.assoc]
      simp only [Functor.mapHomotopyCategoryPlusCompIso_refl_hom_app,
        Functor.mapHomotopyCategoryPlusCompIso_refl_inv_app, evaluationIdentity,
        Iso.refl_hom, NatTrans.mapHomotopyCategoryPlus_id, NatTrans.id_app,
        Functor.map_id]
      dsimp only [Functor.comp_obj]
      erw [Category.id_comp, Category.id_comp, Category.id_comp,
        Category.id_comp, Category.id_comp, Category.id_comp]
      have hn := (Functor.rightDerivedFunctorPlusNatTrans (restriction₀ J f)).naturality
        ((V J Λ).mapDerivedCategoryPlusFactorsh.inv.app M)
      erw [hn, Functor.rightDerivedFunctorPlusNatTrans_app_assoc]
      have hv := (v Λ).mapDerivedCategoryPlusFactorsh.hom.naturality
        ((NatTrans.mapHomotopyCategoryPlus (restriction J Λ f)).app M)
      dsimp only [Functor.comp_map] at hv
      erw [reassoc_of% hv]
      rfl
    exact congr_app heq X
  · intro D _ K _ _ _ _ _ L R adj hL d T hT S hS
    exact ⟨normalizedGlobalPullback J K Λ d hT hS,
      fun X ↦ global_derived J K Λ d hT hS _ X⟩
  · intro W X n
    have : IsIso (comparison J Λ W) := hi W
    infer_instance

end CategoryTheory
