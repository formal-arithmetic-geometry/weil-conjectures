/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NL
-/
module

public import Sheaf.CategoryTheory.DiagramRingRestrictionPushforward
public import Sheaf.CategoryTheory.DiagramSiteModuleEquivalence
public import Sheaf.CategoryTheory.ExactSquareDerivedCounit
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution

import Mathlib.CategoryTheory.Sites.CoverLifting

/-!
# Evaluation and the derived adjunction of an algebra diagram

Source: Stacks Project, Cohomology on Sites, Tags 07A6 and 0D6E, with the vertical
small diagram-site realization 
(blueprint: lem-pur-algebra-diagram-evaluation-adjunction-normalization).

Evaluation below restricts the actual ring sheaf and its module to a vertical slice.
In particular the ring is allowed to vary with the diagram index.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

-- Cache standard sheaf instances once for the large comparison signatures.
/-- Cached canonical sheaf-module property, without changing category data.
Source: Mathlib's small-site sheaf and module instances.
(blueprint: def-pur-algebra-diagram-normalization-interface). -/
theorem evaluationRingCompose
    {C : Type u} [SmallCategory C] (K : GrothendieckTopology C) :
    K.HasSheafCompose (forget RingCat.{u}) := inferInstance

/-- Cached canonical sheaf-module property, without changing category data.
Source: Mathlib's small-site sheaf and module instances.
(blueprint: def-pur-algebra-diagram-normalization-interface). -/
theorem evaluationAddCompose
    {C : Type u} [SmallCategory C] (K : GrothendieckTopology C) :
    K.HasSheafCompose (forget AddCommGrpCat.{u}) := inferInstance

/-- Cached canonical sheaf-module property, without changing category data.
Source: Mathlib's small-site sheaf and module instances.
(blueprint: def-pur-algebra-diagram-normalization-interface). -/
theorem evaluationSheafify
    {C : Type u} [SmallCategory C] (K : GrothendieckTopology C) :
    HasSheafify K AddCommGrpCat.{u} := inferInstance

/-- Cached canonical sheaf-module property, without changing category data.
Source: Mathlib's small-site sheaf and module instances.
(blueprint: def-pur-algebra-diagram-normalization-interface). -/
theorem evaluationLocallyBijective
    {C : Type u} [SmallCategory C] (K : GrothendieckTopology C) :
    K.WEqualsLocallyBijective AddCommGrpCat.{u} := inferInstance

attribute [local instance 100000] evaluationRingCompose evaluationAddCompose evaluationSheafify
  evaluationLocallyBijective

/-- Cached canonical sheaf-module property, without changing category data.
Source: Mathlib's small-site sheaf and module instances.
(blueprint: def-pur-algebra-diagram-normalization-interface). -/
theorem cacheKinj {E : Type u} [SmallCategory E]
    {T : GrothendieckTopology E} (R : Sheaf T RingCat.{u}) :
    Abelian.HasKInjectiveResolutions (ringedSiteModules.{u} R) := by
  let := SheafOfModules.isGrothendieckAbelian R
  infer_instance
attribute [local instance 100000] cacheKinj
/-- Cached canonical sheaf-module property, without changing category data.
Source: Mathlib's small-site sheaf and module instances.
(blueprint: def-pur-algebra-diagram-normalization-interface). -/
theorem cacheSheafLimits {E : Type u} [SmallCategory E]
    {T : GrothendieckTopology E} (R : Sheaf T RingCat.{u}) :
    PreservesFiniteLimits (SheafOfModules.toSheaf.{u} R) := inferInstance
/-- Cached canonical sheaf-module property, without changing category data.
Source: Mathlib's small-site sheaf and module instances.
(blueprint: def-pur-algebra-diagram-normalization-interface). -/
theorem cacheSheafColimits {E : Type u} [SmallCategory E]
    {T : GrothendieckTopology E} (R : Sheaf T RingCat.{u}) :
    PreservesFiniteColimits (SheafOfModules.toSheaf.{u} R) := inferInstance
attribute [local instance 100000] cacheSheafLimits cacheSheafColimits
/-- Cached abelian-category properties of sheaves of modules on a small site.
Source: Mathlib's sheaf-module abelian-category construction
(blueprint: lem-pur-algebra-diagram-evaluation-adjunction-normalization). -/
theorem algebraDiagramModules_abelianConditions {E : Type u} [SmallCategory E]
    {T : GrothendieckTopology E} (R : Sheaf T RingCat.{u}) :
    IsNormalMonoCategory (ringedSiteModules.{u} R) ∧
    IsNormalEpiCategory (ringedSiteModules.{u} R) ∧
    HasFiniteProducts (ringedSiteModules.{u} R) ∧
    HasKernels (ringedSiteModules.{u} R) ∧
    HasCokernels (ringedSiteModules.{u} R) :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩
/-- The canonical preadditive structure, with the abelian properties cached as proofs.
Source: Mathlib's sheaf-module abelian-category construction
(blueprint: lem-pur-algebra-diagram-evaluation-adjunction-normalization). -/
@[instance_reducible] def algebraDiagramModules_abelian {E : Type u} [SmallCategory E]
    {T : GrothendieckTopology E} (R : Sheaf T RingCat.{u}) :
    Abelian (ringedSiteModules.{u} R) where
  toPreadditive := inferInstance
  toIsNormalMonoCategory := (algebraDiagramModules_abelianConditions R).1
  toIsNormalEpiCategory := (algebraDiagramModules_abelianConditions R).2.1
  has_finite_products := (algebraDiagramModules_abelianConditions R).2.2.1
  has_kernels := (algebraDiagramModules_abelianConditions R).2.2.2.1
  has_cokernels := (algebraDiagramModules_abelianConditions R).2.2.2.2
attribute [local instance 100000] algebraDiagramModules_abelian
/-- The ring at a vertex of the actual ring diagram.
Source: Stacks 07A6, vertical diagram-site realization
(blueprint: lem-pur-algebra-diagram-evaluation-adjunction-normalization). -/
abbrev algebraDiagramRingAt
    {J C : Type u} [SmallCategory J] [SmallCategory C]
    {K : GrothendieckTopology C}
    (B : Sheaf (diagramSiteTopology J C K) RingCat.{u}) (j : J) :
    Sheaf K RingCat.{u} :=
  ⟨(Prod.sectR (op j) C).op ⋙ B.obj,
    (diagramSite_isSheaf_iff J C K B.obj).1 B.property (op j)⟩

/-- The actual map of rings along a diagram arrow.
Source: Stacks 07A6, semilinear transitions on the vertical diagram site
(blueprint: lem-pur-algebra-diagram-evaluation-adjunction-normalization). -/
def algebraDiagramRingArrow
    {J C : Type u} [SmallCategory J] [SmallCategory C]
    {K : GrothendieckTopology C}
    (B : Sheaf (diagramSiteTopology J C K) RingCat.{u})
    {j k : J} (a : j ⟶ k) : algebraDiagramRingAt B j ⟶ algebraDiagramRingAt B k :=
  ⟨{ app := fun U ↦ B.obj.map (Prod.mkHom a.op (𝟙 U.unop)).op
     naturality := by
       intro U V f
       dsimp [algebraDiagramRingAt]
       rw [← B.obj.map_comp, ← B.obj.map_comp, ← op_comp, ← op_comp]
       congr 2
       ext <;> simp }⟩

/-- Restriction of a coefficient morphism to a vertex.
Source: Stacks 0D6E, coefficient restriction on a vertical slice
(blueprint: lem-pur-algebra-diagram-evaluation-adjunction-normalization). -/
def algebraDiagramCoefficientAt
    {J C : Type u} [SmallCategory J] [SmallCategory C]
    {K : GrothendieckTopology C} {A B : Sheaf (diagramSiteTopology J C K) RingCat.{u}}
    (a : A ⟶ B) (j : J) : algebraDiagramRingAt A j ⟶ algebraDiagramRingAt B j :=
  ⟨Functor.whiskerLeft (Prod.sectR (op j) C).op a.hom⟩

/-- Exact evaluation of modules over the actual varying-ring diagram.
Source: Stacks 07A6, componentwise module inverse image
(blueprint: lem-pur-algebra-diagram-evaluation-adjunction-normalization). -/
def algebraDiagramEvaluation
    {J C : Type u} [SmallCategory J] [SmallCategory C]
    {K : GrothendieckTopology C}
    (B : Sheaf (diagramSiteTopology J C K) RingCat.{u}) (j : J) :
    ringedSiteModules.{u} B ⥤ ringedSiteModules.{u} (algebraDiagramRingAt B j) where
  obj M :=
    { val := PresheafOfModules.pushforward₀Obj (Prod.sectR (op j) C) B.obj M.val
      isSheaf := (diagramSite_isSheaf_iff J C K M.val.presheaf).1 M.isSheaf (op j) }
  map f :=
    { val :=
        { app := fun U ↦ f.val.app ((Prod.sectR (op j) C).op.obj U)
          naturality := fun a ↦ f.val.naturality ((Prod.sectR (op j) C).op.map a) } }
  map_id _M := rfl
  map_comp _f _g := rfl

/-- The actual semilinear transition, viewed as a linear map after restriction of scalars.
Source: Stacks 07A6, module restriction law on the diagram site
(blueprint: lem-pur-algebra-diagram-evaluation-adjunction-normalization). -/
def algebraDiagramTransition
    {J C : Type u} [SmallCategory J] [SmallCategory C]
    {K : GrothendieckTopology C}
    (B : Sheaf (diagramSiteTopology J C K) RingCat.{u})
    {j k : J} (a : j ⟶ k) : algebraDiagramEvaluation B j ⟶
      algebraDiagramEvaluation B k ⋙ SheafOfModules.restrictScalars (algebraDiagramRingArrow B a)
    where
  app M :=
    { val :=
        { app := fun U ↦ @ModuleCat.ofHom
            ((algebraDiagramRingAt B j).obj.obj U) inferInstance
            (((algebraDiagramEvaluation B j).obj M).val.obj U)
            (((SheafOfModules.restrictScalars (algebraDiagramRingArrow B a)).obj
              ((algebraDiagramEvaluation B k).obj M)).val.obj U)
            inferInstance inferInstance inferInstance inferInstance
            { toFun := M.val.map (Prod.mkHom a.op (𝟙 U.unop)).op
              map_add' := map_add _
              map_smul' := fun r x ↦ M.val.map_smul _ r x }
          naturality := by
            intro U V f
            ext x
            change M.val.map (Prod.mkHom a.op (𝟙 V.unop)).op
              (M.val.map ((Prod.sectR (op j) C).op.map f) x) =
              M.val.map ((Prod.sectR (op k) C).op.map f)
                (M.val.map (Prod.mkHom a.op (𝟙 U.unop)).op x)
            have H : ((Prod.sectR (op j) C).op.map f) ≫
                (Prod.mkHom a.op (𝟙 V.unop)).op =
                (Prod.mkHom a.op (𝟙 U.unop)).op ≫ ((Prod.sectR (op k) C).op.map f) := by
              apply Quiver.Hom.unop_inj
              ext <;> simp
            have HH := M.val.presheaf.congr_map H
            rw [Functor.map_comp, Functor.map_comp] at HH
            exact ConcreteCategory.congr_hom HH x } }
  naturality := by
    intro M N f
    ext U x
    exact (PresheafOfModules.naturality_apply f.val (Prod.mkHom a.op (𝟙 U.unop)).op x).symm

/-- Evaluation is additive.
Source: Stacks 07A6; addition of maps is sectionwise. This is the additivity clause
of exact evaluation in the node 
(blueprint: lem-pur-algebra-diagram-evaluation-adjunction-normalization).
Proof: at every object of the slice, both sides are the same sum of linear maps. -/
theorem algebraDiagramEvaluation_additive
    {J C : Type u} [SmallCategory J] [SmallCategory C]
    {K : GrothendieckTopology C}
    (B : Sheaf (diagramSiteTopology J C K) RingCat.{u}) (j : J) :
    (algebraDiagramEvaluation B j).Additive := by
  constructor
  intro M N f g
  ext U x
  rfl

private theorem algebraDiagramSlice_continuous
    {J C : Type u} [SmallCategory J] [SmallCategory C]
    (K : GrothendieckTopology C) (j : J) :
    (Prod.sectR (op j) C).IsContinuous K (diagramSiteTopology J C K) where
  op_comp_isSheaf_of_types F :=
    (isSheaf_iff_isSheaf_of_type K _).1
      ((diagramSite_isSheaf_iff J C K F.obj).1 F.property (op j))

private theorem algebraDiagramSlice_cocontinuous
    {J C : Type u} [SmallCategory J] [SmallCategory C]
    (K : GrothendieckTopology C) (j : J) :
    (Prod.sectR (op j) C).IsCocontinuous K (diagramSiteTopology J C K) where
  cover_lift h := h

/-- Evaluation preserves finite limits.
Source: Stacks 07A6, vertical kernels 
(blueprint: lem-pur-algebra-diagram-evaluation-adjunction-normalization).
Proof: kernels and finite products of module sheaves are computed sectionwise;
restriction to the slice commutes with both constructions. -/
theorem algebraDiagramEvaluation_preservesFiniteLimits
    {J C : Type u} [SmallCategory J] [SmallCategory C]
    {K : GrothendieckTopology C}
    (B : Sheaf (diagramSiteTopology J C K) RingCat.{u}) (j : J) :
    PreservesFiniteLimits (algebraDiagramEvaluation B j) := by
  let := algebraDiagramSlice_continuous K j
  let ev := (Prod.sectR (op j) C).sheafPushforwardContinuous AddCommGrpCat.{u} K
    (diagramSiteTopology J C K)
  have : PreservesFiniteLimits (ev ⋙ sheafToPresheaf K AddCommGrpCat.{u}) := by
    change PreservesFiniteLimits (sheafToPresheaf (diagramSiteTopology J C K) AddCommGrpCat.{u} ⋙
      (Functor.whiskeringLeft _ _ AddCommGrpCat.{u}).obj (Prod.sectR (op j) C).op)
    infer_instance
  have : PreservesFiniteLimits ev :=
    preservesFiniteLimits_of_reflects_of_preserves ev (sheafToPresheaf K AddCommGrpCat.{u})
  have : PreservesFiniteLimits
      (algebraDiagramEvaluation B j ⋙ SheafOfModules.toSheaf (algebraDiagramRingAt B j)) := by
    change PreservesFiniteLimits (SheafOfModules.toSheaf B ⋙ ev)
    infer_instance
  exact preservesFiniteLimits_of_reflects_of_preserves _
    (SheafOfModules.toSheaf (algebraDiagramRingAt B j))

/-- Evaluation preserves finite colimits.
Source: Stacks 07A6, vertical cokernels 
(blueprint: lem-pur-algebra-diagram-evaluation-adjunction-normalization).
Proof: sectionwise cokernels are sheafified vertically. The sheaf condition on the
diagram site is exactly the sheaf condition on each slice, so this sheafification
restricts to the slice sheafification. Evaluation also commutes with finite sums. -/
theorem algebraDiagramEvaluation_preservesFiniteColimits
    {J C : Type u} [SmallCategory J] [SmallCategory C]
    {K : GrothendieckTopology C}
    (B : Sheaf (diagramSiteTopology J C K) RingCat.{u}) (j : J) :
    PreservesFiniteColimits (algebraDiagramEvaluation B j) := by
  let := algebraDiagramSlice_continuous K j
  let := algebraDiagramSlice_cocontinuous K j
  let ev := (Prod.sectR (op j) C).sheafPushforwardContinuous AddCommGrpCat.{u} K
    (diagramSiteTopology J C K)
  have : PreservesColimitsOfSize.{0, 0} ev :=
    ((Prod.sectR (op j) C).sheafAdjunctionCocontinuous AddCommGrpCat.{u} K
      (diagramSiteTopology J C K)).leftAdjoint_preservesColimits
  have : PreservesFiniteColimits ev := inferInstance
  have : PreservesFiniteColimits
      (algebraDiagramEvaluation B j ⋙ SheafOfModules.toSheaf (algebraDiagramRingAt B j)) := by
    change PreservesFiniteColimits (SheafOfModules.toSheaf B ⋙ ev)
    infer_instance
  have : ReflectsFiniteColimits (SheafOfModules.toSheaf (algebraDiagramRingAt B j)) :=
    reflectsFiniteColimitsOfReflectsIsomorphisms _
  exact preservesFiniteColimits_of_reflects_of_preserves _
    (SheafOfModules.toSheaf (algebraDiagramRingAt B j))

attribute [instance] algebraDiagramEvaluation_additive
  algebraDiagramEvaluation_preservesFiniteLimits algebraDiagramEvaluation_preservesFiniteColimits

/-- Set-sheaf evaluation on the specified small diagram site.
Source: Stacks 07A6, diagram-site realization
(blueprint: lem-pur-algebra-diagram-evaluation-adjunction-normalization). -/
abbrev algebraDiagramSetEvaluation
    (J C : Type u) [SmallCategory J] [SmallCategory C]
    (K : GrothendieckTopology C) (j : J) :=
  (diagramSiteSheafEquivalence J C K).functor ⋙ (evaluation J (Sheaf K (Type u))).obj j

/-- Componentwise direct image commutes with evaluation, with the site-equivalence counit.
Source: Stacks 07A6, componentwise direct image
(blueprint: lem-pur-algebra-diagram-evaluation-adjunction-normalization). -/
def algebraDiagramSetDirectEvaluation
    (J C D : Type u) [SmallCategory J] [SmallCategory C] [SmallCategory D]
    (K : GrothendieckTopology C) (L : GrothendieckTopology D)
    (G : Sheaf K (Type u) ⥤ Sheaf L (Type u)) (j : J) :
    diagramCoefficientDirect J C D K L G ⋙ algebraDiagramSetEvaluation J D L j ≅
      algebraDiagramSetEvaluation J C K j ⋙ G :=
  NatIso.ofComponents
    (fun M ↦ ((evaluation J (Sheaf L (Type u))).obj j).mapIso
      ((diagramSiteSheafEquivalence J D L).counitIso.app
        (((Functor.whiskeringRight J _ _).obj G).obj
          ((diagramSiteSheafEquivalence J C K).functor.obj M))))
    (by
      intro M N f
      have h := (diagramSiteSheafEquivalence J D L).counitIso.hom.naturality
        (((Functor.whiskeringRight J _ _).obj G).map
          ((diagramSiteSheafEquivalence J C K).functor.map f))
      exact congrArg (fun t ↦ t.app j) h)

/-- K-injective resolutions on the small module site, supplied by the existing
Grothendieck category theorem. Source: Stacks 07A6
(blueprint: lem-pur-algebra-diagram-evaluation-adjunction-normalization). -/
instance algebraDiagramKInjectives
    {C : Type u} [SmallCategory C] {K : GrothendieckTopology C}
    (R : Sheaf K RingCat.{u}) : Abelian.HasKInjectiveResolutions (ringedSiteModules.{u} R) := by
  let := SheafOfModules.isGrothendieckAbelian R
  infer_instance


/-- Exact restriction of coefficients, finite-limit part.
Source: Stacks 0D6E, identity-topos coefficient change 
(blueprint: lem-pur-algebra-diagram-evaluation-adjunction-normalization).
Proof: restriction leaves the underlying abelian sheaf unchanged. The faithful
forgetful functors create finite limits, so restriction preserves them. -/
theorem algebraDiagramRestriction_preservesFiniteLimits
    {C : Type u} [SmallCategory C] {K : GrothendieckTopology C}
    {R S : Sheaf K RingCat.{u}} (a : R ⟶ S) :
    PreservesFiniteLimits (SheafOfModules.restrictScalars.{u} a) := by
  have : PreservesFiniteLimits
      (SheafOfModules.restrictScalars.{u} a ⋙ SheafOfModules.toSheaf R) :=
    inferInstanceAs (PreservesFiniteLimits (SheafOfModules.toSheaf.{u} S))
  exact preservesFiniteLimits_of_reflects_of_preserves _ (SheafOfModules.toSheaf R)

/-- Exact restriction of coefficients, finite-colimit part.
Source: Stacks 0D6E, identity-topos coefficient change 
(blueprint: lem-pur-algebra-diagram-evaluation-adjunction-normalization).
Proof: restriction leaves the underlying abelian sheaf unchanged. Cokernels are
sheafified sectionwise cokernels and finite sums are sectionwise; their underlying
abelian sheaves are unchanged, so the comparison is an isomorphism. -/
theorem algebraDiagramRestriction_preservesFiniteColimits
    {C : Type u} [SmallCategory C] {K : GrothendieckTopology C}
    {R S : Sheaf K RingCat.{u}} (a : R ⟶ S) :
    PreservesFiniteColimits (SheafOfModules.restrictScalars.{u} a) := by
  have : PreservesFiniteColimits
      (SheafOfModules.restrictScalars.{u} a ⋙ SheafOfModules.toSheaf R) :=
    inferInstanceAs (PreservesFiniteColimits (SheafOfModules.toSheaf.{u} S))
  have : ReflectsFiniteColimits (SheafOfModules.toSheaf.{u} R) :=
    reflectsFiniteColimitsOfReflectsIsomorphisms _
  exact preservesFiniteColimits_of_reflects_of_preserves _ (SheafOfModules.toSheaf R)

attribute [instance] algebraDiagramRestriction_preservesFiniteLimits
  algebraDiagramRestriction_preservesFiniteColimits

/-- The equality between evaluating scalar restriction and restricting an evaluated module.
Source: Stacks 0D6E, common coefficient route on each slice
(blueprint: lem-pur-algebra-diagram-evaluation-adjunction-normalization). -/
def algebraDiagramRestrictionEvaluation
    {J C : Type u} [SmallCategory J] [SmallCategory C]
    {K : GrothendieckTopology C} {R S : Sheaf (diagramSiteTopology J C K) RingCat.{u}}
    (a : R ⟶ S) (j : J) :
    SheafOfModules.restrictScalars.{u} a ⋙ algebraDiagramEvaluation R j ≅
      algebraDiagramEvaluation S j ⋙
        SheafOfModules.restrictScalars.{u} (algebraDiagramCoefficientAt a j) :=
  Iso.refl _

/-- The derived square is normalized by the units of the two specified right derived
functors, with termwise localization of the exact horizontal functors.
Source: Stacks 0D6E, common-composite normalization 
(blueprint: lem-pur-algebra-diagram-evaluation-adjunction-normalization). -/
def AlgebraDiagramDerivedSquareNormalized
    {A B Ap Bp : Type (u + 1)}
    [Category.{u} A] [Category.{u} B] [Category.{u} Ap] [Category.{u} Bp]
    [Abelian A] [Abelian B] [Abelian Ap] [Abelian Bp]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    [HasDerivedCategory.{w} Ap] [HasDerivedCategory.{w} Bp]
    [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions Ap]
    (F : A ⥤ B) (G : Ap ⥤ Bp) (x : A ⥤ Ap) (y : B ⥤ Bp)
    [F.Additive] [G.Additive] [x.Additive] [y.Additive]
    [PreservesFiniteLimits x] [PreservesFiniteColimits x]
    [PreservesFiniteLimits y] [PreservesFiniteColimits y]
    (c : F ⋙ y ≅ x ⋙ G)
    (b : F.rightDerivedFunctor ⋙ y.mapDerivedCategory ≅
      x.mapDerivedCategory ⋙ G.rightDerivedFunctor) : Prop :=
  ∀ M : CochainComplex A ℤ,
    y.mapDerivedCategory.map (F.rightDerivedFunctorUnitQ M) ≫
        b.hom.app (DerivedCategory.Q.obj M) ≫
        G.rightDerivedFunctor.map (x.mapDerivedCategoryFactors.hom.app M) =
      y.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj M) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex c.hom (.up ℤ)).app M) ≫
        G.rightDerivedFunctorUnitQ ((x.mapHomologicalComplex (.up ℤ)).obj M)

/-- Transport the chosen derived localization to a constant vertical slice.
Source: Stacks 07A6; its ring is definitionally the original coefficient ring
(blueprint: lem-pur-algebra-diagram-evaluation-adjunction-normalization). -/
instance algebraDiagramConstantDerivedAt
    {J C : Type u} [SmallCategory J] [SmallCategory C]
    {K : GrothendieckTopology C} (R : Sheaf K RingCat.{u})
    [HasDerivedCategory.{w} (ringedSiteModules.{u} R)] (j : J) :
    HasDerivedCategory.{w}
      (ringedSiteModules.{u} (algebraDiagramRingAt (diagramSiteRing J C K R) j)) := by
  change HasDerivedCategory.{w} (ringedSiteModules.{u} R)
  infer_instance

/-- Transport exact evaluation to the definitionally identical constant coefficient ring.
Source: Stacks 07A6 
(blueprint: lem-pur-algebra-diagram-evaluation-adjunction-normalization). -/
instance algebraDiagramConstantEvaluation_additive
    {J C : Type u} [SmallCategory J] [SmallCategory C]
    {K : GrothendieckTopology C} (R : Sheaf K RingCat.{u}) (j : J) :
    (algebraDiagramEvaluation (diagramSiteRing J C K R) j :
      ringedSiteModules.{u} (diagramSiteRing J C K R) ⥤ ringedSiteModules.{u} R).Additive :=
  algebraDiagramEvaluation_additive (diagramSiteRing J C K R) j

/-- Transport exact evaluation to the definitionally identical constant coefficient ring.
Source: Stacks 07A6 
(blueprint: lem-pur-algebra-diagram-evaluation-adjunction-normalization). -/
instance algebraDiagramConstantEvaluation_limits
    {J C : Type u} [SmallCategory J] [SmallCategory C]
    {K : GrothendieckTopology C} (R : Sheaf K RingCat.{u}) (j : J) :
    PreservesFiniteLimits (algebraDiagramEvaluation (diagramSiteRing J C K R) j :
      ringedSiteModules.{u} (diagramSiteRing J C K R) ⥤ ringedSiteModules.{u} R) :=
  algebraDiagramEvaluation_preservesFiniteLimits (diagramSiteRing J C K R) j

/-- Transport exact evaluation to the definitionally identical constant coefficient ring.
Source: Stacks 07A6 
(blueprint: lem-pur-algebra-diagram-evaluation-adjunction-normalization). -/
instance algebraDiagramConstantEvaluation_colimits
    {J C : Type u} [SmallCategory J] [SmallCategory C]
    {K : GrothendieckTopology C} (R : Sheaf K RingCat.{u}) (j : J) :
    PreservesFiniteColimits (algebraDiagramEvaluation (diagramSiteRing J C K R) j :
      ringedSiteModules.{u} (diagramSiteRing J C K R) ⥤ ringedSiteModules.{u} R) :=
  algebraDiagramEvaluation_preservesFiniteColimits (diagramSiteRing J C K R) j

/-- The constant coefficient ring sheaf used in the node.
Source: Stacks 07A6, constant coefficients 
(blueprint: lem-pur-algebra-diagram-evaluation-adjunction-normalization). -/
def algebraDiagramConstantRing
    {C : Type u} [SmallCategory C] (K : GrothendieckTopology C) (A : CommRingCat.{u}) :=
  (constantSheaf K RingCat.{u}).obj (RingCat.of A)

/-- An ordinary evaluation comparison is fixed on underlying sheaves by the given
geometric direct image and the counit of the concrete diagram-site equivalence.
Source: Stacks 07A6, componentwise direct image 
(blueprint: lem-pur-algebra-diagram-evaluation-adjunction-normalization). -/
def AlgebraDiagramOrdinaryEvaluationNormalized
    {J C D : Type u} [SmallCategory J] [SmallCategory C] [SmallCategory D]
    {K : GrothendieckTopology C} {L : GrothendieckTopology D}
    {BX : Sheaf (diagramSiteTopology J C K) RingCat.{u}}
    {BY : Sheaf (diagramSiteTopology J D L) RingCat.{u}}
    (G : Sheaf K (Type u) ⥤ Sheaf L (Type u))
    (f : RingedToposMorphism BX BY) (j : J)
    (g : RingedToposMorphism (algebraDiagramRingAt BX j) (algebraDiagramRingAt BY j))
    (hf : f.direct = diagramCoefficientDirect J C D K L G) (hg : g.direct = G)
    (c : f.modules ⋙ algebraDiagramEvaluation BY j ≅
      algebraDiagramEvaluation BX j ⋙ g.modules) : Prop :=
  ∀ M : ringedSiteModules.{u} BX,
    (diagramCoefficientUnderlying (algebraDiagramRingAt BY j)).map (c.hom.app M) ≫
        g.underlying.hom.app ((algebraDiagramEvaluation BX j).obj M) ≫
        (eqToIso hg).hom.app
          ((diagramCoefficientUnderlying (algebraDiagramRingAt BX j)).obj
            ((algebraDiagramEvaluation BX j).obj M)) =
      (algebraDiagramSetEvaluation J D L j).map (f.underlying.hom.app M) ≫
        (algebraDiagramSetEvaluation J D L j).map
          ((eqToIso hf).hom.app ((diagramCoefficientUnderlying BX).obj M)) ≫
        (algebraDiagramSetDirectEvaluation J C D K L G j).hom.app
          ((diagramCoefficientUnderlying BX).obj M)

/-- The global section of the constant ring sheaf given by a coefficient element.
Source: Stacks 07A6, canonical constant-coefficient identification
(blueprint: lem-pur-algebra-diagram-evaluation-adjunction-normalization). -/
def algebraDiagramConstantSection
    {C : Type u} [SmallCategory C] (K : GrothendieckTopology C)
    (A : CommRingCat.{u}) (a : A) :
    ⊤_ (Sheaf K (Type u)) ⟶
      (sheafCompose K (forget RingCat)).obj (algebraDiagramConstantRing K A) :=
  ⟨{ app := fun U ↦ ↾(fun _ ↦
        ((toSheafify K ((Functor.const Cᵒᵖ).obj (RingCat.of A))).app U).hom a)
     naturality := by
       intro U V f
       ext t
       have h := congrArg (fun z ↦ z.hom a)
         ((toSheafify K ((Functor.const Cᵒᵖ).obj (RingCat.of A))).naturality f)
       change ((toSheafify K ((Functor.const Cᵒᵖ).obj (RingCat.of A))).app V).hom a =
         ((sheafify K ((Functor.const Cᵒᵖ).obj (RingCat.of A))).map f).hom
           (((toSheafify K ((Functor.const Cᵒᵖ).obj (RingCat.of A))).app U).hom a)
       simpa using h }⟩

attribute [local irreducible] algebraDiagramConstantRing

/-- A presentation of the geometric morphism, its pulled-back ring diagram and its
module inverse images. All ring maps and adjunctions are the actual ones: the equations
identify them with the componentwise geometric adjunction, including the structural maps.
The supplied module left adjoints only choose presentations of inverse image; the
comparisons below are normalized relative to those adjunctions.
Source: Stacks 07A6 and 0D6E 
(blueprint: lem-pur-algebra-diagram-evaluation-adjunction-normalization). -/
structure AlgebraDiagramAdjunctionPresentation
    (J C D : Type u) [SmallCategory J] [SmallCategory C] [SmallCategory D]
    (K : GrothendieckTopology C) (L : GrothendieckTopology D) (A : CommRingCat.{u}) where
  /-- The actual commutative algebra diagram on X, as a ring sheaf on the diagram site. -/
  BX : Sheaf (diagramSiteTopology J C K) RingCat.{u}
  /-- The actual commutative algebra diagram on Y. -/
  BY : Sheaf (diagramSiteTopology J D L) RingCat.{u}
  /-- Commutativity of the diagram ring on X. -/
  commX : ∀ (U : (Jᵒᵖ × C)ᵒᵖ) (a b : BX.obj.obj U), a * b = b * a
  /-- Commutativity of the diagram ring on Y. -/
  commY : ∀ (U : (Jᵒᵖ × D)ᵒᵖ) (a b : BY.obj.obj U), a * b = b * a
  /-- Its constant-A algebra structure on X. -/
  aX : diagramSiteRing J C K (algebraDiagramConstantRing K A) ⟶ BX
  /-- Its constant-A algebra structure on Y. -/
  aY : diagramSiteRing J D L (algebraDiagramConstantRing L A) ⟶ BY
  /-- The geometric morphism with its canonical constant-coefficient structure. -/
  s : RingedToposMorphism (algebraDiagramConstantRing K A) (algebraDiagramConstantRing L A)
  /-- The structural map is the canonical one on every constant coefficient element. -/
  constantNormalization : ∀ a : A,
    s.inverse.map (algebraDiagramConstantSection L A a) ≫ s.ringMap =
      terminalComparison s.inverse ≫ algebraDiagramConstantSection K A a
  /-- The constant-A diagram morphism. -/
  fA : RingedToposMorphism (diagramSiteRing J C K (algebraDiagramConstantRing K A))
    (diagramSiteRing J D L (algebraDiagramConstantRing L A))
  /-- The algebra-diagram morphism. -/
  fB : RingedToposMorphism BX BY
  /-- The morphism at each actual vertex ring. -/
  fj : ∀ j : J, RingedToposMorphism (algebraDiagramRingAt BX j) (algebraDiagramRingAt BY j)
  /-- Constant coefficients are pulled back isomorphically. -/
  cartesianA : IsIso s.ringMap
  /-- The diagram of algebras is pulled back isomorphically. -/
  cartesianB : IsIso fB.ringMap
  /-- The constant diagram also has its pulled-back coefficient structure. -/
  cartesianDiagramA : IsIso fA.ringMap
  /-- The level structural coefficient maps are isomorphisms. -/
  cartesianLevel : ∀ j : J, IsIso (fj j).ringMap
  /-- The inverse on A-diagrams is componentwise. -/
  inverseA : fA.inverse = diagramCoefficientInverse J C D K L s.inverse
  /-- The direct on A-diagrams is componentwise. -/
  directA : fA.direct = diagramCoefficientDirect J C D K L s.direct
  /-- Its adjunction is the componentwise adjunction, without a twist. -/
  adjA : HEq fA.adj (diagramCoefficientAdjunction J C D K L s.adj)
  /-- The inverse on B-diagrams is componentwise. -/
  inverseB : fB.inverse = diagramCoefficientInverse J C D K L s.inverse
  /-- The direct on B-diagrams is componentwise. -/
  directB : fB.direct = diagramCoefficientDirect J C D K L s.direct
  /-- Its adjunction is the componentwise adjunction, without a twist. -/
  adjB : HEq fB.adj (diagramCoefficientAdjunction J C D K L s.adj)
  /-- Level inverse image is the given geometric inverse image. -/
  inverseLevel : ∀ j : J, (fj j).inverse = s.inverse
  /-- Level direct image is the given geometric direct image. -/
  directLevel : ∀ j : J, (fj j).direct = s.direct
  /-- Level adjunctions are the given geometric adjunction. -/
  adjLevel : ∀ j : J, HEq (fj j).adj s.adj
  /-- The constant diagram structural map is the actual constant-coefficient map. -/
  structuralA : ∀ j : J,
    HEq (((diagramSiteSheafCurry J C K).map fA.ringMap).app j) s.ringMap
  /-- The algebra diagram structural map is the actual level structural map. -/
  structuralB : ∀ j : J,
    HEq (((diagramSiteSheafCurry J C K).map fB.ringMap).app j) (fj j).ringMap
  /-- The algebra maps commute with the structural coefficient maps. -/
  coefficientSquare :
    fB.inverse.map ((sheafCompose (diagramSiteTopology J D L) (forget RingCat)).map aY) ≫
      fB.ringMap =
    eqToHom (congrArg (fun H ↦ H.obj ((sheafCompose (diagramSiteTopology J D L)
      (forget RingCat)).obj (diagramSiteRing J D L (algebraDiagramConstantRing L A))))
      (inverseB.trans inverseA.symm)) ≫ fA.ringMap ≫
        (sheafCompose (diagramSiteTopology J C K) (forget RingCat)).map aX
  /-- A presentation of module inverse image on the algebra diagram. -/
  pullB : ringedSiteModules.{u} BY ⥤ ringedSiteModules.{u} BX
  /-- Its ordinary module adjunction to the specified induced module direct image. -/
  moduleAdjB : pullB ⊣ fB.modules
  /-- Additivity of inverse image. -/
  additiveB : pullB.Additive
  /-- Exactness of inverse image, finite-limit part. -/
  limitsB : PreservesFiniteLimits pullB
  /-- Exactness of inverse image, finite-colimit part. -/
  colimitsB : PreservesFiniteColimits pullB
  /-- Presentations of module inverse image at the vertices. -/
  pullj : ∀ j : J, ringedSiteModules.{u} (algebraDiagramRingAt BY j) ⥤
    ringedSiteModules.{u} (algebraDiagramRingAt BX j)
  /-- Their ordinary module adjunctions. -/
  moduleAdjj : ∀ j : J, pullj j ⊣ (fj j).modules
  /-- Additivity at the vertices. -/
  additivej : ∀ j : J, (pullj j).Additive
  /-- Exactness at the vertices, finite-limit part. -/
  limitsj : ∀ j : J, PreservesFiniteLimits (pullj j)
  /-- Exactness at the vertices, finite-colimit part. -/
  colimitsj : ∀ j : J, PreservesFiniteColimits (pullj j)

attribute [instance] AlgebraDiagramAdjunctionPresentation.additiveB
  AlgebraDiagramAdjunctionPresentation.limitsB AlgebraDiagramAdjunctionPresentation.colimitsB
  AlgebraDiagramAdjunctionPresentation.additivej AlgebraDiagramAdjunctionPresentation.limitsj
  AlgebraDiagramAdjunctionPresentation.colimitsj

/-- Normalization of a coefficient/direct-image comparison on underlying sheaves.
Source: Stacks 0D6E, the common ringed-topos composite 
(blueprint: lem-pur-algebra-diagram-evaluation-adjunction-normalization). -/
def AlgebraDiagramOrdinaryRestrictionNormalized
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {K : GrothendieckTopology C} {L : GrothendieckTopology D}
    {AX BX : Sheaf K RingCat.{u}} {AY BY : Sheaf L RingCat.{u}}
    (aX : AX ⟶ BX) (aY : AY ⟶ BY)
    (f : RingedToposMorphism BX BY) (g : RingedToposMorphism AX AY)
    (h : f.direct = g.direct)
    (c : f.modules ⋙ SheafOfModules.restrictScalars.{u} aY ≅
      SheafOfModules.restrictScalars.{u} aX ⋙ g.modules) : Prop :=
  ∀ M : ringedSiteModules.{u} BX,
    (diagramCoefficientUnderlying AY).map (c.hom.app M) ≫
        g.underlying.hom.app ((SheafOfModules.restrictScalars.{u} aX).obj M) =
      f.underlying.hom.app M ≫
        (eqToIso h).hom.app ((diagramCoefficientUnderlying BX).obj M)

/-- The actual semilinear diagram transition, localized as a map of exact functors.
Source: Stacks 07A6 and 0D6E, localization of the diagram restriction laws
(blueprint: lem-pur-algebra-diagram-evaluation-adjunction-normalization). -/
def algebraDiagramDerivedTransition
    {J C : Type u} [SmallCategory J] [SmallCategory C]
    {K : GrothendieckTopology C}
    (B : Sheaf (diagramSiteTopology J C K) RingCat.{u})
    [HasDerivedCategory.{w} (ringedSiteModules.{u} B)]
    [∀ j : J, HasDerivedCategory.{w} (ringedSiteModules.{u} (algebraDiagramRingAt B j))]
    {j k : J} (a : j ⟶ k) :
    (algebraDiagramEvaluation B j).mapDerivedCategory ⟶
      (algebraDiagramEvaluation B k).mapDerivedCategory ⋙
        (SheafOfModules.restrictScalars.{u} (algebraDiagramRingArrow B a)).mapDerivedCategory :=
  Localization.liftNatTrans DerivedCategory.Q
    (HomologicalComplex.quasiIso (ringedSiteModules.{u} B) (.up ℤ))
    ((algebraDiagramEvaluation B j).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    ((algebraDiagramEvaluation B k ⋙ SheafOfModules.restrictScalars.{u}
      (algebraDiagramRingArrow B a)).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (algebraDiagramEvaluation B j).mapDerivedCategory
    (algebraDiagramEvaluation B k ⋙ SheafOfModules.restrictScalars.{u}
      (algebraDiagramRingArrow B a)).mapDerivedCategory
    (Functor.whiskerRight (NatTrans.mapHomologicalComplex
      (algebraDiagramTransition B a) (.up ℤ)) DerivedCategory.Q) ≫
      (Functor.mapDerivedCategoryCompIso (algebraDiagramEvaluation B k)
        (SheafOfModules.restrictScalars.{u} (algebraDiagramRingArrow B a))).hom

namespace AlgebraDiagramAdjunctionPresentation

variable {J C D : Type u} [SmallCategory J] [SmallCategory C] [SmallCategory D]
    {K : GrothendieckTopology C} {L : GrothendieckTopology D} {A : CommRingCat.{u}}
    (p : AlgebraDiagramAdjunctionPresentation J C D K L A)

/-- The constant coefficient ring on the diagram site.
Source: Stacks 07A6 
(blueprint: lem-pur-algebra-diagram-evaluation-adjunction-normalization). -/
abbrev AX (_p : AlgebraDiagramAdjunctionPresentation J C D K L A) :=
  diagramSiteRing J C K (algebraDiagramConstantRing K A)

/-- The constant coefficient ring on the diagram site.
Source: Stacks 07A6 
(blueprint: lem-pur-algebra-diagram-evaluation-adjunction-normalization). -/
abbrev AY (_p : AlgebraDiagramAdjunctionPresentation J C D K L A) :=
  diagramSiteRing J D L (algebraDiagramConstantRing L A)

/-- The specified evaluation or scalar restriction, using its concrete construction.
Source: Stacks 07A6 and 0D6E 
(blueprint: lem-pur-algebra-diagram-evaluation-adjunction-normalization). -/
abbrev eBX (j : J) := algebraDiagramEvaluation p.BX j

/-- The specified evaluation or scalar restriction, using its concrete construction.
Source: Stacks 07A6 and 0D6E 
(blueprint: lem-pur-algebra-diagram-evaluation-adjunction-normalization). -/
abbrev eBY (j : J) := algebraDiagramEvaluation p.BY j

/-- The specified evaluation or scalar restriction, using its concrete construction.
Source: Stacks 07A6 and 0D6E 
(blueprint: lem-pur-algebra-diagram-evaluation-adjunction-normalization). -/
abbrev eAX (j : J) :
    ringedSiteModules.{u} p.AX ⥤
      ringedSiteModules.{u} (algebraDiagramConstantRing K A) :=
  algebraDiagramEvaluation p.AX j

/-- The specified evaluation or scalar restriction, using its concrete construction.
Source: Stacks 07A6 and 0D6E 
(blueprint: lem-pur-algebra-diagram-evaluation-adjunction-normalization). -/
abbrev eAY (j : J) :
    ringedSiteModules.{u} p.AY ⥤
      ringedSiteModules.{u} (algebraDiagramConstantRing L A) :=
  algebraDiagramEvaluation p.AY j

/-- The specified evaluation or scalar restriction, using its concrete construction.
Source: Stacks 07A6 and 0D6E 
(blueprint: lem-pur-algebra-diagram-evaluation-adjunction-normalization). -/
def rX : ringedSiteModules.{u} p.BX ⥤ ringedSiteModules.{u} p.AX :=
  SheafOfModules.restrictScalars.{u} p.aX

/-- The specified evaluation or scalar restriction, using its concrete construction.
Source: Stacks 07A6 and 0D6E 
(blueprint: lem-pur-algebra-diagram-evaluation-adjunction-normalization). -/
def rY : ringedSiteModules.{u} p.BY ⥤ ringedSiteModules.{u} p.AY :=
  SheafOfModules.restrictScalars.{u} p.aY

/-- The specified evaluation or scalar restriction, using its concrete construction.
Source: Stacks 07A6 and 0D6E 
(blueprint: lem-pur-algebra-diagram-evaluation-adjunction-normalization). -/
abbrev rXj (j : J) := SheafOfModules.restrictScalars.{u} (algebraDiagramCoefficientAt p.aX j)

/-- The specified evaluation or scalar restriction, using its concrete construction.
Source: Stacks 07A6 and 0D6E 
(blueprint: lem-pur-algebra-diagram-evaluation-adjunction-normalization). -/
abbrev rYj (j : J) := SheafOfModules.restrictScalars.{u} (algebraDiagramCoefficientAt p.aY j)

/-- Exactness of the constant evaluation with its original coefficient-ring codomain.
Source: Stacks 07A6
(blueprint: lem-pur-algebra-diagram-evaluation-adjunction-normalization). -/
instance eAX_additive (j : J) : (p.eAX j).Additive :=
  algebraDiagramEvaluation_additive p.AX j

/-- Exactness of the constant evaluation with its original coefficient-ring codomain.
Source: Stacks 07A6
(blueprint: lem-pur-algebra-diagram-evaluation-adjunction-normalization). -/
instance eAX_limits (j : J) : PreservesFiniteLimits (p.eAX j) :=
  algebraDiagramEvaluation_preservesFiniteLimits p.AX j

/-- Exactness of the constant evaluation with its original coefficient-ring codomain.
Source: Stacks 07A6
(blueprint: lem-pur-algebra-diagram-evaluation-adjunction-normalization). -/
instance eAX_colimits (j : J) : PreservesFiniteColimits (p.eAX j) :=
  algebraDiagramEvaluation_preservesFiniteColimits p.AX j

/-- Exactness of the constant evaluation with its original coefficient-ring codomain.
Source: Stacks 07A6
(blueprint: lem-pur-algebra-diagram-evaluation-adjunction-normalization). -/
instance eAY_additive (j : J) : (p.eAY j).Additive :=
  algebraDiagramEvaluation_additive p.AY j

/-- Exactness of the constant evaluation with its original coefficient-ring codomain.
Source: Stacks 07A6
(blueprint: lem-pur-algebra-diagram-evaluation-adjunction-normalization). -/
instance eAY_limits (j : J) : PreservesFiniteLimits (p.eAY j) :=
  algebraDiagramEvaluation_preservesFiniteLimits p.AY j

/-- Exactness of the constant evaluation with its original coefficient-ring codomain.
Source: Stacks 07A6
(blueprint: lem-pur-algebra-diagram-evaluation-adjunction-normalization). -/
instance eAY_colimits (j : J) : PreservesFiniteColimits (p.eAY j) :=
  algebraDiagramEvaluation_preservesFiniteColimits p.AY j


/-- Exactness of coefficient restriction, inherited from the concrete functor.
Source: Stacks 0D6E (blueprint: lem-pur-algebra-diagram-evaluation-adjunction-normalization). -/
instance rX_additive : p.rX.Additive := inferInstanceAs
  (SheafOfModules.restrictScalars.{u} p.aX).Additive
/-- Exactness of coefficient restriction.
Source: Stacks 0D6E (blueprint: lem-pur-algebra-diagram-evaluation-adjunction-normalization). -/
instance rY_additive : p.rY.Additive := inferInstanceAs
  (SheafOfModules.restrictScalars.{u} p.aY).Additive
/-- Exactness of coefficient restriction.
Source: Stacks 0D6E (blueprint: lem-pur-algebra-diagram-evaluation-adjunction-normalization). -/
instance rX_limits : PreservesFiniteLimits p.rX :=
  algebraDiagramRestriction_preservesFiniteLimits p.aX
/-- Exactness of coefficient restriction.
Source: Stacks 0D6E (blueprint: lem-pur-algebra-diagram-evaluation-adjunction-normalization). -/
instance rY_limits : PreservesFiniteLimits p.rY :=
  algebraDiagramRestriction_preservesFiniteLimits p.aY
/-- Exactness of coefficient restriction.
Source: Stacks 0D6E (blueprint: lem-pur-algebra-diagram-evaluation-adjunction-normalization). -/
instance rX_colimits : PreservesFiniteColimits p.rX :=
  algebraDiagramRestriction_preservesFiniteColimits p.aX
/-- Exactness of coefficient restriction.
Source: Stacks 0D6E (blueprint: lem-pur-algebra-diagram-evaluation-adjunction-normalization). -/
instance rY_colimits : PreservesFiniteColimits p.rY :=
  algebraDiagramRestriction_preservesFiniteColimits p.aY

variable [HasDerivedCategory.{w} (ringedSiteModules.{u} p.BX)]
    [HasDerivedCategory.{w} (ringedSiteModules.{u} p.BY)]
    [HasDerivedCategory.{w} (ringedSiteModules.{u} p.AX)]
    [HasDerivedCategory.{w} (ringedSiteModules.{u} p.AY)]
    [HasDerivedCategory.{w} (ringedSiteModules.{u} (algebraDiagramConstantRing K A))]
    [HasDerivedCategory.{w} (ringedSiteModules.{u} (algebraDiagramConstantRing L A))]
    [∀ j : J, HasDerivedCategory.{w} (ringedSiteModules.{u} (algebraDiagramRingAt p.BX j))]
    [∀ j : J, HasDerivedCategory.{w} (ringedSiteModules.{u} (algebraDiagramRingAt p.BY j))]

/-- The canonical derived functor or adjunction induced from the specified module adjunction.
Source: Stacks 07A6 
(blueprint: lem-pur-algebra-diagram-evaluation-adjunction-normalization). -/
abbrev PB := p.fB.modules.rightDerivedFunctor

/-- The canonical derived functor or adjunction induced from the specified module adjunction.
Source: Stacks 07A6 
(blueprint: lem-pur-algebra-diagram-evaluation-adjunction-normalization). -/
abbrev PA := p.fA.modules.rightDerivedFunctor

/-- The canonical derived functor or adjunction induced from the specified module adjunction.
Source: Stacks 07A6 
(blueprint: lem-pur-algebra-diagram-evaluation-adjunction-normalization). -/
abbrev P := p.s.modules.rightDerivedFunctor

/-- The canonical derived functor or adjunction induced from the specified module adjunction.
Source: Stacks 07A6 
(blueprint: lem-pur-algebra-diagram-evaluation-adjunction-normalization). -/
abbrev Pj (j : J) := (p.fj j).modules.rightDerivedFunctor

/-- The canonical derived functor or adjunction induced from the specified module adjunction.
Source: Stacks 07A6 
(blueprint: lem-pur-algebra-diagram-evaluation-adjunction-normalization). -/
abbrev GB := p.pullB.mapDerivedCategory

/-- The canonical derived functor or adjunction induced from the specified module adjunction.
Source: Stacks 07A6 
(blueprint: lem-pur-algebra-diagram-evaluation-adjunction-normalization). -/
abbrev Gj (j : J) := (p.pullj j).mapDerivedCategory

/-- The canonical derived functor or adjunction induced from the specified module adjunction.
Source: Stacks 07A6 
(blueprint: lem-pur-algebra-diagram-evaluation-adjunction-normalization). -/
abbrev adjDB := p.moduleAdjB.mapDerivedCategoryRightDerivedAdjunction

/-- The canonical derived functor or adjunction induced from the specified module adjunction.
Source: Stacks 07A6 
(blueprint: lem-pur-algebra-diagram-evaluation-adjunction-normalization). -/
abbrev adjDj (j : J) := (p.moduleAdjj j).mapDerivedCategoryRightDerivedAdjunction

attribute [local irreducible] Functor.rightDerivedFunctor Functor.mapDerivedCategory
  Functor.mapDerivedCategoryCompIso

attribute [-instance] algebraDiagramConstantDerivedAt
  algebraDiagramConstantEvaluation_additive algebraDiagramConstantEvaluation_limits
  algebraDiagramConstantEvaluation_colimits

/-- The full evaluation-adjunction coherence assertion, with its explicit ordinary
and derived comparison normalizations. The internal instance bindings only transport
exactness to the definitionally identical constant-ring slice presentations.
Source: Stacks 07A6 and 0D6E
(blueprint: lem-pur-algebra-diagram-evaluation-adjunction-normalization). -/
def EvaluationAdjunctionNormalization : Prop :=
  letI : ∀ j : J, HasDerivedCategory.{w}
      (ringedSiteModules.{u} (algebraDiagramRingAt p.AX j)) :=
    fun j ↦ algebraDiagramConstantDerivedAt (algebraDiagramConstantRing K A) j
  letI : ∀ j : J, HasDerivedCategory.{w}
      (ringedSiteModules.{u} (algebraDiagramRingAt p.AY j)) :=
    fun j ↦ algebraDiagramConstantDerivedAt (algebraDiagramConstantRing L A) j
  letI : ∀ j : J, (p.eAX j).Additive := p.eAX_additive
  letI : ∀ j : J, (p.eAY j).Additive := p.eAY_additive
  letI : ∀ j : J, PreservesFiniteLimits (p.eAX j) := p.eAX_limits
  letI : ∀ j : J, PreservesFiniteLimits (p.eAY j) := p.eAY_limits
  letI : ∀ j : J, PreservesFiniteColimits (p.eAX j) := p.eAX_colimits
  letI : ∀ j : J, PreservesFiniteColimits (p.eAY j) := p.eAY_colimits
    ∃ (c : p.fB.modules ⋙ p.rY ≅ p.rX ⋙ p.fA.modules)
      (d : p.PB ⋙ p.rY.mapDerivedCategory ≅ p.rX.mapDerivedCategory ⋙ p.PA)
      (cB : ∀ j : J, p.fB.modules ⋙ p.eBY j ≅ p.eBX j ⋙
              (p.fj j).modules)
      (cA : ∀ j : J, p.fA.modules ⋙ p.eAY j ≅ p.eAX j ⋙ p.s.modules)
      (lambda0 : ∀ j : J, p.pullB ⋙ p.eBX j ≅ p.eBY j ⋙ p.pullj j)
      (beta : ∀ j : J, p.PB ⋙ (p.eBY j).mapDerivedCategory ≅
        (p.eBX j).mapDerivedCategory ⋙ p.Pj j)
      (delta : ∀ j : J, p.PA ⋙ (p.eAY j).mapDerivedCategory ≅
        (p.eAX j).mapDerivedCategory ⋙ p.P)
      (cj : ∀ j : J, (p.fj j).modules ⋙ p.rYj j ≅ p.rXj j ⋙ p.s.modules)
      (dj : ∀ j : J, p.Pj j ⋙ (p.rYj j).mapDerivedCategory ≅
        (p.rXj j).mapDerivedCategory ⋙
              p.P),
      AlgebraDiagramOrdinaryRestrictionNormalized p.aX p.aY p.fB p.fA
        (p.directB.trans p.directA.symm) c ∧
      AlgebraDiagramDerivedSquareNormalized p.fB.modules p.fA.modules p.rX p.rY c d ∧
      (∀ j : J,
        AlgebraDiagramOrdinaryEvaluationNormalized p.s.direct p.fB j (p.fj j)
          p.directB (p.directLevel j) (cB j) ∧
        AlgebraDiagramOrdinaryEvaluationNormalized p.s.direct p.fA j p.s
          p.directA rfl (cA j) ∧
        AlgebraDiagramOrdinaryRestrictionNormalized
          (algebraDiagramCoefficientAt p.aX j) (algebraDiagramCoefficientAt p.aY j)
          (p.fj j) p.s (p.directLevel j) (cj j) ∧
        AlgebraDiagramDerivedSquareNormalized p.fB.modules (p.fj j).modules
          (p.eBX j) (p.eBY j) (cB j) (beta j) ∧
        AlgebraDiagramDerivedSquareNormalized p.fA.modules p.s.modules
          (p.eAX j) (p.eAY j) (cA j) (delta j) ∧
        AlgebraDiagramDerivedSquareNormalized (p.fj j).modules p.s.modules
          (p.rXj j) (p.rYj j) (cj j) (dj j) ∧
        (∀ N : ringedSiteModules.{u} p.BX,
          (p.eBX j).map (p.moduleAdjB.counit.app N) =
            (lambda0 j).hom.app (p.fB.modules.obj N) ≫
              (p.pullj j).map ((cB j).hom.app N) ≫
              (p.moduleAdjj j).counit.app ((p.eBX j).obj N)) ∧
        (∀ N : DerivedCategory (ringedSiteModules.{u} p.BX),
          (p.eBX j).mapDerivedCategory.map (p.adjDB.counit.app N) =
            (Functor.mapDerivedCategorySquareIso (lambda0 j)).hom.app (p.PB.obj N) ≫
              (p.Gj j).map ((beta j).hom.app N) ≫
              (p.adjDj j).counit.app ((p.eBX j).mapDerivedCategory.obj N)) ∧
        (∀ (M : DerivedCategory (ringedSiteModules.{u} p.BY))
          (N : DerivedCategory (ringedSiteModules.{u} p.BX)) (t : M ⟶ p.PB.obj N),
          ((p.adjDj j).homEquiv ((p.eBY j).mapDerivedCategory.obj M)
            ((p.eBX j).mapDerivedCategory.obj N)).symm
              ((p.eBY j).mapDerivedCategory.map t ≫ (beta j).hom.app N) =
            (Functor.mapDerivedCategorySquareIso (lambda0 j)).inv.app M ≫
              (p.eBX j).mapDerivedCategory.map ((p.adjDB.homEquiv M N).symm t)) ∧
        (∀ N : DerivedCategory (ringedSiteModules.{u} p.BX),
          (p.eAY j).mapDerivedCategory.map (d.hom.app N) ≫
              (delta j).hom.app (p.rX.mapDerivedCategory.obj N) ≫
              p.P.map
                ((Functor.mapDerivedCategorySquareIso
                  (algebraDiagramRestrictionEvaluation p.aX j)).hom.app N) =
            (Functor.mapDerivedCategorySquareIso
                (algebraDiagramRestrictionEvaluation p.aY j)).hom.app (p.PB.obj N) ≫
              (p.rYj j).mapDerivedCategory.map ((beta j).hom.app N) ≫
              (dj j).hom.app ((p.eBX j).mapDerivedCategory.obj N))) ∧
      (∀ (j k : J) (a : j ⟶ k),
        ∃ (ca : (p.fj k).modules ⋙
              (SheafOfModules.restrictScalars.{u} (algebraDiagramRingArrow p.BY a)) ≅
            (SheafOfModules.restrictScalars.{u} (algebraDiagramRingArrow p.BX a)) ⋙
              (p.fj j).modules)
          (qa : p.Pj k ⋙
              (SheafOfModules.restrictScalars.{u}
                (algebraDiagramRingArrow p.BY a)).mapDerivedCategory ≅
            (SheafOfModules.restrictScalars.{u}
              (algebraDiagramRingArrow p.BX a)).mapDerivedCategory ⋙
              p.Pj j),
          AlgebraDiagramOrdinaryRestrictionNormalized
            (algebraDiagramRingArrow p.BX a) (algebraDiagramRingArrow p.BY a)
            (p.fj k) (p.fj j) (p.directLevel k |>.trans (p.directLevel j).symm) ca ∧
          AlgebraDiagramDerivedSquareNormalized (p.fj k).modules (p.fj j).modules
            (SheafOfModules.restrictScalars.{u} (algebraDiagramRingArrow p.BX a))
            (SheafOfModules.restrictScalars.{u} (algebraDiagramRingArrow p.BY a)) ca qa ∧
          ∀ N : DerivedCategory (ringedSiteModules.{u} p.BX),
            (algebraDiagramDerivedTransition p.BY a).app (p.PB.obj N) ≫
                (SheafOfModules.restrictScalars.{u}
                  (algebraDiagramRingArrow p.BY a)).mapDerivedCategory.map
                  ((beta k).hom.app N) ≫
                qa.hom.app ((p.eBX k).mapDerivedCategory.obj N) =
              (beta j).hom.app N ≫
                (p.Pj j).map ((algebraDiagramDerivedTransition p.BX a).app N)) ∧
      (∀ (j k : J) (a : j ⟶ k),
        ∃ (ca : p.s.modules ⋙
              (SheafOfModules.restrictScalars.{u} (algebraDiagramRingArrow p.AY a)) ≅
            (SheafOfModules.restrictScalars.{u} (algebraDiagramRingArrow p.AX a)) ⋙ p.s.modules)
          (qa : p.P ⋙
              (SheafOfModules.restrictScalars.{u}
                (algebraDiagramRingArrow p.AY a)).mapDerivedCategory ≅
            (SheafOfModules.restrictScalars.{u}
              (algebraDiagramRingArrow p.AX a)).mapDerivedCategory ⋙
              p.P),
          AlgebraDiagramOrdinaryRestrictionNormalized
            (algebraDiagramRingArrow p.AX a) (algebraDiagramRingArrow p.AY a)
            p.s p.s rfl ca ∧
          AlgebraDiagramDerivedSquareNormalized p.s.modules p.s.modules
            (SheafOfModules.restrictScalars.{u} (algebraDiagramRingArrow p.AX a))
            (SheafOfModules.restrictScalars.{u} (algebraDiagramRingArrow p.AY a)) ca qa ∧
          ∀ N : DerivedCategory (ringedSiteModules.{u} p.AX),
            (algebraDiagramDerivedTransition p.AY a).app (p.PA.obj N) ≫
                (SheafOfModules.restrictScalars.{u}
                  (algebraDiagramRingArrow p.AY a)).mapDerivedCategory.map
                  ((delta k).hom.app N) ≫
                qa.hom.app ((p.eAX k).mapDerivedCategory.obj N) =
              (delta j).hom.app N ≫
                p.P.map ((algebraDiagramDerivedTransition p.AX a).app N))

attribute [instance] algebraDiagramConstantDerivedAt
  algebraDiagramConstantEvaluation_additive algebraDiagramConstantEvaluation_limits
  algebraDiagramConstantEvaluation_colimits

end AlgebraDiagramAdjunctionPresentation

end CategoryTheory
