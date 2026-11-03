/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import WeilConjectures.AlgebraicGeometry.Abelian.AbelianEtaleProEtaleCohomologyComparison
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.ProEtaleComparisonPullbackSections
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.CategoryTheory.Sites.Over
import WeilConjectures.Algebra.Homology.LiftToInjectiveUniqueUpToHomotopy
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import WeilConjectures.CategoryTheory.Curve.OverPullbackAdjunctionMono
import WeilConjectures.CategoryTheory.Sites.CohomologyRightDerivedSections
import WeilConjectures.AlgebraicGeometry.SiteRestrictionInjectives
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import WeilConjectures.AlgebraicGeometry.DerivedEtaleCohomologyLimit
import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.AlgebraicGeometry.ProEtaleQcqsFiniteFamilyGeometry
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.ProperBaseChange.ModuleAbelianEvaluationComparison
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresAbelian
import WeilConjectures.AlgebraicGeometry.SiteRestrictionExact
import WeilConjectures.SmoothPurity.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.CategoryTheory.Abelian.RightDerived.LongExactSequence
import WeilConjectures.AlgebraicGeometry.Classical.ClassicalContinuityMapSupplement
import WeilConjectures.CategoryTheory.ProEtaleCoefficients.InjectiveComplexSliceSectionModel
import WeilConjectures.CategoryTheory.Constant.ConstantLeftModuleTransportSupplement
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Homology.DerivedCategory.Plus
import Mathlib.Algebra.Homology.CochainComplexPlus
import WeilConjectures.CategoryTheory.Constant.ConstantLeftModuleInverseImageCoherence
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.LeftModuleDerivedEvaluation.LeftModuleDerivedEvaluationForget
import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageRestriction
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Mathlib.CategoryTheory.Limits.Cones
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic

/-!
# Cohomology of a pro-etale affine presentation

Source: blueprint main-20261015, sec-proetale-coefficients/sk-prop-sf-comparison,
Pro-etale cohomology of a pro-etale affine; Stacks Tags 099W and 0GIT
(blueprint: det-sf-comparison-affine-continuity).

Fixed-coefficient sheaves are encoded as sheaves valued in `ModuleCat Λ`, as in
`Scheme.proEtaleSiteComparisonModules`. This encoding permits arbitrary unital rings
and left modules. All maps below are units of the recorded inverse-image adjunctions
and restrictions of sheaves, with no choices of comparison maps.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

set_option backward.isDefEq.respectTransparency false in
/-- Base change of all presentation projections, regarded as a cone with terminal vertex.
Source: blueprint, restriction to the limiting scheme
(blueprint: def-pe-affine-continuity-etale-cone). -/
def affineContinuityEtaleCone {I : Type u} [SmallCategory I] {X : Scheme.{u}}
    (D : I ⥤ X.Etale) (c : Cone (D ⋙ Scheme.toProEt X)) :
    Cone (D ⋙ MorphismProperty.Over.pullback @Etale ⊤ c.pt.hom) where
  pt := Scheme.Etale.mk (𝟙 c.pt.left)
  π :=
    { app := fun i ↦ MorphismProperty.Over.homMk
        (pullback.lift (c.π.app i).left (𝟙 c.pt.left)
          ((MorphismProperty.Over.w (c.π.app i)).trans (Category.id_comp _).symm))
        (by simp)
      naturality := fun i j f ↦ by
        -- Equality on the two pullback projections reduces to the original cone equation
        -- and the identity of the limiting scheme, respectively.
        apply MorphismProperty.Over.Hom.ext
        apply pullback.hom_ext
        · dsimp
          have h := congrArg (fun g ↦ g.left) (c.w f).symm
          change (c.π.app j).left = (c.π.app i).left ≫ (D.map f).left at h
          simpa using h
        · simp }

/-- Section pullback to the limiting etale scheme, before taking any colimit.
Source: blueprint, the canonical continuity cocone
(blueprint: det-sf-comparison-affine-continuity). -/
def affineContinuityEtaleUnit {Λ : Type (u + 1)} [Ring Λ] {X U : Scheme.{u}}
    (f : U ⟶ X) (L : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ) :
    (((sheafToPresheaf _ (ModuleCat.{u + 1} Λ)).mapHomologicalComplex (.up ℤ)).obj L).asFunctor ⟶
      (MorphismProperty.Over.pullback @Etale ⊤ f).op ⋙
        (((sheafToPresheaf _ (ModuleCat.{u + 1} Λ)).mapHomologicalComplex (.up ℤ)).obj
          (((Etale.upperStar (ModuleCat.{u + 1} Λ) f).mapHomologicalComplex
            (.up ℤ)).obj L)).asFunctor where
  app V :=
    { f := fun n ↦ ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).unit.app
        (L.X n)).hom.app V
      comm' := fun i j _ ↦ by
        exact congrArg (fun g ↦ g.hom.app V)
          ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).unit.naturality
            (L.d i j)).symm }
  naturality := fun V W g ↦ by
    apply HomologicalComplex.Hom.ext
    funext n
    exact ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).unit.app
      (L.X n)).hom.naturality g

/-- Section pullback to the pro-etale site, before taking any colimit.
Source: blueprint, comparison inverse image
(blueprint: det-sf-comparison-affine-continuity). -/
def affineContinuityProEtaleUnit {Λ : Type (u + 1)} [Ring Λ] (X : Scheme.{u})
    (L : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ) :
    (((sheafToPresheaf _ (ModuleCat.{u + 1} Λ)).mapHomologicalComplex (.up ℤ)).obj L).asFunctor ⟶
      (Scheme.toProEt X).op ⋙
      (((sheafToPresheaf _ (ModuleCat.{u + 1} Λ)).mapHomologicalComplex (.up ℤ)).obj
        (((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapHomologicalComplex
          (.up ℤ)).obj L)).asFunctor
    where
  app V :=
    { f := fun n ↦ ((comparisonAdjunction (ModuleCat.{u + 1} Λ) X).unit.app
        (L.X n)).hom.app V
      comm' := fun i j _ ↦ by
        exact congrArg (fun g ↦ g.hom.app V)
          ((comparisonAdjunction (ModuleCat.{u + 1} Λ) X).unit.naturality (L.d i j)).symm }
  naturality := fun V W g ↦ by
    apply HomologicalComplex.Hom.ext
    funext n
    exact ((comparisonAdjunction (ModuleCat.{u + 1} Λ) X).unit.app
      (L.X n)).hom.naturality g

/-- The strict diagram of stage section complexes, indexed by the opposite presentation.
Source: blueprint, definition of the filtered derived colimit
(blueprint: det-sf-comparison-affine-continuity). -/
def affineContinuityDiagram {I : Type u} [SmallCategory I] {X : Scheme.{u}}
    {Λ : Type (u + 1)} [Ring Λ] (D : I ⥤ X.Etale)
    (L : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ) :=
  D.op ⋙ (((sheafToPresheaf _ (ModuleCat.{u + 1} Λ)).mapHomologicalComplex (.up ℤ)).obj L).asFunctor

/-- The canonical cocone to sections on the limiting etale scheme.
Source: blueprint, first displayed arrow
(blueprint: det-sf-comparison-affine-continuity). -/
def affineContinuityEtaleCocone {I : Type u} [SmallCategory I] {X : Scheme.{u}}
    {Λ : Type (u + 1)} [Ring Λ] (D : I ⥤ X.Etale)
    (c : Cone (D ⋙ Scheme.toProEt X))
    (L : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ) :
    Cocone (affineContinuityDiagram D L) :=
  (Cocone.precompose (Functor.whiskerLeft D.op (affineContinuityEtaleUnit c.pt.hom L))).obj
    (((((sheafToPresheaf _ (ModuleCat.{u + 1} Λ)).mapHomologicalComplex (.up ℤ)).obj
      (((Etale.upperStar (ModuleCat.{u + 1} Λ) c.pt.hom).mapHomologicalComplex
        (.up ℤ)).obj L)).asFunctor).mapCocone
        ((affineContinuityEtaleCone D c).op))

/-- The canonical cocone to pro-etale sections: comparison unit followed by restriction
along the given projections. Its legs are actual maps of complexes.
Source: blueprint, composite of the displayed arrows
(blueprint: det-sf-comparison-affine-continuity). -/
def affineContinuityProEtaleCocone {I : Type u} [SmallCategory I] {X : Scheme.{u}}
    {Λ : Type (u + 1)} [Ring Λ] (D : I ⥤ X.Etale)
    (c : Cone (D ⋙ Scheme.toProEt X))
    (L : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ) :
    Cocone (affineContinuityDiagram D L) :=
  (Cocone.precompose (Functor.whiskerLeft D.op (affineContinuityProEtaleUnit X L))).obj
    (((((sheafToPresheaf _ (ModuleCat.{u + 1} Λ)).mapHomologicalComplex (.up ℤ)).obj
      (((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapHomologicalComplex
        (.up ℤ)).obj L)).asFunctor).mapCocone c.op)

/-- The canonical map from a section complex to its right-derived evaluation.
It is the unit of the right derived functor, with the quotient factorizations made explicit.
Source: blueprint, acyclic-resolution interpretation of sections
(blueprint: det-sf-comparison-affine-continuity). -/
def affineContinuityDerivedUnit {C : Type (u + 1)} [Category.{u} C]
    {J : GrothendieckTopology C} {Λ : Type (u + 1)} [Ring Λ]
    [HasSheafify J (ModuleCat.{u + 1} Λ)]
    [HasDerivedCategory.{u + 1} (Sheaf J (ModuleCat.{u + 1} Λ))]
    [Abelian.HasKInjectiveResolutions (Sheaf J (ModuleCat.{u + 1} Λ))] (V : C)
    (L : CochainComplex (Sheaf J (ModuleCat.{u + 1} Λ)) ℤ) :
    DerivedCategory.Q.obj
      (((((sheafToPresheaf _ (ModuleCat.{u + 1} Λ)).mapHomologicalComplex
        (.up ℤ)).obj L).asFunctor).obj (op V)) ⟶
      ((sheafSections J (ModuleCat.{u + 1} Λ)).obj (op V)).rightDerivedFunctor.obj
        (DerivedCategory.Q.obj L) :=
  (DerivedCategory.quotientCompQhIso (ModuleCat.{u + 1} Λ)).inv.app _ ≫
    (((sheafSections J (ModuleCat.{u + 1} Λ)).obj (op V)).rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ _).obj L)) ≫
    ((sheafSections J (ModuleCat.{u + 1} Λ)).obj (op V)).rightDerivedFunctor.map
      ((DerivedCategory.quotientCompQhIso _).hom.app L)

/-- Derived evaluation after an exact inverse image, normalized on the given representative.
Source: blueprint, definition of the two derived section objects
(blueprint: det-sf-comparison-affine-continuity). -/
def affineContinuityTargetComparison
    {C B : Type (u + 1)} [Category.{u} C] [Category.{u} B]
    {JC : GrothendieckTopology C} {JB : GrothendieckTopology B}
    {Λ : Type (u + 1)} [Ring Λ]
    [HasSheafify JC (ModuleCat.{u + 1} Λ)] [HasSheafify JB (ModuleCat.{u + 1} Λ)]
    [HasDerivedCategory.{u + 1} (Sheaf JC (ModuleCat.{u + 1} Λ))]
    [HasDerivedCategory.{u + 1} (Sheaf JB (ModuleCat.{u + 1} Λ))]
    [Abelian.HasKInjectiveResolutions (Sheaf JB (ModuleCat.{u + 1} Λ))]
    (F : Sheaf JC (ModuleCat.{u + 1} Λ) ⥤ Sheaf JB (ModuleCat.{u + 1} Λ))
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] (V : B)
    (K : DerivedCategory (Sheaf JC (ModuleCat.{u + 1} Λ)))
    (L : CochainComplex (Sheaf JC (ModuleCat.{u + 1} Λ)) ℤ)
    (e : DerivedCategory.Q.obj L ≅ K) :
    DerivedCategory.Q.obj
      (((((sheafToPresheaf _ (ModuleCat.{u + 1} Λ)).mapHomologicalComplex (.up ℤ)).obj
        ((F.mapHomologicalComplex (.up ℤ)).obj L)).asFunctor).obj
        (op V)) ⟶
      ((sheafSections JB (ModuleCat.{u + 1} Λ)).obj (op V)).rightDerivedFunctor.obj
        (F.mapDerivedCategory.obj K) :=
  affineContinuityDerivedUnit V ((F.mapHomologicalComplex (.up ℤ)).obj L) ≫
    ((sheafSections JB (ModuleCat.{u + 1} Λ)).obj (op V)).rightDerivedFunctor.map
      (F.mapDerivedCategoryFactors.inv.app L ≫ F.mapDerivedCategory.map e.hom)

/-- The canonical map from sections over an etale object to sections of its inverse image.
The arrow in the base-changed site is the diagonal into the fibre product.
Source: blueprint, the meaning of each stage section complex
(blueprint: det-sf-comparison-affine-continuity). -/
def affineContinuityStageRestriction {Λ : Type (u + 1)} [Ring Λ] {X : Scheme.{u}}
    (V : X.Etale)
    (L : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ) :
    ((((sheafToPresheaf _ (ModuleCat.{u + 1} Λ)).mapHomologicalComplex
      (.up ℤ)).obj L).asFunctor).obj (op V) ⟶
      ((((sheafToPresheaf _ (ModuleCat.{u + 1} Λ)).mapHomologicalComplex (.up ℤ)).obj
        (((Etale.upperStar (ModuleCat.{u + 1} Λ) V.hom).mapHomologicalComplex
          (.up ℤ)).obj L)).asFunctor).obj
          (op (Scheme.Etale.mk (𝟙 V.left))) :=
  (affineContinuityEtaleUnit V.hom L).app (op V) ≫
    ((((sheafToPresheaf _ (ModuleCat.{u + 1} Λ)).mapHomologicalComplex (.up ℤ)).obj
        (((Etale.upperStar (ModuleCat.{u + 1} Λ) V.hom).mapHomologicalComplex
          (.up ℤ)).obj L)).asFunctor).map
        (MorphismProperty.Over.homMk
          (pullback.lift (𝟙 V.left) (𝟙 V.left) (by simp)) (by simp) :
          Scheme.Etale.mk (𝟙 V.left) ⟶
            (MorphismProperty.Over.pullback @Etale ⊤ V.hom).obj V).op

/-- The first canonical derived continuity arrow, constructed on the strict section diagram.
Source: blueprint, first displayed arrow
(blueprint: det-sf-comparison-affine-continuity). -/
def affineContinuityEtaleMap {I : Type u} [SmallCategory I] {X : Scheme.{u}}
    {Λ : Type (u + 1)} [Ring Λ] (D : I ⥤ X.Etale)
    (c : Cone (D ⋙ Scheme.toProEt X))
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ)
    (e : DerivedCategory.Q.obj L ≅ K) :=
  DerivedCategory.Q.map (colimit.desc _ (affineContinuityEtaleCocone D c L)) ≫
    affineContinuityTargetComparison (Etale.upperStar (ModuleCat.{u + 1} Λ) c.pt.hom)
      (Scheme.Etale.mk (𝟙 c.pt.left)) K L e

/-- The canonical derived arrow to pro-etale sections. On every stage it is comparison
inverse image followed by restriction along the specified projection, then derived evaluation.
Source: blueprint, composite of the displayed arrows
(blueprint: det-sf-comparison-affine-continuity). -/
def affineContinuityProEtaleMap {I : Type u} [SmallCategory I] {X : Scheme.{u}}
    {Λ : Type (u + 1)} [Ring Λ] (D : I ⥤ X.Etale)
    (c : Cone (D ⋙ Scheme.toProEt X))
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ)
    (e : DerivedCategory.Q.obj L ≅ K) :=
  DerivedCategory.Q.map (colimit.desc _ (affineContinuityProEtaleCocone D c L)) ≫
    affineContinuityTargetComparison (comparisonUpperStar (ModuleCat.{u + 1} Λ) X)
      c.pt K L e

private theorem stageSection_isIso {Λ : Type (u + 1)} [Ring Λ] {X : Scheme.{u}}
    (V : X.Etale) (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso (((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) V.hom).unit.app F).hom.app
      (op V) ≫
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) V.hom).obj F).obj.map
        (MorphismProperty.Over.homMk
          (pullback.lift (𝟙 V.left) (𝟙 V.left) (by simp)) (by simp) :
          Scheme.Etale.mk (𝟙 V.left) ⟶
            (MorphismProperty.Over.pullback @Etale ⊤ V.hom).obj V).op) := by
  let α := Etale.upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} Λ) V.hom V.prop
  let T := Scheme.Etale.mk (𝟙 V.left)
  let g : T ⟶ (MorphismProperty.Over.pullback @Etale ⊤ V.hom).obj V :=
    MorphismProperty.Over.homMk
      (pullback.lift (𝟙 V.left) (𝟙 V.left) (by simp [T])) (by simp [T])
  have hunit := Adjunction.unit_leftAdjointUniq_hom_app
    (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) V.hom)
    (Etale.localizationRestrictionLowerStarAdjunction (ModuleCat.{u + 1} Λ) V.hom V.prop) F
  have h := congrArg (fun f ↦ f.hom.app (op V)) hunit
  change _ ≫ (α.hom.app F).hom.app _ = _ at h
  have hnat := (α.hom.app F).hom.naturality g.op
  have heq :
      (((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) V.hom).unit.app F).hom.app
        (op V) ≫ ((Etale.upperStar (ModuleCat.{u + 1} Λ) V.hom).obj F).obj.map g.op) ≫
          (α.hom.app F).hom.app (op T) =
      F.obj.map (MorphismProperty.Over.homMk (𝟙 V.left) (by simp [T]) :
        (MorphismProperty.Over.map ⊤ V.prop).obj T ⟶ V).op := by
    rw [Category.assoc, hnat, ← Category.assoc]
    erw [h]
    change F.obj.map _ ≫ F.obj.map _ = _
    rw [← F.obj.map_comp]
    congr 1
    apply Quiver.Hom.unop_inj
    apply MorphismProperty.Over.Hom.ext
    change pullback.lift (𝟙 V.left) (𝟙 V.left) _ ≫ pullback.fst V.hom V.hom = 𝟙 V.left
    simp
  have : IsIso (F.obj.map (MorphismProperty.Over.homMk (𝟙 V.left) (by simp [T]) :
      (MorphismProperty.Over.map ⊤ V.prop).obj T ⟶ V).op) := by
    have : IsIso (MorphismProperty.Over.homMk (𝟙 V.left) (by simp [T]) :
        (MorphismProperty.Over.map ⊤ V.prop).obj T ⟶ V) := by
      let G := MorphismProperty.Over.forget @Etale ⊤ X ⋙ Over.forget X
      have : IsIso (G.map (MorphismProperty.Over.homMk (𝟙 V.left) (by simp [T]) :
          (MorphismProperty.Over.map ⊤ V.prop).obj T ⟶ V)) := by
        change IsIso (𝟙 V.left)
        infer_instance
      exact isIso_of_reflects_iso _ G
    infer_instance
  have : IsIso (_ ≫ (α.hom.app F).hom.app (op T)) := heq ▸ this
  exact IsIso.of_isIso_comp_right _ ((α.hom.app F).hom.app (op T))

private theorem stageRestriction_isIso {Λ : Type (u + 1)} [Ring Λ] {X : Scheme.{u}}
    (V : X.Etale)
    (L : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ) :
    IsIso (affineContinuityStageRestriction V L) := by
  have (n : ℤ) : IsIso ((affineContinuityStageRestriction V L).f n) :=
    stageSection_isIso V (L.X n)
  exact HomologicalComplex.Hom.isIso_of_components _

private theorem derivedUnit_isIso_of_injective
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    {Λ : Type (u + 1)} [Ring Λ] [HasSheafify J (ModuleCat.{u + 1} Λ)]
    [HasDerivedCategory.{u + 1} (Sheaf J (ModuleCat.{u + 1} Λ))]
    [Abelian.HasKInjectiveResolutions (Sheaf J (ModuleCat.{u + 1} Λ))]
    (V : C) (L : CochainComplex (Sheaf J (ModuleCat.{u + 1} Λ)) ℤ)
    (a : ℤ) [L.IsStrictlyGE a] [∀ n : ℤ, Injective (L.X n)] :
    IsIso (affineContinuityDerivedUnit V L) := by
  have : L.IsKInjective := CochainComplex.isKInjective_of_injective L a
  unfold affineContinuityDerivedUnit
  infer_instance

private theorem derivedFunctorUnit_isIso_of_acyclic
    {C B : Type*} [Category.{u + 1} C] [Category.{u + 1} B] [Abelian C] [Abelian B]
    [HasDerivedCategory.{u + 1} C] [HasDerivedCategory.{u + 1} B]
    [Abelian.HasKInjectiveResolutions C] [EnoughInjectives C]
    (E : C ⥤ B) [E.Additive] [PreservesFiniteLimits E]
    (L : CochainComplex C ℤ) (a : ℤ) [L.IsStrictlyGE a]
    (hL : ∀ n, E.rightAcyclic (L.X n)) :
    IsIso (E.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj L)) := by
  let L' : CochainComplex.Plus C := ⟨L, a, inferInstance⟩
  obtain ⟨T, _, i, hi⟩ := CochainComplex.Plus.exists_quasiIso_injective L' a
  let T' := (InjectiveObject.ι C).mapCochainComplexPlus.obj T
  have : QuasiIso i.hom := hi
  have : ∀ n, Injective (T'.obj.X n) := fun n ↦ (T.obj.X n).2
  have : T'.obj.IsStrictlyGE a :=
    (CochainComplex.isStrictlyGE_mapHomologicalComplex_obj_iff _ _ _).2 ‹_›
  have := E.quasiIso_map_of_rightAcyclic i.hom a hL
    (fun n ↦ E.rightAcyclic_of_injective _)
  have h₁ : IsIso (DerivedCategory.Qh.map
      ((HomotopyCategory.quotient _ (.up ℤ)).map i.hom)) :=
    Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso _ _) _
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2
        ((HomologicalComplex.mem_quasiIso_iff _).2 inferInstance))
  have h₂ : IsIso ((E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh).map
      ((HomotopyCategory.quotient _ (.up ℤ)).map i.hom)) := by
    dsimp only [Functor.comp_map]
    rw [Functor.mapHomotopyCategory_map]
    exact Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso _ _) _
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2
        ((HomologicalComplex.mem_quasiIso_iff _).2 inferInstance))
  have : IsIso ((DerivedCategory.Qh ⋙ E.rightDerivedFunctor).map
      ((HomotopyCategory.quotient _ (.up ℤ)).map i.hom)) := by
    dsimp only [Functor.comp_map]
    infer_instance
  have : T'.obj.IsKInjective := CochainComplex.isKInjective_of_injective T'.obj a
  have : IsIso (E.rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj L)) := by
    exact IsIso.of_isIso_fac_right
      (h := (E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh).map
        ((HomotopyCategory.quotient _ (.up ℤ)).map i.hom) ≫ E.rightDerivedFunctorUnit.app _)
      (E.rightDerivedFunctorUnit.naturality _).symm
  exact this

private theorem derivedUnit_isIso_of_acyclic
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    {Λ : Type (u + 1)} [Ring Λ] [HasSheafify J (ModuleCat.{u + 1} Λ)]
    [HasDerivedCategory.{u + 1} (Sheaf J (ModuleCat.{u + 1} Λ))]
    [Abelian.HasKInjectiveResolutions (Sheaf J (ModuleCat.{u + 1} Λ))]
    [EnoughInjectives (Sheaf J (ModuleCat.{u + 1} Λ))]
    (V : C) (L : CochainComplex (Sheaf J (ModuleCat.{u + 1} Λ)) ℤ)
    (a : ℤ) [L.IsStrictlyGE a]
    (hL : ∀ n, ((sheafSections J (ModuleCat.{u + 1} Λ)).obj (op V)).rightAcyclic (L.X n)) :
    IsIso (affineContinuityDerivedUnit V L) := by
  let E := (sheafSections J (ModuleCat.{u + 1} Λ)).obj (op V)
  have : PreservesFiniteLimits E := by
    change PreservesFiniteLimits (sheafToPresheaf J (ModuleCat.{u + 1} Λ) ⋙
      (evaluation _ _).obj (op V))
    infer_instance
  have := derivedFunctorUnit_isIso_of_acyclic E L a hL
  unfold affineContinuityDerivedUnit
  infer_instance

private theorem limitEtale_rightAcyclic {I : Type u} [SmallCategory I] [IsCofiltered I]
    {X : Scheme.{u}} (A : Type*) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] (D : I ⥤ X.Etale)
    (c : Cone (D ⋙ Scheme.toProEt X))
    (hc : IsLimit ((Scheme.ProEt.forget X ⋙ Over.forget X).mapCone c))
    [∀ i : I, IsAffine (D.obj i).left]
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f).left]
    (F : Sheaf X.smallEtaleTopology A) [Injective F] :
    (Etale.sectionsFunctor A c.pt.left).rightAcyclic
      ((Etale.upperStar A c.pt.hom).obj F) := by
  intro q
  have (i : I) : CompactSpace
      ((D ⋙ Scheme.toProEt X ⋙ Scheme.ProEt.forget X).obj i).left :=
    inferInstanceAs (CompactSpace (D.obj i).left)
  have (i : I) : QuasiSeparatedSpace
      ((D ⋙ Scheme.toProEt X ⋙ Scheme.ProEt.forget X).obj i).left :=
    inferInstanceAs (QuasiSeparatedSpace (D.obj i).left)
  have {i j : I} (g : i ⟶ j) : IsAffineHom
      ((D ⋙ Scheme.toProEt X ⋙ Scheme.ProEt.forget X).map g).left :=
    inferInstanceAs (IsAffineHom (D.map g).left)
  refine Etale.isZero_rightDerived_sectionsFunctor_upperStar_of_isLimit
    A F (D ⋙ Scheme.toProEt X ⋙ Scheme.ProEt.forget X)
    ((Scheme.ProEt.forget X).mapCone c) hc (q + 1) (fun i ↦ ?_)
  have : Injective ((Etale.upperStar A (D.obj i).hom).obj F) :=
    Etale.injective_upperStar_obj_of_etale' A (D.obj i).hom F
  change IsZero (((Etale.sectionsFunctor A
    (D.obj i).left).rightDerived (q + 1)).obj
      ((Etale.upperStar A (D.obj i).hom).obj F))
  exact Functor.isZero_rightDerived_obj_injective_succ _ _ _

private theorem limitProEtale_rightAcyclic {I : Type u} [SmallCategory I] [IsCofiltered I]
    {X : Scheme.{u}} (A : Type*) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] (D : I ⥤ X.Etale)
    (c : Cone (D ⋙ Scheme.toProEt X))
    (hc : IsLimit ((Scheme.ProEt.forget X ⋙ Over.forget X).mapCone c))
    [∀ i : I, IsAffine (D.obj i).left]
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f).left]
    (F : Sheaf X.smallEtaleTopology A) [Injective F] :
    (sectionsFunctor A c.pt).rightAcyclic
      ((comparisonUpperStar A X).obj F) := by
  intro q
  refine isZero_rightDerived_sectionsFunctor_of_upperStar A c.pt _ _ ?_
  refine IsZero.of_iso ?_
    (((globalSectionsFunctor A c.pt.left).rightDerived (q + 1)).mapIso
      ((comparisonUpperStarCompUpperStarIso A c.pt.hom).app F))
  exact isZero_rightDerived_globalSectionsFunctor_comparisonUpperStar_obj
    A c.pt.left _ _ (limitEtale_rightAcyclic A D c hc F q)

private theorem proEtaleCocone_isColimit {I : Type u} [SmallCategory I] [IsCofiltered I]
    {X : Scheme.{u}} {Λ : Type (u + 1)} [Ring Λ] (D : I ⥤ X.Etale)
    (c : Cone (D ⋙ Scheme.toProEt X))
    (hc : IsLimit ((Scheme.ProEt.forget X ⋙ Over.forget X).mapCone c))
    [∀ i : I, IsAffine (D.obj i).left]
    (L : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ) :
    Nonempty (IsColimit (affineContinuityProEtaleCocone D c L)) := by
  refine ⟨HomologicalComplex.isColimitOfEval _ _ (fun n ↦ ?_)⟩
  let hn := (isColimit_comparisonUpperStar_mapCocone_of_isAffine
    (ModuleCat.{u + 1} Λ) (L.X n) D c hc).some
  let e : D.op ⋙ (L.X n).obj ≅
      D.op ⋙ (Scheme.toProEt X).op ⋙
        ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).obj (L.X n)).obj :=
    Functor.isoWhiskerLeft D.op
      ((sheafToPresheaf _ _).mapIso (asIso
        ((comparisonAdjunction (ModuleCat.{u + 1} Λ) X).unit.app (L.X n))))
  exact (IsColimit.precomposeHomEquiv e _).symm hn

private noncomputable def sectionComparisonIso {Λ : Type (u + 1)} [Ring Λ]
    {X : Scheme.{u}} (U : X.ProEt) :
    Etale.upperStar (ModuleCat.{u + 1} Λ) U.hom ⋙
        Etale.sectionsFunctor (ModuleCat.{u + 1} Λ) U.left ≅
      comparisonUpperStar (ModuleCat.{u + 1} Λ) X ⋙
        sectionsFunctor (ModuleCat.{u + 1} Λ) U := by
  let A := ModuleCat.{u + 1} Λ
  let T := Scheme.ProEt.mk (𝟙 U.left)
  let r : U ≅ (MorphismProperty.Over.map ⊤ U.prop).obj T :=
    MorphismProperty.Over.isoMk (Iso.refl _) (by exact Category.id_comp _)
  let eΓ : ProEtale.localizationRestriction A U.hom U.prop ⋙
      globalSectionsFunctor A U.left ≅ sectionsFunctor A U :=
    NatIso.ofComponents (fun G ↦ G.obj.mapIso r.op)
      (fun φ ↦ (φ.hom.naturality r.hom.op).symm)
  let eν : Etale.sectionsFunctor A U.left ≅
      comparisonUpperStar A U.left ⋙ globalSectionsFunctor A U.left :=
    NatIso.ofComponents
      (fun F ↦ asIso (((comparisonAdjunction A U.left).unit.app F).hom.app
        (op (Scheme.Etale.mk (𝟙 U.left)))))
      (fun φ ↦ congrArg (fun f ↦ f.hom.app (op (Scheme.Etale.mk (𝟙 U.left))))
        ((comparisonAdjunction A U.left).unit.naturality φ))
  exact Functor.isoWhiskerLeft (Etale.upperStar A U.hom) eν ≪≫
    Functor.isoWhiskerRight (comparisonUpperStarCompUpperStarIso A U.hom).symm
      (globalSectionsFunctor A U.left) ≪≫
    Functor.isoWhiskerLeft (comparisonUpperStar A X)
      (Functor.isoWhiskerRight (ProEtale.upperStarIsoLocalizationRestriction A U.hom U.prop)
        (globalSectionsFunctor A U.left) ≪≫ eΓ)

private theorem proLocalizationUnit {Λ : Type (u + 1)} [Ring Λ]
    {X : Scheme.{u}} (U V : X.ProEt) (f : U ⟶ V)
    (G : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) :
    (((ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) U.hom).unit.app G).hom.app
      (op V) ≫
      ((ProEtale.upperStar (ModuleCat.{u + 1} Λ) U.hom).obj G).obj.map
        (MorphismProperty.Over.homMk
          (pullback.lift f.left (𝟙 U.left)
            ((MorphismProperty.Over.w f).trans (Category.id_comp _).symm))
          (by simp) : Scheme.ProEt.mk (𝟙 U.left) ⟶
            (MorphismProperty.Over.pullback @WeaklyEtale ⊤ U.hom).obj V).op) ≫
      ((ProEtale.upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} Λ)
        U.hom U.prop).hom.app G).hom.app (op (Scheme.ProEt.mk (𝟙 U.left))) ≫
      G.obj.map (MorphismProperty.Over.homMk (𝟙 U.left) (Category.id_comp _) :
        U ⟶ (MorphismProperty.Over.map ⊤ U.prop).obj
          (Scheme.ProEt.mk (𝟙 U.left))).op = G.obj.map f.op := by
  let α := ProEtale.upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} Λ) U.hom U.prop
  let T := Scheme.ProEt.mk (𝟙 U.left)
  let g : T ⟶ (MorphismProperty.Over.pullback @WeaklyEtale ⊤ U.hom).obj V :=
    MorphismProperty.Over.homMk
      (pullback.lift f.left (𝟙 U.left)
        ((MorphismProperty.Over.w f).trans (Category.id_comp _).symm)) (by simp [T])
  have hu := Adjunction.unit_leftAdjointUniq_hom_app
    (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) U.hom)
    (ProEtale.localizationRestrictionLowerStarAdjunction
      (ModuleCat.{u + 1} Λ) U.hom U.prop) G
  have h := congrArg (fun t ↦ t.hom.app (op V)) hu
  change _ ≫ (α.hom.app G).hom.app _ = _ at h
  have hn := (α.hom.app G).hom.naturality g.op
  have heq :
      (((ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) U.hom).unit.app G).hom.app
        (op V) ≫
        ((ProEtale.upperStar (ModuleCat.{u + 1} Λ) U.hom).obj G).obj.map g.op) ≫
        (α.hom.app G).hom.app (op T) =
      ((ProEtale.localizationRestrictionLowerStarAdjunction
        (ModuleCat.{u + 1} Λ) U.hom U.prop).unit.app G).hom.app
        (op V) ≫
        ((ProEtale.localizationRestriction (ModuleCat.{u + 1} Λ) U.hom U.prop).obj G).obj.map
          g.op := by
    rw [Category.assoc]
    erw [hn]
    rw [← Category.assoc]
    erw [h]
  change (((_ ≫ _) ≫ (α.hom.app G).hom.app (op T)) ≫ _) = _
  erw [heq]
  change (G.obj.map _ ≫ G.obj.map _) ≫ G.obj.map _ = _
  rw [← G.obj.map_comp, ← G.obj.map_comp]
  congr 1
  apply Quiver.Hom.unop_inj
  apply MorphismProperty.Over.Hom.ext
  change (𝟙 U.left ≫ pullback.lift f.left (𝟙 U.left) _) ≫
    pullback.fst V.hom U.hom = f.left
  simp

private theorem sectionComparisonIso_canonical {Λ : Type (u + 1)} [Ring Λ]
    {X : Scheme.{u}} (U : X.ProEt) (V : X.Etale)
    (f : U ⟶ (Scheme.toProEt X).obj V)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) U.hom).unit.app F).hom.app
        (op V) ≫
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) U.hom).obj F).obj.map
        (MorphismProperty.Over.homMk
          (pullback.lift f.left (𝟙 U.left)
            ((MorphismProperty.Over.w f).trans (Category.id_comp _).symm))
          (by simp) : Scheme.Etale.mk (𝟙 U.left) ⟶
            (MorphismProperty.Over.pullback @Etale ⊤ U.hom).obj V).op) ≫
      (sectionComparisonIso U).hom.app F =
    ((comparisonAdjunction (ModuleCat.{u + 1} Λ) X).unit.app F).hom.app (op V) ≫
      ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).obj F).obj.map f.op := by
  let A := ModuleCat.{u + 1} Λ
  let α := comparisonUpperStarCompUpperStarIso A U.hom
  let g : Scheme.Etale.mk (𝟙 U.left) ⟶
      (MorphismProperty.Over.pullback @Etale ⊤ U.hom).obj V :=
    MorphismProperty.Over.homMk
      (pullback.lift f.left (𝟙 U.left)
        ((MorphismProperty.Over.w f).trans (Category.id_comp _).symm)) (by simp)
  have hu := unit_conjugateEquiv_symm
    ((Etale.upperStarLowerStarAdjunction A U.hom).comp (comparisonAdjunction A U.left))
    ((comparisonAdjunction A X).comp (ProEtale.upperStarLowerStarAdjunction A U.hom))
    (lowerStarCompComparisonLowerStarIso U.hom A).inv F
  have h := congrArg (fun t ↦ t.hom.app (op V)) hu
  simp only [Adjunction.comp_unit_app, ObjectProperty.FullSubcategory.comp_hom,
    NatTrans.comp_app] at h
  have hα : ((conjugateEquiv
      ((Etale.upperStarLowerStarAdjunction A U.hom).comp (comparisonAdjunction A U.left))
      ((comparisonAdjunction A X).comp (ProEtale.upperStarLowerStarAdjunction A U.hom))).symm
        (lowerStarCompComparisonLowerStarIso U.hom A).inv).app F = α.hom.app F := rfl
  rw [hα] at h
  have hid : ((lowerStarCompComparisonLowerStarIso U.hom A).inv.app
      ((Etale.upperStar A U.hom ⋙ comparisonUpperStar A U.left).obj F)).hom.app (op V) =
      𝟙 _ := by
    simp only [lowerStarCompComparisonLowerStarIso, Functor.sheafPushforwardContinuousComp,
      Functor.sheafPushforwardContinuousIso, Functor.sheafPushforwardContinuousNatTrans,
      toProEtCompOverPullbackIso, Iso.trans_inv, Iso.symm_inv, Iso.refl_hom, Iso.refl_inv,
      NatTrans.comp_app, ObjectProperty.FullSubcategory.comp_hom, Functor.whiskerRight_app,
      NatTrans.op_app, NatIso.ofComponents_hom_app]
    change (𝟙 _ ≫ ((comparisonUpperStar A U.left).obj
      ((Etale.upperStar A U.hom).obj F)).obj.map (𝟙 _)) ≫ 𝟙 _ = 𝟙 _
    erw [((comparisonUpperStar A U.left).obj ((Etale.upperStar A U.hom).obj F)).obj.map_id]
    simp
  rw [hid] at h
  erw [Category.comp_id] at h
  change
    ((Etale.upperStarLowerStarAdjunction A U.hom).unit.app F).hom.app (op V) ≫
      ((comparisonAdjunction A U.left).unit.app
        ((Etale.upperStar A U.hom).obj F)).hom.app
          (op ((MorphismProperty.Over.pullback @Etale ⊤ U.hom).obj V)) =
    (((comparisonAdjunction A X).unit.app F).hom.app (op V) ≫
      ((ProEtale.upperStarLowerStarAdjunction A U.hom).unit.app
        ((comparisonUpperStar A X).obj F)).hom.app (op ((Scheme.toProEt X).obj V))) ≫
      (α.hom.app F).hom.app (op ((Scheme.toProEt U.left).obj
        ((MorphismProperty.Over.pullback @Etale ⊤ U.hom).obj V))) at h
  let H := (Etale.upperStar A U.hom).obj F
  let G := (comparisonUpperStar A X).obj F
  have hn := ((comparisonAdjunction A U.left).unit.app H).hom.naturality g.op
  have ha := (α.inv.app F).hom.naturality ((Scheme.toProEt U.left).map g).op
  change (_ ≫ H.obj.map g.op) ≫
    ((((comparisonAdjunction A U.left).unit.app H).hom.app
      (op (Scheme.Etale.mk (𝟙 U.left))) ≫
      (α.inv.app F).hom.app (op (Scheme.ProEt.mk (𝟙 U.left)))) ≫
      ((ProEtale.upperStarIsoLocalizationRestriction A U.hom U.prop).hom.app G).hom.app
        (op (Scheme.ProEt.mk (𝟙 U.left))) ≫
      G.obj.map (MorphismProperty.Over.homMk (𝟙 U.left) (Category.id_comp _) :
        U ⟶ (MorphismProperty.Over.map ⊤ U.prop).obj (Scheme.ProEt.mk (𝟙 U.left))).op) = _
  simp only [Category.assoc]
  erw [reassoc_of% hn]
  erw [reassoc_of% h]
  erw [reassoc_of% ha]
  have hinv := congrArg (fun t ↦ t.hom.app
    (op ((Scheme.toProEt U.left).obj
      ((MorphismProperty.Over.pullback @Etale ⊤ U.hom).obj V)))) (α.hom_inv_id_app F)
  change (α.hom.app F).hom.app _ ≫ (α.inv.app F).hom.app _ = 𝟙 _ at hinv
  erw [reassoc_of% hinv]
  exact congrArg (_ ≫ ·) (proLocalizationUnit U ((Scheme.toProEt X).obj V) f G)

private theorem etaleCocone_isColimit {I : Type u} [SmallCategory I] [IsCofiltered I]
    {X : Scheme.{u}} {Λ : Type (u + 1)} [Ring Λ] (D : I ⥤ X.Etale)
    (c : Cone (D ⋙ Scheme.toProEt X))
    (hc : IsLimit ((Scheme.ProEt.forget X ⋙ Over.forget X).mapCone c))
    [∀ i : I, IsAffine (D.obj i).left]
    (L : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ) :
    Nonempty (IsColimit (affineContinuityEtaleCocone D c L)) := by
  let e := (NatIso.mapHomologicalComplex (sectionComparisonIso (Λ := Λ) c.pt) (.up ℤ)).app L
  let h := (proEtaleCocone_isColimit D c hc L).some
  refine ⟨h.ofIsoColimit (Cocone.ext e.symm (fun j ↦ ?_))⟩
  apply (cancel_mono e.hom).1
  rw [Category.assoc]
  erw [e.inv_hom_id]
  erw [Category.comp_id]
  apply HomologicalComplex.Hom.ext
  funext n
  exact (sectionComparisonIso_canonical c.pt (D.obj j.unop) (c.π.app j.unop) (L.X n)).symm

/-- The two continuity arrows are isomorphisms, and every stage section complex computes
its specified derived sections. The displayed second arrow is the unique map whose composite
with `affineContinuityEtaleMap` is `affineContinuityProEtaleMap`: this fixes the canonical
comparison, including its maps on cohomology in every integer degree.

The source is the degreewise colimit of the strict diagram `L(U_i)`. Filtered colimits of
left modules are exact, so it is also the left-derived colimit of this same strict diagram,
and its cohomology is the colimit of the stage cohomologies. Evaluation at an object of the
ambient site is sections at the terminal object of its localized site. Thus the target of
the pro-etale arrow is precisely sections of `(ν_X^* K)|_U`, without an arbitrary choice of
a functor on derived stage objects or a comparison morphism.

Source: blueprint main-20261015, Pro-etale cohomology of a pro-etale affine;
Stacks Tags 099W and 0GIT (blueprint: det-sf-comparison-affine-continuity).

Proof:
1. Forget scalars using lem-weil-pbc-module-sheaves-colimits-forgetful and the evaluation
   comparison lem-weil-pbc-ringed-site-module-abelian-evaluation-comparison. Injective module
   sheaves are evaluation-acyclic after forgetting; no preservation of injectives is needed.
   Geometric inverse image transports addition and each scalar endomorphism and is exact by
   lem-weil-pbc-site-pullback-abelian-exact, also for a noncommutative coefficient ring.
2. Identify restriction to U using lem-weil-proetale-weakly-etale-localization,
   lem-cbc-comparison-pullback-sections and lem-weil-pbc-inverse-image-composition. These
   identify `(ν_X^* K)|_U` with `ν_U^* K_U`, naturally in addition and the scalar action.
3. Apply lem-cbc-abelian-etale-proetale-cohomology-comparison to each injective term on U.
   The terms of its inverse image are sections-acyclic; lemma-weil-pbc-leray-acyclicity
   therefore computes derived sections by their section complex. The resulting comparison
   is induced by the degree-zero section pullbacks.
4. Apply lem-weil-pbc-derived-etale-cohomology-limit with base X and the given presentation.
   Its affine stages are qcqs by lem-weil-pbc-proetale-qcqs-finite-family-geometry. This
   gives continuity in every integer degree, compatibly with all scalar endomorphisms.
5. Use the single bounded-below injective representative L on X. Etale localization
   lem-weil-pbc-etale-site-localization-open, lem-weil-pbc-cohomology-over-object-localization
   and lem-weil-pbc-site-restriction-exact show that its stage sections compute the required
   stage derived sections. Applying step 4 to each injective term also makes its inverse
   image on U sections-acyclic and identifies the degreewise colimit with its sections.
   All maps commute with differentials because the units and restrictions are natural.
6. Filtered module colimits are exact on underlying abelian groups by
   lem-weil-pbc-filtered-colimit-abelian-groups-exact; the scalar action is `r[i,x]=[i,rx]`.
   They commute with cohomology and carry objectwise quasi-isomorphisms to quasi-isomorphisms.
   Thus this degreewise colimit computes the filtered derived colimit. Composing the two
   canonical section cocones with the derived evaluation units proves the asserted maps
   are invertible and gives exactly the source's two cohomology arrows. -/
theorem proEtaleAffineContinuity {I : Type u} [SmallCategory I] [IsCofiltered I]
    (X : Scheme.{u}) (Λ : Type (u + 1)) [Ring Λ] (D : I ⥤ X.Etale)
    (c : Cone (D ⋙ Scheme.toProEt X))
    (hc : IsLimit ((Scheme.ProEt.forget X ⋙ Over.forget X).mapCone c))
    [∀ i : I, IsAffine (D.obj i).left]
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f).left]
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ)
    (a : ℤ) [L.IsStrictlyGE a] [∀ n : ℤ, Injective (L.X n)]
    (e : DerivedCategory.Q.obj L ≅ K.obj) :
    IsIso (affineContinuityEtaleMap D c K.obj L e) ∧
      IsIso (affineContinuityProEtaleMap D c K.obj L e) ∧
      ∀ i : I, IsIso
        (DerivedCategory.Q.map (affineContinuityStageRestriction (D.obj i) L) ≫
          affineContinuityTargetComparison
            (Etale.upperStar (ModuleCat.{u + 1} Λ) (D.obj i).hom)
            (Scheme.Etale.mk (𝟙 (D.obj i).left)) K.obj L e) := by
  refine ⟨?_, ?_, ?_⟩
  · have hcol := (etaleCocone_isColimit D c hc L).some
    have : IsIso (colimit.desc _ (affineContinuityEtaleCocone D c L)) := by
      change IsIso (((colimit.isColimit _).coconePointUniqueUpToIso hcol).hom)
      infer_instance
    let F := Etale.upperStar (ModuleCat.{u + 1} Λ) c.pt.hom
    let M : CochainComplex _ ℤ := (F.mapHomologicalComplex (.up ℤ)).obj L
    have : M.IsStrictlyGE a := by dsimp [M]; infer_instance
    have := derivedUnit_isIso_of_acyclic (Scheme.Etale.mk (𝟙 c.pt.left)) M a
      (fun n ↦ limitEtale_rightAcyclic (ModuleCat.{u + 1} Λ) D c hc (L.X n))
    unfold affineContinuityEtaleMap affineContinuityTargetComparison
    infer_instance
  · have hcol := (proEtaleCocone_isColimit D c hc L).some
    have : IsIso (colimit.desc _ (affineContinuityProEtaleCocone D c L)) :=
      (by
        change IsIso (((colimit.isColimit _).coconePointUniqueUpToIso hcol).hom)
        infer_instance)
    let F := comparisonUpperStar (ModuleCat.{u + 1} Λ) X
    let M : CochainComplex _ ℤ := (F.mapHomologicalComplex (.up ℤ)).obj L
    have : M.IsStrictlyGE a := by dsimp [M]; infer_instance
    have := derivedUnit_isIso_of_acyclic c.pt M a
      (fun n ↦ limitProEtale_rightAcyclic (ModuleCat.{u + 1} Λ) D c hc (L.X n))
    unfold affineContinuityProEtaleMap affineContinuityTargetComparison
    infer_instance
  · intro i
    let F := Etale.upperStar (ModuleCat.{u + 1} Λ) (D.obj i).hom
    let M := (F.mapHomologicalComplex (.up ℤ)).obj L
    have : ∀ n : ℤ, Injective (M.X n) := fun n ↦
      Etale.injective_upperStar_obj_of_etale' (ModuleCat.{u + 1} Λ) (D.obj i).hom (L.X n)
    have : CochainComplex.IsStrictlyGE M a := by dsimp [M]; infer_instance
    have := derivedUnit_isIso_of_injective (Scheme.Etale.mk (𝟙 (D.obj i).left)) M a
    have := stageRestriction_isIso (D.obj i) L
    unfold affineContinuityTargetComparison
    infer_instance

end AlgebraicGeometry.ProEtale
