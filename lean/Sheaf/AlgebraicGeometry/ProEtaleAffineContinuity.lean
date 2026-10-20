/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q38
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale
public import Sheaf.CategoryTheory.SiteCoveringAxioms
import Sheaf.AlgebraicGeometry.AbelianEtaleProEtaleCohomologyComparison
import Sheaf.AlgebraicGeometry.ProEtaleComparisonPullbackSections
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Sheaf.CategoryTheory.Sites.CohomologyOverObjectLocalization
import WeilConjectures.AlgebraicGeometry.DerivedEtaleCohomologyLimit
import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Sheaf.AlgebraicGeometry.ProEtaleQcqsFiniteFamilyGeometry
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Sheaf.CategoryTheory.ModuleAbelianEvaluationComparison
import Sheaf.CategoryTheory.SitePullbackAbelianExact
import Sheaf.Paper.SiteRestrictionExact
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.CategoryTheory.Abelian.RightDerived.LongExactSequence
import Sheaf.AlgebraicGeometry.ClassicalContinuityMap
import Sheaf.AlgebraicGeometry.InjectiveComplexSliceSectionModel
import Sheaf.CategoryTheory.ConstantLeftModuleInverseImage
import Sheaf.CategoryTheory.LeftModuleDerivedEvaluationForget
import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageRestriction
import WeilConjectures.AlgebraicGeometry.SiteRestrictionExact
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

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
(blueprint: det-sf-comparison-affine-continuity). -/
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

/-- Evaluation of fixed-coefficient sheaves is additive, section by section.
Source: blueprint, module section complexes
(blueprint: det-sf-comparison-affine-continuity). -/
instance affineContinuitySectionsAdditive {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C) (Λ : Type (u + 1)) [Ring Λ] (V : C) :
    ((sheafSections J (ModuleCat.{u + 1} Λ)).obj (op V)).Additive where
  map_add := rfl

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
  sorry

end AlgebraicGeometry.ProEtale
