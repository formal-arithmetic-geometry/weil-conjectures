/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Limits.Cones
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleAffineContinuity
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
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

/-! # Abelian cohomology of a pro-etale affine

Source: latest blueprint, sec-proetale-coefficients/sk-cor-pe-affine-continuity,
Pro-etale cohomology of a pro-etale affine; Stacks Tags 03Q6 and 099W
(blueprint: prop-pe-derived-affine-continuity).

The coefficient category is `AddCommGrpCat`, as required by the source. The existing
module-valued continuity arrows cannot accept abelian sheaves. The helpers below give
these arrows directly from the existing abelian inverse-image adjunctions, section
restrictions, strict section diagrams and right-derived evaluation units. The geometric
cone is the already recorded `affineContinuityEtaleCone`.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

/-- Section pullback to the limiting etale scheme, before taking any colimit.
Source: blueprint, the canonical continuity cocone
(blueprint: prop-pe-derived-affine-continuity). -/
def abelianAffineContinuityEtaleUnit {X U : Scheme.{u}}
    (f : U ⟶ X) (L : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ) :
    (((sheafToPresheaf _ AddCommGrpCat.{u + 1}).mapHomologicalComplex (.up ℤ)).obj L).asFunctor ⟶
      (MorphismProperty.Over.pullback @Etale ⊤ f).op ⋙
        (((sheafToPresheaf _ AddCommGrpCat.{u + 1}).mapHomologicalComplex (.up ℤ)).obj
          (((Etale.upperStar AddCommGrpCat.{u + 1} f).mapHomologicalComplex
            (.up ℤ)).obj L)).asFunctor where
  app V :=
    { f := fun n ↦ ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app
        (L.X n)).hom.app V
      comm' := fun i j _ ↦ by
        exact congrArg (fun g ↦ g.hom.app V)
          ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.naturality
            (L.d i j)).symm }
  naturality := fun V W g ↦ by
    apply HomologicalComplex.Hom.ext
    funext n
    exact ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app
      (L.X n)).hom.naturality g

/-- Section pullback to the pro-etale site, before taking any colimit.
Source: blueprint, comparison inverse image
(blueprint: prop-pe-derived-affine-continuity). -/
def abelianAffineContinuityProEtaleUnit (X : Scheme.{u})
    (L : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ) :
    (((sheafToPresheaf _ AddCommGrpCat.{u + 1}).mapHomologicalComplex (.up ℤ)).obj L).asFunctor ⟶
      (Scheme.toProEt X).op ⋙
      (((sheafToPresheaf _ AddCommGrpCat.{u + 1}).mapHomologicalComplex (.up ℤ)).obj
        (((comparisonUpperStar AddCommGrpCat.{u + 1} X).mapHomologicalComplex
          (.up ℤ)).obj L)).asFunctor
    where
  app V :=
    { f := fun n ↦ ((comparisonAdjunction AddCommGrpCat.{u + 1} X).unit.app
        (L.X n)).hom.app V
      comm' := fun i j _ ↦ by
        exact congrArg (fun g ↦ g.hom.app V)
          ((comparisonAdjunction AddCommGrpCat.{u + 1} X).unit.naturality (L.d i j)).symm }
  naturality := fun V W g ↦ by
    apply HomologicalComplex.Hom.ext
    funext n
    exact ((comparisonAdjunction AddCommGrpCat.{u + 1} X).unit.app
      (L.X n)).hom.naturality g

/-- The strict diagram of stage section complexes, indexed by the opposite presentation.
Source: blueprint, definition of the filtered derived colimit
(blueprint: prop-pe-derived-affine-continuity). -/
def abelianAffineContinuityDiagram {I : Type u} [SmallCategory I] {X : Scheme.{u}}
    (D : I ⥤ X.Etale)
    (L : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ) :=
  D.op ⋙ (((sheafToPresheaf _ AddCommGrpCat.{u + 1}).mapHomologicalComplex (.up ℤ)).obj L).asFunctor

/-- The canonical cocone to sections on the limiting etale scheme.
Source: blueprint, first displayed arrow
(blueprint: prop-pe-derived-affine-continuity). -/
def abelianAffineContinuityEtaleCocone {I : Type u} [SmallCategory I] {X : Scheme.{u}}
    (D : I ⥤ X.Etale)
    (c : Cone (D ⋙ Scheme.toProEt X))
    (L : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ) :
    Cocone (abelianAffineContinuityDiagram D L) :=
  (Cocone.precompose (Functor.whiskerLeft D.op (abelianAffineContinuityEtaleUnit c.pt.hom L))).obj
    (((((sheafToPresheaf _ AddCommGrpCat.{u + 1}).mapHomologicalComplex (.up ℤ)).obj
      (((Etale.upperStar AddCommGrpCat.{u + 1} c.pt.hom).mapHomologicalComplex
        (.up ℤ)).obj L)).asFunctor).mapCocone
        ((affineContinuityEtaleCone D c).op))

/-- The canonical cocone to pro-etale sections: comparison unit followed by restriction
along the given projections. Its legs are actual maps of complexes.
Source: blueprint, composite of the displayed arrows
(blueprint: prop-pe-derived-affine-continuity). -/
def abelianAffineContinuityProEtaleCocone {I : Type u} [SmallCategory I] {X : Scheme.{u}}
    (D : I ⥤ X.Etale)
    (c : Cone (D ⋙ Scheme.toProEt X))
    (L : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ) :
    Cocone (abelianAffineContinuityDiagram D L) :=
  (Cocone.precompose (Functor.whiskerLeft D.op (abelianAffineContinuityProEtaleUnit X L))).obj
    (((((sheafToPresheaf _ AddCommGrpCat.{u + 1}).mapHomologicalComplex (.up ℤ)).obj
      (((comparisonUpperStar AddCommGrpCat.{u + 1} X).mapHomologicalComplex
        (.up ℤ)).obj L)).asFunctor).mapCocone c.op)

/-- Evaluation of abelian sheaves is additive, section by section.
Source: blueprint, abelian section complexes
(blueprint: prop-pe-derived-affine-continuity). -/
instance abelianAffineContinuitySectionsAdditive {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C) (V : C) :
    ((sheafSections J AddCommGrpCat.{u + 1}).obj (op V)).Additive where
  map_add := rfl

/-- The canonical map from a section complex to its right-derived evaluation.
It is the unit of the right derived functor, with the quotient factorizations made explicit.
Source: blueprint, acyclic-resolution interpretation of sections
(blueprint: prop-pe-derived-affine-continuity). -/
def abelianAffineContinuityDerivedUnit {C : Type (u + 1)} [Category.{u} C]
    {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{u + 1}]
    [HasDerivedCategory.{u + 1} (Sheaf J AddCommGrpCat.{u + 1})]
    [Abelian.HasKInjectiveResolutions (Sheaf J AddCommGrpCat.{u + 1})] (V : C)
    (L : CochainComplex (Sheaf J AddCommGrpCat.{u + 1}) ℤ) :
    DerivedCategory.Q.obj
      (((((sheafToPresheaf _ AddCommGrpCat.{u + 1}).mapHomologicalComplex
        (.up ℤ)).obj L).asFunctor).obj (op V)) ⟶
      ((sheafSections J AddCommGrpCat.{u + 1}).obj (op V)).rightDerivedFunctor.obj
        (DerivedCategory.Q.obj L) :=
  (DerivedCategory.quotientCompQhIso AddCommGrpCat.{u + 1}).inv.app _ ≫
    (((sheafSections J AddCommGrpCat.{u + 1}).obj (op V)).rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ _).obj L)) ≫
    ((sheafSections J AddCommGrpCat.{u + 1}).obj (op V)).rightDerivedFunctor.map
      ((DerivedCategory.quotientCompQhIso _).hom.app L)

/-- Derived evaluation after an exact inverse image, normalized on the given representative.
Source: blueprint, definition of the two derived section objects
(blueprint: prop-pe-derived-affine-continuity). -/
def abelianAffineContinuityTargetComparison
    {C B : Type (u + 1)} [Category.{u} C] [Category.{u} B]
    {JC : GrothendieckTopology C} {JB : GrothendieckTopology B}
    [HasSheafify JC AddCommGrpCat.{u + 1}] [HasSheafify JB AddCommGrpCat.{u + 1}]
    [HasDerivedCategory.{u + 1} (Sheaf JC AddCommGrpCat.{u + 1})]
    [HasDerivedCategory.{u + 1} (Sheaf JB AddCommGrpCat.{u + 1})]
    [Abelian.HasKInjectiveResolutions (Sheaf JB AddCommGrpCat.{u + 1})]
    (F : Sheaf JC AddCommGrpCat.{u + 1} ⥤ Sheaf JB AddCommGrpCat.{u + 1})
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] (V : B)
    (K : DerivedCategory (Sheaf JC AddCommGrpCat.{u + 1}))
    (L : CochainComplex (Sheaf JC AddCommGrpCat.{u + 1}) ℤ)
    (e : DerivedCategory.Q.obj L ≅ K) :
    DerivedCategory.Q.obj
      (((((sheafToPresheaf _ AddCommGrpCat.{u + 1}).mapHomologicalComplex (.up ℤ)).obj
        ((F.mapHomologicalComplex (.up ℤ)).obj L)).asFunctor).obj
        (op V)) ⟶
      ((sheafSections JB AddCommGrpCat.{u + 1}).obj (op V)).rightDerivedFunctor.obj
        (F.mapDerivedCategory.obj K) :=
  abelianAffineContinuityDerivedUnit V ((F.mapHomologicalComplex (.up ℤ)).obj L) ≫
    ((sheafSections JB AddCommGrpCat.{u + 1}).obj (op V)).rightDerivedFunctor.map
      (F.mapDerivedCategoryFactors.inv.app L ≫ F.mapDerivedCategory.map e.hom)

/-- The canonical map from sections over an etale object to sections of its inverse image.
The arrow in the base-changed site is the diagonal into the fibre product.
Source: blueprint, the meaning of each stage section complex
(blueprint: prop-pe-derived-affine-continuity). -/
def abelianAffineContinuityStageRestriction {X : Scheme.{u}}
    (V : X.Etale)
    (L : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ) :
    ((((sheafToPresheaf _ AddCommGrpCat.{u + 1}).mapHomologicalComplex
      (.up ℤ)).obj L).asFunctor).obj (op V) ⟶
      ((((sheafToPresheaf _ AddCommGrpCat.{u + 1}).mapHomologicalComplex (.up ℤ)).obj
        (((Etale.upperStar AddCommGrpCat.{u + 1} V.hom).mapHomologicalComplex
          (.up ℤ)).obj L)).asFunctor).obj
          (op (Scheme.Etale.mk (𝟙 V.left))) :=
  (abelianAffineContinuityEtaleUnit V.hom L).app (op V) ≫
    ((((sheafToPresheaf _ AddCommGrpCat.{u + 1}).mapHomologicalComplex (.up ℤ)).obj
        (((Etale.upperStar AddCommGrpCat.{u + 1} V.hom).mapHomologicalComplex
          (.up ℤ)).obj L)).asFunctor).map
        (MorphismProperty.Over.homMk
          (pullback.lift (𝟙 V.left) (𝟙 V.left) (by simp)) (by simp) :
          Scheme.Etale.mk (𝟙 V.left) ⟶
            (MorphismProperty.Over.pullback @Etale ⊤ V.hom).obj V).op

/-- The first canonical derived continuity arrow, constructed on the strict section diagram.
Source: blueprint, first displayed arrow
(blueprint: prop-pe-derived-affine-continuity). -/
def abelianAffineContinuityEtaleMap {I : Type u} [SmallCategory I] {X : Scheme.{u}}
    (D : I ⥤ X.Etale)
    (c : Cone (D ⋙ Scheme.toProEt X))
    (K : DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (L : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ)
    (e : DerivedCategory.Q.obj L ≅ K) :=
  DerivedCategory.Q.map (colimit.desc _ (abelianAffineContinuityEtaleCocone D c L)) ≫
    abelianAffineContinuityTargetComparison (Etale.upperStar AddCommGrpCat.{u + 1} c.pt.hom)
      (Scheme.Etale.mk (𝟙 c.pt.left)) K L e

/-- The canonical derived arrow to pro-etale sections. On every stage it is comparison
inverse image followed by restriction along the specified projection, then derived evaluation.
Source: blueprint, composite of the displayed arrows
(blueprint: prop-pe-derived-affine-continuity). -/
def abelianAffineContinuityProEtaleMap {I : Type u} [SmallCategory I] {X : Scheme.{u}}
    (D : I ⥤ X.Etale)
    (c : Cone (D ⋙ Scheme.toProEt X))
    (K : DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (L : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ)
    (e : DerivedCategory.Q.obj L ≅ K) :=
  DerivedCategory.Q.map (colimit.desc _ (abelianAffineContinuityProEtaleCocone D c L)) ≫
    abelianAffineContinuityTargetComparison (comparisonUpperStar AddCommGrpCat.{u + 1} X)
      c.pt K L e

/-- The canonical continuity map and its composite with the canonical etale/pro-etale
comparison are invertible in the derived category of abelian groups. Every stage section
complex computes the derived sections of the inverse image `K_i`.

The common source is `Q.obj (colimit (abelianAffineContinuityDiagram D L))`, the degreewise
filtered colimit of the strict section complexes `L(U_i)`. Filtered colimits of abelian
groups are exact, so this also represents the filtered derived colimit. Applying the
cohomology functor in any integer degree yields the source's cohomology isomorphisms.
The second displayed arrow is characterized by composing it with the first to obtain
`abelianAffineContinuityProEtaleMap`; its invertibility follows equivalently from the
two invertibilities stated here. Its pro-etale target is derived evaluation at `c.pt`,
namely derived sections of the restriction of `ν_X^* K` to the localized site over `U`.

`L`, `a` and `e` specify any bounded-below injective representative of `K`. They are
computational choices, available for every `K` in `D^+`, and impose no extra condition
on `K` or on the scheme presentation.

Source: latest blueprint, sec-proetale-coefficients/sk-cor-pe-affine-continuity,
Pro-etale cohomology of a pro-etale affine; Stacks Tags 03Q6 and 099W
(blueprint: prop-pe-derived-affine-continuity).

Proof (the three steps of the node):
1. Give every abelian sheaf its canonical integer action: integer sections act by
   repeated addition locally, and the sheaf axiom glues these actions. Unitality and
   additivity force this action, and every additive morphism is integer-linear.
   Forgetting integer scalars is consequently an exact equivalence with inverse the
   construction just described (def-weil-sheaf-of-modules-category). It identifies
   sections, restrictions, injective resolutions, derived sections and filtered colimits.
2. Apply lem-pe-constant-left-module-inverse-image for the integers. Its normalized
   comparisons identify the inverse images of `K`, the stage and limit inverse images,
   the comparison inverse image, their units and their localized restrictions with the
   abelian constructions used here. Exactness gives these identifications on complexes
   and on the bounded-below derived categories, including the canonical section maps.
3. Apply det-sf-comparison-affine-continuity with integer coefficients to the complex
   corresponding to `K`. The presentation is small, nonempty and cofiltered, with affine
   etale stages and affine transitions, exactly as in sk-def-pe-morphisms. Transport its
   two canonical isomorphisms and stage-section identifications through the equivalence
   of step 1 using the compatibilities of step 2. This identifies the strict diagrams,
   hence their degreewise filtered colimits and the specified maps. Exactness of filtered
   abelian colimits identifies cohomology of this derived colimit with the colimit of
   stage cohomologies in every integer degree, giving both displayed arrows. -/
theorem proEtaleAbelianAffineContinuity {I : Type u} [SmallCategory I] [IsCofiltered I]
    (X : Scheme.{u}) (D : I ⥤ X.Etale)
    (c : Cone (D ⋙ Scheme.toProEt X))
    (hc : IsLimit ((Scheme.ProEt.forget X ⋙ Over.forget X).mapCone c))
    [∀ i : I, IsAffine (D.obj i).left]
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f).left]
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (L : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ)
    (a : ℤ) [L.IsStrictlyGE a] [∀ n : ℤ, Injective (L.X n)]
    (e : DerivedCategory.Q.obj L ≅ K.obj) :
    IsIso (abelianAffineContinuityEtaleMap D c K.obj L e) ∧
      IsIso (abelianAffineContinuityProEtaleMap D c K.obj L e) ∧
      ∀ i : I, IsIso
        (DerivedCategory.Q.map (abelianAffineContinuityStageRestriction (D.obj i) L) ≫
          abelianAffineContinuityTargetComparison
            (Etale.upperStar AddCommGrpCat.{u + 1} (D.obj i).hom)
            (Scheme.Etale.mk (𝟙 (D.obj i).left)) K.obj L e) := by
  sorry

/-- In every integer degree, the canonical continuity arrow and its composite with
etale/pro-etale comparison induce isomorphisms of abelian groups. Under exactness of
filtered colimits the source is canonically the colimit of the stage cohomology groups;
the stage identifications are those of `proEtaleAbelianAffineContinuity`.

Source: latest blueprint, sec-proetale-coefficients/sk-cor-pe-affine-continuity,
Pro-etale cohomology of a pro-etale affine; Stacks Tag 03Q6
(blueprint: prop-pe-derived-affine-continuity).

Proof: apply `DerivedCategory.homologyFunctor` in degree `n` to the two isomorphisms
of `proEtaleAbelianAffineContinuity`. Filtered abelian colimits are exact and commute
with cohomology, so the cohomology of the source identifies with the displayed colimit.
The second arrow is characterized by factoring the composite through the first arrow.
The stage-identification clause identifies its summands with the required `K_i`. -/
theorem proEtaleAbelianAffineContinuity_cohomology
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (X : Scheme.{u}) (D : I ⥤ X.Etale)
    (c : Cone (D ⋙ Scheme.toProEt X))
    (hc : IsLimit ((Scheme.ProEt.forget X ⋙ Over.forget X).mapCone c))
    [∀ i : I, IsAffine (D.obj i).left]
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f).left]
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (L : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ)
    (a : ℤ) [L.IsStrictlyGE a] [∀ n : ℤ, Injective (L.X n)]
    (e : DerivedCategory.Q.obj L ≅ K.obj) (n : ℤ) :
    IsIso ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n).map
      (abelianAffineContinuityEtaleMap D c K.obj L e)) ∧
    IsIso ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n).map
      (abelianAffineContinuityProEtaleMap D c K.obj L e)) := by
  sorry

end AlgebraicGeometry.ProEtale
