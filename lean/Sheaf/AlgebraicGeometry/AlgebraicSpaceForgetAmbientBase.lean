/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q56
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules
public import Mathlib.AlgebraicGeometry.Limits
public import Sheaf.AlgebraicGeometry.SpaceChangeBase
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Forgetting the ambient base of an algebraic space

Source: Stacks Project, spaces.tex, lemma-change-base-scheme, parts (1)--(3),
and Properties of Spaces, small etale sites
(blueprint: def-sfb-space-absolute-module-transport).

The absolute presheaf is the dependent sum of the original sections over all
maps to the old base. Restriction to the same scheme charts gives the canonical
module equivalence. Thus its inverse is fixed by an actual restriction functor.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- The absolute section set, including its original structure map.
Source: Stacks, spaces.tex, lemma-change-base-scheme (1)
(blueprint: def-sfb-space-absolute-module-transport). -/
def absoluteSection {S : Scheme.{u}} (X : AlgebraicSpace S)
    (T : Over (Spec (.of (ULift.{u} ℤ)))) : Type u :=
  Σ s : T.left ⟶ S, X.obj.obj.obj (op (Over.mk s))

/-- Restriction of absolute sections along the underlying scheme map.
Source: Stacks, lemma-change-base-scheme (1)
(blueprint: def-sfb-space-absolute-module-transport). -/
def absoluteSectionMap {S : Scheme.{u}} (X : AlgebraicSpace S)
    {T V : Over (Spec (.of (ULift.{u} ℤ)))} (g : T ⟶ V)
    (x : absoluteSection X V) : absoluteSection X T :=
  ⟨g.left ≫ x.1, X.obj.obj.map
    (Over.homMk g.left rfl : Over.mk (g.left ≫ x.1) ⟶ Over.mk x.1).op x.2⟩

/-- The section restriction preserves identities.
Source: Stacks, lemma-change-base-scheme (1)
(blueprint: def-sfb-space-absolute-module-transport).
Proof: the structure map composed with the identity is unchanged. Transporting
along that equality, the second component is the original presheaf identity law. -/
theorem absoluteSectionMap_id {S : Scheme.{u}} (X : AlgebraicSpace S)
    (T : Over (Spec (.of (ULift.{u} ℤ)))) :
    absoluteSectionMap X (𝟙 T) = id := by
  sorry

/-- The section restriction preserves composition.
Source: Stacks, lemma-change-base-scheme (1)
(blueprint: def-sfb-space-absolute-module-transport).
Proof: associativity identifies the first components; after that identification,
the second components agree by the original presheaf composition law. -/
theorem absoluteSectionMap_comp {S : Scheme.{u}} (X : AlgebraicSpace S)
    {T V W : Over (Spec (.of (ULift.{u} ℤ)))} (f : T ⟶ V) (g : V ⟶ W) :
    absoluteSectionMap X (f ≫ g) = absoluteSectionMap X f ∘ absoluteSectionMap X g := by
  sorry

/-- The dependent-sum presheaf forgetting the old ambient base.
Source: Stacks, lemma-change-base-scheme (1)
(blueprint: def-sfb-space-absolute-module-transport). -/
def absolutePresheaf {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (Over (Spec (.of (ULift.{u} ℤ))))ᵒᵖ ⥤ Type u where
  obj T := absoluteSection X T.unop
  map g := ↾(absoluteSectionMap X g.unop)
  map_id T := congrArg (fun f ↦ ↾f) (absoluteSectionMap_id X T.unop)
  map_comp f g := congrArg (fun h ↦ ↾h) (absoluteSectionMap_comp X g.unop f.unop)

/-- Absolute sections satisfy fppf descent.
Source: Stacks, lemma-change-base-scheme (1)
(blueprint: def-sfb-space-absolute-module-transport).
Proof: first glue the maps to S, since schemes are fppf sheaves. The matching
second components then lie over this glued map and glue by the sheaf axiom for X.
Uniqueness in these two steps proves the sheaf axiom, including empty covers. -/
theorem absolutePresheaf_isSheaf {S : Scheme.{u}} (X : AlgebraicSpace S) :
    Presheaf.IsSheaf (Scheme.fppfTopology.over (Spec (.of (ULift.{u} ℤ))))
      (absolutePresheaf X) := by
  sorry

/-- The fppf sheaf of absolute sections.
Source: Stacks, lemma-change-base-scheme (1)
(blueprint: def-sfb-space-absolute-module-transport). -/
def absoluteSheaf {S : Scheme.{u}} (X : AlgebraicSpace S) :
    Sheaf (Scheme.fppfTopology.over (Spec (.of (ULift.{u} ℤ)))) (Type u) :=
  ⟨absolutePresheaf X, absolutePresheaf_isSheaf X⟩

/-- Forgetting the base preserves algebraic spaces.
Source: Stacks, lemma-change-base-scheme (2)--(3)
(blueprint: def-sfb-space-absolute-module-transport).
Proof: apply lem-sfb-space-change-base-to-integers (exists_spaceChangeBase)
with S' = Spec Z and the unique structure morphism. Its section and restriction
formulas identify its extension with absolutePresheaf. Equivalently, write X as
its etale scheme equivalence relation U/R. The dependent-sum
construction preserves fibre products over X and coequalizers, so the absolute
sheaf is the quotient of the same etale relation on the underlying schemes.
Their quotient has representable diagonal and the original surjective etale atlas. -/
theorem absoluteSheaf_isAlgebraicSpace {S : Scheme.{u}} (X : AlgebraicSpace S) :
    IsAlgebraicSpace (absoluteSheaf X) := by
  sorry

/-- The same algebraic space over Spec Z, with no chosen S-structure in its type.
Source: Stacks, lemma-change-base-scheme (3)
(blueprint: def-sfb-space-absolute-module-transport). -/
def absoluteSpace {S : Scheme.{u}} (X : AlgebraicSpace S) :
    AlgebraicSpace (Spec (.of (ULift.{u} ℤ))) :=
  ⟨absoluteSheaf X, absoluteSheaf_isAlgebraicSpace X⟩

/-- The underlying map to a scheme, evaluated on an absolute test section.
Source: Stacks, lemma-change-base-scheme (1)--(2)
(blueprint: def-sfb-space-absolute-module-transport). -/
def absoluteSchemeTargetComponent {S : Scheme.{u}} {X : AlgebraicSpace S}
    (U : Over S) (f : X ⟶ schemeSpace U)
    (T : Over (Spec (.of (ULift.{u} ℤ)))) (x : absoluteSection X T) :
    T ⟶ Over.mk (specULiftZIsTerminal.from U.left) :=
  Over.homMk (f.hom.hom.app (op (Over.mk x.1)) x.2).left
    (specULiftZIsTerminal.hom_ext _ _)

/-- The scheme-target components are natural.
Source: Stacks, lemma-change-base-scheme (1)--(2)
(blueprint: def-sfb-space-absolute-module-transport).
Proof: the target component is the underlying scheme map of the original section
image under f. Naturality of f states exactly that these maps commute with
restriction. The terminal-base compatibility is unique. -/
theorem absoluteSchemeTargetComponent_naturality
    {S : Scheme.{u}} {X : AlgebraicSpace S} (U : Over S) (f : X ⟶ schemeSpace U)
    {T V : Over (Spec (.of (ULift.{u} ℤ)))} (g : T ⟶ V) :
    (absolutePresheaf X).map g.op ≫ ↾(absoluteSchemeTargetComponent U f T) =
      ↾(absoluteSchemeTargetComponent U f V) ≫
        (yoneda.obj (Over.mk (specULiftZIsTerminal.from U.left))).map g.op := by
  sorry

/-- The map to the same underlying scheme, now over the terminal base.
Source: Stacks, lemma-change-base-scheme (1)--(2)
(blueprint: def-sfb-space-absolute-module-transport). -/
def absoluteSchemeTargetMap {S : Scheme.{u}} {X : AlgebraicSpace S}
    (U : Over S) (f : X ⟶ schemeSpace U) :
    absoluteSpace X ⟶ schemeSpace (Over.mk (specULiftZIsTerminal.from U.left)) :=
  ObjectProperty.homMk ⟨{
    app T := ↾(absoluteSchemeTargetComponent U f T.unop)
    naturality _ _ g := absoluteSchemeTargetComponent_naturality U f g.unop }⟩

/-- The same scheme chart, now mapped to the absolute space.
Source: Stacks, lemma-change-base-scheme (1)--(3)
(blueprint: def-sfb-space-absolute-module-transport). -/
def absoluteChartMap {S : Scheme.{u}} (X : AlgebraicSpace S) (T : X.EtaleSite) :
    yoneda.obj (Over.mk (specULiftZIsTerminal.from T.obj.left.left)) ⟶
      (absoluteSpace X).obj.obj :=
  yonedaEquiv.symm ⟨T.obj.left.hom, yonedaEquiv T.obj.hom⟩

/-- The unchanged chart map is etale after forgetting the ambient base.
Source: Stacks, lemma-change-base-scheme (3)
(blueprint: def-sfb-space-absolute-module-transport).
Proof: a scheme test of the absolute map includes its compatible map to S.
Its fibre product is exactly the original scheme test over S. Its projection
is therefore etale by the original chart's representable-etale property. -/
theorem absoluteChartMap_isEtale {S : Scheme.{u}} (X : AlgebraicSpace S)
    (T : X.EtaleSite) : IsEtale (absoluteChartMap X T) := by
  sorry

/-- The unchanged underlying chart arrow commutes with the absolute chart maps.
Source: Stacks, lemma-change-base-scheme (1)
(blueprint: def-sfb-space-absolute-module-transport).
Proof: by Yoneda the equality is the original chart triangle; its first component
is the equality of the scheme structure maps and its second is naturality. -/
theorem absoluteChartMap_naturality {S : Scheme.{u}} (X : AlgebraicSpace S)
    {T V : X.EtaleSite} (g : T ⟶ V) :
    yoneda.map (Over.homMk g.hom.left.left (specULiftZIsTerminal.hom_ext _ _) :
      Over.mk (specULiftZIsTerminal.from T.obj.left.left) ⟶
        Over.mk (specULiftZIsTerminal.from V.obj.left.left)) ≫
      absoluteChartMap X V = absoluteChartMap X T := by
  sorry

/-- The functor retaining the original etale scheme charts and arrows.
Source: Stacks, lemma-change-base-scheme (3); Properties of Spaces, small etale sites
(blueprint: def-sfb-space-absolute-module-transport). -/
def absoluteCharts {S : Scheme.{u}} (X : AlgebraicSpace S) :
    X.EtaleSite ⥤ (absoluteSpace X).EtaleSite where
  obj T := ⟨CostructuredArrow.mk (absoluteChartMap X T), absoluteChartMap_isEtale X T⟩
  map g := ObjectProperty.homMk (CostructuredArrow.homMk
    (Over.homMk g.hom.left.left (specULiftZIsTerminal.hom_ext _ _))
    (absoluteChartMap_naturality X g))

/-- The unchanged charts give a continuous equivalence of etale sites.
Source: Stacks, lemma-change-base-scheme (1)--(3); Properties of Spaces, small etale sites
(blueprint: def-sfb-space-absolute-module-transport).
Proof: any absolute chart supplies its unique map to S by projection of its section.
This reverses absoluteCharts on objects and arrows. Coverings on both sites are
jointly surjective etale maps of the same schemes, so the equivalence is continuous. -/
@[instance] theorem absoluteCharts_continuous {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (absoluteCharts X).IsContinuous X.etaleTopology (absoluteSpace X).etaleTopology := by
  sorry

/-- Restriction of modules on exactly the same schemes, with the identity on functions.
Source: Stacks, lemma-change-base-scheme (3); Properties of Spaces, structure sheaf
(blueprint: def-sfb-space-absolute-module-transport). -/
def absoluteModuleRestriction {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (absoluteSpace X).Modules ⥤ X.Modules :=
  SheafOfModules.pushforward (F := absoluteCharts X) ⟨𝟙 _⟩

/-- Restriction of modules is an equivalence.
Source: Stacks, lemma-change-base-scheme (3); Properties of Spaces, small etale sites
(blueprint: def-sfb-space-absolute-module-transport).
Proof: the inverse chart equivalence of absoluteCharts_continuous preserves the
same regular-function rings and coverings. Precomposition in both directions gives
mutually inverse module functors, with the identity comparisons on sections. -/
@[instance] theorem absoluteModuleRestriction_isEquivalence
    {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (absoluteModuleRestriction X).IsEquivalence := by
  sorry

/-- The module equivalence fixed by restriction on the same charts.
Source: Stacks, lemma-change-base-scheme (3)
(blueprint: def-sfb-space-absolute-module-transport). -/
def absoluteModuleEquivalence {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (absoluteSpace X).Modules ≌ X.Modules :=
  (absoluteModuleRestriction X).asEquivalence

/-- The inverse of restriction is additive, as an equivalence of module categories.
Source: Stacks, Tag 03I4; Tag 04KK, identical ringed etale sites
(blueprint: def-sfb-space-absolute-module-transport).
Proof: the inverse of the chart restriction equivalence preserves biproducts.
Their diagonal and codiagonal describe addition, so it preserves addition. -/
@[instance] theorem absoluteModuleInverse_additive {S : Scheme.{u}}
    (X : AlgebraicSpace S) : (absoluteModuleEquivalence X).inverse.Additive := by
  sorry

/-- Transport from the original small model to the absolute small model.
Source: Stacks, lemma-change-base-scheme (3), and the small ringed model
(blueprint: def-sfb-space-absolute-module-transport). -/
def absoluteSmallModuleTransport {S : Scheme.{u}} (X : AlgebraicSpace S) :
    X.SmallModules ⥤ (absoluteSpace X).SmallModules :=
  X.smallModuleEquivalence.inverse ⋙ (absoluteModuleEquivalence X).inverse ⋙
    (absoluteSpace X).smallModuleRestriction

/-- The canonical transport is an equivalence, hence exact.
Source: Stacks, lemma-change-base-scheme (3)
(blueprint: def-sfb-space-absolute-module-transport).
Proof: the three factors are the inverse small-model equivalence, the inverse
of absoluteModuleRestriction, and the absolute small-model restriction. Each
is an equivalence; their composite is one as well. -/
@[instance] theorem absoluteSmallModuleTransport_isEquivalence
    {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (absoluteSmallModuleTransport X).IsEquivalence := by
  sorry

/-- The canonical transport is additive and exact.
Source: Stacks, lemma-change-base-scheme (3)
(blueprint: def-sfb-space-absolute-module-transport).
Proof: each factor is restriction on the same regular-function rings or the inverse
of such an equivalence. These preserve finite limits, finite colimits and sums.
Consequently the composite preserves these as well. -/
@[instance] theorem absoluteSmallModuleTransport_additive
    {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (absoluteSmallModuleTransport X).Additive := by
  sorry

/-- Transport of derived objects under the exact equivalence of module categories.
Source: Stacks, lemma-change-base-scheme (3), and derived-category localization
(blueprint: def-sfb-space-absolute-module-transport). -/
def absoluteDerivedTransport {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasDerivedCategory.{w} X.SmallModules]
    [HasDerivedCategory.{w} (absoluteSpace X).SmallModules] :
    X.DerivedModules ⥤ (absoluteSpace X).DerivedModules :=
  (absoluteSmallModuleTransport X).mapDerivedCategory

end AlgebraicGeometry.AlgebraicSpace
