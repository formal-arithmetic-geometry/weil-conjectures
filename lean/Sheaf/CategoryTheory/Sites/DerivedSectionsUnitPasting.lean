/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q27
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.Sites.GeometricMorphism
public import Sheaf.CategoryTheory.ConstantLeftModuleTransport
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import Sheaf.Algebra.Homology.BoundedBelowInjectiveResolutionMono
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.Algebra.Homology.ModelCategory.Injective
import WeilConjectures.Algebra.Homology.LiftToInjectiveUniqueUpToHomotopy
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-! # Derived sections, geometric pullback, and unit--Leray pasting

Source: Stacks Project, Derived Categories, Tag 015M; Cohomology on Sites, Tags 071J
and 08J6; Sites, Tag 04IA (blueprint: lem-pur-site-derived-sections-unit-pasting).

The ordinary section comparison is specified on maps from the terminal sheaf.
Its derived comparison is specified by the right-derived units. These normalizations
exclude arbitrary linear automorphisms of module inverse images.

## Main statements

* `existsUnique_comparison`: the canonically normalized natural Leray isomorphism.
* `geometric_pasting` and `composition_pasting`: the two derived pullback identities.
* `resolution_formula` and `cohomology_resolution_formula`: the injective-resolution formulas.
* `negative_cohomology`: vanishing below zero for a sheaf in degree zero.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.ConstantLeftModuleInverseImage

namespace CategoryTheory.SiteDerivedSections

variable {C D E : Type u} [SmallCategory C] [SmallCategory D] [SmallCategory E]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {H : GrothendieckTopology E}
  {R : Type u} [CommRing R]

/-- Terminal evaluation, with scalars restricted along the constant-section unit.
Source: Stacks, 071J (blueprint: lem-pur-site-derived-sections-unit-pasting). -/
def sections (J : GrothendieckTopology C) (R : Type u) [CommRing R] (T : C) :
    Modules J R ⥤ ModuleCat.{u} R :=
  SheafOfModules.evaluation _ (op T) ⋙ ModuleCat.restrictScalars
    (((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of R))).app (op T)).hom)

/-- Additivity is the inherited pointwise additivity of module evaluation and restriction.
Source: Stacks, 071J (blueprint: lem-pur-site-derived-sections-unit-pasting). -/
instance sectionsAdditive (J : GrothendieckTopology C) (R : Type u) [CommRing R] (T : C) :
    (sections J R T).Additive where
  map_add := by intro M N a b; rfl

/-- Module sheaves on a small site have their canonical Grothendieck structure.
Source: Stacks, 07A5 (blueprint: lem-pur-site-derived-sections-unit-pasting). -/
instance modulesGrothendieck (J : GrothendieckTopology C) (R : Type u) [CommRing R] :
    IsGrothendieckAbelian.{u} (Modules J R) := SheafOfModules.isGrothendieckAbelian _

/-- A section at the terminal site object, as a map from the terminal set sheaf.
Source: Stacks, 00XA and 071J (blueprint: lem-pur-site-derived-sections-unit-pasting). -/
def sectionHom {T : C} (hT : IsTerminal T) (M : Modules J R)
    (x : (sections J R T).obj M) :
    (constantSheaf J (Type u)).obj PUnit.{u + 1} ⟶ (W J R).obj M :=
  ((constantSheafAdj J (Type u) hT).homEquiv _ _).symm (TypeCat.ofHom (fun _ ↦ x))

variable (f : GeometricMorphism (Sheaf K (Type u)) (Sheaf J (Type u)))
  (d : ConstantLeftModuleInverseImageLift J K R f.inverse f.direct f.adj f.leftExact)

/-- The already specified induced direct image on underlying set sheaves.
Source: Stacks, 00YV (blueprint: lem-pur-site-derived-sections-unit-pasting). -/
def directSets : d.moduleDirect ⋙ W J R ≅ W K R ⋙ f.direct :=
  Functor.isoWhiskerRight d.directUnderlyingIso (U J) ≪≫
    Functor.isoWhiskerLeft (V K R) d.abelianDirectSetIso

/-- Exactness and additivity are fields of the normalized module lift.
Source: Stacks, 00YV (blueprint: lem-pur-site-derived-sections-unit-pasting). -/
instance inverseAdditive : d.moduleFunctor.Additive := d.additive

/-- The normalized inverse image preserves finite limits.
Source: Stacks, 00YV (blueprint: lem-pur-site-derived-sections-unit-pasting). -/
instance inverseLeftExact : PreservesFiniteLimits d.moduleFunctor := d.preservesFiniteLimits

/-- The normalized inverse image preserves finite colimits.
Source: Stacks, 00YV (blueprint: lem-pur-site-derived-sections-unit-pasting). -/
instance inverseRightExact : PreservesFiniteColimits d.moduleFunctor := d.preservesFiniteColimits

/-- A right adjoint of an additive functor is additive.
Source: Stacks, 00YV (blueprint: lem-pur-site-derived-sections-unit-pasting). -/
instance directAdditive : d.moduleDirect.Additive := d.moduleAdj.right_adjoint_additive

/-- The right adjoint of the exact module inverse image preserves injectives.
Source: Stacks, 015M (blueprint: lem-pur-site-derived-sections-unit-pasting). -/
instance directPreservesInjectives : d.moduleDirect.PreservesInjectiveObjects :=
  d.moduleAdj.preservesInjectiveObjects_of_preservesFiniteLimits

variable [HasDerivedCategory.{w} (Modules J R)] [HasDerivedCategory.{w} (Modules K R)]
  [HasDerivedCategory.{w} (ModuleCat.{u} R)]

/-- Ordinary and derived comparisons, with their canonical normalizations.
The ordinary comparison is the adjunction bijection on terminal sections. The derived
unit equation is precisely the normalization of Stacks 015M.
Source: Stacks, 00XA, 015M, 071J and 08J6
(blueprint: lem-pur-site-derived-sections-unit-pasting). -/
structure Comparison {TC : C} {TD : D} (hC : IsTerminal TC) (hD : IsTerminal TD) where
  ordinary : d.moduleDirect ⋙ sections J R TC ≅ sections K R TD
  ordinary_normalization : ∀ (M : Modules K R)
    (x : (sections J R TC).obj (d.moduleDirect.obj M)),
    sectionHom hD M (ordinary.hom.app M x) =
      d.pointIso.inv ≫ (f.adj.homEquiv _ _).symm
        (sectionHom hC (d.moduleDirect.obj M) x ≫ (directSets f d).hom.app M)
  leray : d.moduleDirect.rightDerivedFunctorPlus ⋙
      (sections J R TC).rightDerivedFunctorPlus ≅ (sections K R TD).rightDerivedFunctorPlus
  leray_normalization :
    Functor.rightDerivedFunctorPlusCompUnit d.moduleDirect (sections J R TC) ≫
        Functor.whiskerLeft DerivedCategory.Plus.Qh leray.hom =
      Functor.whiskerRight (NatTrans.mapHomotopyCategoryPlus ordinary.hom)
        DerivedCategory.Plus.Qh ≫ (sections K R TD).rightDerivedFunctorPlusUnit

/-- The canonical ordinary and derived section comparisons exist and are uniquely normalized.

Source: Stacks, 015M, 071J and 08J6
(blueprint: lem-pur-site-derived-sections-unit-pasting).

Proof:
1. Module sheaves are Grothendieck abelian by
   lem-pur-ringed-site-grothendieck-abelian, hence have enough injectives by
   lem-sp-grothendieck-enough-injectives. The section functor is additive and left exact.
2. Sections are maps from the terminal sheaf. The set adjunction and d.pointIso give
   the displayed bijection; transported addition and constant scalar endomorphisms
   make it R-linear. The unit compatibility of the normalized lift makes it the
   canonical section comparison, uniquely on every section.
3. The exact inverse image makes its right adjoint preserve injectives by
   lem-sp-right-adjoint-preserves-injectives. Bounded-below injective resolutions exist
   by lem-weil-pbc-complex-injective-resolution-mono, are K-injective by
   lem-weil-pbc-bounded-below-injectives-kinjective, and compute morphisms by
   lem-sc-kinjective-quasi-iso-comparison.
4. Compute both derived section functors on these resolutions using
   lem-weil-pbc-right-derived-plus-injective. Apply the ordinary comparison termwise.
   Naturality along an injective replacement gives the displayed derived-unit equation.
   Right-derived uniqueness gives existence and uniqueness of this normalized natural
   isomorphism on all D-plus objects. This is the inverse of the canonical 015M
   composition comparison, followed by the derived ordinary section comparison. -/
theorem existsUnique_comparison {TC : C} {TD : D}
    (hC : IsTerminal TC) (hD : IsTerminal TD) :
    ∃! e : Comparison f d hC hD, True := by
  sorry

/-- The uniquely normalized comparison. Its data are determined by the preceding
unique-existence theorem, rather than chosen from an unspecified isomorphism class.
Source: Stacks, 015M and 08J6 (blueprint: lem-pur-site-derived-sections-unit-pasting). -/
def comparison {TC : C} {TD : D} (hC : IsTerminal TC) (hD : IsTerminal TD) :
    Comparison f d hC hD :=
  (existsUnique_comparison f d hC hD).exists.choose

attribute [local irreducible] comparison

/-- The ordinary section pullback is the unit followed by the terminal-section comparison.
Source: Stacks, 071J (blueprint: lem-pur-site-derived-sections-unit-pasting). -/
def ordinaryPullback {TC : C} {TD : D} (hC : IsTerminal TC) (hD : IsTerminal TD) :
    sections J R TC ⟶ d.moduleFunctor ⋙ sections K R TD :=
  (Functor.leftUnitor _).inv ≫
    Functor.whiskerRight d.moduleAdj.unit (sections J R TC) ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft d.moduleFunctor (comparison f d hC hD).ordinary.hom

/-- The natural map T is RΓ of the derived unit followed by the canonical Leray comparison.
Source: Stacks, 015M and 071J (blueprint: lem-pur-site-derived-sections-unit-pasting). -/
def pullback {TC : C} {TD : D} (hC : IsTerminal TC) (hD : IsTerminal TD) :
    (sections J R TC).rightDerivedFunctorPlus ⟶
      d.moduleFunctor.mapDerivedCategoryPlus ⋙ (sections K R TD).rightDerivedFunctorPlus :=
  (Functor.leftUnitor _).inv ≫
    Functor.whiskerRight d.moduleAdj.derivedPlus.unit (sections J R TC).rightDerivedFunctorPlus ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft d.moduleFunctor.mapDerivedCategoryPlus (comparison f d hC hD).leray.hom

attribute [local irreducible] pullback

section Pasting

variable (g : GeometricMorphism (Sheaf H (Type u)) (Sheaf K (Type u)))
  (dg : ConstantLeftModuleInverseImageLift K H R g.inverse g.direct g.adj g.leftExact)
  [HasDerivedCategory.{w} (Modules H R)]

/-- The inverse-image comparison of a geometric 2-isomorphism, normalized on underlying
set sheaves, and the resulting unit--Leray pasting equation.

Source: Stacks, Sites, 04IA; Derived Categories, 015M
(blueprint: lem-pur-site-derived-sections-unit-pasting).

Proof:
1. Lift the inverse-image mate of t to modules using transported addition and the
   normalized constant scalar maps. Faithfulness on underlying set sheaves makes
   the displayed normalization determine alpha uniquely: it holds exactly for alpha.
   The same construction for t inverse gives its inverse, so alpha is an isomorphism.
2. For an ordinary section x, the triangle identity identifies ordinaryPullback(x)
   with inverse image of x. Naturality of the set mate at x proves the ordinary
   composition equation, since its terminal component is the unique terminal map.
3. Represent the source by an injective complex I, replace f-inverse(I) by an injective
   J, and g-inverse(J) by an injective V. The derived unit formula of
   lem-trf-bounded-below-derived-adjunction and the Leray normalization identify T
   with sections of these comparison maps. This uses
   lem-weil-pbc-exact-functor-derived-factorization and never claims that inverse
   image preserves injectives.
4. Naturality of ordinaryPullback moves the first replacement past the second
   pullback. Apply the ordinary composition equation from step 2. The normalized
   alpha changes the target representative by its inverse; cancellation proves the
   displayed equality in the derived category. K-injective localization makes it
   independent of representatives. The mate is on set sheaves; a scalar multiple
   of a module comparison cannot satisfy its displayed normalization. -/
theorem geometric_pasting {TC : C} {TD : D} {TE : E}
    (hC : IsTerminal TC) (hD : IsTerminal TD) (hE : IsTerminal TE)
    (h : GeometricMorphism (Sheaf H (Type u)) (Sheaf J (Type u)))
    (dh : ConstantLeftModuleInverseImageLift J H R h.inverse h.direct h.adj h.leftExact)
    (t : h.direct ≅ (g.comp f).direct) :
    ∃ α : d.moduleFunctor ⋙ dg.moduleFunctor ≅ dh.moduleFunctor,
      (∀ α' : d.moduleFunctor ⋙ dg.moduleFunctor ≅ dh.moduleFunctor,
        (∀ M : Modules J R,
          (W H R).map (α'.hom.app M) ≫ dh.moduleSetIso.hom.app M =
            dg.moduleSetIso.hom.app (d.moduleFunctor.obj M) ≫
              g.inverse.map (d.moduleSetIso.hom.app M) ≫
              (GeometricMorphism.inverseIso t).hom.app ((W J R).obj M)) ↔ α' = α) ∧
      (∀ M : DerivedCategory.Plus (Modules J R),
        (pullback h dh hC hE).app M =
          (pullback f d hC hD).app M ≫
            (pullback g dg hD hE).app (d.moduleFunctor.mapDerivedCategoryPlus.obj M) ≫
            (sections H R TE).rightDerivedFunctorPlus.map
              (((Functor.mapDerivedCategoryPlusCompIso d.moduleFunctor dg.moduleFunctor).inv ≫
                (Functor.mapDerivedCategoryPlusNatIso α).hom).app M)) := by
  sorry

/-- The special case h = fg, with the canonical inverse-image compositor c.
Source: Stacks, 015M and Sites, 04IA
(blueprint: lem-pur-site-derived-sections-unit-pasting).

Proof: apply geometric_pasting to the composite geometric morphism with the identity
2-isomorphism. The normalization alone characterizes the canonical module compositor:
it holds exactly for c, by faithfulness of the underlying set-sheaf functor.
Its exact derived descent is mapDerivedCategoryPlusCompIso inverse followed by
mapDerivedCategoryPlusNatIso. This gives exactly T_fg = RΓ(c) T_g T_f. -/
theorem composition_pasting {TC : C} {TD : D} {TE : E}
    (hC : IsTerminal TC) (hD : IsTerminal TD) (hE : IsTerminal TE)
    (dfg : ConstantLeftModuleInverseImageLift J H R
      (g.comp f).inverse (g.comp f).direct (g.comp f).adj (g.comp f).leftExact) :
    ∃ c : d.moduleFunctor ⋙ dg.moduleFunctor ≅ dfg.moduleFunctor,
      (∀ c' : d.moduleFunctor ⋙ dg.moduleFunctor ≅ dfg.moduleFunctor,
        (∀ M : Modules J R,
          (W H R).map (c'.hom.app M) ≫ dfg.moduleSetIso.hom.app M =
            dg.moduleSetIso.hom.app (d.moduleFunctor.obj M) ≫
              g.inverse.map (d.moduleSetIso.hom.app M)) ↔ c' = c) ∧
      (∀ M : DerivedCategory.Plus (Modules J R),
        (pullback (g.comp f) dfg hC hE).app M =
          (pullback f d hC hD).app M ≫
            (pullback g dg hD hE).app (d.moduleFunctor.mapDerivedCategoryPlus.obj M) ≫
            (sections H R TE).rightDerivedFunctorPlus.map
              (((Functor.mapDerivedCategoryPlusCompIso d.moduleFunctor dg.moduleFunctor).inv ≫
                (Functor.mapDerivedCategoryPlusNatIso c).hom).app M)) := by
  sorry

end Pasting

section Resolutions

variable {TC : C} {TD : D} (hC : IsTerminal TC) (hD : IsTerminal TD)
  (I : CochainComplex.Plus (Modules J R)) (L : CochainComplex.Plus (Modules K R))
  (b : d.moduleFunctor.mapCochainComplexPlus.obj I ⟶ L)

/-- The actual map of section complexes: ordinary section pullback followed by sections of b.
Source: Stacks, 071J, 013P and 013S
(blueprint: lem-pur-site-derived-sections-unit-pasting). -/
def sectionChainMap : (sections J R TC).mapCochainComplexPlus.obj I ⟶
    (sections K R TD).mapCochainComplexPlus.obj L :=
  ObjectProperty.homMk
    ((NatTrans.mapHomologicalComplex (ordinaryPullback f d hC hD) (.up ℤ)).app I.obj ≫
      ((sections K R TD).mapHomologicalComplex (.up ℤ)).map b.hom)

/-- The identification of the inverse-image derived object with its chosen representative.
For a quasi-isomorphism b this is invertible by exact localization.
Source: Stacks, 015F (blueprint: lem-pur-site-derived-sections-unit-pasting). -/
def resolutionIdentification :
    d.moduleFunctor.mapDerivedCategoryPlus.obj (DerivedCategory.Plus.Q.obj I) ⟶
      DerivedCategory.Plus.Q.obj L :=
  d.moduleFunctor.mapDerivedCategoryPlusFactorsh.hom.app
      ((HomotopyCategory.Plus.quotient _).obj I) ≫
    DerivedCategory.Plus.Qh.map ((HomotopyCategory.Plus.quotient _).map b)

variable [∀ n : ℤ, Injective (L.obj.X n)]

/-- Express T in the two section-complex coordinates supplied by injective resolutions.
Source: Stacks, 071J and 015M (blueprint: lem-pur-site-derived-sections-unit-pasting). -/
def resolvedPullback :
    DerivedCategory.Plus.Q.obj ((sections J R TC).mapCochainComplexPlus.obj I) ⟶
      DerivedCategory.Plus.Q.obj ((sections K R TD).mapCochainComplexPlus.obj L) :=
  (sections J R TC).rightDerivedFunctorPlusUnit.app
      ((HomotopyCategory.Plus.quotient _).obj I) ≫
    (pullback f d hC hD).app (DerivedCategory.Plus.Q.obj I) ≫
    (sections K R TD).rightDerivedFunctorPlus.map (resolutionIdentification f d I L b) ≫
    inv ((sections K R TD).rightDerivedFunctorPlusUnit.app
      ((HomotopyCategory.Plus.quotient _).obj L))

/-- On injective representatives, the derived unit--Leray map is the actual section map.

Source: Stacks, 071J, 015M, 013P and 013S
(blueprint: lem-pur-site-derived-sections-unit-pasting).

Proof:
1. The unit formula of lem-trf-bounded-below-derived-adjunction identifies the derived
   unit on I with the ordinary unit followed by the right-derived comparison for f_*.
2. Apply the Leray normalization in Comparison. Naturality of the section-derived unit
   turns this composite into the class of ordinaryPullback on I followed by the
   section-derived unit on f-inverse(I).
3. Naturality along b replaces this last complex by L. On the injective complex L its
   section-derived unit is invertible by lem-weil-pbc-right-derived-plus-injective.
   Cancel it to obtain exactly the displayed sectionChainMap.
4. For a degree-zero sheaf M, take injective resolutions M -> I and f-inverse(M) -> L.
   By lem-weil-pbc-lift-along-injective-quasi-iso any comparison b over f-inverse(M)
   exists; its two augmentations make it a quasi-isomorphism. All such b are covered
   by this formula. By lem-weil-pbc-lift-to-injective-unique-up-to-homotopy their section
   maps are homotopic, hence give the same derived arrow and cohomology maps. -/
theorem resolution_formula [∀ n : ℤ, Injective (I.obj.X n)] [QuasiIso b.hom] :
    resolvedPullback f d hC hD I L b =
      DerivedCategory.Plus.Q.map (sectionChainMap f d hC hD I L b) := by
  sorry

/-- In every integer degree, H^q(T) is cohomology of the usual comparison of section complexes.
The homology-factor isomorphisms make the passage from derived objects to actual complexes
explicit, including negative degrees.

Source: Stacks, 071J, 013P and 013S
(blueprint: lem-pur-site-derived-sections-unit-pasting).

Proof: exactness makes the inverse image of a a quasi-isomorphism. The equation
hb and the quasi-isomorphism a' then make b a quasi-isomorphism. Apply H^q to
resolution_formula and use naturality of DerivedCategory.homologyFunctorFactors.
The resulting right hand side is exactly the
cohomology map of ordinary pullback followed by sections of b. Thus every comparison
between the stated resolutions, rather than just one chosen comparison, gives H^q(T). -/
theorem cohomology_resolution_formula [∀ n : ℤ, Injective (I.obj.X n)]
    [I.obj.IsStrictlyGE 0] [L.obj.IsStrictlyGE 0] (M : Modules J R)
    (a : (HomologicalComplex.single (Modules J R) (.up ℤ) 0).obj M ⟶ I.obj)
    [QuasiIso a]
    (a' : (d.moduleFunctor.mapHomologicalComplex (.up ℤ)).obj
      ((HomologicalComplex.single (Modules J R) (.up ℤ) 0).obj M) ⟶ L.obj)
    [QuasiIso a']
    (hb : (d.moduleFunctor.mapHomologicalComplex (.up ℤ)).map a ≫ b.hom = a') (q : ℤ) :
    (DerivedCategory.homologyFunctor.{w} (ModuleCat.{u} R) q).map
        (DerivedCategory.Plus.ι.map (resolvedPullback f d hC hD I L b)) ≫
      (DerivedCategory.homologyFunctorFactors.{w} (ModuleCat.{u} R) q).hom.app
        (((sections K R TD).mapHomologicalComplex (.up ℤ)).obj L.obj) =
    (DerivedCategory.homologyFunctorFactors.{w} (ModuleCat.{u} R) q).hom.app
        (((sections J R TC).mapHomologicalComplex (.up ℤ)).obj I.obj) ≫
      HomologicalComplex.homologyMap (sectionChainMap f d hC hD I L b).hom q := by
  sorry

end Resolutions

/-- Both cohomology groups of the degree-zero pullback vanish in negative degrees.
Source: Stacks, 071J (blueprint: lem-pur-site-derived-sections-unit-pasting).

Proof: choose injective resolutions of M and its inverse image with zero terms below
zero, using lem-weil-pbc-complex-injective-resolution-mono. Applying sections retains
those zero terms. Their cohomology is zero for q < 0. Exact inverse image identifies
its derived value on M[0] with f-inverse(M)[0] by
lem-weil-pbc-exact-functor-derived-factorization. -/
theorem negative_cohomology {TC : C} {TD : D} (hC : IsTerminal TC) (hD : IsTerminal TD)
    (M : Modules J R) (q : ℤ) (hq : q < 0) :
    IsZero ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) q).obj
      ((sections J R TC).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor (Modules J R) 0).obj M))) ∧
    IsZero ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) q).obj
      ((sections K R TD).rightDerivedFunctorPlus.obj
        (d.moduleFunctor.mapDerivedCategoryPlus.obj
          ((DerivedCategory.Plus.singleFunctor (Modules J R) 0).obj M)))) := by
  sorry

end CategoryTheory.SiteDerivedSections
