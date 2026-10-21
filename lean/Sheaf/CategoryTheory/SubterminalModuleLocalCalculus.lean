/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.CategoryTheory.Sites.Subcanonical
import Sheaf.CategoryTheory.ModuleSheafificationRestriction

/-! # Local calculus of module sheaves on two covering subterminals

Source: Stacks Project, Modules on Sites, Tags 03DI, 03DJ and 0F6Z; Sites,
Tag 04B8 (blueprint: lem-sp-subterminal-module-local-calculus).

## Main definitions

* `Intersection`: the module-linear comparisons with their adjunction normalizations.
* `JointDetection`: the zero, exactness, cohomology and quasi-isomorphism tests.
* `nested`: the canonical map induced by an inclusion of subterminals.

## Main statements

* `subterminal_module_local_calculus`: the full calculus for a binary subterminal cover.
-/

@[expose] public noncomputable section
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe c v r a b ha hb wa wb w s
open CategoryTheory CategoryTheory.Limits Opposite
namespace SheafOfModules.SubterminalLocal

/-- The coefficient ring sheaf used by the recorded module-sheaf category.
Source: Stacks 03DI (blueprint: lem-sp-subterminal-module-local-calculus). -/
abbrev coefficients {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{max c v r}) : Sheaf J RingCat.{max c v r} :=
  (sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R

/-- The recorded module sheafification with identity coefficient map.
Source: Stacks 03DI (blueprint: lem-sp-subterminal-module-local-calculus). -/
abbrev sheafify {D : Type a} [Category.{ha} D] {K : GrothendieckTopology D}
    [HasSheafify K AddCommGrpCat.{s}] [K.WEqualsLocallyBijective AddCommGrpCat.{s}]
    (S : Sheaf K RingCat.{s}) :=
  PresheafOfModules.sheafification.{s, ha, s, a}
    (J := K) (R := S) (R₀ := S.obj) (𝟙 S.obj)

/-- Modules on the ambient ringed site.
Source: Stacks 03DI (blueprint: lem-sp-subterminal-module-local-calculus). -/
abbrev Modules {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{max c v r}) :=
  ringedSiteModules.{max c v r} (coefficients.{c, v, r} R)

/-- Modules on a slice ringed site.
Source: Stacks 03DI (blueprint: lem-sp-subterminal-module-local-calculus). -/
abbrev SliceModules {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{max c v r}) (Z : C) :=
  ringedSiteModules.{max c v r} ((coefficients.{c, v, r} R).over Z)

variable {C : Type c} [Category.{v} C] [HasFiniteLimits C]
  {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{max c v r})

/-- The exact extension-by-zero functor supplied by the localized-site framework.
Source: Stacks 03DI--03DJ (blueprint: lem-sp-subterminal-module-local-calculus). -/
abbrev jbang (Z : C) : SliceModules.{c, v, r} R Z ⥤ Modules.{c, v, r} R :=
  localizedSystemExtension.{c, v, r} R Z

/-- Restriction to a slice, supplied by the localized-site framework.
Source: Stacks 03DH (blueprint: lem-sp-subterminal-module-local-calculus). -/
abbrev jstar (Z : C) : Modules.{c, v, r} R ⥤ SliceModules.{c, v, r} R Z :=
  localizedSystemRestriction.{c, v, r} R Z

/-- The recorded extension/restriction adjunction.
Source: Stacks 03DI (blueprint: lem-sp-subterminal-module-local-calculus). -/
abbrev adj (Z : C) : jbang.{c, v, r} R Z ⊣ jstar.{c, v, r} R Z :=
  localizedSystemAdjunction.{c, v, r} R Z

/-- The canonical nested-open map, obtained by transposing restriction of the unit.
Source: Stacks 03DI and 04IY (blueprint: lem-sp-subterminal-module-local-calculus). -/
def nested {A B : C} (f : A ⟶ B) (M : Modules.{c, v, r} R) :
    (jbang.{c, v, r} R A).obj ((jstar.{c, v, r} R A).obj M) ⟶
      (jbang.{c, v, r} R B).obj ((jstar.{c, v, r} R B).obj M) :=
  ((adj.{c, v, r} R A).homEquiv _ _).symm
    ((overFunctorMap.{max c v r} (coefficients.{c, v, r} R) f).inv.app M ≫
      (overMap.{max c v r} (coefficients.{c, v, r} R) f).map
        ((adj.{c, v, r} R B).unit.app ((jstar.{c, v, r} R B).obj M)) ≫
      (overFunctorMap.{max c v r} (coefficients.{c, v, r} R) f).hom.app
        ((jbang.{c, v, r} R B).obj ((jstar.{c, v, r} R B).obj M)))

/-- Restriction commutes with sheafification on the original presheaf sections.
Source: Stacks 04B8 and 04IY (blueprint: lem-sp-subterminal-module-local-calculus). -/
def SheafificationRestriction (Z : C) : Prop :=
  ∃ e : PresheafOfModules.pushforward.{max c v r} (F := Over.forget Z)
        (𝟙 ((coefficients.{c, v, r} R).over Z).obj) ⋙
        sheafify.{max c v, v, max c v r} ((coefficients.{c, v, r} R).over Z) ≅
      sheafify.{c, v, max c v r} (coefficients.{c, v, r} R) ⋙ jstar.{c, v, r} R Z,
    ∀ (P : PresheafOfModules.{max c v r} (coefficients.{c, v, r} R).obj)
      (X : (Over Z)ᵒᵖ) (x : P.obj (op X.unop.left)),
      (e.hom.app P).val.app X
        (((PresheafOfModules.sheafificationAdjunction.{max c v r}
          (J := J.over Z) (R := (coefficients.{c, v, r} R).over Z)
          (𝟙 ((coefficients.{c, v, r} R).over Z).obj)).unit.app
            ((PresheafOfModules.pushforward.{max c v r}
              (F := Over.forget Z) (𝟙 _)).obj P)).app X x) =
        ((PresheafOfModules.sheafificationAdjunction.{max c v r}
          (J := J) (R := coefficients.{c, v, r} R)
          (𝟙 (coefficients.{c, v, r} R).obj)).unit.app P).app (op X.unop.left) x

/-- The same unit-normalized sheafification comparison for further slice restriction.
Source: Stacks 04B8 and 04IY (blueprint: lem-sp-subterminal-module-local-calculus). -/
def MapSheafificationRestriction {Y Z : C} (f : Y ⟶ Z) : Prop :=
  ∃ e : PresheafOfModules.pushforward.{max c v r} (F := Over.map f)
        (Sheaf.pushforwardOverMapIso (coefficients.{c, v, r} R) f).inv.hom ⋙
        sheafify.{max c v, v, max c v r} ((coefficients.{c, v, r} R).over Y) ≅
      sheafify.{max c v, v, max c v r} ((coefficients.{c, v, r} R).over Z) ⋙
        overMap.{max c v r} (coefficients.{c, v, r} R) f,
    ∀ (P : PresheafOfModules.{max c v r} ((coefficients.{c, v, r} R).over Z).obj)
      (X : (Over Y)ᵒᵖ) (x : P.obj ((Over.map f).op.obj X)),
      (e.hom.app P).val.app X
        (((PresheafOfModules.sheafificationAdjunction.{max c v r}
          (J := J.over Y) (R := (coefficients.{c, v, r} R).over Y)
          (𝟙 ((coefficients.{c, v, r} R).over Y).obj)).unit.app
            ((PresheafOfModules.pushforward.{max c v r} (F := Over.map f)
              (Sheaf.pushforwardOverMapIso (coefficients.{c, v, r} R) f).inv.hom).obj P)).app
                X x) =
        ((PresheafOfModules.sheafificationAdjunction.{max c v r}
          (J := J.over Z) (R := (coefficients.{c, v, r} R).over Z)
          (𝟙 ((coefficients.{c, v, r} R).over Z).obj)).unit.app P).app
            ((Over.map f).op.obj X) x

open Classical in
/-- The explicit pre-sheaf extension-by-zero formula before sheafification.
Source: Stacks 03DI and 0F6Z (blueprint: lem-sp-subterminal-module-local-calculus). -/
def PresheafFormula (Z : C) : Prop :=
  ∀ (F : SliceModules.{c, v, r} R Z) (X : C),
    ((¬ Nonempty (X ⟶ Z)) →
      Subsingleton (extensionByZeroPresheafSection.{max c v r}
        (coefficients.{c, v, r} R) Z F (op X))) ∧
    (∀ a : X ⟶ Z, ∃ e : extensionByZeroPresheafSection.{max c v r}
      (coefficients.{c, v, r} R) Z F (op X) ≅ F.val.obj (op (Over.mk a)),
      ∀ x : F.val.obj (op (Over.mk a)),
        e.hom (DirectSum.of (fun b : X ⟶ Z ↦ F.val.obj (op (Over.mk b))) a x) = x)

/-- Restriction from the intersection slice and its extension are exact termwise.
The corresponding derived statement is recorded separately by `DerivedExact`.
Source: Stacks 03DI--03DJ (blueprint: lem-sp-subterminal-module-local-calculus). -/
structure ExactRestriction {A : Type a} [Category.{ha} A] [Abelian A]
    {B : Type b} [Category.{hb} B] [Abelian B] (F : A ⥤ B) : Prop where
  additive : F.Additive
  finiteLimits : PreservesFiniteLimits F
  finiteColimits : PreservesFiniteColimits F
  homology (q : ℤ) : Nonempty
    (F.mapHomologicalComplex (.up ℤ) ⋙ HomologicalComplex.homologyFunctor B (.up ℤ) q ≅
      HomologicalComplex.homologyFunctor A (.up ℤ) q ⋙ F)

/-- The derived-category part of termwise exactness.
Source: Stacks 03DI--03DJ (blueprint: lem-sp-subterminal-module-local-calculus). -/
def DerivedExact {A : Type a} [Category.{ha} A] [Abelian A]
    {B : Type b} [Category.{hb} B] [Abelian B] (F : A ⥤ B) : Prop :=
  ∀ [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [HasDerivedCategory.{wa} A] [HasDerivedCategory.{wb} B],
    F.mapDerivedCategory.IsTriangulated ∧
      Nonempty (DerivedCategory.Q ⋙ F.mapDerivedCategory ≅
        F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) ∧
      (∀ q : ℤ, Nonempty
        (F.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor B q ≅
          DerivedCategory.homologyFunctor A q ⋙ F))

/-- Intersection exchange and the two adjunctions on a covering pair.
The natural-isomorphism fields express the two cross-restriction formulas.
Their unit, counit and nested-map equations fix the canonical normalizations.
Source: Stacks 03DI, 0F6Z and 04IY (blueprint: lem-sp-subterminal-module-local-calculus). -/
structure Intersection (U V W : C) (f : W ⟶ U) (g : W ⟶ V) where
  kU : SliceModules.{c, v, r} R W ⥤ SliceModules.{c, v, r} R U
  kV : SliceModules.{c, v, r} R W ⥤ SliceModules.{c, v, r} R V
  adjU : kU ⊣ overMap.{max c v r} (coefficients.{c, v, r} R) f
  adjV : kV ⊣ overMap.{max c v r} (coefficients.{c, v, r} R) g
  exactU : ExactRestriction kU
  exactV : ExactRestriction kV
  restrictionU : ExactRestriction (overMap.{max c v r} (coefficients.{c, v, r} R) f)
  restrictionV : ExactRestriction (overMap.{max c v r} (coefficients.{c, v, r} R) g)
  derivedU : DerivedExact.{_, _, _, _, w, w} kU
  derivedV : DerivedExact.{_, _, _, _, w, w} kV
  derivedRestrictionU : DerivedExact.{_, _, _, _, w, w}
    (overMap.{max c v r} (coefficients.{c, v, r} R) f)
  derivedRestrictionV : DerivedExact.{_, _, _, _, w, w}
    (overMap.{max c v r} (coefficients.{c, v, r} R) g)
  sheafificationU : MapSheafificationRestriction.{c, v, r} R f
  sheafificationV : MapSheafificationRestriction.{c, v, r} R g
  selfU : jbang.{c, v, r} R U ⋙ jstar.{c, v, r} R U ≅ 𝟭 _
  selfV : jbang.{c, v, r} R V ⋙ jstar.{c, v, r} R V ≅ 𝟭 _
  selfU_unit : selfU.inv = (adj.{c, v, r} R U).unit
  selfV_unit : selfV.inv = (adj.{c, v, r} R V).unit
  composeU : kU ⋙ jbang.{c, v, r} R U ≅ jbang.{c, v, r} R W
  composeV : kV ⋙ jbang.{c, v, r} R V ≅ jbang.{c, v, r} R W
  composeU_unit (F : SliceModules.{c, v, r} R W) :
    (adj.{c, v, r} R W).unit.app F = (adjU.comp (adj.{c, v, r} R U)).unit.app F ≫
      (overMap.{max c v r} (coefficients.{c, v, r} R) f).map
        ((jstar.{c, v, r} R U).map (composeU.hom.app F)) ≫
      (overFunctorMap.{max c v r} (coefficients.{c, v, r} R) f).hom.app
        ((jbang.{c, v, r} R W).obj F)
  composeV_unit (F : SliceModules.{c, v, r} R W) :
    (adj.{c, v, r} R W).unit.app F = (adjV.comp (adj.{c, v, r} R V)).unit.app F ≫
      (overMap.{max c v r} (coefficients.{c, v, r} R) g).map
        ((jstar.{c, v, r} R V).map (composeV.hom.app F)) ≫
      (overFunctorMap.{max c v r} (coefficients.{c, v, r} R) g).hom.app
        ((jbang.{c, v, r} R W).obj F)
  exchangeU : jbang.{c, v, r} R V ⋙ jstar.{c, v, r} R U ≅
    overMap.{max c v r} (coefficients.{c, v, r} R) g ⋙ kU
  exchangeV : jbang.{c, v, r} R U ⋙ jstar.{c, v, r} R V ≅
    overMap.{max c v r} (coefficients.{c, v, r} R) f ⋙ kV
  exchangeU_unit (F : SliceModules.{c, v, r} R V) :
    (overMap.{max c v r} (coefficients.{c, v, r} R) g).map
      ((adj.{c, v, r} R V).unit.app F) ≫
      (overFunctorMap.{max c v r} (coefficients.{c, v, r} R) g).hom.app
        ((jbang.{c, v, r} R V).obj F) =
    adjU.unit.app ((overMap.{max c v r} (coefficients.{c, v, r} R) g).obj F) ≫
      (overMap.{max c v r} (coefficients.{c, v, r} R) f).map (exchangeU.inv.app F) ≫
      (overFunctorMap.{max c v r} (coefficients.{c, v, r} R) f).hom.app
        ((jbang.{c, v, r} R V).obj F)
  exchangeV_unit (F : SliceModules.{c, v, r} R U) :
    (overMap.{max c v r} (coefficients.{c, v, r} R) f).map
      ((adj.{c, v, r} R U).unit.app F) ≫
      (overFunctorMap.{max c v r} (coefficients.{c, v, r} R) f).hom.app
        ((jbang.{c, v, r} R U).obj F) =
    adjV.unit.app ((overMap.{max c v r} (coefficients.{c, v, r} R) f).obj F) ≫
      (overMap.{max c v r} (coefficients.{c, v, r} R) g).map (exchangeV.inv.app F) ≫
      (overFunctorMap.{max c v r} (coefficients.{c, v, r} R) g).hom.app
        ((jbang.{c, v, r} R U).obj F)
  exchangeU_counit (M : Modules.{c, v, r} R) :
    (jstar.{c, v, r} R U).map ((adj.{c, v, r} R V).counit.app M) =
      exchangeU.hom.app ((jstar.{c, v, r} R V).obj M) ≫
      kU.map ((overFunctorMap.{max c v r} (coefficients.{c, v, r} R) g).hom.app M) ≫
      kU.map ((overFunctorMap.{max c v r} (coefficients.{c, v, r} R) f).inv.app M) ≫
      adjU.counit.app ((jstar.{c, v, r} R U).obj M)
  exchangeV_counit (M : Modules.{c, v, r} R) :
    (jstar.{c, v, r} R V).map ((adj.{c, v, r} R U).counit.app M) =
      exchangeV.hom.app ((jstar.{c, v, r} R U).obj M) ≫
      kV.map ((overFunctorMap.{max c v r} (coefficients.{c, v, r} R) f).hom.app M) ≫
      kV.map ((overFunctorMap.{max c v r} (coefficients.{c, v, r} R) g).inv.app M) ≫
      adjV.counit.app ((jstar.{c, v, r} R V).obj M)
  nestedU_self (M : Modules.{c, v, r} R) :
    (jstar.{c, v, r} R U).map (nested.{c, v, r} R f M) ≫
      selfU.hom.app ((jstar.{c, v, r} R U).obj M) =
    (jstar.{c, v, r} R U).map
      (composeU.inv.app ((jstar.{c, v, r} R W).obj M)) ≫
      selfU.hom.app (kU.obj ((jstar.{c, v, r} R W).obj M)) ≫
      kU.map ((overFunctorMap.{max c v r} (coefficients.{c, v, r} R) f).inv.app M) ≫
      adjU.counit.app ((jstar.{c, v, r} R U).obj M)
  nestedU_cross (M : Modules.{c, v, r} R) :
    (jstar.{c, v, r} R V).map (nested.{c, v, r} R f M) ≫
      exchangeV.hom.app ((jstar.{c, v, r} R U).obj M) =
    (jstar.{c, v, r} R V).map
      (composeV.inv.app ((jstar.{c, v, r} R W).obj M)) ≫
      selfV.hom.app (kV.obj ((jstar.{c, v, r} R W).obj M)) ≫
      kV.map ((overFunctorMap.{max c v r} (coefficients.{c, v, r} R) f).inv.app M)
  nestedU_counit (M : Modules.{c, v, r} R) :
    nested.{c, v, r} R f M ≫ (adj.{c, v, r} R U).counit.app M =
      (adj.{c, v, r} R W).counit.app M
  nestedV_self (M : Modules.{c, v, r} R) :
    (jstar.{c, v, r} R V).map (nested.{c, v, r} R g M) ≫
      selfV.hom.app ((jstar.{c, v, r} R V).obj M) =
    (jstar.{c, v, r} R V).map
      (composeV.inv.app ((jstar.{c, v, r} R W).obj M)) ≫
      selfV.hom.app (kV.obj ((jstar.{c, v, r} R W).obj M)) ≫
      kV.map ((overFunctorMap.{max c v r} (coefficients.{c, v, r} R) g).inv.app M) ≫
      adjV.counit.app ((jstar.{c, v, r} R V).obj M)
  nestedV_cross (M : Modules.{c, v, r} R) :
    (jstar.{c, v, r} R U).map (nested.{c, v, r} R g M) ≫
      exchangeU.hom.app ((jstar.{c, v, r} R V).obj M) =
    (jstar.{c, v, r} R U).map
      (composeU.inv.app ((jstar.{c, v, r} R W).obj M)) ≫
      selfU.hom.app (kU.obj ((jstar.{c, v, r} R W).obj M)) ≫
      kU.map ((overFunctorMap.{max c v r} (coefficients.{c, v, r} R) g).inv.app M)
  nestedV_counit (M : Modules.{c, v, r} R) :
    nested.{c, v, r} R g M ≫ (adj.{c, v, r} R V).counit.app M =
      (adj.{c, v, r} R W).counit.app M

/-- Joint detection on modules, complexes and ordinary derived categories.
Source: Stacks 03DI--03DJ and the covering-pair proof
(blueprint: lem-sp-subterminal-module-local-calculus). -/
def JointDetection (U V : C) : Prop :=
  (∀ M : Modules.{c, v, r} R,
    IsZero M ↔ IsZero ((jstar.{c, v, r} R U).obj M) ∧
      IsZero ((jstar.{c, v, r} R V).obj M)) ∧
  (∀ (M N : Modules.{c, v, r} R) (a : M ⟶ N),
    a = 0 ↔ (jstar.{c, v, r} R U).map a = 0 ∧
      (jstar.{c, v, r} R V).map a = 0) ∧
  (∀ K : ShortComplex (Modules.{c, v, r} R),
    K.Exact ↔ (K.map (jstar.{c, v, r} R U)).Exact ∧
      (K.map (jstar.{c, v, r} R V)).Exact) ∧
  (∀ (K : CochainComplex (Modules.{c, v, r} R) ℤ) (q : ℤ),
    IsZero (K.homology q) ↔
      IsZero ((((jstar.{c, v, r} R U).mapHomologicalComplex (.up ℤ)).obj K).homology q) ∧
      IsZero ((((jstar.{c, v, r} R V).mapHomologicalComplex (.up ℤ)).obj K).homology q)) ∧
  (∀ (K L : CochainComplex (Modules.{c, v, r} R) ℤ) (a : K ⟶ L),
    QuasiIso a ↔
      QuasiIso (((jstar.{c, v, r} R U).mapHomologicalComplex (.up ℤ)).map a) ∧
      QuasiIso (((jstar.{c, v, r} R V).mapHomologicalComplex (.up ℤ)).map a)) ∧
  (∀ [HasDerivedCategory.{w} (Modules.{c, v, r} R)]
    [HasDerivedCategory.{w} (SliceModules.{c, v, r} R U)]
    [HasDerivedCategory.{w} (SliceModules.{c, v, r} R V)]
    (K : DerivedCategory (Modules.{c, v, r} R)) (q : ℤ),
    IsZero ((DerivedCategory.homologyFunctor (Modules.{c, v, r} R) q).obj K) ↔
      IsZero ((DerivedCategory.homologyFunctor (SliceModules.{c, v, r} R U) q).obj
        ((jstar.{c, v, r} R U).mapDerivedCategory.obj K)) ∧
      IsZero ((DerivedCategory.homologyFunctor (SliceModules.{c, v, r} R V) q).obj
        ((jstar.{c, v, r} R V).mapDerivedCategory.obj K))) ∧
  (∀ [HasDerivedCategory.{w} (Modules.{c, v, r} R)]
    [HasDerivedCategory.{w} (SliceModules.{c, v, r} R U)]
    [HasDerivedCategory.{w} (SliceModules.{c, v, r} R V)]
    (K L : DerivedCategory (Modules.{c, v, r} R)) (a : K ⟶ L),
    IsIso a ↔ IsIso ((jstar.{c, v, r} R U).mapDerivedCategory.map a) ∧
      IsIso ((jstar.{c, v, r} R V).mapDerivedCategory.map a))

/-- Local calculus for two covering subterminal objects.
Source: Stacks Project, Modules on Sites, Tags 03DI, 03DJ and 0F6Z; Sites,
Tag 04B8 (blueprint: lem-sp-subterminal-module-local-calculus).
Proof (the nine DAG steps):
1. Apply [lem-pur-site-restriction-module-adjunction-exact] with coefficient sheaf $R$ and object
   $Z$, for $Z=U,V,W$. It gives exact restriction and its exact left adjoint, constructed as the
   module sheafification of [def-weil-extension-by-zero-presheaf]. Since $Z\hookrightarrow1$ is
   monic, any two arrows $C\to Z$ coincide. Thus the direct sum defining that presheaf has one
   summand $F(C\to Z)$ or no summands, giving exactly $P_F$ in the statement, with its specified
   $R(C)$-action and restrictions. Restriction is additive sectionwise; extension is additive
   because both the summand maps and sheafification preserve addition of morphisms (the latter
   follows from its linear universal property [def-weil-presheaf-modules-sheafification]). Apply
   the same exact-adjunction lemma on $\mathcal E/U$ at $W\to U$ and on $\mathcal E/V$ at $W\to
   V$ to obtain $k_{U!}$ and $k_{V!}$. Their coefficient rings are the literal restrictions of
   $R$ by [def-pur-localized-ringed-site].
2. For $q:\mathcal E/Z\to\mathcal E$, every covering of $(C\to Z)$ is an underlying covering of
   $C$, and every covering of $C$ lifts to one of $(C\to Z)$ by composing its arrows with $C\to
   Z$. Pullbacks of these covering arrows are the same in the slice and the base. Thus $q$ is
   continuous and cocontinuous. The identical verification applies to further slice restriction.
   Apply [lem-weil-pbc-module-sheafification-restriction] to these functors: restriction of
   $P^\#$ is canonically the sheafification of the restricted module presheaf, and the comparison
   sends the unit image of each presheaf section to the same unit image. This also fixes the
   normalization of all comparisons below. The smallness hypothesis holds for the slices, and
   their ring sheaves are restrictions along the identity coefficient map.
3. On an object $(C\to U)$, the presheaf extending $F$ from $\mathcal E/U$ evaluates to $F(C\to
   U)$, since the arrow to $U$ is unique. Consequently its restriction to $\mathcal E/U$ is
   exactly the already sheaf-valued presheaf $F$. Step 2 and the universal property of
   [def-weil-presheaf-modules-sheafification] identify $j_U^*j_{U!}F$ with $F$, with the unit
   $F\to j_U^*j_{U!}F$ corresponding to the identity. Interchanging $U$ and $V$ gives the other
   self-restriction identification.
4. Let $F$ be an $R|_V$-module sheaf. At $(C,a:C\to U)$ the presheaf underlying $j_U^*j_{V!}F$
   before sheafification is $F(C\to V)$ if $C\to V$ exists, and zero otherwise. An arrow $b:C\to
   V$ is equivalent, by the product universal property, to an arrow $(a,b):C\to W$ over $U$. The
   presheaf extending $k_V^*F$ from $\mathcal E/W$ to $\mathcal E/U$ therefore has precisely the
   same values. Its restrictions are those of $F$ when the source has an arrow to $V$, and zero
   out of a zero summand otherwise, on both sides. The scalar ring on each summand is $R(C)$ on
   both sides. Sheafifying this identity and using Step 2 gives $j_U^*j_{V!}\cong k_{U!}k_V^*$.
   The identity commutes with maps $F\to F'$, so is natural. Interchanging $U,V$ proves the
   remaining intersection identification.
5. The adjunction of Step 1 can be computed directly from the universal property in
   [def-weil-presheaf-modules-sheafification]. A map $a:F\to j_Z^*G$ induces $j_{Z!}F\to G$ by
   sending a summand section $s\in F(C\to Z)$ to $a_{(C\to Z)}(s)\in G(C)$; conversely precompose
   a restricted map with the summand inclusion $F(C\to Z)\to P_F(C)\to P_F^\#(C)$. These
   operations are inverse, since every map out of the sheafification is determined on those
   summand sections. Hence the unit is this summand inclusion and the counit sends each summand
   section of $G(C)$ to that same section of $G(C)$. Under Steps 3 and 4 all nonzero summands and
   their sections are identified by identity maps. Step 2 preserves their sheafification-unit
   images. Thus the unit and counit diagrams commute on every presheaf summand, hence after
   sheafification by its universal property.
6. For nested subterminals $A\hookrightarrow B\hookrightarrow1$, write $h^*$ for restriction from
   the $B$-slice to the $A$-slice and $h_!$ for its left adjoint. Composition of the natural Hom
   bijections of Step 1 identifies $j_{B!}h_!$ with $j_{A!}$: both represent
   $F\mapsto\operatorname{Hom}(F,j_A^*G)$, and the identification is uniquely fixed by the
   summand section maps. The nested-open map $j_{A!}h^*H\to j_{B!}H$ is $j_{B!}$ of the counit
   $h_!h^*H\to H$. By Step 5 it sends the summand indexed by $C\to A$ to the summand indexed by
   its composite $C\to B$, carrying $s$ to $s$. Restriction and the intersection identifications
   send the same section to $s$ whenever that summand exists; otherwise the source is zero.
   Therefore their diagrams with nested-open maps commute, again by the sheafification universal
   property. This covers the inclusions of $W$ in $U,V$ and their inclusions in $1$.
7. For any $C$, pullback stability of the covering sieve generated by $U,V\to1$ says that
   $C\times U\to C$ and $C\times V\to C$ generate a covering sieve. If $j_U^*M=j_V^*M=0$, a
   section $s\in M(C)$ restricts to zero on both objects, since they map to $U$ and $V$. Every
   arrow in the covering sieve factors through one of them, so all restrictions of $s$ on that
   sieve are zero. Uniqueness in the sheaf condition gives $s=0$. Thus all section modules vanish
   and $M=0$. The same argument applied to the section $t_C(s)$ proves that a morphism $t:M\to N$
   whose two restrictions are zero is zero. This uses only the site axioms and the sheaf
   condition in [def-weil-sheaf-of-modules-category], not existence of points.
8. For module maps $A\xrightarrow{f}B\xrightarrow{g}C$ whose restrictions are exact, the
   restrictions of $gf$ vanish, so Step 7 gives $gf=0$. Form $H=\ker(g)/\operatorname{im}(f)$ in
   the abelian category of module sheaves [def-weil-sheaf-of-modules-category]. By exactness of
   the two restriction functors from Step 1 and [lem-sp-exact-functor-preserves-homology],
   $j_Z^*H\cong\ker(j_Z^*g)/\operatorname{im}(j_Z^*f)=0$ for $Z=U,V$. Step 7 gives $H=0$, which
   is exactly exactness at $B$. Conversely, the two exact functors preserve exactness by the same
   cited lemma. Applying this to each successive triple proves joint detection for sequences,
   including endpoint mono/epi conditions by inserting zero objects.
9. Apply [lem-weil-pbc-exact-functor-complex-cohomology] to exact restriction: $H^q(j_Z^*K)\cong
   j_Z^*H^q(K)$ naturally, for every integer $q$. Step 7 now gives joint detection of vanishing
   of each $H^q(K)$. For a chain map $a$, exact restriction preserves its cohomology kernels and
   cokernels by [lem-sp-exact-functor-preserves-homology]. If both restrictions of $a$ are
   quasi-isomorphisms, these kernels and cokernels restrict to zero; Step 7 makes them zero, so
   each $H^q(a)$ is an isomorphism and $a$ is a quasi-isomorphism. The converse follows from the
   cohomology comparison. Finally apply [lem-sf-exact-functor-derived-triangulated] to all exact
   restriction and extension functors of Step 1: their termwise actions descend to the ordinary
   unbounded derived categories as triangulated functors. The natural cohomology comparison
   descends through localization [def-weil-abstract-derived-category], so the same cohomological
   vanishing tests hold there, with no boundedness assumption.
-/
theorem subterminal_module_local_calculus
    [J.Subcanonical]
    (U V : C) [Mono (terminal.from U)] [Mono (terminal.from V)]
    (hcover : Sieve.ofArrows (fun b : Bool ↦ if b then U else V)
      (fun b ↦ terminal.from (if b then U else V)) ∈ J (⊤_ C)) :
    Nonempty (Intersection.{c, v, r, w} R U V (U ⨯ V) prod.fst prod.snd) ∧
    (∀ Z : C, Z = U ∨ Z = V ∨ Z = (U ⨯ V) →
      ExactRestriction (jstar.{c, v, r} R Z) ∧
      ExactRestriction (jbang.{c, v, r} R Z) ∧
      DerivedExact.{_, _, _, _, w, w} (jstar.{c, v, r} R Z) ∧
      DerivedExact.{_, _, _, _, w, w} (jbang.{c, v, r} R Z) ∧
      PresheafFormula.{c, v, r} R Z ∧ SheafificationRestriction.{c, v, r} R Z) ∧
    JointDetection.{c, v, r, w} R U V := by
  sorry

end SheafOfModules.SubterminalLocal
