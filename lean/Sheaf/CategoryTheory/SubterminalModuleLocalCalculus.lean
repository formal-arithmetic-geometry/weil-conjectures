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
import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Sites.CoversTop.Basic
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization
import Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Adjunction.Additive

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

section LocalCalculusProof
set_option backward.defeqAttrib.useBackward true

section SheafificationComparison

open PresheafOfModules
variable {D : Type a} [Category.{ha} D] {E : Type b} [Category.{hb} E]
  {K : GrothendieckTopology D} {L : GrothendieckTopology E}
  [HasSheafify K AddCommGrpCat.{s}] [K.WEqualsLocallyBijective AddCommGrpCat.{s}]
  [HasSheafify L AddCommGrpCat.{s}] [L.WEqualsLocallyBijective AddCommGrpCat.{s}]
  (F : D ⥤ E) [F.IsContinuous K L] [F.IsCocontinuous K L]
  (S : Sheaf L RingCat.{s})

private def restrictedRing : Sheaf K RingCat.{s} :=
  (F.sheafPushforwardContinuous RingCat.{s} K L).obj S

private def restrictionP : PresheafOfModules.{s} S.obj ⥤
    PresheafOfModules.{s} (restrictedRing (K := K) F S).obj :=
  PresheafOfModules.pushforward (F := F) (𝟙 _)

private def restrictionS : SheafOfModules.{s} S ⥤
    SheafOfModules.{s} (restrictedRing (K := K) F S) :=
  SheafOfModules.pushforward (F := F) (𝟙 _)

private def restrictionUnit (M : PresheafOfModules.{s} S.obj) :
    (restrictionP (K := K) F S).obj M ⟶
      (SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars (𝟙 (restrictedRing (K := K) F
        S).obj)).obj
        ((restrictionS (K := K) F S).obj
          ((PresheafOfModules.sheafification.{s} (J := L) (R := S) (R₀ := S.obj) (𝟙 S.obj)).obj
            M)) :=
  (restrictionP (K := K) F S).map
    ((PresheafOfModules.sheafificationAdjunction (J := L) (R := S) (𝟙 S.obj)).unit.app M)

omit [HasSheafify K AddCommGrpCat.{s}] in
private theorem restrictionUnit_W (M : PresheafOfModules.{s} S.obj) :
    K.W ((PresheafOfModules.toPresheaf _).map (restrictionUnit (K := K) F S M)) := by
  let η := CategoryTheory.toSheafify L M.presheaf
  change K.W (Functor.whiskerLeft F.op η)
  have : Presheaf.IsLocallyInjective K (Functor.whiskerLeft F.op η) :=
    Presheaf.isLocallyInjective_whisker K L F η
  have : Presheaf.IsLocallySurjective K (Functor.whiskerLeft F.op η) :=
    Presheaf.isLocallySurjective_whisker K L F η
  exact K.W_of_isLocallyBijective _

private theorem restrictionComparison_isIso (M : PresheafOfModules.{s} S.obj) :
    IsIso (((PresheafOfModules.sheafificationAdjunction (𝟙 (restrictedRing (K := K) F
      S).obj)).homEquiv _ _).symm
      (restrictionUnit (K := K) F S M)) := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 (restrictedRing (K := K) F S).obj)
  let T := PresheafOfModules.sheafification (𝟙 (restrictedRing (K := K) F S).obj)
  have h := restrictionUnit_W (K := K) F S M
  have : IsIso (T.map (restrictionUnit (K := K) F S M)) := by
    change ((MorphismProperty.isomorphisms _).inverseImage T) _
    rw [← PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms]
    exact h
  rw [Adjunction.homEquiv_counit]
  infer_instance

/-- Sheafification commutes with restriction along a continuous, cocontinuous functor.
Source: Stacks 04B8 and 04IY; the proof of `ModuleSheafificationRestriction` with independent
site, hom and coefficient universes. Restrict the sheafification unit and transpose it under
sheafification on the source. Cocontinuity preserves local bijectivity, so this transpose is
invertible. Naturality and the normalization follow from the adjunction hom equivalence. -/
private theorem exists_comparison :
    ∃ z : PresheafOfModules.pushforward (F := F) (𝟙 ((F.sheafPushforwardContinuous RingCat.{s} K
      L).obj S).obj) ⋙
        PresheafOfModules.sheafification (𝟙 ((F.sheafPushforwardContinuous RingCat.{s} K L).obj
          S).obj) ≅
      PresheafOfModules.sheafification.{s} (J := L) (R := S) (R₀ := S.obj) (𝟙 S.obj) ⋙
        SheafOfModules.pushforward (F := F)
          (𝟙 ((F.sheafPushforwardContinuous RingCat.{s} K L).obj S)),
      ∀ (M : PresheafOfModules.{s} S.obj) (X : Dᵒᵖ)
        (x : M.obj (F.op.obj X)),
        ((z.app M).hom.val.app X)
          (((PresheafOfModules.sheafificationAdjunction
            (𝟙 ((F.sheafPushforwardContinuous RingCat.{s} K L).obj S).obj)).unit.app
              ((PresheafOfModules.pushforward (F := F) (𝟙 _)).obj M)).app X x) =
            ((PresheafOfModules.sheafificationAdjunction (J := L) (R := S) (𝟙 S.obj)).unit.app
              M).app
              (F.op.obj X) x := by
  let P := restrictionP (K := K) F S
  let Q := restrictionS (K := K) F S
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 (restrictedRing (K := K) F S).obj)
  let T := PresheafOfModules.sheafification (𝟙 (restrictedRing (K := K) F S).obj)
  let t : P ⋙ T ⟶ PresheafOfModules.sheafification.{s} (J := L) (R := S) (R₀ := S.obj) (𝟙 S.obj) ⋙
    Q :=
    { app M := (adj.homEquiv _ _).symm (restrictionUnit (K := K) F S M)
      naturality := by
        intro M N f
        apply (adj.homEquiv _ _).injective
        simp only [CategoryTheory.Functor.comp_map]
        rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
        simp only [Equiv.apply_symm_apply]
        have h := (PresheafOfModules.sheafificationAdjunction (J := L) (R := S) (𝟙
          S.obj)).unit.naturality f
        ext X x
        exact congrArg (fun z ↦ z.app (F.op.obj X) x) h }
  have ht : IsIso t := (NatTrans.isIso_iff_isIso_app t).2
    (fun M => restrictionComparison_isIso (K := K) F S M)
  refine ⟨asIso t, ?_⟩
  intro M X x
  have h := (adj.homEquiv _ _).apply_symm_apply (restrictionUnit (K := K) F S M)
  exact congrArg (fun z ↦ z.app X x) h

end SheafificationComparison

omit [HasFiniteLimits C] in
private theorem sheafificationRestriction (Z : C) :
    SheafificationRestriction.{c, v, r} R Z := by
  exact exists_comparison (Over.forget Z) (coefficients.{c, v, r} R)

omit [HasFiniteLimits C] in
private theorem mapSheafificationRestriction {A B : C} (f : A ⟶ B) :
    MapSheafificationRestriction.{c, v, r} R f := by
  exact exists_comparison (Over.map f) ((coefficients.{c, v, r} R).over B)

private theorem exactRestriction_of_exact
    {A : Type a} [Category.{ha} A] [Abelian A]
    {B : Type b} [Category.{hb} B] [Abelian B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    ExactRestriction F :=
  ⟨inferInstance, inferInstance, inferInstance,
    fun q ↦ ⟨F.mapHomologicalComplexHomologyIso (.up ℤ) q⟩⟩

private theorem derivedExact_of_exact
    {A : Type a} [Category.{ha} A] [Abelian A]
    {B : Type b} [Category.{hb} B] [Abelian B] (F : A ⥤ B) :
    DerivedExact.{_, _, _, _, wa, wb} F := by
  intro _ _ _ _ _
  exact ⟨inferInstance, ⟨F.mapDerivedCategoryFactors⟩,
    fun q ↦ ⟨(F.mapDerivedCategoryHomologyFunctorIso q).symm⟩⟩

private theorem presheafFormula_of_subterminal (Z : C) [Mono (terminal.from Z)] :
    PresheafFormula.{c, v, r} R Z := by
  classical
  intro F X
  have : Subsingleton (X ⟶ Z) := ⟨fun a b ↦ by
    apply (cancel_mono (terminal.from Z)).1
    subsingleton⟩
  constructor
  · intro h
    let : IsEmpty (X ⟶ Z) := ⟨fun a ↦ h ⟨a⟩⟩
    exact extensionByZeroPresheafSection_isEmpty _ _ _ _
  · intro a
    let M : (X ⟶ Z) → Type (max c v r) := fun b ↦ F.val.obj (op (Over.mk b))
    let e : DirectSum (X ⟶ Z) M ≃ₗ[(coefficients.{c, v, r} R).obj.obj (op X)] M a :=
      { DirectSum.component _ _ M a with
        invFun := DirectSum.of M a
        left_inv := fun x ↦ by
          apply DirectSum.ext
          intro i
          have hi : i = a := Subsingleton.elim _ _
          subst i
          exact DFinsupp.single_eq_same
        right_inv := fun x ↦ DFinsupp.single_eq_same }
    refine ⟨e.toModuleIso, ?_⟩
    intro x
    simp +instances [e, M, LinearEquiv.toModuleIso, DirectSum.component, DFinsupp.lapply]

omit [HasFiniteLimits C] in
open Classical in
private theorem extensionRestrict_of
    (Z : C) (F : SliceModules.{c, v, r} R Z) {X Y : Cᵒᵖ} (a : X ⟶ Y)
    (φ : X.unop ⟶ Z) (ψ : Y.unop ⟶ Z) (h : a.unop ≫ φ = ψ)
    (x : F.val.obj (op (Over.mk φ))) :
    extensionByZeroPresheafRestrictAdd (coefficients.{c, v, r} R) Z F a
        (DirectSum.of (fun b : X.unop ⟶ Z ↦ F.val.obj (op (Over.mk b))) φ x) =
      DirectSum.of (fun b : Y.unop ⟶ Z ↦ F.val.obj (op (Over.mk b))) ψ (F.val.map
        (op (Over.homMk a.unop h : Over.mk ψ ⟶ Over.mk φ)) x) := by
  classical
  subst ψ
  change (DirectSum.toAddMonoid _)
    (DirectSum.of (fun b : X.unop ⟶ Z ↦ F.val.obj (op (Over.mk b))) φ x) = _
  rw [DirectSum.toAddMonoid_of]
  rfl

open Classical in
private def singletonInclusion (Z : C) (F : SliceModules.{c, v, r} R Z) :
    F.val ⟶ (restrictionP (Over.forget Z) (coefficients.{c, v, r} R)).obj
      ((extensionByZeroPresheaf (coefficients.{c, v, r} R) Z).obj F) where
  app X := ModuleCat.ofHom (DirectSum.lof _ _
    (fun b : X.unop.left ⟶ Z ↦ F.val.obj (op (Over.mk b))) X.unop.hom)
  naturality {X Y} f := by
    ext x
    change DirectSum.of (fun b : Y.unop.left ⟶ Z ↦ F.val.obj (op (Over.mk b)))
      Y.unop.hom (F.val.map f x) =
      extensionByZeroPresheafRestrictAdd (coefficients.{c, v, r} R) Z F
        ((Over.forget Z).op.map f)
        (DirectSum.of (fun b : X.unop.left ⟶ Z ↦ F.val.obj (op (Over.mk b))) X.unop.hom x)
    have hr := extensionRestrict_of.{c, v, r} R Z F ((Over.forget Z).op.map f)
      X.unop.hom Y.unop.hom (Over.w f.unop) x
    have hf : (Over.homMk f.unop.left (Over.w f.unop) : Y.unop ⟶ X.unop) =
        f.unop := by ext; rfl
    erw [hf] at hr
    exact hr.symm

private theorem singletonInclusion_isIso (Z : C) [Mono (terminal.from Z)]
    (F : SliceModules.{c, v, r} R Z) : IsIso (singletonInclusion.{c, v, r} R Z F) := by
  classical
  have hcomp : ∀ X, IsIso ((singletonInclusion.{c, v, r} R Z F).app X) := by
    intro X
    apply (ConcreteCategory.isIso_iff_bijective _).2
    constructor
    · change Function.Injective
        (DirectSum.of (fun b : X.unop.left ⟶ Z ↦ F.val.obj (op (Over.mk b))) X.unop.hom)
      exact DirectSum.of_injective
        (β := fun b : X.unop.left ⟶ Z ↦ F.val.obj (op (Over.mk b))) X.unop.hom
    · intro x
      refine ⟨DirectSum.component ((coefficients.{c, v, r} R).obj.obj (op X.unop.left)) _
        (fun b : X.unop.left ⟶ Z ↦ F.val.obj (op (Over.mk b))) X.unop.hom x, ?_⟩
      change DirectSum.of (fun b : X.unop.left ⟶ Z ↦ F.val.obj (op (Over.mk b)))
        X.unop.hom (DirectSum.component ((coefficients.{c, v, r} R).obj.obj (op X.unop.left)) _
          (fun b : X.unop.left ⟶ Z ↦ F.val.obj (op (Over.mk b))) X.unop.hom x) = x
      apply DirectSum.ext
      intro a
      have ha : a = X.unop.hom := by
        apply (cancel_mono (terminal.from Z)).1
        subsingleton
      subst a
      exact DFinsupp.single_eq_same
  let e := PresheafOfModules.isoMk
    (fun X ↦ asIso ((singletonInclusion.{c, v, r} R Z F).app X))
    (fun {X Y} f ↦ (singletonInclusion.{c, v, r} R Z F).naturality f)
  exact inferInstanceAs (IsIso e.hom)

private theorem adj_unit_isIso (Z : C) [Mono (terminal.from Z)] :
    IsIso (adj.{c, v, r} R Z).unit := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro F
  have hi := singletonInclusion_isIso.{c, v, r} R Z F
  let η := restrictionUnit (K := J.over Z) (Over.forget Z) (coefficients.{c, v, r} R)
    ((extensionByZeroPresheaf (coefficients.{c, v, r} R) Z).obj F)
  have heq : ((adj.{c, v, r} R Z).unit.app F).val =
      singletonInclusion.{c, v, r} R Z F ≫ η := by
    ext X x
    exact (localizedSystemAdjunction_existsUnique.{c, v, r} R Z).exists.choose_spec F X x
  apply (isIso_iff_of_reflects_iso _ (toSheaf ((coefficients.{c, v, r} R).over Z))).1
  apply ((J.over Z).W_sheafToPresheaf_map_iff_isIso _).1
  change (J.over Z).W ((PresheafOfModules.toPresheaf _).map
    ((adj.{c, v, r} R Z).unit.app F).val)
  rw [heq, CategoryTheory.Functor.map_comp]
  apply (J.over Z).W.comp_mem _ _
  · exact (J.over Z).W.of_isIso _
  · exact restrictionUnit_W (Over.forget Z) (coefficients.{c, v, r} R) _

private def nestedRightIso {A B : C} (f : A ⟶ B) [Mono (terminal.from B)] :
    SheafOfModules.pushforward.{max c v r} (pushforwardOver (R := coefficients.{c, v, r} R) B) ⋙
        jstar.{c, v, r} R A ≅ overMap.{max c v r} (coefficients.{c, v, r} R) f := by
  let e : Over.map f ≅ Over.forget A ⋙ Over.star B := NatIso.ofComponents
    (fun X ↦
      { hom := Over.homMk (prod.lift (X.hom ≫ f) (𝟙 _)) (by simp)
        inv := Over.homMk prod.snd (by
          apply (cancel_mono (terminal.from B)).1
          subsingleton)
        hom_inv_id := by ext; simp
        inv_hom_id := by
          ext
          apply prod.hom_ext
          · apply (cancel_mono (terminal.from B)).1
            subsingleton
          · simp })
    (fun g ↦ by ext; simp)
  letI := Functor.isContinuous_comp (Over.forget A) (Over.star B)
    (J.over A) J (J.over B)
  exact pushforwardComp.{max c v r} (F := Over.forget A) (𝟙 ((coefficients.{c, v, r} R).over A))
      (pushforwardOver (R := coefficients.{c, v, r} R) B) ≪≫
    pushforwardCongr₂.{max c v r} (F := Over.map f) (G := Over.forget A ⋙ Over.star B) _ e
      (by ext X x; simp [e, pushforwardOver, ← CategoryTheory.Functor.map_comp, ← op_comp])

private def sliceExtension {A B : C} (_f : A ⟶ B) :
    SliceModules.{c, v, r} R A ⥤ SliceModules.{c, v, r} R B :=
  jbang.{c, v, r} R A ⋙ jstar.{c, v, r} R B

private def sliceAdjunction {A B : C} (f : A ⟶ B) [Mono (terminal.from B)] :
    sliceExtension.{c, v, r} R f ⊣ overMap.{max c v r} (coefficients.{c, v, r} R) f :=
  ((adj.{c, v, r} R A).comp (overPushforwardOverAdj.{max c v r} B)).ofNatIsoRight
    (nestedRightIso.{c, v, r} R f)

omit [HasFiniteLimits C] in
private theorem sliceExtension_additive {A B : C} (f : A ⟶ B) :
    (sliceExtension.{c, v, r} R f).Additive :=
  inferInstanceAs ((jbang.{c, v, r} R A ⋙ jstar.{c, v, r} R B).Additive)

attribute [local instance] sliceExtension_additive

omit [HasFiniteLimits C] in
private theorem sliceExtension_limits {A B : C} (f : A ⟶ B) :
    PreservesFiniteLimits (sliceExtension.{c, v, r} R f) :=
  inferInstanceAs (PreservesFiniteLimits (jbang.{c, v, r} R A ⋙ jstar.{c, v, r} R B))

attribute [local instance] sliceExtension_limits

omit [HasFiniteLimits C] in
private theorem sliceExtension_colimits {A B : C} (f : A ⟶ B) :
    PreservesFiniteColimits (sliceExtension.{c, v, r} R f) :=
  inferInstanceAs (PreservesFiniteColimits (jbang.{c, v, r} R A ⋙ jstar.{c, v, r} R B))

attribute [local instance] sliceExtension_colimits

private theorem sliceRestriction_additive {A B : C} (f : A ⟶ B)
    [Mono (terminal.from B)] :
    (overMap.{max c v r} (coefficients.{c, v, r} R) f).Additive :=
  (sliceAdjunction.{c, v, r} R f).right_adjoint_additive

attribute [local instance] sliceRestriction_additive

private theorem sliceRestriction_limits {A B : C} (f : A ⟶ B)
    [Mono (terminal.from B)] :
    PreservesFiniteLimits (overMap.{max c v r} (coefficients.{c, v, r} R) f) := by
  have : PreservesLimitsOfSize.{0, 0}
      (overMap.{max c v r} (coefficients.{c, v, r} R) f) :=
    (sliceAdjunction.{c, v, r} R f).rightAdjoint_preservesLimits
  infer_instance

attribute [local instance] sliceRestriction_limits

private theorem sliceRestriction_colimits {A B : C} (f : A ⟶ B) :
    PreservesFiniteColimits (overMap.{max c v r} (coefficients.{c, v, r} R) f) := by
  have : PreservesColimitsOfSize.{0, 0}
      (overMap.{max c v r} (coefficients.{c, v, r} R) f) :=
    (overMapPushforwardAdj.{v, c, max c v r, max c v r}
      (coefficients.{c, v, r} R) f).leftAdjoint_preservesColimits
  infer_instance

attribute [local instance] sliceRestriction_colimits

private def restrictionSquare {U V W : C} (f : W ⟶ U) (g : W ⟶ V) :
    TwoSquare (jstar.{c, v, r} R V) (jstar.{c, v, r} R U)
      (overMap.{max c v r} (coefficients.{c, v, r} R) g)
      (overMap.{max c v r} (coefficients.{c, v, r} R) f) :=
  (overFunctorMap.{max c v r} (coefficients.{c, v, r} R) g).hom ≫
    (overFunctorMap.{max c v r} (coefficients.{c, v, r} R) f).inv

private def rightMate {U V W : C} (f : W ⟶ U) (g : W ⟶ V) :
    SheafOfModules.pushforward.{max c v r}
        (pushforwardOver (R := coefficients.{c, v, r} R) U) ⋙ jstar.{c, v, r} R V ⟶
      overMap.{max c v r} (coefficients.{c, v, r} R) f ⋙
        overPullback.{max c v r} (coefficients.{c, v, r} R) g :=
  (mateEquiv (overPushforwardOverAdj.{max c v r} U)
    (overMapPushforwardAdj.{v, c, max c v r, max c v r} (coefficients.{c, v, r} R) g)
    (restrictionSquare.{c, v, r} R f g)).natTrans

private def productPullbackIso {U V W : C} (f : W ⟶ U) (g : W ⟶ V)
    (h : IsLimit (BinaryFan.mk f g)) (X : Over V) :
    Over.mk (pullback.snd X.hom g ≫ f) ≅ (Over.star U).obj X.left := by
  let l := BinaryFan.IsLimit.lift h (prod.fst : U ⨯ X.left ⟶ U)
    (prod.snd ≫ X.hom)
  have lf : l ≫ f = prod.fst := BinaryFan.IsLimit.lift_fst h _ _
  have lg : l ≫ g = prod.snd ≫ X.hom := BinaryFan.IsLimit.lift_snd h _ _
  refine
    { hom := Over.homMk (prod.lift (pullback.snd _ _ ≫ f) (pullback.fst _ _)) (by simp)
      inv := Over.homMk (pullback.lift prod.snd l (by rw [lg])) (by simp [lf])
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · ext
    apply pullback.hom_ext
    · simp
    · apply BinaryFan.IsLimit.hom_ext h
      · simp [lf]
      · simp [lg, pullback.condition]
  · ext
    apply prod.hom_ext <;> simp [lf, Category.id_comp]

private theorem rightMate_isIso {U V W : C} (f : W ⟶ U) (g : W ⟶ V)
    (h : IsLimit (BinaryFan.mk f g)) : IsIso (rightMate.{c, v, r} R f g) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  apply (isIso_iff_of_reflects_iso _ (toSheaf ((coefficients.{c, v, r} R).over V))).1
  apply (isIso_iff_of_reflects_iso _ (sheafToPresheaf _ _)).1
  rw [NatTrans.isIso_iff_isIso_app]
  intro X
  let e := productPullbackIso f g h X.unop
  have heq : ((sheafToPresheaf _ _).map
      ((toSheaf _).map ((rightMate.{c, v, r} R f g).app M))).app X =
      M.val.presheaf.map e.hom.op := by
    ext x
    dsimp only [rightMate, mateEquiv, TwoSquare.mk, TwoSquare.natTrans,
      Equiv.coe_fn_mk, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.rightUnitor_inv_app, Functor.leftUnitor_hom_app]
    simp +instances only [Category.id_comp, Category.comp_id,
      CategoryTheory.Functor.comp_obj, CategoryTheory.Functor.id_obj]
    change M.val.map ((Over.forgetAdjStar U).unit.app
      ((Over.map f).obj ((Over.pullback g).obj X.unop))).op
      (M.val.map ((Over.star U).map ((Over.mapPullbackAdj g).counit.app X.unop).left).op x) =
        M.val.map e.hom.op x
    have hm : ((Over.star U).map ((Over.mapPullbackAdj g).counit.app X.unop).left).op ≫
        ((Over.forgetAdjStar U).unit.app
          ((Over.map f).obj ((Over.pullback g).obj X.unop))).op = e.hom.op := by
      apply Quiver.Hom.unop_inj
      ext
      apply prod.hom_ext <;> simp [e, productPullbackIso]
    erw [← PresheafOfModules.map_comp_apply, hm]
    rfl
  rw [heq]
  infer_instance

private def exchangeMap {U V W : C} (f : W ⟶ U) (g : W ⟶ V)
    [Mono (terminal.from U)] :=
  ((mateEquiv (adj.{c, v, r} R V) (sliceAdjunction.{c, v, r} R f)).symm
    (restrictionSquare.{c, v, r} R f g)).natTrans

private theorem exchangeMap_isIso {U V W : C} (f : W ⟶ U) (g : W ⟶ V)
    [Mono (terminal.from U)] (h : IsLimit (BinaryFan.mk f g)) :
    IsIso (exchangeMap.{c, v, r} R f g) := by
  have hi := rightMate_isIso.{c, v, r} R f g h
  have heq := iterated_mateEquiv_conjugateEquiv (adj.{c, v, r} R V)
    (sliceAdjunction.{c, v, r} R f)
    (overMapPushforwardAdj.{v, c, max c v r, max c v r} (coefficients.{c, v, r} R) g)
    (overPushforwardOverAdj.{max c v r} U)
    (TwoSquare.mk _ _ _ _ (exchangeMap.{c, v, r} R f g))
  have he : rightMate.{c, v, r} R f g =
      conjugateEquiv
        ((adj.{c, v, r} R V).comp (overPushforwardOverAdj.{max c v r} U))
        ((overMapPushforwardAdj.{v, c, max c v r, max c v r} (coefficients.{c, v, r} R) g).comp
          (sliceAdjunction.{c, v, r} R f)) (exchangeMap.{c, v, r} R f g) := by
    have hm : (mateEquiv (adj.{c, v, r} R V) (sliceAdjunction.{c, v, r} R f))
        (TwoSquare.mk _ _ _ _ (exchangeMap.{c, v, r} R f g)) =
        restrictionSquare.{c, v, r} R f g :=
      Equiv.apply_symm_apply _ _
    erw [hm] at heq
    exact heq
  have hj : IsIso (conjugateEquiv
      ((adj.{c, v, r} R V).comp (overPushforwardOverAdj.{max c v r} U))
      ((overMapPushforwardAdj.{v, c, max c v r, max c v r}
        (coefficients.{c, v, r} R) g).comp (sliceAdjunction.{c, v, r} R f))
      (exchangeMap.{c, v, r} R f g)) := by
    rw [← he]
    exact hi
  exact conjugateEquiv_of_iso
    ((adj.{c, v, r} R V).comp (overPushforwardOverAdj.{max c v r} U))
    ((overMapPushforwardAdj.{v, c, max c v r, max c v r} (coefficients.{c, v, r} R) g).comp
      (sliceAdjunction.{c, v, r} R f))
    (exchangeMap.{c, v, r} R f g)

private def compositionIso {A B : C} (f : A ⟶ B) [Mono (terminal.from B)] :
    sliceExtension.{c, v, r} R f ⋙ jbang.{c, v, r} R B ≅ jbang.{c, v, r} R A :=
  Adjunction.leftAdjointUniq
    (((sliceAdjunction.{c, v, r} R f).comp (adj.{c, v, r} R B)).ofNatIsoRight
      (overFunctorMap.{max c v r} (coefficients.{c, v, r} R) f))
    (adj.{c, v, r} R A)

private theorem compositionIso_unit {A B : C} (f : A ⟶ B)
    [Mono (terminal.from B)] (F : SliceModules.{c, v, r} R A) :
    (adj.{c, v, r} R A).unit.app F =
      ((sliceAdjunction.{c, v, r} R f).comp (adj.{c, v, r} R B)).unit.app F ≫
      (overMap.{max c v r} (coefficients.{c, v, r} R) f).map
        ((jstar.{c, v, r} R B).map ((compositionIso.{c, v, r} R f).hom.app F)) ≫
      (overFunctorMap.{max c v r} (coefficients.{c, v, r} R) f).hom.app
        ((jbang.{c, v, r} R A).obj F) := by
  let a := ((sliceAdjunction.{c, v, r} R f).comp (adj.{c, v, r} R B)).ofNatIsoRight
    (overFunctorMap.{max c v r} (coefficients.{c, v, r} R) f)
  have h := Adjunction.unit_leftAdjointUniq_hom_app a (adj.{c, v, r} R A) F
  change ((((sliceAdjunction.{c, v, r} R f).comp (adj.{c, v, r} R B)).unit.app F ≫
      (overFunctorMap.{max c v r} (coefficients.{c, v, r} R) f).hom.app _) ≫
      (jstar.{c, v, r} R A).map ((compositionIso.{c, v, r} R f).hom.app F)) = _ at h
  rw [Category.assoc, ← NatTrans.naturality] at h
  exact h.symm

private theorem compositionIso_transpose {A B : C} (f : A ⟶ B)
    [Mono (terminal.from B)] (F : SliceModules.{c, v, r} R A)
    (M : Modules.{c, v, r} R)
    (t : (jbang.{c, v, r} R B).obj ((sliceExtension.{c, v, r} R f).obj F) ⟶ M) :
    (adj.{c, v, r} R A).homEquiv _ _ ((compositionIso.{c, v, r} R f).inv.app F ≫ t) =
      ((sliceAdjunction.{c, v, r} R f).comp (adj.{c, v, r} R B)).homEquiv _ _ t ≫
        (overFunctorMap.{max c v r} (coefficients.{c, v, r} R) f).hom.app M := by
  let a := ((sliceAdjunction.{c, v, r} R f).comp (adj.{c, v, r} R B)).ofNatIsoRight
    (overFunctorMap.{max c v r} (coefficients.{c, v, r} R) f)
  have h := Adjunction.unit_leftAdjointUniq_hom_app a (adj.{c, v, r} R A) F
  change a.unit.app F ≫ (jstar.{c, v, r} R A).map
    ((compositionIso.{c, v, r} R f).hom.app F) = _ at h
  calc
    _ = a.unit.app F ≫ (jstar.{c, v, r} R A).map t := by
      rw [Adjunction.homEquiv_unit, ← h, CategoryTheory.Functor.map_comp, Category.assoc,
        ← CategoryTheory.Functor.map_comp_assoc, Iso.hom_inv_id_app,
        CategoryTheory.Functor.map_id, Category.id_comp]
    _ = a.homEquiv _ _ t := (Adjunction.homEquiv_unit _ _ _ _).symm
    _ = _ := Adjunction.homEquiv_ofNatIsoRight_apply _ _ _

private theorem nested_formula {A B : C} (f : A ⟶ B) [Mono (terminal.from B)]
    (M : Modules.{c, v, r} R) :
    nested.{c, v, r} R f M =
      (compositionIso.{c, v, r} R f).inv.app ((jstar.{c, v, r} R A).obj M) ≫
        (jbang.{c, v, r} R B).map
          ((sliceExtension.{c, v, r} R f).map
            ((overFunctorMap.{max c v r} (coefficients.{c, v, r} R) f).inv.app M) ≫
            (sliceAdjunction.{c, v, r} R f).counit.app ((jstar.{c, v, r} R B).obj M)) := by
  apply ((adj.{c, v, r} R A).homEquiv _ _).injective
  rw [show ((adj.{c, v, r} R A).homEquiv _ _) (nested.{c, v, r} R f M) = _ from
    Equiv.apply_symm_apply _ _]
  rw [compositionIso_transpose.{c, v, r} R f]
  let t := (sliceExtension.{c, v, r} R f).map
    ((overFunctorMap.{max c v r} (coefficients.{c, v, r} R) f).inv.app M) ≫
    (sliceAdjunction.{c, v, r} R f).counit.app ((jstar.{c, v, r} R B).obj M)
  have ht : (sliceAdjunction.{c, v, r} R f).homEquiv _ _ t =
      (overFunctorMap.{max c v r} (coefficients.{c, v, r} R) f).inv.app M := by
    change (sliceAdjunction.{c, v, r} R f).homEquiv _ _
      (((sliceAdjunction.{c, v, r} R f).homEquiv _ _).symm _) = _
    exact Equiv.apply_symm_apply _ _
  have hb : (adj.{c, v, r} R B).homEquiv _ _ ((jbang.{c, v, r} R B).map t) =
      t ≫ (adj.{c, v, r} R B).unit.app ((jstar.{c, v, r} R B).obj M) := by
    rw [Adjunction.homEquiv_unit]
    exact ((adj.{c, v, r} R B).unit.naturality t).symm
  change _ = (sliceAdjunction.{c, v, r} R f).homEquiv _ _
    ((adj.{c, v, r} R B).homEquiv _ _ ((jbang.{c, v, r} R B).map t)) ≫ _
  rw [hb, Adjunction.homEquiv_naturality_right, ht]
  exact (Category.assoc _ _ _).symm

private def selfIso (Z : C) [Mono (terminal.from Z)] :
    jbang.{c, v, r} R Z ⋙ jstar.{c, v, r} R Z ≅ 𝟭 _ :=
  have := adj_unit_isIso.{c, v, r} R Z
  (asIso (adj.{c, v, r} R Z).unit).symm

private theorem selfIso_counit (Z : C) [Mono (terminal.from Z)]
    (M : Modules.{c, v, r} R) :
    (jstar.{c, v, r} R Z).map ((adj.{c, v, r} R Z).counit.app M) =
      (selfIso.{c, v, r} R Z).hom.app ((jstar.{c, v, r} R Z).obj M) := by
  have := adj_unit_isIso.{c, v, r} R Z
  apply (cancel_epi ((adj.{c, v, r} R Z).unit.app _)).1
  change (asIso (adj.{c, v, r} R Z).unit).hom.app _ ≫ _ =
    (asIso (adj.{c, v, r} R Z).unit).hom.app _ ≫
      (asIso (adj.{c, v, r} R Z).unit).inv.app _
  rw [Iso.hom_inv_id_app]
  exact (adj.{c, v, r} R Z).right_triangle_components M

private theorem sliceAdjunction_unit_isIso {A B : C} (f : A ⟶ B)
    [Mono (terminal.from A)] [Mono (terminal.from B)] :
    IsIso (sliceAdjunction.{c, v, r} R f).unit := by
  have := adj_unit_isIso.{c, v, r} R A
  have := adj_unit_isIso.{c, v, r} R B
  rw [NatTrans.isIso_iff_isIso_app]
  intro F
  let t := (overMap.{max c v r} (coefficients.{c, v, r} R) f).map
      ((adj.{c, v, r} R B).unit.app ((sliceExtension.{c, v, r} R f).obj F)) ≫
    (overMap.{max c v r} (coefficients.{c, v, r} R) f).map
      ((jstar.{c, v, r} R B).map ((compositionIso.{c, v, r} R f).hom.app F)) ≫
    (overFunctorMap.{max c v r} (coefficients.{c, v, r} R) f).hom.app _
  have ht : (sliceAdjunction.{c, v, r} R f).unit.app F ≫ t =
      (adj.{c, v, r} R A).unit.app F := by
    simpa only [Adjunction.comp_unit_app, Category.assoc] using
      (compositionIso_unit.{c, v, r} R f F).symm
  have hi : IsIso t := by dsimp only [t]; infer_instance
  have he : (sliceAdjunction.{c, v, r} R f).unit.app F =
      (adj.{c, v, r} R A).unit.app F ≫ inv t := by
    rw [← ht, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [he]
  infer_instance

private def exchangeIso {U V W : C} (f : W ⟶ U) (g : W ⟶ V)
    [Mono (terminal.from U)] (h : IsLimit (BinaryFan.mk f g)) :
    jbang.{c, v, r} R V ⋙ jstar.{c, v, r} R U ≅
      overMap.{max c v r} (coefficients.{c, v, r} R) g ⋙ sliceExtension.{c, v, r} R f :=
  have := exchangeMap_isIso.{c, v, r} R f g h
  (asIso (exchangeMap.{c, v, r} R f g)).symm

private theorem exchangeIso_unit {U V W : C} (f : W ⟶ U) (g : W ⟶ V)
    [Mono (terminal.from U)] (h : IsLimit (BinaryFan.mk f g))
    (F : SliceModules.{c, v, r} R V) :
    (overMap.{max c v r} (coefficients.{c, v, r} R) g).map
      ((adj.{c, v, r} R V).unit.app F) ≫
      (overFunctorMap.{max c v r} (coefficients.{c, v, r} R) g).hom.app _ =
    (sliceAdjunction.{c, v, r} R f).unit.app _ ≫
      (overMap.{max c v r} (coefficients.{c, v, r} R) f).map
        ((exchangeIso.{c, v, r} R f g h).inv.app F) ≫
      (overFunctorMap.{max c v r} (coefficients.{c, v, r} R) f).hom.app _ := by
  have he := unit_mateEquiv_symm (adj.{c, v, r} R V)
    (sliceAdjunction.{c, v, r} R f) (restrictionSquare.{c, v, r} R f g) F
  have hh := congrArg (fun t ↦ t ≫
    (overFunctorMap.{max c v r} (coefficients.{c, v, r} R) f).hom.app _) he
  simpa only [restrictionSquare, TwoSquare.mk, TwoSquare.natTrans, NatTrans.comp_app,
    exchangeIso, exchangeMap, Iso.symm_inv, asIso_hom, Category.assoc, Iso.inv_hom_id_app,
    Category.comp_id, CategoryTheory.Functor.id_obj] using hh

private theorem exchangeIso_counit {U V W : C} (f : W ⟶ U) (g : W ⟶ V)
    [Mono (terminal.from U)] (h : IsLimit (BinaryFan.mk f g))
    (M : Modules.{c, v, r} R) :
    (jstar.{c, v, r} R U).map ((adj.{c, v, r} R V).counit.app M) =
      (exchangeIso.{c, v, r} R f g h).hom.app ((jstar.{c, v, r} R V).obj M) ≫
      (sliceExtension.{c, v, r} R f).map
        ((overFunctorMap.{max c v r} (coefficients.{c, v, r} R) g).hom.app M) ≫
      (sliceExtension.{c, v, r} R f).map
        ((overFunctorMap.{max c v r} (coefficients.{c, v, r} R) f).inv.app M) ≫
      (sliceAdjunction.{c, v, r} R f).counit.app _ := by
  have he := mateEquiv_counit_symm (adj.{c, v, r} R V)
    (sliceAdjunction.{c, v, r} R f) (restrictionSquare.{c, v, r} R f g) M
  apply (cancel_epi ((exchangeIso.{c, v, r} R f g h).inv.app
    ((jstar.{c, v, r} R V).obj M))).1
  rw [Iso.inv_hom_id_app_assoc]
  simpa only [restrictionSquare, TwoSquare.mk, TwoSquare.natTrans, NatTrans.comp_app,
    CategoryTheory.Functor.map_comp, exchangeIso, exchangeMap, Iso.symm_inv, asIso_hom,
    Category.assoc] using he.symm

private theorem nested_self {A B : C} (f : A ⟶ B) [Mono (terminal.from B)]
    (M : Modules.{c, v, r} R) :
    (jstar.{c, v, r} R B).map (nested.{c, v, r} R f M) ≫
      (selfIso.{c, v, r} R B).hom.app ((jstar.{c, v, r} R B).obj M) =
    (jstar.{c, v, r} R B).map
      ((compositionIso.{c, v, r} R f).inv.app ((jstar.{c, v, r} R A).obj M)) ≫
      (selfIso.{c, v, r} R B).hom.app
        ((sliceExtension.{c, v, r} R f).obj ((jstar.{c, v, r} R A).obj M)) ≫
      (sliceExtension.{c, v, r} R f).map
        ((overFunctorMap.{max c v r} (coefficients.{c, v, r} R) f).inv.app M) ≫
      (sliceAdjunction.{c, v, r} R f).counit.app ((jstar.{c, v, r} R B).obj M) := by
  rw [nested_formula.{c, v, r} R f, CategoryTheory.Functor.map_comp, Category.assoc]
  let t := (sliceExtension.{c, v, r} R f).map
    ((overFunctorMap.{max c v r} (coefficients.{c, v, r} R) f).inv.app M) ≫
    (sliceAdjunction.{c, v, r} R f).counit.app ((jstar.{c, v, r} R B).obj M)
  simpa only [CategoryTheory.Functor.comp_map, CategoryTheory.Functor.id_map,
    CategoryTheory.Functor.id_obj, Category.assoc] using congrArg
      (fun z ↦ (jstar.{c, v, r} R B).map
        ((compositionIso.{c, v, r} R f).inv.app ((jstar.{c, v, r} R A).obj M)) ≫ z)
      ((selfIso.{c, v, r} R B).hom.naturality t)

omit [HasFiniteLimits C] in
private theorem nested_counit {A B : C} (f : A ⟶ B) (M : Modules.{c, v, r} R) :
    nested.{c, v, r} R f M ≫ (adj.{c, v, r} R B).counit.app M =
      (adj.{c, v, r} R A).counit.app M := by
  apply ((adj.{c, v, r} R A).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right]
  rw [show ((adj.{c, v, r} R A).homEquiv _ _) (nested.{c, v, r} R f M) = _ from
    Equiv.apply_symm_apply _ _]
  rw [Adjunction.homEquiv_unit, Adjunction.right_triangle_components]
  let α := overFunctorMap.{max c v r} (coefficients.{c, v, r} R) f
  change (α.inv.app M ≫
    (overMap.{max c v r} (coefficients.{c, v, r} R) f).map
      ((adj.{c, v, r} R B).unit.app ((jstar.{c, v, r} R B).obj M)) ≫
    α.hom.app ((jbang.{c, v, r} R B).obj ((jstar.{c, v, r} R B).obj M))) ≫
    (jstar.{c, v, r} R A).map ((adj.{c, v, r} R B).counit.app M) = 𝟙 _
  rw [Category.assoc, Category.assoc, ← α.hom.naturality]
  simp only [CategoryTheory.Functor.comp_map]
  rw [← CategoryTheory.Functor.map_comp_assoc,
    Adjunction.right_triangle_components, CategoryTheory.Functor.map_id, Category.id_comp]
  exact α.inv_hom_id_app M

private theorem counit_postcomp_injective
    {A : Type a} [Category.{ha} A] {B : Type b} [Category.{hb} B]
    {F : A ⥤ B} {G : B ⥤ A} (a : F ⊣ G) [IsIso a.unit]
    (X : A) (Y : B) (t u : F.obj X ⟶ F.obj (G.obj Y))
    (h : t ≫ a.counit.app Y = u ≫ a.counit.app Y) : t = u := by
  have he : G.map (a.counit.app Y) = inv (a.unit.app (G.obj Y)) := by
    apply (cancel_epi (a.unit.app (G.obj Y))).1
    rw [a.right_triangle_components, IsIso.hom_inv_id]
    rfl
  have hi : IsIso (G.map (a.counit.app Y)) := by rw [he]; infer_instance
  apply (a.homEquiv _ _).injective
  apply (cancel_mono (G.map (a.counit.app Y))).1
  have hh := congrArg (a.homEquiv X ((𝟭 B).obj Y)) h
  rw [Adjunction.homEquiv_naturality_right,
    Adjunction.homEquiv_naturality_right] at hh
  exact hh

private theorem nested_cross {U V W : C} (f : W ⟶ U) (g : W ⟶ V)
    [Mono (terminal.from U)] [Mono (terminal.from V)] [Mono (terminal.from W)]
    (h : IsLimit (BinaryFan.mk g f)) (M : Modules.{c, v, r} R) :
    (jstar.{c, v, r} R V).map (nested.{c, v, r} R f M) ≫
      (exchangeIso.{c, v, r} R g f h).hom.app ((jstar.{c, v, r} R U).obj M) =
    (jstar.{c, v, r} R V).map
      ((compositionIso.{c, v, r} R g).inv.app ((jstar.{c, v, r} R W).obj M)) ≫
      (selfIso.{c, v, r} R V).hom.app
        ((sliceExtension.{c, v, r} R g).obj ((jstar.{c, v, r} R W).obj M)) ≫
      (sliceExtension.{c, v, r} R g).map
        ((overFunctorMap.{max c v r} (coefficients.{c, v, r} R) f).inv.app M) := by
  have := sliceAdjunction_unit_isIso.{c, v, r} R g
  let k := sliceExtension.{c, v, r} R g
  let σ := k.map ((overFunctorMap.{max c v r} (coefficients.{c, v, r} R) f).hom.app M) ≫
    k.map ((overFunctorMap.{max c v r} (coefficients.{c, v, r} R) g).inv.app M)
  have hi : IsIso σ := by dsimp only [σ]; infer_instance
  apply (cancel_mono σ).1
  apply counit_postcomp_injective (sliceAdjunction.{c, v, r} R g)
    ((jstar.{c, v, r} R W).obj M) ((jstar.{c, v, r} R V).obj M)
  have hs : (jstar.{c, v, r} R V).map ((adj.{c, v, r} R W).counit.app M) =
      (jstar.{c, v, r} R V).map
        ((compositionIso.{c, v, r} R g).inv.app ((jstar.{c, v, r} R W).obj M)) ≫
      (selfIso.{c, v, r} R V).hom.app (k.obj ((jstar.{c, v, r} R W).obj M)) ≫
      k.map ((overFunctorMap.{max c v r} (coefficients.{c, v, r} R) g).inv.app M) ≫
      (sliceAdjunction.{c, v, r} R g).counit.app ((jstar.{c, v, r} R V).obj M) := by
    rw [← nested_self.{c, v, r} R g, ← selfIso_counit.{c, v, r} R V,
      ← CategoryTheory.Functor.map_comp, nested_counit.{c, v, r} R g]
  simp only [σ, Category.assoc]
  rw [← exchangeIso_counit.{c, v, r} R g f h,
    ← CategoryTheory.Functor.map_comp, nested_counit.{c, v, r} R f, hs]
  dsimp only [k]
  simp only [← CategoryTheory.Functor.map_comp_assoc, Iso.inv_hom_id_app_assoc]

omit [HasFiniteLimits C] in
private theorem hom_eq_zero_of_cover
    {I : Type*} (Y : I → C) (hY : J.CoversTop Y)
    {M N : Modules.{c, v, r} R} (f : M ⟶ N)
    (hf : ∀ i, (jstar.{c, v, r} R (Y i)).map f = 0) : f = 0 := by
  apply (toSheaf (coefficients.{c, v, r} R)).map_injective
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext X
  obtain ⟨X⟩ := X
  apply N.isSheaf.hom_ext (hY.cover X)
  rintro ⟨T, a, ⟨i, ⟨b⟩⟩⟩
  have h := congrArg (fun k ↦ k.val.app (op (Over.mk b))) (hf i)
  have hb : ((PresheafOfModules.toPresheaf _).map f.val).app (op T) = 0 := by
    apply AddCommGrpCat.hom_ext
    exact congrArg (fun k ↦ k.hom.toAddMonoidHom) h
  change ((PresheafOfModules.toPresheaf _).map f.val).app (op X) ≫
    N.val.presheaf.map a.op = 0 ≫ _
  have hn : M.val.presheaf.map a.op ≫
      ((PresheafOfModules.toPresheaf _).map f.val).app (op T) =
      ((PresheafOfModules.toPresheaf _).map f.val).app (op X) ≫
        N.val.presheaf.map a.op :=
    ((PresheafOfModules.toPresheaf _).map f.val).naturality a.op
  rw [← hn, hb, comp_zero, zero_comp]

private theorem jointDetection (U V : C)
    (hcover : Sieve.ofArrows (fun b : Bool ↦ if b then U else V)
      (fun b ↦ terminal.from (if b then U else V)) ∈ J (⊤_ C)) :
    JointDetection.{c, v, r, w} R U V := by
  let Y := fun b : Bool ↦ if b then U else V
  have hY : J.CoversTop Y := by
    apply (J.coversTop_iff_of_isTerminal _ terminalIsTerminal Y).2
    rwa [Sieve.ofArrows_eq_ofObjects terminalIsTerminal] at hcover
  have hzero {M N : Modules.{c, v, r} R} (f : M ⟶ N) :
      f = 0 ↔ (jstar.{c, v, r} R U).map f = 0 ∧ (jstar.{c, v, r} R V).map f = 0 := by
    constructor
    · intro h
      subst f
      exact ⟨CategoryTheory.Functor.map_zero _ _ _, CategoryTheory.Functor.map_zero _ _ _⟩
    · rintro ⟨hu, hv⟩
      exact hom_eq_zero_of_cover.{c, v, r} R Y hY f (fun b ↦ by cases b <;> assumption)
  have hz (M : Modules.{c, v, r} R) :
      IsZero M ↔ IsZero ((jstar.{c, v, r} R U).obj M) ∧
        IsZero ((jstar.{c, v, r} R V).obj M) := by
    constructor
    · intro h
      exact ⟨(jstar.{c, v, r} R U).map_isZero h, (jstar.{c, v, r} R V).map_isZero h⟩
    · rintro ⟨hu, hv⟩
      apply (IsZero.iff_id_eq_zero M).2
      exact (hzero _).2 ⟨by simpa using hu.eq_of_src (𝟙 _) 0,
        by simpa using hv.eq_of_src (𝟙 _) 0⟩
  have hiso {M N : Modules.{c, v, r} R} (f : M ⟶ N)
      (hu : IsIso ((jstar.{c, v, r} R U).map f))
      (hv : IsIso ((jstar.{c, v, r} R V).map f)) : IsIso f := by
    let T := (jstar.{c, v, r} R U).prod' (jstar.{c, v, r} R V)
    have : T.Faithful := ⟨fun {M N} a b hab ↦ by
      apply sub_eq_zero.mp
      apply (hzero (a - b)).2
      have ha : (jstar.{c, v, r} R U).map a = (jstar.{c, v, r} R U).map b :=
        congrArg Prod.fst hab
      have hb : (jstar.{c, v, r} R V).map a = (jstar.{c, v, r} R V).map b :=
        congrArg Prod.snd hab
      exact ⟨by simpa only [CategoryTheory.Functor.map_sub] using sub_eq_zero.mpr ha,
        by simpa only [CategoryTheory.Functor.map_sub] using sub_eq_zero.mpr hb⟩⟩
    have : IsIso (T.map f) := by
      exact (CategoryTheory.isIso_prod_iff _ _).2 ⟨hu, hv⟩
    exact isIso_of_reflects_iso f T
  refine ⟨hz, fun M N f ↦ hzero f, ?_, ?_, ?_, ?_, ?_⟩
  · intro K
    rw [ShortComplex.exact_iff_isZero_homology,
      ShortComplex.exact_iff_isZero_homology, ShortComplex.exact_iff_isZero_homology]
    rw [hz]
    exact and_congr
      ⟨fun h ↦ h.of_iso (K.mapHomologyIso (jstar.{c, v, r} R U)),
        fun h ↦ h.of_iso (K.mapHomologyIso (jstar.{c, v, r} R U)).symm⟩
      ⟨fun h ↦ h.of_iso (K.mapHomologyIso (jstar.{c, v, r} R V)),
        fun h ↦ h.of_iso (K.mapHomologyIso (jstar.{c, v, r} R V)).symm⟩
  · intro K q
    rw [hz]
    exact and_congr
      ⟨fun h ↦ h.of_iso (((jstar.{c, v, r} R U).mapHomologicalComplexHomologyIso (.up ℤ) q).app K),
        fun h ↦ h.of_iso (((jstar.{c, v, r} R U).mapHomologicalComplexHomologyIso
          (.up ℤ) q).symm.app K)⟩
      ⟨fun h ↦ h.of_iso (((jstar.{c, v, r} R V).mapHomologicalComplexHomologyIso (.up ℤ) q).app K),
        fun h ↦ h.of_iso (((jstar.{c, v, r} R V).mapHomologicalComplexHomologyIso
          (.up ℤ) q).symm.app K)⟩
  · intro K L f
    constructor
    · intro h
      exact ⟨inferInstance, inferInstance⟩
    · rintro ⟨hu, hv⟩
      rw [quasiIso_iff]
      intro q
      rw [quasiIsoAt_iff_isIso_homologyMap]
      apply hiso
      · exact (NatIso.isIso_map_iff
          ((jstar.{c, v, r} R U).mapHomologicalComplexHomologyIso (.up ℤ) q) f).1 (by
            change IsIso (HomologicalComplex.homologyMap
              (((jstar.{c, v, r} R U).mapHomologicalComplex (.up ℤ)).map f) q)
            infer_instance)
      · exact (NatIso.isIso_map_iff
          ((jstar.{c, v, r} R V).mapHomologicalComplexHomologyIso (.up ℤ) q) f).1 (by
            change IsIso (HomologicalComplex.homologyMap
              (((jstar.{c, v, r} R V).mapHomologicalComplex (.up ℤ)).map f) q)
            infer_instance)
  · intro _ _ _ K q
    rw [hz]
    exact and_congr
      ⟨fun h ↦ h.of_iso (((jstar.{c, v, r} R U).mapDerivedCategoryHomologyFunctorIso q).symm.app K),
        fun h ↦ h.of_iso (((jstar.{c, v, r} R U).mapDerivedCategoryHomologyFunctorIso q).app K)⟩
      ⟨fun h ↦ h.of_iso (((jstar.{c, v, r} R V).mapDerivedCategoryHomologyFunctorIso q).symm.app K),
        fun h ↦ h.of_iso (((jstar.{c, v, r} R V).mapDerivedCategoryHomologyFunctorIso q).app K)⟩
  · intro _ _ _ K L f
    constructor
    · intro h
      exact ⟨inferInstance, inferInstance⟩
    · rintro ⟨hu, hv⟩
      rw [DerivedCategory.isIso_iff]
      intro q
      apply hiso
      · exact (NatIso.isIso_map_iff
          ((jstar.{c, v, r} R U).mapDerivedCategoryHomologyFunctorIso q) f).2 (by
            change IsIso ((DerivedCategory.homologyFunctor _ q).map
              ((jstar.{c, v, r} R U).mapDerivedCategory.map f))
            infer_instance)
      · exact (NatIso.isIso_map_iff
          ((jstar.{c, v, r} R V).mapDerivedCategoryHomologyFunctorIso q) f).2 (by
            change IsIso ((DerivedCategory.homologyFunctor _ q).map
              ((jstar.{c, v, r} R V).mapDerivedCategory.map f))
            infer_instance)

/-- Local calculus for two covering subterminal objects.
Source: Stacks Project, Modules on Sites, Tags 03DI, 03DJ and 0F6Z; Sites,
Tags 04B8 and 04IY (blueprint: lem-sp-subterminal-module-local-calculus).

Proof:
1. Use localizedSystemExtension and localizedSystemRestriction with their proved exactness
   instances and the normalized localizedSystemAdjunction. For a subterminal Z, cancellation
   against Z → 1 makes Hom(X,Z) a subsingleton. The direct sum is zero when this type is empty;
   evaluation at any existing index is a linear equivalence with inverse the summand inclusion.
   This proves the stated presheaf formula with its specified generators.
2. For a continuous and cocontinuous functor, restrict the module sheafification unit and
   transpose under source sheafification. Cocontinuity preserves its local bijectivity;
   localization identifies its sheafification as invertible, and the sheafification counit is
   invertible. Naturality follows by applying the adjunction hom equivalence. The same equivalence
   pins the comparison on unit images. Apply this independently universe-polymorphic argument to
   Over.forget and Over.map. This directly proves the required normalized comparisons.
3. The singleton-summand inclusions define a presheaf isomorphism from F to restriction of its
   extension presheaf when Z is subterminal. Compose it with the restricted sheafification unit.
   The normalized adjunction identifies this composite with its unit. It is locally bijective and
   is a map between sheaves, hence invertible. Define the self-restriction comparison as the
   inverse of this unit.
4. For f:A→B with B subterminal, set k! = j_A! followed by j_B*. Restriction j_B* has the standard
   right adjoint along Over.star B. The functors Over.map f and Over.forget A followed by
   Over.star B are naturally isomorphic: on each object the inverse is the second projection, and
   subterminality gives the other inverse equation. Transporting the composite adjunction gives k!
   ⊣ f*. The extension is exact as a composite; f* is additive as its right adjoint, left exact as
   a right adjoint, and right exact by the standard adjunction f* ⊣ overPullback.
5. Let θ: j_V* followed by g* ≅ j_U* followed by f* be the canonical restriction comparison.
   Define the inverse exchange as its inverse mate under j_V! ⊣ j_V* and k_U! ⊣ f*. Mate θ again
   under the standard right adjoints of j_U* and g*. At Y→V its component is restriction of a
   module along the canonical slice isomorphism Y×_V W ≅ U×Y, for W=U×V. Its inverse is
   constructed by the product and pullback universal properties. Thus this second mate is
   invertible. The iterated-mate/conjugation theorem reflects its invertibility to the exchange
   map. The unit and counit mate identities give exactly the required normalized exchange
   equations. Repeat with U,V interchanged.
6. Define k_U! followed by j_U! ≅ j_W! by uniqueness of left adjoints after transporting the right
   adjoint through the canonical restriction isomorphism. The uniqueness unit equation is the
   required composition normalization. Transpose the nested map: it equals the inverse composition
   comparison followed by j_U! of k_U! applied to the inverse restriction comparison and then the
   k_U counit. Self-comparison naturality proves the self equation. The global triangle identities
   prove nested followed by counit equals the global W counit. The normalized composition units
   and the invertible global units imply each k-unit is invertible. For maps out of kX into kRY,
   postcomposition with its counit is injective: transpose and cancel R of the counit, which is
   invertible by the triangle identity. Apply this to the cross equation; after composing with the
   exchange counit, both sides reduce to restriction of the global W counit, using the self
   equation just proved. This proves both cross equations.
7. A morphism whose U and V restrictions vanish is zero: on each object, use the cover by arrows
   whose domains map to U or V; naturality makes the restricted morphism zero and sheaf
   separatedness gives equality. Applying this to the identity detects zero objects. The product
   of the restriction functors is faithful by subtracting morphisms. It preserves finite limits
   and colimits; faithfulness therefore reflects monomorphisms and epimorphisms and hence
   isomorphisms in the abelian module category.
8. For a short complex, exactness is vanishing of its homology. The standard exact-functor
   homology comparison and joint zero detection give the exactness test. Use
   mapHomologicalComplexHomologyIso for all integer cohomology degrees; the same zero test gives
   cohomological vanishing, and joint isomorphism reflection gives the quasi-isomorphism test on
   homology maps. Exact functors act triangulated on ordinary unbounded derived categories with
   their Q-factorization. Use the proved source-library mapDerivedCategoryHomologyFunctorIso to
   obtain all derived comparisons, derived vanishing and isomorphism tests. No boundedness
   hypothesis is used.
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
  have hprod : Mono (terminal.from (U ⨯ V)) := by
    constructor
    intro X a b hab
    apply prod.hom_ext
    · apply (cancel_mono (terminal.from U)).1
      subsingleton
    · apply (cancel_mono (terminal.from V)).1
      subsingleton
  refine ⟨?_, ?_, jointDetection.{c, v, r, w} R U V hcover⟩
  · let hp : IsLimit (BinaryFan.mk (prod.fst : U ⨯ V ⟶ U) (prod.snd : U ⨯ V ⟶ V)) :=
      prodIsProd U V
    let hq : IsLimit (BinaryFan.mk (prod.snd : U ⨯ V ⟶ V) (prod.fst : U ⨯ V ⟶ U)) :=
      BinaryFan.isLimitFlip
        (c := BinaryFan.mk (prod.fst : U ⨯ V ⟶ U) (prod.snd : U ⨯ V ⟶ V)) hp
    exact ⟨{
      kU := sliceExtension.{c, v, r} R prod.fst
      kV := sliceExtension.{c, v, r} R prod.snd
      adjU := sliceAdjunction.{c, v, r} R prod.fst
      adjV := sliceAdjunction.{c, v, r} R prod.snd
      exactU := exactRestriction_of_exact _
      exactV := exactRestriction_of_exact _
      restrictionU := exactRestriction_of_exact _
      restrictionV := exactRestriction_of_exact _
      derivedU := derivedExact_of_exact _
      derivedV := derivedExact_of_exact _
      derivedRestrictionU := derivedExact_of_exact _
      derivedRestrictionV := derivedExact_of_exact _
      sheafificationU := mapSheafificationRestriction.{c, v, r} R prod.fst
      sheafificationV := mapSheafificationRestriction.{c, v, r} R prod.snd
      selfU := selfIso.{c, v, r} R U
      selfV := selfIso.{c, v, r} R V
      selfU_unit := rfl
      selfV_unit := rfl
      composeU := compositionIso.{c, v, r} R prod.fst
      composeV := compositionIso.{c, v, r} R prod.snd
      composeU_unit := compositionIso_unit.{c, v, r} R prod.fst
      composeV_unit := compositionIso_unit.{c, v, r} R prod.snd
      exchangeU := exchangeIso.{c, v, r} R prod.fst prod.snd hp
      exchangeV := exchangeIso.{c, v, r} R prod.snd prod.fst hq
      exchangeU_unit := exchangeIso_unit.{c, v, r} R prod.fst prod.snd hp
      exchangeV_unit := exchangeIso_unit.{c, v, r} R prod.snd prod.fst hq
      exchangeU_counit := exchangeIso_counit.{c, v, r} R prod.fst prod.snd hp
      exchangeV_counit := exchangeIso_counit.{c, v, r} R prod.snd prod.fst hq
      nestedU_self := nested_self.{c, v, r} R prod.fst
      nestedU_cross := nested_cross.{c, v, r} R prod.fst prod.snd hq
      nestedU_counit := nested_counit.{c, v, r} R prod.fst
      nestedV_self := nested_self.{c, v, r} R prod.snd
      nestedV_cross := nested_cross.{c, v, r} R prod.snd prod.fst hp
      nestedV_counit := nested_counit.{c, v, r} R prod.snd }⟩
  · intro Z hZ
    have : Mono (terminal.from Z) := by
      rcases hZ with rfl | rfl | rfl <;> infer_instance
    exact ⟨exactRestriction_of_exact _, exactRestriction_of_exact _,
      derivedExact_of_exact _, derivedExact_of_exact _,
      presheafFormula_of_subterminal R Z, sheafificationRestriction R Z⟩

end LocalCalculusProof

end SheafOfModules.SubterminalLocal


