/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N0
-/
module

public import Sheaf.CategoryTheory.FlatRingedDiagramRestrictionDefs
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.Data.PNat.Basic
import Mathlib.CategoryTheory.Localization.Predicate
import Mathlib.Tactic.FastInstance

/-! # Flat scalar transport of strict-tower exchange

Source: blueprint main-20261015, completed-exchange-coherence proof, second paragraph,
strict coefficient supplement; Stacks 07A7, remark-base-change
(blueprint: lem-weil-pbc-flat-scalar-tower-exchange).

The auxiliary records only spell out the given corners, edges, derived operations,
and canonical square comparisons. In particular the square comparisons are normalized
on underlying sheaves and on complexes, rather than arbitrary derived isomorphisms.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.checkUnivs false
set_option synthInstance.maxSize 2048
attribute [local instance 2000] CategoryTheory.Preadditive.preadditiveHasZeroMorphisms
attribute [local instance 2000] CategoryTheory.Functor.preservesZeroMorphisms_of_additive
set_option backward.defeqAttrib.useBackward true
universe u w uA vA uB vB uC vC uD vD
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
namespace CategoryTheory
namespace FlatScalarTowerExchange

/-- The positive inverse-sequence category, lifted to the site universe.
Source: strict coefficient supplement, J = positive integers opposite
(blueprint: lem-weil-pbc-flat-scalar-tower-exchange). -/
abbrev Index := ULiftHom.{u} (ULift.{u} ℕ+ᵒᵖ)

/-- Ring-forgetting preserves the sheaf condition.
Source: Mathlib preservation of sheaves by limit-preserving functors
(blueprint: lem-weil-pbc-flat-scalar-tower-exchange). -/
instance (priority := 2000) ringSheafCompose
    {C : Type u} [SmallCategory C] (K : GrothendieckTopology C) :
    K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u}) := inferInstance

/-- Underlying sets of commutative rings preserve the sheaf condition.
Source: Mathlib preservation of sheaves by limit-preserving functors
(blueprint: lem-weil-pbc-flat-scalar-tower-exchange). -/
instance (priority := 2000) commRingSheafCompose
    {C : Type u} [SmallCategory C] (K : GrothendieckTopology C) :
    K.HasSheafCompose (forget CommRingCat.{u}) := inferInstance

/-- Underlying sets of abelian groups preserve the sheaf condition.
Source: Mathlib preservation of sheaves by limit-preserving functors
(blueprint: lem-weil-pbc-flat-scalar-tower-exchange). -/
instance (priority := 2000) groupSheafCompose
    {C : Type u} [SmallCategory C] (K : GrothendieckTopology C) :
    K.HasSheafCompose (forget AddCommGrpCat.{u}) := inferInstance


/-- The canonical preadditive structure, shared by all derived and complex interfaces.
Source: Mathlib functor-category preadditivity and the strict coefficient supplement
(blueprint: lem-weil-pbc-flat-scalar-tower-exchange). -/
instance (priority := 2500) diagramPreadditive
    {C : Type u} [SmallCategory C] {K : GrothendieckTopology C}
    (R : Sheaf K RingCat.{u}) : Preadditive (Index.{u} ⥤ SheafOfModules.{u} R) :=
  CategoryTheory.functorCategoryPreadditive

attribute [-instance] Abelian.functorCategoryAbelian in
/-- The inherited abelian structure with canonical parent instances.
Source: Mathlib functor-category abelian structure and strict coefficient supplement
(blueprint: lem-weil-pbc-flat-scalar-tower-exchange). -/
instance (priority := 2000) diagramAbelian
    {C : Type u} [SmallCategory C] {K : GrothendieckTopology C}
    (R : Sheaf K RingCat.{u}) : Abelian (Index.{u} ⥤ SheafOfModules.{u} R) :=
  fast_instance% (Abelian.functorCategoryAbelian (C := Index.{u})
    (D := SheafOfModules.{u} R))

/-- The actual coefficient ring sheaf, with a fixed interface for module categories.
Source: the strict coefficient supplement, forgetting commutativity of coefficient sheaves
(blueprint: lem-weil-pbc-flat-scalar-tower-exchange). -/
@[irreducible]
def coefficientRing {C : Type u} [SmallCategory C] {K : GrothendieckTopology C}
    (R : Sheaf K CommRingCat.{u}) : Sheaf K RingCat.{u} :=
  (sheafCompose K (forget₂ CommRingCat RingCat)).obj R

set_option genInjectivity false in
set_option linter.checkUnivs false in
/-- One of the four sites with its compatible flat coefficient change.
Source: strict coefficient supplement, corner data
(blueprint: lem-weil-pbc-flat-scalar-tower-exchange). -/
structure Corner where
  site : Type u
  category : SmallCategory site
  topology : GrothendieckTopology site
  R : Sheaf topology CommRingCat.{u}
  S : Sheaf topology CommRingCat.{u}
  a : R ⟶ S
  flat : SheafOfModules.IsFlatOnSite.{u, u, u, u}
    ((SheafOfModules.restrictScalars.{u}
      ((sheafCompose topology (forget₂ CommRingCat RingCat)).map a)).obj
      (SheafOfModules.unit.{u} ((sheafCompose topology (forget₂ CommRingCat RingCat)).obj S)))

  /-- A chosen unbounded localization for the R diagrams, in Hom universe w. -/
  derivedR : HasDerivedCategory.{w} ((Index.{u} ⥤ ringedSiteModules.{u} (coefficientRing R)))
  /-- A chosen unbounded localization for the S diagrams, in Hom universe w. -/
  derivedS : HasDerivedCategory.{w} ((Index.{u} ⥤ ringedSiteModules.{u} (coefficientRing S)))

attribute [instance] Corner.category Corner.derivedR Corner.derivedS

/-- R-module strict diagrams at a corner.
Source: strict coefficient supplement, derived strict diagrams
(blueprint: lem-weil-pbc-flat-scalar-tower-exchange). -/
abbrev Corner.modulesR (T : Corner.{u, w}) :=
  (Index.{u} ⥤ ringedSiteModules.{u} (coefficientRing T.R))

/-- S-module strict diagrams at a corner.
Source: strict coefficient supplement, derived strict diagrams
(blueprint: lem-weil-pbc-flat-scalar-tower-exchange). -/
abbrev Corner.modulesS (T : Corner.{u, w}) :=
  (Index.{u} ⥤ ringedSiteModules.{u} (coefficientRing T.S))

/-- The inherited abelian structure, named once to keep subsequent type elaboration small.
Source: Stacks 03DA and the product-site realization
(blueprint: lem-weil-pbc-flat-scalar-tower-exchange). -/
abbrev Corner.modulesRAbelian (T : Corner.{u, w}) : Abelian T.modulesR := inferInstance

/-- The inherited abelian structure for S diagrams, with no new category structure.
Source: Stacks 03DA and the product-site realization
(blueprint: lem-weil-pbc-flat-scalar-tower-exchange). -/
abbrev Corner.modulesSAbelian (T : Corner.{u, w}) : Abelian T.modulesS := inferInstance

/-- The underlying set-sheaf functor for a coefficient sheaf.
Source: Stacks 03D3, underlying sheaves of modules
(blueprint: lem-weil-pbc-flat-scalar-tower-exchange). -/
abbrev underlying {C : Type u} [SmallCategory C] {K : GrothendieckTopology C}
    (R : Sheaf K CommRingCat.{u}) :=
  SheafOfModules.toSheaf.{u} ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R) ⋙
    sheafCompose K (forget AddCommGrpCat)

/-- The actual ordinary scalar restriction on strict diagrams at a corner.
Source: Stacks 03D3 and strict coefficient supplement
(blueprint: lem-weil-pbc-flat-scalar-tower-exchange). -/
@[irreducible]
def Corner.restrict (T : Corner.{u, w}) : T.modulesS ⥤ T.modulesR := by
  unfold Corner.modulesR Corner.modulesS coefficientRing
  exact (Functor.whiskeringRight Index.{u} _ _).obj (SheafOfModules.restrictScalars.{u}
    ((sheafCompose T.topology (forget₂ CommRingCat RingCat)).map T.a))

/-- Additivity of actual termwise scalar restriction.
Source: Mathlib change of rings (blueprint: lem-weil-pbc-flat-scalar-tower-exchange). -/
instance (priority := 2000) Corner.restrict_additive (T : Corner.{u, w}) :
    T.restrict.Additive := by
  delta Corner.restrict Corner.modulesR Corner.modulesS coefficientRing id
  infer_instance

/-- The actual termwise module inverse image, between the named diagram categories.
Source: the strict coefficient supplement, degreewise inverse image
(blueprint: lem-weil-pbc-flat-scalar-tower-exchange). -/
@[irreducible]
def inverseDiagram {C D : Type u} [SmallCategory C] [SmallCategory D]
    {K : GrothendieckTopology C} {H : GrothendieckTopology D}
    {RV : Sheaf K CommRingCat.{u}} {RU : Sheaf H CommRingCat.{u}}
    (e : FlatRingedModuleImage RV RU) :
    (Index.{u} ⥤ ringedSiteModules.{u} (coefficientRing RV)) ⥤
      (Index.{u} ⥤ ringedSiteModules.{u} (coefficientRing RU)) := by
  unfold coefficientRing
  exact (Functor.whiskeringRight Index.{u} _ _).obj e.inverse.modules

/-- The actual termwise module direct image, between the named diagram categories.
Source: the strict coefficient supplement, degreewise direct image
(blueprint: lem-weil-pbc-flat-scalar-tower-exchange). -/
@[irreducible]
def directDiagram {C D : Type u} [SmallCategory C] [SmallCategory D]
    {K : GrothendieckTopology C} {H : GrothendieckTopology D}
    {RV : Sheaf K CommRingCat.{u}} {RU : Sheaf H CommRingCat.{u}}
    (e : FlatRingedModuleImage RV RU) :
    (Index.{u} ⥤ ringedSiteModules.{u} (coefficientRing RU)) ⥤
      (Index.{u} ⥤ ringedSiteModules.{u} (coefficientRing RV)) := by
  unfold coefficientRing
  exact (Functor.whiskeringRight Index.{u} _ _).obj e.morphism.modules

section

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
    {K : GrothendieckTopology C} {H : GrothendieckTopology D}
    {RV : Sheaf K CommRingCat.{u}} {RU : Sheaf H CommRingCat.{u}}
    (e : FlatRingedModuleImage RV RU)

/-- Additivity of the actual termwise inverse image.
Source: Mathlib whiskering (blueprint: lem-weil-pbc-flat-scalar-tower-exchange). -/
instance (priority := 2000) inverseDiagram_additive : (inverseDiagram e).Additive := by
  delta inverseDiagram coefficientRing id
  infer_instance

/-- Additivity of the actual termwise direct image.
Source: Mathlib whiskering (blueprint: lem-weil-pbc-flat-scalar-tower-exchange). -/
instance (priority := 2000) directDiagram_additive : (directDiagram e).Additive := by
  delta directDiagram coefficientRing id
  infer_instance

/-- The original degreewise adjunction, with the named actual diagram functors.
Source: Mathlib whiskering (blueprint: lem-weil-pbc-flat-scalar-tower-exchange). -/
@[irreducible]
def diagramAdjunction : inverseDiagram e ⊣ directDiagram e := by
  unfold inverseDiagram directDiagram coefficientRing
  exact Adjunction.whiskerRight Index.{u} e.adjunction

end

/-- The degreewise complex functor, with a fixed interface for localization factors.
Source: Mathlib functoriality of homological complexes and the strict coefficient supplement
(blueprint: lem-weil-pbc-flat-scalar-tower-exchange). -/
@[irreducible]
def complexFunctor {A B : Type*} [Category A] [Category B]
    [Abelian A] [Abelian B]
    (F : A ⥤ B) [F.Additive] :
    CochainComplex A ℤ ⥤ CochainComplex B ℤ :=
  F.mapHomologicalComplex (.up ℤ)

/-- The original degreewise adjunction expressed through the fixed complex functors.
Source: the induced adjunction on complexes, Stacks 0FND/0DVC
(blueprint: lem-weil-pbc-flat-scalar-tower-exchange). -/
@[irreducible]
def complexAdjunction {A B : Type*} [Category A] [Category B]
    [Abelian A] [Abelian B] {L : A ⥤ B} {F : B ⥤ A}
    [L.Additive] [F.Additive] (a : L ⊣ F) :
    complexFunctor L ⊣ complexFunctor F := by
  unfold complexFunctor
  exact a.mapHomologicalComplex (.up ℤ)

set_option genInjectivity false in
/-- A specified exact localization, determined by its comparison on complexes.
Source: Stacks 04VG and strict coefficient supplement, termwise restriction
(blueprint: lem-weil-pbc-flat-scalar-tower-exchange). -/
structure LocalizedFunctor
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{w} A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{w} B]
    (F₀ : A ⥤ B) [F₀.Additive] where
  functor : DerivedCategory A ⥤ DerivedCategory B
  factor : DerivedCategory.Q ⋙ functor ≅ F₀.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q

set_option genInjectivity false in
/-- The actual derived restriction at a corner, with its exact-localization factor.
Source: normalized restriction comparisons in the strict coefficient supplement
(blueprint: lem-weil-pbc-flat-scalar-tower-exchange). -/
structure Corner.Restriction (T : Corner.{u, w}) where
  functor : DerivedCategory.{w} T.modulesS ⥤ DerivedCategory.{w} T.modulesR
  factor : DerivedCategory.Q.{w} (C := T.modulesS) ⋙ functor ≅
    (complexFunctor T.restrict) ⋙ DerivedCategory.Q.{w} (C := T.modulesR)

set_option genInjectivity false in
/-- A geometric edge on the prescribed corner rings; the fields are exactly those
of FlatRingedDiagramInput not already supplied by the corners.
Source: strict coefficient supplement, edge data
(blueprint: lem-weil-pbc-flat-scalar-tower-exchange). -/
structure EdgeData (U V : Corner.{u, w}) where
  R : FlatRingedModuleImage V.R U.R
  S : FlatRingedModuleImage V.S U.S
  sameInverse : R.morphism.inverse = S.morphism.inverse
  sameDirect : R.morphism.direct = S.morphism.direct
  sameAdjunction : HEq R.morphism.adj S.morphism.adj
  coherent : R.inverse.ringUnderlying.hom ≫
      (sheafCompose U.topology (forget CommRingCat)).map U.a =
    R.morphism.inverse.map ((sheafCompose V.topology (forget CommRingCat)).map V.a) ≫
      eqToHom (congrArg (fun F ↦ F.obj
        ((sheafCompose V.topology (forget CommRingCat)).obj V.S)) sameInverse) ≫
      S.inverse.ringUnderlying.hom

/-- The edge's existing flat-restriction input, formed from the shared corner data.
Source: strict coefficient supplement, normalized restriction
(blueprint: lem-weil-pbc-flat-scalar-tower-exchange). -/
abbrev EdgeData.input {U V : Corner.{u, w}} (e : EdgeData U V) :
    FlatRingedDiagramInput V.topology U.topology where
  RU := U.R
  SU := U.S
  RV := V.R
  SV := V.S
  aU := U.a
  aV := V.a
  flatU := U.flat
  flatV := V.flat
  R := e.R
  S := e.S
  sameInverse := e.sameInverse
  sameDirect := e.sameDirect
  sameAdjunction := e.sameAdjunction
  coherent := e.coherent

set_option genInjectivity false in
/-- The specified derived adjunction, with the 0FND/0DVC representative normalization.
Source: Stacks 0FND/0DVC and strict coefficient supplement
(blueprint: lem-weil-pbc-flat-scalar-tower-exchange). -/
structure NormalizedDerivedAdjunction
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{w} A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{w} B]
    (L₀ : A ⥤ B) [L₀.Additive] (F₀ : B ⥤ A) [F₀.Additive] (adj₀ : L₀ ⊣ F₀) where
  L : DerivedCategory A ⥤ DerivedCategory B
  F : DerivedCategory B ⥤ DerivedCategory A
  q : DerivedCategory.Q ⋙ L ≅ (complexFunctor L₀) ⋙ DerivedCategory.Q
  η : (complexFunctor F₀) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ F
  adj : L ⊣ F
  derived : F.IsRightDerivedFunctor η (HomologicalComplex.quasiIso B (.up ℤ))
  computes : ∀ I : CochainComplex B ℤ, I.IsKInjective → IsIso (η.app I)
  transpose : ∀ (P : CochainComplex A ℤ) (I : CochainComplex B ℤ)
    (f : (complexFunctor L₀).obj P ⟶ I),
    adj.homEquiv (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj I)
      (q.hom.app P ≫ DerivedCategory.Q.map f) =
    DerivedCategory.Q.map ((complexAdjunction adj₀).homEquiv P I f) ≫ η.app I


set_option genInjectivity false in
/-- The chosen derived termwise operations of an edge with an invertible ring map.
Source: strict coefficient supplement, specified derived termwise adjunctions
(blueprint: lem-weil-pbc-flat-scalar-tower-exchange). -/
abbrev DerivedImage {C D : Type u} [SmallCategory C] [SmallCategory D]
    {K : GrothendieckTopology C} {H : GrothendieckTopology D}
    {RV : Sheaf K CommRingCat.{u}} {RU : Sheaf H CommRingCat.{u}}
    (e : FlatRingedModuleImage RV RU)
    [HasDerivedCategory.{w} ((Index.{u} ⥤ ringedSiteModules.{u} (coefficientRing RV)))]
    [HasDerivedCategory.{w} ((Index.{u} ⥤ ringedSiteModules.{u} (coefficientRing RU)))] :=
  NormalizedDerivedAdjunction
    (inverseDiagram e)
    (directDiagram e)
    (diagramAdjunction e)


/-- The termwise comparison of the two complex functors.
Source: strict coefficient supplement, degreewise ordinary comparison
(blueprint: lem-weil-pbc-flat-scalar-tower-exchange). -/
@[irreducible]
def complexComparison
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B]
    [Abelian C] [Abelian D]
    {F : A ⥤ B} {G : B ⥤ D} {H : A ⥤ C} {K : C ⥤ D}
    [F.Additive] [G.Additive]
    [H.Additive] [K.Additive]
    (α : F ⋙ G ≅ H ⋙ K) :
    (complexFunctor F) ⋙ (complexFunctor G) ≅
      (complexFunctor H) ⋙ (complexFunctor K) :=
  by
    unfold complexFunctor
    exact NatIso.mapHomologicalComplex α (.up ℤ)

/-- One of the three original normalization equations, with only its own inputs.
Source: strict coefficient supplement (blueprint: lem-weil-pbc-flat-scalar-tower-exchange). -/
def inverseNormalization
    {A₀ B₀ AR₀ BR₀ A B AR BR : Type*}
    [Category A₀] [Category B₀] [Category AR₀] [Category BR₀]
    [Category A] [Category B] [Category AR] [Category BR]
    {QA : A₀ ⥤ A} {QB : B₀ ⥤ B} {QAR : AR₀ ⥤ AR} {QBR : BR₀ ⥤ BR}
    {L₀ : A₀ ⥤ B₀} {LR₀ : AR₀ ⥤ BR₀}
    {rA₀ : A₀ ⥤ AR₀} {rB₀ : B₀ ⥤ BR₀}
    {L : A ⥤ B} {LR : AR ⥤ BR} {rA : A ⥤ AR} {rB : B ⥤ BR}
    (qL : QA ⋙ L ≅ L₀ ⋙ QB) (qLR : QAR ⋙ LR ≅ LR₀ ⋙ QBR)
    (qA : QA ⋙ rA ≅ rA₀ ⋙ QAR) (qB : QB ⋙ rB ≅ rB₀ ⋙ QBR)
    (b₀ : L₀ ⋙ rB₀ ≅ rA₀ ⋙ LR₀) (p : L ⋙ rB ≅ rA ⋙ LR) : Prop :=
  (∀ P, rB.map (qL.hom.app P) ≫ qB.hom.app (L₀.obj P) ≫
      QBR.map (b₀.hom.app P) =
    p.hom.app (QA.obj P) ≫ LR.map (qA.hom.app P) ≫ qLR.hom.app (rA₀.obj P))

/-- The inverse, direct and adjunct equations for fixed localization comparisons.
Source: strict coefficient supplement, normalized comparisons and their adjunction compatibility
(blueprint: lem-weil-pbc-flat-scalar-tower-exchange). -/
def derivedNormalization
    {A₀ B₀ AR₀ BR₀ A B AR BR : Type*}
    [Category A₀] [Category B₀] [Category AR₀] [Category BR₀]
    [Category A] [Category B] [Category AR] [Category BR]
    {QA : A₀ ⥤ A} {QB : B₀ ⥤ B} {QAR : AR₀ ⥤ AR} {QBR : BR₀ ⥤ BR}
    {L₀ : A₀ ⥤ B₀} {LR₀ : AR₀ ⥤ BR₀}
    {F₀ : B₀ ⥤ A₀} {FR₀ : BR₀ ⥤ AR₀}
    {rA₀ : A₀ ⥤ AR₀} {rB₀ : B₀ ⥤ BR₀}
    {L : A ⥤ B} {LR : AR ⥤ BR} {F : B ⥤ A} {FR : BR ⥤ AR}
    {rA : A ⥤ AR} {rB : B ⥤ BR}
    (qL : QA ⋙ L ≅ L₀ ⋙ QB) (qLR : QAR ⋙ LR ≅ LR₀ ⋙ QBR)
    (qA : QA ⋙ rA ≅ rA₀ ⋙ QAR) (qB : QB ⋙ rB ≅ rB₀ ⋙ QBR)
    (ηF : F₀ ⋙ QA ⟶ QB ⋙ F) (ηFR : FR₀ ⋙ QAR ⟶ QBR ⋙ FR)
    (adj : L ⊣ F) (adjR : LR ⊣ FR)
    (b₀ : L₀ ⋙ rB₀ ≅ rA₀ ⋙ LR₀) (d₀ : F₀ ⋙ rA₀ ≅ rB₀ ⋙ FR₀)
    (p : L ⋙ rB ≅ rA ⋙ LR) (d : F ⋙ rA ≅ rB ⋙ FR) : Prop :=
  inverseNormalization qL qLR qA qB b₀ p ∧
  (∀ I, rA.map (ηF.app I) ≫ d.hom.app (QB.obj I) ≫ FR.map (qB.hom.app I) =
    qA.hom.app (F₀.obj I) ≫ QAR.map (d₀.hom.app I) ≫ ηFR.app (rB₀.obj I)) ∧
  (∀ (M : A) (N : B) (t : L.obj M ⟶ N),
    adjR.homEquiv (rA.obj M) (rB.obj N) (p.inv.app M ≫ rB.map t) =
      rA.map (adj.homEquiv M N t) ≫ d.hom.app N)

/-- The original ordinary sheaf normalization, through the named actual diagram functors.
Source: the strict coefficient supplement, identified underlying sheaf comparisons
(blueprint: lem-weil-pbc-flat-scalar-tower-exchange). -/
def ordinaryNormalization {U V : Corner.{u, w}} (e : EdgeData U V)
    (b : inverseDiagram e.S ⋙ U.restrict ≅ V.restrict ⋙ inverseDiagram e.R)
    (d : directDiagram e.S ⋙ V.restrict ≅ U.restrict ⋙ directDiagram e.R) : Prop := by
  delta inverseDiagram directDiagram Corner.restrict Corner.modulesR Corner.modulesS
    coefficientRing id at b d
  exact e.input.OrdinaryComparisonsNormalized Index.{u} b d

/-- The supplied comparisons satisfy the ordinary, complex and adjunct normalizations.
Source: strict coefficient supplement, normalized p and d comparisons
(blueprint: lem-weil-pbc-flat-scalar-tower-exchange). -/
def EdgeNormalized {U V : Corner.{u, w}}
    (e : EdgeData U V) (R : DerivedImage e.R) (S : DerivedImage e.S)
    (rU : U.Restriction) (rV : V.Restriction)
    (p : S.L ⋙ rU.functor ≅ rV.functor ⋙ R.L)
    (d : S.F ⋙ rV.functor ≅ rU.functor ⋙ R.F) : Prop :=
  ∃ (b₀ : (inverseDiagram e.S) ⋙ U.restrict ≅
    V.restrict ⋙
    (inverseDiagram e.R))
    (d₀ : (directDiagram e.S) ⋙ V.restrict ≅
      U.restrict ⋙
      (directDiagram e.R)),
    ordinaryNormalization e b₀ d₀ ∧
    derivedNormalization
      (QA := DerivedCategory.Q.{w} (C := V.modulesS))
      (QB := DerivedCategory.Q.{w} (C := U.modulesS))
      (QAR := DerivedCategory.Q.{w} (C := V.modulesR))
      (QBR := DerivedCategory.Q.{w} (C := U.modulesR))
      S.q R.q rV.factor rU.factor S.η R.η S.adj R.adj
      (complexComparison b₀) (complexComparison d₀) p d

set_option genInjectivity false in
/-- The two normalized natural isomorphisms on the shared restrictions.
Source: strict coefficient supplement, p_u and d_u
(blueprint: lem-weil-pbc-flat-scalar-tower-exchange). -/
structure DerivedEdge {U V : Corner.{u, w}}
    (e : EdgeData U V) (R : DerivedImage e.R) (S : DerivedImage e.S)
    (rU : U.Restriction) (rV : V.Restriction) where
  /-- The prescribed inverse-image comparison, on the shared restrictions. -/
  p : S.L ⋙ rU.functor ≅ rV.functor ⋙ R.L
  /-- The prescribed direct-image comparison, on the shared restrictions. -/
  d : S.F ⋙ rV.functor ≅ rU.functor ⋙ R.F
  normalized : EdgeNormalized e R S rU rV p d

set_option genInjectivity false in
/-- A coefficient-normalized ordinary pullback square. The underlying sheaf equation
uniquely specifies the module comparison from the geometric square; its components
are linear morphisms for the given coefficient actions.
Source: Stacks 07A7 and strict coefficient supplement, canonical pullback square
(blueprint: lem-weil-pbc-flat-scalar-tower-exchange). -/
structure ModuleSquare
    {CX CY CX' CY' : Type u}
    [SmallCategory CX] [SmallCategory CY] [SmallCategory CX'] [SmallCategory CY']
    {KX : GrothendieckTopology CX} {KY : GrothendieckTopology CY}
    {KX' : GrothendieckTopology CX'} {KY' : GrothendieckTopology CY'}
    {RX : Sheaf KX CommRingCat.{u}} {RY : Sheaf KY CommRingCat.{u}}
    {RX' : Sheaf KX' CommRingCat.{u}} {RY' : Sheaf KY' CommRingCat.{u}}
    (f : FlatRingedModuleImage RY RX) (g : FlatRingedModuleImage RY RY')
    (fp : FlatRingedModuleImage RY' RX') (gp : FlatRingedModuleImage RX RX') where
  geometry : g.morphism.inverse ⋙ fp.morphism.inverse ≅
    f.morphism.inverse ⋙ gp.morphism.inverse
  coefficient : fp.morphism.inverse.map g.inverse.ringUnderlying.hom ≫
      fp.inverse.ringUnderlying.hom =
    geometry.hom.app ((sheafCompose KY (forget CommRingCat)).obj RY) ≫
      gp.morphism.inverse.map f.inverse.ringUnderlying.hom ≫ gp.inverse.ringUnderlying.hom
  modules : g.inverse.modules ⋙ fp.inverse.modules ≅ f.inverse.modules ⋙ gp.inverse.modules
  normalized : ∀ M : ringedSiteModules.{u}
      ((sheafCompose KY (forget₂ CommRingCat RingCat)).obj RY),
    (underlying RX').map (modules.hom.app M) ≫
        gp.inverse.moduleUnderlying.hom.app (f.inverse.modules.obj M) ≫
        gp.morphism.inverse.map (f.inverse.moduleUnderlying.hom.app M) =
      fp.inverse.moduleUnderlying.hom.app (g.inverse.modules.obj M) ≫
        fp.morphism.inverse.map (g.inverse.moduleUnderlying.hom.app M) ≫
        geometry.hom.app ((underlying RY).obj M)


/-- The square comparison on strict diagrams is the specified module comparison
applied termwise. Source: Stacks 07A7, strict coefficient supplement
(blueprint: lem-weil-pbc-flat-scalar-tower-exchange). -/
def ModuleSquare.diagrams
    {CX CY CX' CY' : Type u}
    [SmallCategory CX] [SmallCategory CY] [SmallCategory CX'] [SmallCategory CY']
    {KX : GrothendieckTopology CX} {KY : GrothendieckTopology CY}
    {KX' : GrothendieckTopology CX'} {KY' : GrothendieckTopology CY'}
    {RX : Sheaf KX CommRingCat.{u}} {RY : Sheaf KY CommRingCat.{u}}
    {RX' : Sheaf KX' CommRingCat.{u}} {RY' : Sheaf KY' CommRingCat.{u}}
    {f : FlatRingedModuleImage RY RX} {g : FlatRingedModuleImage RY RY'}
    {fp : FlatRingedModuleImage RY' RX'} {gp : FlatRingedModuleImage RX RX'}
    (s : ModuleSquare f g fp gp) :
    inverseDiagram g ⋙ inverseDiagram fp ≅ inverseDiagram f ⋙ inverseDiagram gp := by
  unfold inverseDiagram coefficientRing
  exact (Functor.whiskeringRight Index.{u} _ _).mapIso s.modules

/-- The localization factor of a composite, built from the two given factors.
Source: Stacks 04VG and strict coefficient supplement, composition under localization
(blueprint: lem-weil-pbc-flat-scalar-tower-exchange). -/
@[irreducible]
def composeFactor
    {A₀ B₀ C₀ A B C : Type*}
    [Category A₀] [Category B₀] [Category C₀]
    [Category A] [Category B] [Category C]
    {QA : A₀ ⥤ A} {QB : B₀ ⥤ B} {QC : C₀ ⥤ C}
    {F₀ : A₀ ⥤ B₀} {G₀ : B₀ ⥤ C₀} {F : A ⥤ B} {G : B ⥤ C}
    (qF : QA ⋙ F ≅ F₀ ⋙ QB) (qG : QB ⋙ G ≅ G₀ ⋙ QC) :
    QA ⋙ (F ⋙ G) ≅ (F₀ ⋙ G₀) ⋙ QC :=
  (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight qF G ≪≫
    Functor.associator _ _ _ ≪≫ isoWhiskerLeft F₀ qG ≪≫
    (Functor.associator _ _ _).symm

/-- The normalization equation for a square of localized functors.
Source: Stacks 04VG and strict coefficient supplement, localization of composition
(blueprint: lem-weil-pbc-flat-scalar-tower-exchange). -/
def squareNormalization
    {A₀ B₀ C₀ D₀ A B C D : Type*}
    [Category A₀] [Category B₀] [Category C₀] [Category D₀]
    [Category A] [Category B] [Category C] [Category D]
    {QA : A₀ ⥤ A} {QB : B₀ ⥤ B} {QC : C₀ ⥤ C} {QD : D₀ ⥤ D}
    {f₀ : A₀ ⥤ B₀} {g₀ : A₀ ⥤ C₀} {fp₀ : C₀ ⥤ D₀} {gp₀ : B₀ ⥤ D₀}
    {f : A ⥤ B} {g : A ⥤ C} {fp : C ⥤ D} {gp : B ⥤ D}
    (qf : QA ⋙ f ≅ f₀ ⋙ QB) (qg : QA ⋙ g ≅ g₀ ⋙ QC)
    (qfp : QC ⋙ fp ≅ fp₀ ⋙ QD) (qgp : QB ⋙ gp ≅ gp₀ ⋙ QD)
    (θ₀ : g₀ ⋙ fp₀ ≅ f₀ ⋙ gp₀) (θ : g ⋙ fp ≅ f ⋙ gp) : Prop :=
  ∀ P, θ.hom.app (QA.obj P) ≫ (composeFactor qf qgp).hom.app P =
    (composeFactor qg qfp).hom.app P ≫ QD.map (θ₀.hom.app P)

/-- Normalization of an exact-localization square on complexes. This generic form
keeps the four abelian categories opaque while checking the composition formula.
Source: Stacks 04VG and strict coefficient supplement, localization of pullback composition
(blueprint: lem-weil-pbc-flat-scalar-tower-exchange). -/
def LocalizationSquareNormalized
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{w} A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{w} B]
    {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory.{w} C]
    {D : Type uD} [Category.{vD} D] [Abelian D] [HasDerivedCategory.{w} D]
    (g₀ : A ⥤ B) [g₀.Additive] (fp₀ : B ⥤ D) [fp₀.Additive]
    (f₀ : A ⥤ C) [f₀.Additive] (gp₀ : C ⥤ D) [gp₀.Additive]
    (θ₀ : g₀ ⋙ fp₀ ≅ f₀ ⋙ gp₀)
    (gL : DerivedCategory A ⥤ DerivedCategory B)
    (fpL : DerivedCategory B ⥤ DerivedCategory D)
    (fL : DerivedCategory A ⥤ DerivedCategory C)
    (gpL : DerivedCategory C ⥤ DerivedCategory D)
    (qg : DerivedCategory.Q ⋙ gL ≅ g₀.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (qfp : DerivedCategory.Q ⋙ fpL ≅ fp₀.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (qf : DerivedCategory.Q ⋙ fL ≅ f₀.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (qgp : DerivedCategory.Q ⋙ gpL ≅ gp₀.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (θ : gL ⋙ fpL ≅ fL ⋙ gpL) : Prop :=
  ∀ P : CochainComplex A ℤ,
    fpL.map (qg.hom.app P) ≫ qfp.hom.app ((g₀.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex θ₀ (.up ℤ)).hom.app P) =
      θ.hom.app (DerivedCategory.Q.obj P) ≫ gpL.map (qf.hom.app P) ≫
        qgp.hom.app ((f₀.mapHomologicalComplex (.up ℤ)).obj P)

variable {X Y X' Y' : Corner.{u, w}}
  {f : EdgeData X Y} {g : EdgeData Y' Y}
  {fp : EdgeData X' Y'} {gp : EdgeData X' X}
  {rX : X.Restriction} {rY : Y.Restriction}
  {rX' : X'.Restriction} {rY' : Y'.Restriction}
  {fR : DerivedImage f.R} {fS : DerivedImage f.S}
  {gR : DerivedImage g.R} {gS : DerivedImage g.S}
  {fpR : DerivedImage fp.R} {fpS : DerivedImage fp.S}
  {gpR : DerivedImage gp.R} {gpS : DerivedImage gp.S}

set_option genInjectivity false in
/-- The two specified coefficient squares lie over the same geometric square.
The HEq only transports along the four sameInverse identifications in EdgeData;
it does not impose equality of differently typed module functors.
Source: strict coefficient supplement, specified commutative square
(blueprint: lem-weil-pbc-flat-scalar-tower-exchange). -/
structure Square where
  R : ModuleSquare f.R g.R fp.R gp.R
  S : ModuleSquare f.S g.S fp.S gp.S
  sameGeometry : HEq R.geometry S.geometry


/-- The specified derived square and its normalization by termwise pullback composition.
The two equations characterize exact localization of the ordinary canonical squares.
Source: strict coefficient supplement, canonical pullback composition after localization
(blueprint: lem-weil-pbc-flat-scalar-tower-exchange). -/
def SquareNormalized (s : Square (f := f) (g := g) (fp := fp) (gp := gp))
    (R : gR.L ⋙ fpR.L ≅ fR.L ⋙ gpR.L)
    (S : gS.L ⋙ fpS.L ≅ fS.L ⋙ gpS.L) : Prop :=
  squareNormalization fR.q gR.q fpR.q gpR.q
    (complexComparison
      (F := inverseDiagram g.R)
      (G := inverseDiagram fp.R)
      (H := inverseDiagram f.R)
      (K := inverseDiagram gp.R)
      s.R.diagrams) R ∧
  squareNormalization fS.q gS.q fpS.q gpS.q
    (complexComparison
      (F := inverseDiagram g.S)
      (G := inverseDiagram fp.S)
      (H := inverseDiagram f.S)
      (K := inverseDiagram gp.S)
      s.S.diagrams) S

/-- The source comparison b, composed from p_g and d_f exactly as in the node.
Source: strict coefficient supplement, displayed definition of b_Z
(blueprint: lem-weil-pbc-flat-scalar-tower-exchange). -/
def sourceComparison (df : DerivedEdge f fR fS rX rY) (dg : DerivedEdge g gR gS rY' rY) :
    (fS.F ⋙ gS.L) ⋙ rY'.functor ≅ rX.functor ⋙ (fR.F ⋙ gR.L) :=
  Functor.associator _ _ _ ≪≫ isoWhiskerLeft fS.F dg.p ≪≫
    (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight df.d gR.L ≪≫
    Functor.associator _ _ _

/-- The target comparison d, composed from d_f' and p_g' exactly as in the node.
Source: strict coefficient supplement, displayed definition of d_Z
(blueprint: lem-weil-pbc-flat-scalar-tower-exchange). -/
def targetComparison (dfp : DerivedEdge fp fpR fpS rX' rY') (dgp : DerivedEdge gp gpR gpS rX' rX) :
    (gpS.L ⋙ fpS.F) ⋙ rY'.functor ≅ rX.functor ⋙ (gpR.L ⋙ fpR.F) :=
  Functor.associator _ _ _ ≪≫ isoWhiskerLeft gpS.L dfp.d ≪≫
    (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight dgp.p fpR.F ≪≫
    Functor.associator _ _ _


/-- Compatibility of inverse comparisons around a coefficient square.
Source: strict coefficient supplement, pullback composition square
(blueprint: lem-weil-pbc-flat-scalar-tower-exchange). -/
private def comparisonSquare
    {A B C D AR BR CR DR : Type*}
    [Category A] [Category B] [Category C] [Category D]
    [Category AR] [Category BR] [Category CR] [Category DR]
    {f : A ⥤ B} {g : A ⥤ C} {fp : C ⥤ D} {gp : B ⥤ D}
    {fR : AR ⥤ BR} {gR : AR ⥤ CR} {fpR : CR ⥤ DR} {gpR : BR ⥤ DR}
    {rA : A ⥤ AR} {rB : B ⥤ BR} {rC : C ⥤ CR} {rD : D ⥤ DR}
    (bf : f ⋙ rB ≅ rA ⋙ fR) (bg : g ⋙ rC ≅ rA ⋙ gR)
    (bfp : fp ⋙ rD ≅ rC ⋙ fpR) (bgp : gp ⋙ rD ≅ rB ⋙ gpR)
    (θ : g ⋙ fp ≅ f ⋙ gp) (θR : gR ⋙ fpR ≅ fR ⋙ gpR) : Prop :=
  ∀ M, rD.map (θ.hom.app M) ≫ bgp.hom.app (f.obj M) ≫
      gpR.map (bf.hom.app M) =
    bfp.hom.app (g.obj M) ≫ fpR.map (bg.hom.app M) ≫ θR.hom.app (rA.obj M)

private def composeComparison
    {A B C AR BR CR : Type*}
    [Category A] [Category B] [Category C]
    [Category AR] [Category BR] [Category CR]
    {F : A ⥤ B} {G : B ⥤ C} {FR : AR ⥤ BR} {GR : BR ⥤ CR}
    {r : A ⥤ AR} {s : B ⥤ BR} {t : C ⥤ CR}
    (pF : F ⋙ s ≅ r ⋙ FR) (pG : G ⋙ t ≅ s ⋙ GR) :
    (F ⋙ G) ⋙ t ≅ r ⋙ (FR ⋙ GR) :=
  Functor.associator _ _ _ ≪≫ isoWhiskerLeft F pG ≪≫
    (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight pF GR ≪≫
    Functor.associator _ _ _

private theorem composeComparison_app
    {A B C AR BR CR : Type*}
    [Category A] [Category B] [Category C]
    [Category AR] [Category BR] [Category CR]
    {F : A ⥤ B} {G : B ⥤ C} {FR : AR ⥤ BR} {GR : BR ⥤ CR}
    {r : A ⥤ AR} {s : B ⥤ BR} {t : C ⥤ CR}
    (pF : F ⋙ s ≅ r ⋙ FR) (pG : G ⋙ t ≅ s ⋙ GR) (M : A) :
    (composeComparison pF pG).hom.app M =
      pG.hom.app (F.obj M) ≫ GR.map (pF.hom.app M) := by
  simp [composeComparison]


private theorem comparison_comp
    {A₀ B₀ C₀ AR₀ BR₀ CR₀ A B C AR BR CR : Type*}
    [Category A₀] [Category B₀] [Category C₀]
    [Category AR₀] [Category BR₀] [Category CR₀]
    [Category A] [Category B] [Category C]
    [Category AR] [Category BR] [Category CR]
    {QA : A₀ ⥤ A} {QB : B₀ ⥤ B} {QC : C₀ ⥤ C}
    {QAR : AR₀ ⥤ AR} {QBR : BR₀ ⥤ BR} {QCR : CR₀ ⥤ CR}
    {r₀ : A₀ ⥤ AR₀} {s₀ : B₀ ⥤ BR₀} {t₀ : C₀ ⥤ CR₀}
    {r : A ⥤ AR} {s : B ⥤ BR} {t : C ⥤ CR}
    {F₀ : A₀ ⥤ B₀} {G₀ : B₀ ⥤ C₀}
    {FR₀ : AR₀ ⥤ BR₀} {GR₀ : BR₀ ⥤ CR₀}
    {F : A ⥤ B} {G : B ⥤ C} {FR : AR ⥤ BR} {GR : BR ⥤ CR}
    (qr : QA ⋙ r ≅ r₀ ⋙ QAR) (qs : QB ⋙ s ≅ s₀ ⋙ QBR)
    (qt : QC ⋙ t ≅ t₀ ⋙ QCR)
    (qF : QA ⋙ F ≅ F₀ ⋙ QB) (qG : QB ⋙ G ≅ G₀ ⋙ QC)
    (qFR : QAR ⋙ FR ≅ FR₀ ⋙ QBR) (qGR : QBR ⋙ GR ≅ GR₀ ⋙ QCR)
    (pF₀ : F₀ ⋙ s₀ ≅ r₀ ⋙ FR₀) (pG₀ : G₀ ⋙ t₀ ≅ s₀ ⋙ GR₀)
    (pF : F ⋙ s ≅ r ⋙ FR) (pG : G ⋙ t ≅ s ⋙ GR)
    (hpF : ∀ P, s.map (qF.hom.app P) ≫ qs.hom.app (F₀.obj P) ≫
        QBR.map (pF₀.hom.app P) =
      pF.hom.app (QA.obj P) ≫ FR.map (qr.hom.app P) ≫ qFR.hom.app (r₀.obj P))
    (hpG : ∀ P, t.map (qG.hom.app P) ≫ qt.hom.app (G₀.obj P) ≫
        QCR.map (pG₀.hom.app P) =
      pG.hom.app (QB.obj P) ≫ GR.map (qs.hom.app P) ≫ qGR.hom.app (s₀.obj P))
    (P : A₀) :
    t.map ((composeFactor qF qG).hom.app P) ≫
        qt.hom.app ((F₀ ⋙ G₀).obj P) ≫
        QCR.map ((composeComparison pF₀ pG₀).hom.app P) =
      (composeComparison pF pG).hom.app (QA.obj P) ≫
        (FR ⋙ GR).map (qr.hom.app P) ≫
        (composeFactor qFR qGR).hom.app (r₀.obj P) := by
  simp only [composeFactor, composeComparison, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, isoWhiskerRight_hom, isoWhiskerLeft_hom,
    whiskerRight_app, whiskerLeft_app, associator_hom_app, associator_inv_app,
    Category.id_comp, Category.comp_id]
  change t.map (G.map (qF.hom.app P) ≫ qG.hom.app (F₀.obj P)) ≫
      qt.hom.app (G₀.obj (F₀.obj P)) ≫
      QCR.map (pG₀.hom.app (F₀.obj P) ≫ GR₀.map (pF₀.hom.app P)) =
    (pG.hom.app (F.obj (QA.obj P)) ≫ GR.map (pF.hom.app (QA.obj P))) ≫
      GR.map (FR.map (qr.hom.app P)) ≫
      GR.map (qFR.hom.app (r₀.obj P)) ≫ qGR.hom.app (FR₀.obj (r₀.obj P))
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% (hpG (F₀.obj P))]
  have hn := pG.hom.naturality (qF.hom.app P)
  simp only [Functor.comp_map, Functor.comp_obj] at hn
  rw [reassoc_of% hn]
  have hn' := qGR.hom.naturality (pF₀.hom.app P)
  simp only [Functor.comp_map, Functor.comp_obj] at hn'
  rw [← hn']
  rw [← GR.map_comp_assoc, ← GR.map_comp_assoc]
  simp only [Category.assoc]
  rw [hpF]
  simp only [Functor.map_comp, Category.assoc]


private theorem comparison_square
    {A₀ B₀ C₀ D₀ A B C D : Type*}
    [Category A₀] [Category B₀] [Category C₀] [Category D₀]
    [Category A] [Category B] [Category C] [Category D]
    {QA : A₀ ⥤ A} {QB : B₀ ⥤ B} {QC : C₀ ⥤ C} {QD : D₀ ⥤ D}
    {r₀ : A₀ ⥤ B₀} {s₀ : C₀ ⥤ D₀} {r : A ⥤ B} {s : C ⥤ D}
    {F₀ G₀ : A₀ ⥤ C₀} {FR₀ GR₀ : B₀ ⥤ D₀}
    {F G : A ⥤ C} {FR GR : B ⥤ D}
    (qr : QA ⋙ r ≅ r₀ ⋙ QB) (qs : QC ⋙ s ≅ s₀ ⋙ QD)
    (qF : QA ⋙ F ≅ F₀ ⋙ QC) (qG : QA ⋙ G ≅ G₀ ⋙ QC)
    (qFR : QB ⋙ FR ≅ FR₀ ⋙ QD) (qGR : QB ⋙ GR ≅ GR₀ ⋙ QD)
    (pF₀ : F₀ ⋙ s₀ ≅ r₀ ⋙ FR₀) (pG₀ : G₀ ⋙ s₀ ≅ r₀ ⋙ GR₀)
    (pF : F ⋙ s ≅ r ⋙ FR) (pG : G ⋙ s ≅ r ⋙ GR)
    (θ₀ : F₀ ≅ G₀) (θR₀ : FR₀ ≅ GR₀) (θ : F ≅ G) (θR : FR ≅ GR)
    (hpF : ∀ P, s.map (qF.hom.app P) ≫ qs.hom.app (F₀.obj P) ≫
        QD.map (pF₀.hom.app P) =
      pF.hom.app (QA.obj P) ≫ FR.map (qr.hom.app P) ≫ qFR.hom.app (r₀.obj P))
    (hpG : ∀ P, s.map (qG.hom.app P) ≫ qs.hom.app (G₀.obj P) ≫
        QD.map (pG₀.hom.app P) =
      pG.hom.app (QA.obj P) ≫ GR.map (qr.hom.app P) ≫ qGR.hom.app (r₀.obj P))
    (hθ : ∀ P, θ.hom.app (QA.obj P) ≫ qG.hom.app P =
      qF.hom.app P ≫ QC.map (θ₀.hom.app P))
    (hθR : ∀ P, θR.hom.app (QB.obj P) ≫ qGR.hom.app P =
      qFR.hom.app P ≫ QD.map (θR₀.hom.app P))
    (h₀ : ∀ P, s₀.map (θ₀.hom.app P) ≫ pG₀.hom.app P =
      pF₀.hom.app P ≫ θR₀.hom.app (r₀.obj P)) (P : A₀) :
    s.map (θ.hom.app (QA.obj P)) ≫ pG.hom.app (QA.obj P) =
      pF.hom.app (QA.obj P) ≫ θR.hom.app (r.obj (QA.obj P)) := by
  apply (cancel_mono (GR.map (qr.hom.app P) ≫ qGR.hom.app (r₀.obj P))).mp
  simp only [Category.assoc]
  rw [← hpG]
  rw [← s.map_comp_assoc, hθ, s.map_comp, Category.assoc]
  have hn := qs.hom.naturality (θ₀.hom.app P)
  simp only [Functor.comp_map, Functor.comp_obj] at hn
  rw [reassoc_of% hn]
  rw [← QD.map_comp, h₀, QD.map_comp]
  rw [reassoc_of% (hpF P)]
  have hn' := θR.hom.naturality (qr.hom.app P)
  simp only [Functor.comp_obj] at hn'
  rw [← reassoc_of% hn', hθR]


private theorem counit_from_adjunct
    {A B AR BR : Type*} [Category A] [Category B] [Category AR] [Category BR]
    {LS : A ⥤ B} {FS : B ⥤ A} {LR : AR ⥤ BR} {FR : BR ⥤ AR}
    {rU : B ⥤ BR} {rV : A ⥤ AR}
    (aS : LS ⊣ FS) (aR : LR ⊣ FR)
    (b : LS ⋙ rU ≅ rV ⋙ LR) (d : FS ⋙ rV ≅ rU ⋙ FR)
    (h : ∀ (M : A) (N : B) (t : LS.obj M ⟶ N),
      aR.homEquiv (rV.obj M) (rU.obj N) (b.inv.app M ≫ rU.map t) =
        rV.map (aS.homEquiv M N t) ≫ d.hom.app N) (N : B) :
    b.hom.app (FS.obj N) ≫ LR.map (d.hom.app N) ≫ aR.counit.app (rU.obj N) =
      rU.map (aS.counit.app N) := by
  have hc : aS.homEquiv (FS.obj N) N (aS.counit.app N) = 𝟙 _ := by
    rw [← aS.homEquiv_symm_id]
    exact (aS.homEquiv _ _).apply_symm_apply _
  have ht := h (FS.obj N) N (aS.counit.app N)
  rw [hc, Functor.map_id, Category.id_comp] at ht
  have ht' := congrArg (aR.homEquiv _ _).symm ht
  rw [Equiv.symm_apply_apply, aR.homEquiv_counit] at ht'
  rw [← ht']
  simp only [Iso.hom_inv_id_app_assoc]

set_option backward.defeqAttrib.useBackward true in
private theorem exchange_of_square
    {AS BS CS DS AR BR CR DR : Type*}
    [Category AS] [Category BS] [Category CS] [Category DS]
    [Category AR] [Category BR] [Category CR] [Category DR]
    {LS : AS ⥤ BS} {FS : BS ⥤ AS} {LSp : CS ⥤ DS} {FSp : DS ⥤ CS}
    {LR : AR ⥤ BR} {FR : BR ⥤ AR} {LRp : CR ⥤ DR} {FRp : DR ⥤ CR}
    {GS : AS ⥤ CS} {HS : BS ⥤ DS} {GR : AR ⥤ CR} {HR : BR ⥤ DR}
    {rA : AS ⥤ AR} {rB : BS ⥤ BR} {rC : CS ⥤ CR} {rD : DS ⥤ DR}
    (aS : LS ⊣ FS) (aSp : LSp ⊣ FSp) (aR : LR ⊣ FR) (aRp : LRp ⊣ FRp)
    (pf : LS ⋙ rB ≅ rA ⋙ LR) (pg : GS ⋙ rC ≅ rA ⋙ GR)
    (pfp : LSp ⋙ rD ≅ rC ⋙ LRp) (pgp : HS ⋙ rD ≅ rB ⋙ HR)
    (df : FS ⋙ rA ≅ rB ⋙ FR) (dfp : FSp ⋙ rC ≅ rD ⋙ FRp)
    (θR : GR ⋙ LRp ≅ LR ⋙ HR) (θS : GS ⋙ LSp ≅ LS ⋙ HS)
    (hcF : ∀ N, pf.hom.app (FS.obj N) ≫ LR.map (df.hom.app N) ≫
      aR.counit.app (rB.obj N) = rB.map (aS.counit.app N))
    (hcFp : ∀ N, pfp.hom.app (FSp.obj N) ≫ LRp.map (dfp.hom.app N) ≫
      aRp.counit.app (rD.obj N) = rD.map (aSp.counit.app N))
    (hC : ∀ M, rD.map (θS.hom.app M) ≫ pgp.hom.app (LS.obj M) ≫
        HR.map (pf.hom.app M) =
      pfp.hom.app (GS.obj M) ≫ LRp.map (pg.hom.app M) ≫ θR.hom.app (rA.obj M)) :
    whiskerRight (mateEquiv aS aSp (TwoSquare.mk _ _ _ _ θS.hom)).natTrans rC ≫
        (composeComparison pgp dfp).hom =
      (composeComparison df pg).hom ≫
        whiskerLeft rB (mateEquiv aR aRp (TwoSquare.mk _ _ _ _ θR.hom)).natTrans := by
  ext Z
  simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
    composeComparison, Iso.trans_hom, Iso.symm_hom,
    isoWhiskerRight_hom, isoWhiskerLeft_hom, NatTrans.comp_app,
    whiskerRight_app, whiskerLeft_app, associator_hom_app, associator_inv_app,
    Category.id_comp, Category.comp_id, Category.assoc]
  change rC.map ((mateEquiv aS aSp
      (TwoSquare.mk _ _ _ _ θS.hom)).natTrans.app Z) ≫
        dfp.hom.app (HS.obj Z) ≫ FRp.map (pgp.hom.app Z) =
      pg.hom.app (FS.obj Z) ≫ GR.map (df.hom.app Z) ≫
        (mateEquiv aR aRp (TwoSquare.mk _ _ _ _ θR.hom)).natTrans.app
          (rB.obj Z)
  apply (aRp.homEquiv _ _).symm.injective
  simp only [aRp.homEquiv_counit, Functor.map_comp, Category.assoc]
  apply (cancel_epi (pfp.hom.app (GS.obj (FS.obj Z)))).mp
  try simp only [Category.assoc]
  have hnε := aRp.counit.naturality (pgp.hom.app Z)
  simp only [Functor.comp_map, Functor.id_map, Functor.comp_obj] at hnε
  dsimp only [Functor.comp_obj]
  rw [hnε]
  have hnp := pfp.hom.naturality
    ((mateEquiv aS aSp (TwoSquare.mk _ _ _ _ θS.hom)).natTrans.app Z)
  simp only [Functor.comp_map, Functor.comp_obj] at hnp
  rw [← reassoc_of% hnp]
  change rD.map (LSp.map _) ≫ pfp.hom.app _ ≫
      LRp.map (dfp.hom.app _) ≫ aRp.counit.app _ ≫ pgp.hom.app Z = _
  rw [reassoc_of% (hcFp (HS.obj Z))]
  rw [← rD.map_comp_assoc, mateEquiv_counit]
  change rD.map (θS.hom.app _ ≫ HS.map (aS.counit.app Z)) ≫ pgp.hom.app Z = _
  rw [rD.map_comp, Category.assoc]
  have hnε' := pgp.hom.naturality (aS.counit.app Z)
  simp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hnε'
  rw [hnε']
  change rD.map (θS.hom.app _) ≫ pgp.hom.app _ ≫
      HR.map (rB.map (aS.counit.app Z)) = _
  rw [← hcF Z, HR.map_comp, HR.map_comp]
  rw [reassoc_of% (hC (FS.obj Z))]
  have hnθ := θR.hom.naturality (df.hom.app Z)
  simp only [Functor.comp_map, Functor.comp_obj] at hnθ
  rw [← reassoc_of% hnθ]
  rw [mateEquiv_counit]


private theorem exchange_and_transpose
    {AS BS CS DS AR BR CR DR : Type*}
    [Category AS] [Category BS] [Category CS] [Category DS]
    [Category AR] [Category BR] [Category CR] [Category DR]
    {LS : AS ⥤ BS} {FS : BS ⥤ AS} {LSp : CS ⥤ DS} {FSp : DS ⥤ CS}
    {LR : AR ⥤ BR} {FR : BR ⥤ AR} {LRp : CR ⥤ DR} {FRp : DR ⥤ CR}
    {GS : AS ⥤ CS} {HS : BS ⥤ DS} {GR : AR ⥤ CR} {HR : BR ⥤ DR}
    {rA : AS ⥤ AR} {rB : BS ⥤ BR} {rC : CS ⥤ CR} {rD : DS ⥤ DR}
    (aS : LS ⊣ FS) (aSp : LSp ⊣ FSp) (aR : LR ⊣ FR) (aRp : LRp ⊣ FRp)
    (pf : LS ⋙ rB ≅ rA ⋙ LR) (pg : GS ⋙ rC ≅ rA ⋙ GR)
    (pfp : LSp ⋙ rD ≅ rC ⋙ LRp) (pgp : HS ⋙ rD ≅ rB ⋙ HR)
    (df : FS ⋙ rA ≅ rB ⋙ FR) (dfp : FSp ⋙ rC ≅ rD ⋙ FRp)
    (θR : GR ⋙ LRp ≅ LR ⋙ HR) (θS : GS ⋙ LSp ≅ LS ⋙ HS)
    (hcF : ∀ N, pf.hom.app (FS.obj N) ≫ LR.map (df.hom.app N) ≫
      aR.counit.app (rB.obj N) = rB.map (aS.counit.app N))
    (hcFp : ∀ N, pfp.hom.app (FSp.obj N) ≫ LRp.map (dfp.hom.app N) ≫
      aRp.counit.app (rD.obj N) = rD.map (aSp.counit.app N))
    (hC : ∀ M, rD.map (θS.hom.app M) ≫ pgp.hom.app (LS.obj M) ≫
        HR.map (pf.hom.app M) =
      pfp.hom.app (GS.obj M) ≫ LRp.map (pg.hom.app M) ≫ θR.hom.app (rA.obj M)) :
    (whiskerRight (mateEquiv aS aSp (TwoSquare.mk _ _ _ _ θS.hom)).natTrans rC ≫
        (composeComparison pgp dfp).hom =
      (composeComparison df pg).hom ≫
        whiskerLeft rB (mateEquiv aR aRp (TwoSquare.mk _ _ _ _ θR.hom)).natTrans) ∧
    (∀ Z : BS,
      (aRp.homEquiv _ _).symm
        ((composeComparison df pg).inv.app Z ≫
          rC.map ((mateEquiv aS aSp (TwoSquare.mk _ _ _ _ θS.hom)).app Z) ≫
          (composeComparison pgp dfp).hom.app Z) =
        θR.hom.app (FR.obj (rB.obj Z)) ≫ HR.map (aR.counit.app (rB.obj Z))) := by
  have hE := exchange_of_square aS aSp aR aRp
    pf pg pfp pgp df dfp θR θS hcF hcFp hC
  refine ⟨hE, ?_⟩
  intro Z
  have h := NatTrans.congr_app hE Z
  simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app] at h
  rw [h, Iso.inv_hom_id_app_assoc, aRp.homEquiv_counit]
  exact mateEquiv_counit aR aRp (TwoSquare.mk _ _ _ _ θR.hom) (rB.obj Z)


private theorem transport_naturality
    {A B : Type*} [Category A] [Category B] {F G : A ⥤ B}
    (h : F = G) {M N : A} (t : M ⟶ N) :
    eqToHom (congrArg (fun E ↦ E.obj M) h) ≫ G.map t =
      F.map t ≫ eqToHom (congrArg (fun E ↦ E.obj N) h) := by
  subst G
  simp


private theorem geometry_transport
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {fR fS : A ⥤ B} {gR gS : A ⥤ C} {fpR fpS : C ⥤ D} {gpR gpS : B ⥤ D}
    (hf : fR = fS) (hg : gR = gS) (hfp : fpR = fpS) (hgp : gpR = gpS)
    (θR : gR ⋙ fpR ≅ fR ⋙ gpR) (θS : gS ⋙ fpS ≅ fS ⋙ gpS)
    (hθ : HEq θR θS) (M : A) :
    θS.hom.app M ≫ eqToHom (congrArg (fun F ↦ F.obj (fS.obj M)) hgp.symm) ≫
        gpR.map (eqToHom (congrArg (fun F ↦ F.obj M) hf.symm)) =
      eqToHom (congrArg (fun F ↦ F.obj (gS.obj M)) hfp.symm) ≫
        fpR.map (eqToHom (congrArg (fun F ↦ F.obj M) hg.symm)) ≫ θR.hom.app M := by
  subst fS
  subst gS
  subst fpS
  subst gpS
  cases eq_of_heq hθ
  simp


private theorem comp_iso_of_eq
    {C : Type*} [Category C] {A B D E : C}
    {a : A ⟶ B} {b : B ⟶ D} {t : A ⟶ E}
    (i : E ≅ D) (h : t = a ≫ b ≫ i.inv) : t ≫ i.hom = a ≫ b := by
  rw [h]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]


private theorem inverse_underlying_naturality
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {K : GrothendieckTopology C} {H : GrothendieckTopology D}
    {R : Sheaf K CommRingCat.{u}} {S : Sheaf H CommRingCat.{u}}
    (e : FlatRingedModuleImage R S)
    {M N : ringedSiteModules.{u}
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R)} (t : M ⟶ N) :
    (underlying S).map (e.inverse.modules.map t) ≫ e.inverse.moduleUnderlying.hom.app N =
      e.inverse.moduleUnderlying.hom.app M ≫ e.morphism.inverse.map ((underlying R).map t) :=
  e.inverse.moduleUnderlying.hom.naturality t

private theorem descend_square
    {A B C D AR BR CR DR A₀ B₀ C₀ D₀ AR₀ BR₀ CR₀ DR₀ : Type*}
    [Category A] [Category A₀]
    [Category B] [Category B₀]
    [Category C] [Category C₀]
    [Category D] [Category D₀]
    [Category AR] [Category AR₀]
    [Category BR] [Category BR₀]
    [Category CR] [Category CR₀]
    [Category DR] [Category DR₀]
    (QA : A₀ ⥤ A) (W : MorphismProperty A₀) [QA.IsLocalization W]
    (QB : B₀ ⥤ B)
    (QC : C₀ ⥤ C)
    (QD : D₀ ⥤ D)
    (QAR : AR₀ ⥤ AR)
    (QBR : BR₀ ⥤ BR)
    (QCR : CR₀ ⥤ CR)
    (QDR : DR₀ ⥤ DR)
    {f₀ : A₀ ⥤ B₀} {g₀ : A₀ ⥤ C₀}
    {fp₀ : C₀ ⥤ D₀} {gp₀ : B₀ ⥤ D₀}
    {fR₀ : AR₀ ⥤ BR₀} {gR₀ : AR₀ ⥤ CR₀}
    {fpR₀ : CR₀ ⥤ DR₀} {gpR₀ : BR₀ ⥤ DR₀}
    {rA₀ : A₀ ⥤ AR₀} {rB₀ : B₀ ⥤ BR₀}
    {rC₀ : C₀ ⥤ CR₀} {rD₀ : D₀ ⥤ DR₀}
    {f : A ⥤ B}
    {g : A ⥤ C}
    {fp : C ⥤ D}
    {gp : B ⥤ D}
    {fR : AR ⥤ BR}
    {gR : AR ⥤ CR}
    {fpR : CR ⥤ DR}
    {gpR : BR ⥤ DR}
    {rA : A ⥤ AR}
    {rB : B ⥤ BR}
    {rC : C ⥤ CR}
    {rD : D ⥤ DR}
    (qf : QA ⋙ f ≅ f₀ ⋙ QB)
    (qg : QA ⋙ g ≅ g₀ ⋙ QC)
    (qfp : QC ⋙ fp ≅ fp₀ ⋙ QD)
    (qgp : QB ⋙ gp ≅ gp₀ ⋙ QD)
    (qfR : QAR ⋙ fR ≅ fR₀ ⋙ QBR)
    (qgR : QAR ⋙ gR ≅ gR₀ ⋙ QCR)
    (qfpR : QCR ⋙ fpR ≅ fpR₀ ⋙ QDR)
    (qgpR : QBR ⋙ gpR ≅ gpR₀ ⋙ QDR)
    (qrA : QA ⋙ rA ≅ rA₀ ⋙ QAR)
    (qrB : QB ⋙ rB ≅ rB₀ ⋙ QBR)
    (qrC : QC ⋙ rC ≅ rC₀ ⋙ QCR)
    (qrD : QD ⋙ rD ≅ rD₀ ⋙ QDR)
    (bf : f₀ ⋙ rB₀ ≅ rA₀ ⋙ fR₀) (bg : g₀ ⋙ rC₀ ≅ rA₀ ⋙ gR₀)
    (bfp : fp₀ ⋙ rD₀ ≅ rC₀ ⋙ fpR₀) (bgp : gp₀ ⋙ rD₀ ≅ rB₀ ⋙ gpR₀)
    (pf : f ⋙ rB ≅ rA ⋙ fR) (pg : g ⋙ rC ≅ rA ⋙ gR)
    (pfp : fp ⋙ rD ≅ rC ⋙ fpR) (pgp : gp ⋙ rD ≅ rB ⋙ gpR)
    (hf : inverseNormalization qf qfR qrA qrB bf pf)
    (hg : inverseNormalization qg qgR qrA qrC bg pg)
    (hfp : inverseNormalization qfp qfpR qrC qrD bfp pfp)
    (hgp : inverseNormalization qgp qgpR qrB qrD bgp pgp)
    (θ₀ : g₀ ⋙ fp₀ ≅ f₀ ⋙ gp₀) (θR₀ : gR₀ ⋙ fpR₀ ≅ fR₀ ⋙ gpR₀)
    (θ : g ⋙ fp ≅ f ⋙ gp) (θR : gR ⋙ fpR ≅ fR ⋙ gpR)
    (hθ : squareNormalization qf qg qfp qgp θ₀ θ)
    (hθR : squareNormalization qfR qgR qfpR qgpR θR₀ θR)
    (h₀ : comparisonSquare bf bg bfp bgp θ₀ θR₀) :
    ∀ M, rD.map (θ.hom.app M) ≫ pgp.hom.app (f.obj M) ≫ gpR.map (pf.hom.app M) =
      pfp.hom.app (g.obj M) ≫ fpR.map (pg.hom.app M) ≫ θR.hom.app (rA.obj M) := by
  unfold comparisonSquare at h₀
  unfold inverseNormalization at hf hg hfp hgp
  unfold squareNormalization at hθ hθR
  let α := whiskerRight θ.hom rD ≫ (composeComparison pf pgp).hom
  let β := (composeComparison pg pfp).hom ≫ whiskerLeft rA θR.hom
  have hab : α = β := by
    apply Localization.natTrans_ext QA W
    intro P
    exact comparison_square qrA qrD
      (composeFactor qg qfp) (composeFactor qf qgp)
      (composeFactor qgR qfpR) (composeFactor qfR qgpR)
      (composeComparison bg bfp) (composeComparison bf bgp)
      (composeComparison pg pfp) (composeComparison pf pgp) θ₀ θR₀ θ θR
      (comparison_comp qrA qrC qrD qg qfp qgR qfpR bg bfp pg pfp hg hfp)
      (comparison_comp qrA qrB qrD qf qgp qfR qgpR bf bgp pf pgp hf hgp)
      hθ hθR (fun P ↦ by simpa only [composeComparison_app, Category.assoc] using h₀ P) P
  intro M
  have h := NatTrans.congr_app hab M
  simpa only [α, β, composeComparison_app, NatTrans.comp_app,
    whiskerRight_app, whiskerLeft_app, Category.assoc] using h


private theorem ordinary_square
    (s : Square (f := f) (g := g) (fp := fp) (gp := gp))
    (bf : (inverseDiagram f.S) ⋙ X.restrict ≅
      Y.restrict ⋙
      (inverseDiagram f.R))
    (bg : (inverseDiagram g.S) ⋙ Y'.restrict ≅
      Y.restrict ⋙
      (inverseDiagram g.R))
    (bfp : (inverseDiagram fp.S) ⋙ X'.restrict ≅
      Y'.restrict ⋙ (inverseDiagram fp.R))
    (bgp : (inverseDiagram gp.S) ⋙ X'.restrict ≅
      X.restrict
      ⋙ (inverseDiagram gp.R))
    (df₀ : (directDiagram f.S) ⋙ Y.restrict ≅
      X.restrict
      ⋙ (directDiagram f.R))
    (dg₀ : (directDiagram g.S) ⋙ Y.restrict ≅
      Y'.restrict
      ⋙ (directDiagram g.R))
    (dfp₀ : (directDiagram fp.S) ⋙ Y'.restrict ≅
      X'.restrict ⋙ (directDiagram fp.R))
    (dgp₀ : (directDiagram gp.S) ⋙ X.restrict ≅
      X'.restrict ⋙ (directDiagram gp.R))
    (hbf : ordinaryNormalization f bf df₀)
    (hbg : ordinaryNormalization g bg dg₀)
    (hbfp : ordinaryNormalization fp bfp dfp₀)
    (hbgp : ordinaryNormalization gp bgp dgp₀)
    (M : Y.modulesS) :
    X'.restrict.map (s.S.diagrams.hom.app M) ≫
        bgp.hom.app (((inverseDiagram f.S)).obj M) ≫
        ((inverseDiagram gp.R)).map (bf.hom.app M) =
      bfp.hom.app (((inverseDiagram g.S)).obj M) ≫
        ((inverseDiagram fp.R)).map (bg.hom.app M) ≫
        s.R.diagrams.hom.app (Y.restrict.obj M) := by
  delta ordinaryNormalization inverseDiagram directDiagram Corner.restrict
    Corner.modulesR Corner.modulesS coefficientRing id at *
  let rY₀ := (Functor.whiskeringRight Index.{u} _ _).obj
    (SheafOfModules.restrictScalars.{u}
      ((sheafCompose Y.topology (forget₂ CommRingCat RingCat)).map Y.a))
  ext j : 2
  apply (underlying X'.R).map_injective
  simp only [NatTrans.comp_app, Functor.map_comp]
  apply (cancel_mono (gp.R.inverse.moduleUnderlying.hom.app
    (f.R.inverse.modules.obj ((rY₀.obj M).obj j)) ≫
      gp.R.morphism.inverse.map (f.R.inverse.moduleUnderlying.hom.app
        ((rY₀.obj M).obj j)))).mp
  try simp only [Category.assoc]
  let rX₀ := (Functor.whiskeringRight Index.{u} _ _).obj
    (SheafOfModules.restrictScalars.{u}
      ((sheafCompose X.topology (forget₂ CommRingCat RingCat)).map X.a))
  let rY'₀ := (Functor.whiskeringRight Index.{u} _ _).obj
    (SheafOfModules.restrictScalars.{u}
      ((sheafCompose Y'.topology (forget₂ CommRingCat RingCat)).map Y'.a))
  let Mf := ((Functor.whiskeringRight Index.{u} _ _).obj f.S.inverse.modules).obj M
  let Mg := ((Functor.whiskeringRight Index.{u} _ _).obj g.S.inverse.modules).obj M
  have hf := comp_iso_of_eq (f.R.inverse.moduleUnderlying.app ((rY₀.obj M).obj j))
    (eq_of_heq (hbf.1 M j))
  have hg := comp_iso_of_eq (g.R.inverse.moduleUnderlying.app ((rY₀.obj M).obj j))
    (eq_of_heq (hbg.1 M j))
  have hfp := comp_iso_of_eq (fp.R.inverse.moduleUnderlying.app ((rY'₀.obj Mg).obj j))
    (eq_of_heq (hbfp.1 Mg j))
  have hgp := comp_iso_of_eq (gp.R.inverse.moduleUnderlying.app ((rX₀.obj Mf).obj j))
    (eq_of_heq (hbgp.1 Mf j))
  have hn := inverse_underlying_naturality gp.R ((bf.hom.app M).app j)
  change (underlying X'.S).map (s.S.modules.hom.app (M.obj j)) ≫
      (underlying X'.R).map ((bgp.hom.app ((((Functor.whiskeringRight Index.{u} _ _).obj
        f.S.inverse.modules)).obj M)).app j) ≫
      (underlying X'.R).map
        (gp.R.inverse.modules.map ((bf.hom.app M).app j)) ≫
      gp.R.inverse.moduleUnderlying.hom.app
        (f.R.inverse.modules.obj ((rY₀.obj M).obj j)) ≫
      gp.R.morphism.inverse.map
        (f.R.inverse.moduleUnderlying.hom.app ((rY₀.obj M).obj j)) =
    (underlying X'.R).map ((bfp.hom.app ((((Functor.whiskeringRight Index.{u} _ _).obj
      g.S.inverse.modules)).obj M)).app j) ≫
      (underlying X'.R).map
        (fp.R.inverse.modules.map ((bg.hom.app M).app j)) ≫
      (underlying X'.R).map (s.R.modules.hom.app ((rY₀.obj M).obj j)) ≫
      gp.R.inverse.moduleUnderlying.hom.app
        (f.R.inverse.modules.obj ((rY₀.obj M).obj j)) ≫
      gp.R.morphism.inverse.map
        (f.R.inverse.moduleUnderlying.hom.app ((rY₀.obj M).obj j))
  conv_lhs => arg 2; arg 2; erw [reassoc_of% hn]
  conv_lhs => arg 2; erw [reassoc_of% hgp]
  conv_lhs =>
    arg 2; arg 2; arg 2
    rw [← gp.R.morphism.inverse.map_comp]
    erw [hf]
    rw [gp.R.morphism.inverse.map_comp]
  conv_rhs => arg 2; arg 2; erw [s.R.normalized ((rY₀.obj M).obj j)]
  have hn' := inverse_underlying_naturality fp.R ((bg.hom.app M).app j)
  conv_rhs => arg 2; erw [reassoc_of% hn']
  conv_rhs => erw [reassoc_of% hfp]
  conv_rhs =>
    arg 2; arg 2
    rw [← fp.R.morphism.inverse.map_comp_assoc]
    erw [hg]
    rw [fp.R.morphism.inverse.map_comp, Category.assoc]
  conv_lhs =>
    arg 2; arg 2
    erw [reassoc_of% (transport_naturality gp.sameInverse.symm
      (f.S.inverse.moduleUnderlying.hom.app (M.obj j)))]
  conv_lhs => erw [reassoc_of% (s.S.normalized (M.obj j))]
  conv_rhs =>
    arg 2
    erw [reassoc_of% (transport_naturality fp.sameInverse.symm
      (g.S.inverse.moduleUnderlying.hom.app (M.obj j)))]
  exact congrArg (fun k ↦ fp.S.inverse.moduleUnderlying.hom.app _ ≫
    fp.S.morphism.inverse.map (g.S.inverse.moduleUnderlying.hom.app (M.obj j)) ≫ k)
      (geometry_transport f.sameInverse g.sameInverse fp.sameInverse gp.sameInverse
        s.R.geometry s.S.geometry s.sameGeometry ((underlying Y.S).obj (M.obj j)))


private theorem complex_square
    {A B C D AR BR CR DR : Type*}
    [Category A] [Abelian A] [Category AR] [Abelian AR]
    [Category B] [Abelian B] [Category BR] [Abelian BR]
    [Category C] [Abelian C] [Category CR] [Abelian CR]
    [Category D] [Abelian D] [Category DR] [Abelian DR]
    (f : A ⥤ B) (g : A ⥤ C) (fp : C ⥤ D) (gp : B ⥤ D)
    (fR : AR ⥤ BR) (gR : AR ⥤ CR) (fpR : CR ⥤ DR) (gpR : BR ⥤ DR)
    (rA : A ⥤ AR) (rB : B ⥤ BR) (rC : C ⥤ CR) (rD : D ⥤ DR)
    [f.Additive] [g.Additive]
    [fp.Additive] [gp.Additive]
    [fR.Additive] [gR.Additive]
    [fpR.Additive] [gpR.Additive]
    [rA.Additive] [rB.Additive]
    [rC.Additive] [rD.Additive]
    (bf : f ⋙ rB ≅ rA ⋙ fR) (bg : g ⋙ rC ≅ rA ⋙ gR)
    (bfp : fp ⋙ rD ≅ rC ⋙ fpR) (bgp : gp ⋙ rD ≅ rB ⋙ gpR)
    (θ : g ⋙ fp ≅ f ⋙ gp) (θR : gR ⋙ fpR ≅ fR ⋙ gpR)
    (h : ∀ M, rD.map (θ.hom.app M) ≫ bgp.hom.app (f.obj M) ≫
        gpR.map (bf.hom.app M) =
      bfp.hom.app (g.obj M) ≫ fpR.map (bg.hom.app M) ≫ θR.hom.app (rA.obj M)) :
    comparisonSquare (complexComparison bf) (complexComparison bg)
      (complexComparison bfp) (complexComparison bgp)
      (complexComparison θ) (complexComparison θR) := by
  unfold comparisonSquare
  intro P
  unfold complexComparison complexFunctor
  ext n : 1
  change rD.map (θ.hom.app (P.X n)) ≫ bgp.hom.app (f.obj (P.X n)) ≫
      gpR.map (bf.hom.app (P.X n)) =
    bfp.hom.app (g.obj (P.X n)) ≫ fpR.map (bg.hom.app (P.X n)) ≫
      θR.hom.app (rA.obj (P.X n))
  exact h (P.X n)


-- Use the abelian parent consistently in the complex and localization interfaces.
attribute [-instance] diagramPreadditive CategoryTheory.functorCategoryPreadditive in
private theorem derived_square
    (s : Square (f := f) (g := g) (fp := fp) (gp := gp))
    (df : DerivedEdge f fR fS rX rY) (dg : DerivedEdge g gR gS rY' rY)
    (dfp : DerivedEdge fp fpR fpS rX' rY') (dgp : DerivedEdge gp gpR gpS rX' rX)
    (θR : gR.L ⋙ fpR.L ≅ fR.L ⋙ gpR.L)
    (θS : gS.L ⋙ fpS.L ≅ fS.L ⋙ gpS.L)
    (hθ : SquareNormalized s θR θS) :
    ∀ M : DerivedCategory.{w} Y.modulesS,
      rX'.functor.map (θS.hom.app M) ≫ dgp.p.hom.app (fS.L.obj M) ≫
          gpR.L.map (df.p.hom.app M) =
        dfp.p.hom.app (gS.L.obj M) ≫ fpR.L.map (dg.p.hom.app M) ≫
          θR.hom.app (rY.functor.obj M) := by
  let bf := df.normalized.choose
  let df₀ := df.normalized.choose_spec.choose
  have hbf := df.normalized.choose_spec.choose_spec.1
  have hf := df.normalized.choose_spec.choose_spec.2.1
  let bg := dg.normalized.choose
  let dg₀ := dg.normalized.choose_spec.choose
  have hbg := dg.normalized.choose_spec.choose_spec.1
  have hg := dg.normalized.choose_spec.choose_spec.2.1
  let bfp := dfp.normalized.choose
  let dfp₀ := dfp.normalized.choose_spec.choose
  have hbfp := dfp.normalized.choose_spec.choose_spec.1
  have hfp := dfp.normalized.choose_spec.choose_spec.2.1
  let bgp := dgp.normalized.choose
  let dgp₀ := dgp.normalized.choose_spec.choose
  have hbgp := dgp.normalized.choose_spec.choose_spec.1
  have hgp := dgp.normalized.choose_spec.choose_spec.2.1
  apply descend_square
    (A := DerivedCategory.{w} Y.modulesS) (B := DerivedCategory.{w} X.modulesS)
    (C := DerivedCategory.{w} Y'.modulesS) (D := DerivedCategory.{w} X'.modulesS)
    (AR := DerivedCategory.{w} Y.modulesR) (BR := DerivedCategory.{w} X.modulesR)
    (CR := DerivedCategory.{w} Y'.modulesR) (DR := DerivedCategory.{w} X'.modulesR)
    (f := fS.L) (g := gS.L) (fp := fpS.L) (gp := gpS.L)
    (fR := fR.L) (gR := gR.L) (fpR := fpR.L) (gpR := gpR.L)
    (rA := rY.functor) (rB := rX.functor)
    (rC := rY'.functor) (rD := rX'.functor)
    (A₀ := CochainComplex Y.modulesS ℤ) (B₀ := CochainComplex X.modulesS ℤ)
    (C₀ := CochainComplex Y'.modulesS ℤ) (D₀ := CochainComplex X'.modulesS ℤ)
    (AR₀ := CochainComplex Y.modulesR ℤ) (BR₀ := CochainComplex X.modulesR ℤ)
    (CR₀ := CochainComplex Y'.modulesR ℤ) (DR₀ := CochainComplex X'.modulesR ℤ)
    (f₀ := (complexFunctor ((inverseDiagram f.S)))) (g₀ := (complexFunctor ((inverseDiagram g.S))))
    (fp₀ :=
    (complexFunctor ((inverseDiagram fp.S)))) (gp₀ := (complexFunctor ((inverseDiagram gp.S))))
    (fR₀ :=
    (complexFunctor ((inverseDiagram f.R)))) (gR₀ := (complexFunctor ((inverseDiagram g.R))))
    (fpR₀ :=
    (complexFunctor ((inverseDiagram fp.R)))) (gpR₀ := (complexFunctor ((inverseDiagram gp.R))))
    (rA₀ := (complexFunctor Y.restrict)) (rB₀ := (complexFunctor X.restrict))
    (rC₀ := (complexFunctor Y'.restrict)) (rD₀ := (complexFunctor X'.restrict))
    (DerivedCategory.Q.{w} (C := Y.modulesS))
    (HomologicalComplex.quasiIso Y.modulesS (.up ℤ))
    (DerivedCategory.Q.{w} (C := X.modulesS))
    (DerivedCategory.Q.{w} (C := Y'.modulesS)) (DerivedCategory.Q.{w} (C := X'.modulesS))
    (DerivedCategory.Q.{w} (C := Y.modulesR)) (DerivedCategory.Q.{w} (C := X.modulesR))
    (DerivedCategory.Q.{w} (C := Y'.modulesR)) (DerivedCategory.Q.{w} (C := X'.modulesR))
    fS.q gS.q fpS.q gpS.q fR.q gR.q fpR.q gpR.q
    rY.factor rX.factor rY'.factor rX'.factor
    (complexComparison (F := (inverseDiagram f.S))
      (G :=
      X.restrict)
      (H := Y.restrict) (K := (inverseDiagram f.R))
        bf)
        (complexComparison (F := (inverseDiagram g.S)) (G
        := Y'.restrict)
      (H := Y.restrict) (K := (inverseDiagram g.R))
        bg)
    (complexComparison (F := (inverseDiagram fp.S))
      (G :=
      X'.restrict)
      (H := Y'.restrict) (K := (inverseDiagram fp.R))
        bfp) (complexComparison (F := (inverseDiagram gp.S)) (G := X'.restrict)
      (H := X.restrict) (K := (inverseDiagram gp.R)) bgp)
        df.p dg.p dfp.p dgp.p
    hf hg hfp hgp (complexComparison (F := (inverseDiagram g.S)) (G := (inverseDiagram fp.S))
      (H := (inverseDiagram f.S)) (K :=
        (inverseDiagram gp.S)) s.S.diagrams)
        (complexComparison (F := (inverseDiagram g.R)) (G
        := (inverseDiagram fp.R))
      (H := (inverseDiagram f.R)) (K :=
        (inverseDiagram gp.R)) s.R.diagrams)
    θS θR hθ.2 hθ.1 ?_
  exact complex_square
    ((inverseDiagram f.S)) ((inverseDiagram g.S))
    ((inverseDiagram fp.S))
      ((inverseDiagram gp.S))
    ((inverseDiagram f.R)) ((inverseDiagram g.R))
    ((inverseDiagram fp.R))
      ((inverseDiagram gp.R))
    Y.restrict X.restrict Y'.restrict X'.restrict
    bf bg bfp bgp s.S.diagrams s.R.diagrams
    (ordinary_square s bf bg bfp bgp df₀ dg₀ dfp₀ dgp₀ hbf hbg hbfp hbgp)


private theorem edge_counit
    {U V : Corner.{u, w}} {e : EdgeData U V}
    {R : DerivedImage e.R} {S : DerivedImage e.S}
    {rU : U.Restriction} {rV : V.Restriction}
    (d : DerivedEdge e R S rU rV) (N : DerivedCategory.{w} U.modulesS) :
    d.p.hom.app (S.F.obj N) ≫ R.L.map (d.d.hom.app N) ≫
        R.adj.counit.app (rU.functor.obj N) = rU.functor.map (S.adj.counit.app N) := by
  have ha := d.normalized.choose_spec.choose_spec.2.2.2
  exact counit_from_adjunct
    (A := DerivedCategory.{w} V.modulesS) (B := DerivedCategory.{w} U.modulesS)
    (AR := DerivedCategory.{w} V.modulesR) (BR := DerivedCategory.{w} U.modulesR)
    S.adj R.adj d.p d.d ha N

/-- Flat scalar restriction identifies the canonical pullback composition squares,
their exchange mates as natural transformations on actual derived strict towers,
and the explicitly specified counit transpose.

Source: blueprint main-20261015, completed-exchange-coherence proof, second paragraph,
strict coefficient supplement; Stacks 07A7, remark-base-change
(blueprint: lem-weil-pbc-flat-scalar-tower-exchange).

Proof plan:
1. Use the four given edge normalizations. They supply the ordinary comparisons,
their localization equations and the adjunct equation (A) for the fixed p and d.
2. Before localization, apply the faithful underlying-sheaf functor. The four
normalized ordinary edge comparisons and the two normalized square comparisons
reduce the square to naturality and the equality of the shared geometric transports.
Hence the normalized ordinary comparison commutes with the square. Apply it
degreewise and use lem-weil-pbc-localization-universal-property to descend and detect
equality. The normalization equations of SquareNormalized give the first conjunct (C).
3. Apply the edge-f adjunct equation to its S-counit, whose adjunct is the identity.
The inverse Hom formula gives rX(epsilonS) p_f inverse L_f(d_f inverse) = epsilonR (K).
4. By def-weil-pbc-adjunction-mate, E_S transposes to thetaS followed by L_g'(epsilonS).
The edge-f' adjunct equation, and pre/postcomposition naturality of that Hom bijection,
transpose the conjugate b inverse; rY'(E_S); d to the composite (T) in the node.
5. Naturality of p_g' moves it past epsilonS. Substitute (C) and cancel the invertible
comparisons. Expanding b gives p_g b inverse = L_g(d_f inverse), yielding (T').
6. Naturality of thetaR moves d_f inverse to the counit. Equation (K) reduces (T')
to thetaR followed by L_g'(epsilonR), the stated explicit transpose. The adjunction
bijection is injective, giving the mate equality. Compose with b to obtain the second
conjunct. Every constituent is a natural transformation of full derived diagram
functors, proving the natural-transformation equality, with no transition, completeness,
cartesianness, reduction-tower, or boundedness condition on Z. -/
theorem flatScalarTowerExchange
    (s : Square (f := f) (g := g) (fp := fp) (gp := gp))
    (df : DerivedEdge f fR fS rX rY) (dg : DerivedEdge g gR gS rY' rY)
    (dfp : DerivedEdge fp fpR fpS rX' rY') (dgp : DerivedEdge gp gpR gpS rX' rX)
    (θR : gR.L ⋙ fpR.L ≅ fR.L ⋙ gpR.L)
    (θS : gS.L ⋙ fpS.L ≅ fS.L ⋙ gpS.L)
    (hθ : SquareNormalized s θR θS) :
    (∀ M : DerivedCategory Y.modulesS,
      rX'.functor.map (θS.hom.app M) ≫ dgp.p.hom.app (fS.L.obj M) ≫
          gpR.L.map (df.p.hom.app M) =
        dfp.p.hom.app (gS.L.obj M) ≫ fpR.L.map (dg.p.hom.app M) ≫
          θR.hom.app (rY.functor.obj M)) ∧
    (whiskerRight (mateEquiv fS.adj fpS.adj
        (TwoSquare.mk _ _ _ _ θS.hom)).natTrans rY'.functor ≫
          (targetComparison dfp dgp).hom =
      (sourceComparison df dg).hom ≫ whiskerLeft rX.functor
        (mateEquiv fR.adj fpR.adj (TwoSquare.mk _ _ _ _ θR.hom)).natTrans) ∧
    (∀ Z : DerivedCategory X.modulesS,
      (fpR.adj.homEquiv _ _).symm
        ((sourceComparison df dg).inv.app Z ≫
          rY'.functor.map ((mateEquiv fS.adj fpS.adj
            (TwoSquare.mk _ _ _ _ θS.hom)).app Z) ≫
          (targetComparison dfp dgp).hom.app Z) =
        θR.hom.app (fR.F.obj (rX.functor.obj Z)) ≫
          gpR.L.map (fR.adj.counit.app (rX.functor.obj Z))) := by
  have hC := derived_square s df dg dfp dgp θR θS hθ
  refine ⟨hC, ?_⟩
  exact exchange_and_transpose
    (AS := DerivedCategory.{w} Y.modulesS) (BS := DerivedCategory.{w} X.modulesS)
    (CS := DerivedCategory.{w} Y'.modulesS) (DS := DerivedCategory.{w} X'.modulesS)
    (AR := DerivedCategory.{w} Y.modulesR) (BR := DerivedCategory.{w} X.modulesR)
    (CR := DerivedCategory.{w} Y'.modulesR) (DR := DerivedCategory.{w} X'.modulesR)
    fS.adj fpS.adj fR.adj fpR.adj
    df.p dg.p dfp.p dgp.p df.d dfp.d θR θS (edge_counit df) (edge_counit dfp) hC

end FlatScalarTowerExchange
end CategoryTheory
