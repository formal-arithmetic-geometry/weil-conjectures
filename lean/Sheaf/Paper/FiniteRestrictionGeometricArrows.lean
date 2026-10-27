/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.FiniteRestrictionCoefficientGeometry
public import Sheaf.Paper.OrdinaryCompletedIntegralPullback
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction

/-!
# The geometric mate and counit arrows in a finite fibre

Source: Stacks 03D8, 0D6D, 099N; Bhatt--Scholze 6.8.14, 6.8.15
(blueprint: def-zl-finite-restriction-geometric-arrows).

## Main definitions

* `GeometricArrows`: completed geometric adjunctions and pasting comparisons.
* `GeometricArrows.Normalized`: ordinary chain, completion-unit and reconstruction pins.
* `Endpoints.ArrowsNormalized`: equality of the transported strict arrows with these mates.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.CompletedCoefficientPushforward.modAbelian
  WeilConjectures.CompletedCoefficientPushforward.hasDerived
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
namespace WeilConjectures.FiniteRestrictionCoefficient
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Sectionwise ordinary direct image is additive.
Source: Stacks 03D1 (blueprint: def-zl-finite-restriction-geometric-arrows). -/
instance ordinaryPushAdditive {X Y : Scheme.{u}} (g : X ⟶ Y) :
    (ordinaryIntegralModulePush l E g).Additive where
  map_add := by intros; rfl

/-- Ordinary derived adjunction data; the law below fixes the adjunction on cochains.
Source: Stacks 06YY (blueprint: def-zl-finite-restriction-geometric-arrows). -/
structure OrdinaryAdjunction {X Y : Scheme.{u}} (g : X ⟶ Y) where
  push : ordinaryIntegralModulePush l E g ≅ sfCompletedModuleDirectImage l E g
  adj : ordinaryIntegralDerivedPull l E g ⊣ sfCompletedDerivedDirectImage l E g

attribute [local irreducible] HasDerivedCategory.standard ordinaryIntegralDerivedPull
  ordinaryIntegralModulePull
  integralDerivedPullback ordinaryIntegralPullComplexCounit
  ordinaryIntegralCompletionComparison
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

set_option backward.isDefEq.respectTransparency false in
/-- Identity on direct-image sections and the universal cochain adjunct equation.
The equation is imposed on all cochain maps, including resolving representatives.
Source: Stacks 06YY (blueprint: def-zl-finite-restriction-geometric-arrows). -/
def OrdinaryAdjunction.Normalized {X Y : Scheme.{u}} {g : X ⟶ Y}
    (D : OrdinaryAdjunction l E g) : Prop :=
  (∀ (M : integralTowerModules l E X) (U : Y.ProEtᵒᵖ)
    (m : M.val.obj ((proEtaleBaseChange g).op.obj U)),
    (D.push.hom.app M).val.app U m = m) ∧
  (∀ (P : CochainComplex (integralTowerModules l E Y) ℤ)
    (Q : CochainComplex (integralTowerModules l E X) ℤ)
    (a : (ordinaryIntegralPullComplex l E g).obj P ⟶ Q),
    D.adj.homEquiv (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)
      (ordinaryIntegralPullComplexCounit l E g P ≫ DerivedCategory.Q.map a) =
      DerivedCategory.Q.map
        (((ordinaryIntegralModuleAdjunction l E g).mapHomologicalComplex (.up ℤ)).homEquiv
          P Q a ≫ (NatIso.mapHomologicalComplex D.push (.up ℤ)).hom.app Q) ≫
        (sfCompletedModuleDirectImage l E g).rightDerivedFunctorUnitQ Q)

variable {V W Z : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V)

set_option genSizeOf false in
set_option genInjectivity false in
/-- Ordinary pasting with its derived realization retained.
Source: Stacks 03D8, 0D6D (blueprint: def-zl-finite-restriction-geometric-arrows). -/
structure OrdinaryComposition where
  direct : ordinaryIntegralModulePush l E h ⋙ ordinaryIntegralModulePush l E k ≅
    ordinaryIntegralModulePush l E (h ≫ k)
  derived : ordinaryIntegralDerivedPull l E (h ≫ k) ≅
    ordinaryIntegralDerivedPull l E k ⋙ ordinaryIntegralDerivedPull l E h

/-- The ordinary inverse-image compositor is the conjugate of direct-image pasting.
Source: Stacks 03D8 (blueprint: def-zl-finite-restriction-geometric-arrows). -/
def OrdinaryComposition.pull (D : OrdinaryComposition l E h k) :
    ordinaryIntegralModulePull l E (h ≫ k) ≅
      ordinaryIntegralModulePull l E k ⋙ ordinaryIntegralModulePull l E h :=
  (conjugateIsoEquiv
    ((ordinaryIntegralModuleAdjunction l E k).comp (ordinaryIntegralModuleAdjunction l E h))
    (ordinaryIntegralModuleAdjunction l E (h ≫ k))).symm D.direct

/-- The actual ordinary compositor on cochain complexes.
Source: Stacks 0D6D (blueprint: def-zl-finite-restriction-geometric-arrows). -/
def OrdinaryComposition.complex (D : OrdinaryComposition l E h k) :
    ordinaryIntegralPullComplex l E (h ≫ k) ≅
      ordinaryIntegralPullComplex l E k ⋙ ordinaryIntegralPullComplex l E h :=
  NatIso.mapHomologicalComplex (D.pull l E h k) (.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso (Iso.refl _) (.up ℤ)).symm

set_option backward.isDefEq.respectTransparency false in
/-- Pasting restricts sections along the actual fibre-product isomorphism. Derived
pasting is fixed on every flat-term K-flat complex by the universal pullback counits.
Source: Stacks 03D8, 0D6D (blueprint: def-zl-finite-restriction-geometric-arrows). -/
def OrdinaryComposition.Normalized (D : OrdinaryComposition l E h k) : Prop :=
  (∀ (M : integralTowerModules l E Z) (U : V.ProEt)
    (m : ((ordinaryIntegralModulePush l E h ⋙ ordinaryIntegralModulePush l E k).obj M).val.obj
      (op U)),
    (D.direct.hom.app M).val.app (op U) m =
      M.val.map
        ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) h k).hom.app U).op m) ∧
  (∀ P : (integralOperationsGoodComplex l E V).FullSubcategory,
    D.derived.hom.app (DerivedCategory.Q.obj P.obj) ≫
        (ordinaryIntegralDerivedPull l E h).map (ordinaryIntegralPullComplexCounit l E k P.obj) ≫
        ordinaryIntegralPullComplexCounit l E h ((ordinaryIntegralPullComplex l E k).obj P.obj) =
      ordinaryIntegralPullComplexCounit l E (h ≫ k) P.obj ≫
        DerivedCategory.Q.map ((D.complex l E h k).hom.app P.obj))

/-- Ordinary identity comparisons retain the section and derived normalizations.
Source: Stacks 03D8, 0D6D (blueprint: def-zl-finite-restriction-geometric-arrows). -/
structure OrdinaryIdentity (T : Scheme.{u}) where
  direct : ordinaryIntegralModulePush l E (𝟙 T) ≅ 𝟭 _
  derived : ordinaryIntegralDerivedPull l E (𝟙 T) ≅ 𝟭 _

/-- The identity pullback is the inverse of the conjugated direct-image identity.
Source: Stacks 03D8 (blueprint: def-zl-finite-restriction-geometric-arrows). -/
def OrdinaryIdentity.pull {T : Scheme.{u}} (D : OrdinaryIdentity l E T) :
    ordinaryIntegralModulePull l E (𝟙 T) ≅ 𝟭 _ :=
  ((conjugateIsoEquiv (ordinaryIntegralModuleAdjunction l E (𝟙 T))
    (Adjunction.id : (𝟭 (integralTowerModules l E T)) ⊣ 𝟭 _)).symm D.direct).symm

set_option backward.isDefEq.respectTransparency false in
/-- Identity normalization on sections and all good cochain representatives.
Source: Stacks 03D8, 0D6D (blueprint: def-zl-finite-restriction-geometric-arrows). -/
def OrdinaryIdentity.Normalized {T : Scheme.{u}} (D : OrdinaryIdentity l E T) : Prop :=
  (∀ (M : integralTowerModules l E T) (U : T.ProEt)
    (m : ((ordinaryIntegralModulePush l E (𝟙 T)).obj M).val.obj (op U)),
    (D.direct.hom.app M).val.app (op U) m =
      M.val.map ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ T).inv.app U).op m) ∧
  (∀ P : (integralOperationsGoodComplex l E T).FullSubcategory,
    D.derived.hom.app (DerivedCategory.Q.obj P.obj) =
      ordinaryIntegralPullComplexCounit l E (𝟙 T) P.obj ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex D.pull (.up ℤ) ≪≫
          Functor.mapHomologicalComplexIdIso _ (.up ℤ)).hom.app P.obj))

open AlgebraicallyClosedCoefficients (Index Coefficient)
variable (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  {s X Y : Scheme.{u}} (f : X ⟶ Y) (y : s ⟶ Y)

set_option genSizeOf false in
set_option genInjectivity false in
/-- Geometric adjunctions and compositors. Their law predicate below fixes every
comparison by ordinary pasting, completion units and the retained reconstruction.
Source: Stacks 099N (blueprint: def-zl-finite-restriction-geometric-arrows). -/
structure GeometricArrows (G : Geometry l Ω f y) where
  fPull : PullbackDiagram l Ω f
  ordinaryF : ∀ A : Index l Ω, OrdinaryAdjunction l (Coefficient.{u} l Ω A) f
  ordinaryH : ∀ A : Index l Ω, OrdinaryAdjunction l (Coefficient.{u} l Ω A) (pullback.snd f y)
  adjF : ∀ A : Index l Ω, fPull.functor A ⊣ (G.image.integral A).image
  adjH : ∀ A : Index l Ω,
    G.structurePull.integral.functor A ⊣ (G.fibreImage.integral A).image
  yh : ∀ A : Index l Ω,
    OrdinaryComposition l (Coefficient.{u} l Ω A) (pullback.snd f y) y
  fv : ∀ A : Index l Ω,
    OrdinaryComposition l (Coefficient.{u} l Ω A) (pullback.fst f y) f
  hi : ∀ (A : Index l Ω) (x : FiniteCounitTowers.Points f y),
    OrdinaryComposition l (Coefficient.{u} l Ω A) (FiniteCounitTowers.lift f y x) (pullback.snd f y)
  vi : ∀ (A : Index l Ω) (x : FiniteCounitTowers.Points f y),
    OrdinaryComposition l (Coefficient.{u} l Ω A) (FiniteCounitTowers.lift f y x) (pullback.fst f y)
  identity : ∀ A : Index l Ω, OrdinaryIdentity l (Coefficient.{u} l Ω A) s
  square : ∀ A : Index l Ω,
    G.pointPull.integral.functor A ⋙ G.structurePull.integral.functor A ≅
      fPull.functor A ⋙ G.fibrePull.integral.functor A
  pointH : ∀ (A : Index l Ω) (x : FiniteCounitTowers.Points f y),
    G.structurePull.integral.functor A ⋙ (G.liftPull x).integral.functor A ≅ 𝟭 _
  pointV : ∀ (A : Index l Ω) (x : FiniteCounitTowers.Points f y),
    G.fibrePull.integral.functor A ⋙ (G.liftPull x).integral.functor A ≅
      (G.pointComponent x).integral.functor A

attribute [local irreducible] IntegralDiagram.functor
  sfIntegralConstructible sfConstructibleIntegralScalarExtension

/-- The completed adjunction unit is the actual ordinary derived unit followed by
completion and the normalized reconstruction into the strict direct-image model.
Source: Stacks 099N (blueprint: def-zl-finite-restriction-geometric-arrows). -/
def CompletedAdjunctionNormalized {Z V : Scheme.{u}} (g : Z ⟶ V) (A : Index l Ω)
    (O : OrdinaryAdjunction l (Coefficient.{u} l Ω A) g)
    (P : PullbackDiagram l Ω g)
    (M : SfStrictDirectImageScalar.IntegralModel l (Coefficient.{u} l Ω A) g)
    (a : P.functor A ⊣ M.image) : Prop :=
  ∀ K : IntegralStage l Ω V A,
    (a.unit.app K).hom = O.adj.unit.app K.obj ≫
      (sfCompletedDerivedDirectImage l (Coefficient.{u} l Ω A) g).map
        ((ordinaryIntegralCompletionComparison l (Coefficient.{u} l Ω A) g).app K.obj) ≫
      M.reconstruction.hom.app ((P.functor A).obj K)

/-- Completion of the ordinary square, with its exact pasting and units.
Source: Stacks 099N (blueprint: def-zl-finite-restriction-geometric-arrows). -/
def GeometricArrows.SquareNormalized {G : Geometry l Ω f y} (D : GeometricArrows l Ω f y G) :
    Prop :=
  ∀ (A : Index l Ω) (K : IntegralStage l Ω Y A),
    (ordinaryIntegralDerivedPull l (Coefficient.{u} l Ω A) (pullback.snd f y)).map
        ((ordinaryIntegralCompletionComparison l (Coefficient.{u} l Ω A) y).app K.obj) ≫
      (ordinaryIntegralCompletionComparison l (Coefficient.{u} l Ω A) (pullback.snd f y)).app
        (((G.pointPull.integral.functor A).obj K).obj) ≫
      ((D.square A).hom.app K).hom =
    (D.yh A).derived.inv.app K.obj ≫
      eqToHom (congrArg (fun g ↦ (ordinaryIntegralDerivedPull l (Coefficient.{u} l Ω A) g).obj
        K.obj) (pullback.condition (f := f) (g := y)).symm) ≫
      (D.fv A).derived.hom.app K.obj ≫
      (ordinaryIntegralDerivedPull l (Coefficient.{u} l Ω A) (pullback.fst f y)).map
        ((ordinaryIntegralCompletionComparison l (Coefficient.{u} l Ω A) f).app K.obj) ≫
      (ordinaryIntegralCompletionComparison l (Coefficient.{u} l Ω A) (pullback.fst f y)).app
        (((D.fPull.functor A).obj K).obj)

/-- Completion-unit normalization of the two point compositors, including identity.
Source: Stacks 099N (blueprint: def-zl-finite-restriction-geometric-arrows). -/
def GeometricArrows.PointNormalized {G : Geometry l Ω f y} (D : GeometricArrows l Ω f y G) :
    Prop :=
  (∀ (A : Index l Ω) (x : FiniteCounitTowers.Points f y) (K : IntegralStage l Ω s A),
    (ordinaryIntegralDerivedPull l (Coefficient.{u} l Ω A) (FiniteCounitTowers.lift f y x)).map
        ((ordinaryIntegralCompletionComparison l (Coefficient.{u} l Ω A) (pullback.snd f y)).app
          K.obj) ≫
      (ordinaryIntegralCompletionComparison l (Coefficient.{u} l Ω A)
        (FiniteCounitTowers.lift f y x)).app
          (((G.structurePull.integral.functor A).obj K).obj) ≫
      ((D.pointH A x).hom.app K).hom =
    (D.hi A x).derived.inv.app K.obj ≫
      eqToHom (congrArg (fun g ↦ (ordinaryIntegralDerivedPull l (Coefficient.{u} l Ω A) g).obj
        K.obj) (pullback.lift_snd x.val (𝟙 s)
          (x.property.trans (Category.id_comp y).symm))) ≫
      (D.identity A).derived.hom.app K.obj) ∧
  (∀ (A : Index l Ω) (x : FiniteCounitTowers.Points f y) (K : IntegralStage l Ω X A),
    (ordinaryIntegralDerivedPull l (Coefficient.{u} l Ω A) (FiniteCounitTowers.lift f y x)).map
        ((ordinaryIntegralCompletionComparison l (Coefficient.{u} l Ω A) (pullback.fst f y)).app
          K.obj) ≫
      (ordinaryIntegralCompletionComparison l (Coefficient.{u} l Ω A)
        (FiniteCounitTowers.lift f y x)).app
          (((G.fibrePull.integral.functor A).obj K).obj) ≫
      ((D.pointV A x).hom.app K).hom =
    (D.vi A x).derived.inv.app K.obj ≫
      eqToHom (congrArg (fun g ↦ (ordinaryIntegralDerivedPull l (Coefficient.{u} l Ω A) g).obj
        K.obj) (pullback.lift_fst x.val (𝟙 s)
          (x.property.trans (Category.id_comp y).symm))) ≫
      (ordinaryIntegralCompletionComparison l (Coefficient.{u} l Ω A) x.val).app K.obj)

/-- All normalizations precede the geometric mate construction. In particular no
scalar square is used to choose a sign for a geometric comparison.
Source: Stacks 099N (blueprint: def-zl-finite-restriction-geometric-arrows). -/
def GeometricArrows.Normalized {G : Geometry l Ω f y} (D : GeometricArrows l Ω f y G) : Prop :=
  (∀ A : Index l Ω, (D.ordinaryF A).Normalized ∧ (D.ordinaryH A).Normalized ∧
    (D.yh A).Normalized l _ _ _ ∧ (D.fv A).Normalized l _ _ _ ∧
    (D.identity A).Normalized l _) ∧
  (∀ (A : Index l Ω) (x : FiniteCounitTowers.Points f y),
    (D.hi A x).Normalized l _ _ _ ∧ (D.vi A x).Normalized l _ _ _) ∧
  (∀ A : Index l Ω,
    CompletedAdjunctionNormalized l Ω f A (D.ordinaryF A) D.fPull
      (G.image.integral A) (D.adjF A) ∧
    CompletedAdjunctionNormalized l Ω (pullback.snd f y) A (D.ordinaryH A)
      G.structurePull.integral (G.fibreImage.integral A) (D.adjH A)) ∧
  D.SquareNormalized l Ω f y ∧ D.PointNormalized l Ω f y

/-- The exchange on the geometric composites is the actual completed counit mate.
Source: Stacks 0959, 099N (blueprint: def-zl-finite-restriction-geometric-arrows). -/
def GeometricArrows.exchange {G : Geometry l Ω f y} (D : GeometricArrows l Ω f y G)
    (A : Index l Ω) :
    (G.image.integral A).image ⋙ G.pointPull.integral.functor A ⟶
      G.fibrePull.integral.functor A ⋙ (G.fibreImage.integral A).image :=
  (mateEquiv (D.adjF A) (D.adjH A) (TwoSquare.mk _ _ _ _ (D.square A).hom)).natTrans

/-- Each geometric point component pulls back the actual h-counit and uses the
normalized h i=id and v i=x compositors.
Source: Stacks 03QP, 099N (blueprint: def-zl-finite-restriction-geometric-arrows). -/
def GeometricArrows.component {G : Geometry l Ω f y} (D : GeometricArrows l Ω f y G)
    (A : Index l Ω) (x : FiniteCounitTowers.Points f y) :
    G.fibrePull.integral.functor A ⋙ (G.fibreImage.integral A).image ⟶
      (G.pointComponent x).integral.functor A :=
  Functor.whiskerLeft (G.fibrePull.integral.functor A)
    ((Functor.rightUnitor _).inv ≫
      Functor.whiskerLeft ((G.fibreImage.integral A).image) (D.pointH A x).inv ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (D.adjH A).counit ((G.liftPull x).integral.functor A) ≫
      (Functor.leftUnitor _).hom) ≫
    (D.pointV A x).hom

/-- The transported strict-system arrows equal the geometrically normalized mate
and counit components. These equalities forbid the simultaneous middle/projection
sign change that scalar compatibility alone leaves undetected.
Source: Stacks 0959, 03QP (blueprint: def-zl-finite-restriction-geometric-arrows). -/
def Endpoints.ArrowsNormalized {G : Geometry l Ω f y} {I : IntegralComparisons l f y Ω}
    (N : Endpoints l Ω f y G I) (D : GeometricArrows l Ω f y G) : Prop :=
  (∀ (A : Index l Ω) (K : IntegralStage l Ω X A),
    (N.source A).inv.app K ≫ (I.diagram A).exchange.app K ≫
      (N.middle A).hom.app K = (D.exchange l Ω f y A).app K) ∧
  (∀ (A : Index l Ω) (x : FiniteCounitTowers.Points f y) (K : IntegralStage l Ω X A),
    (N.middle A).inv.app K ≫ (I.diagram A).restriction.app K ≫
      (N.projection A x).app K = (D.component l Ω f y A x).app K)

end WeilConjectures.FiniteRestrictionCoefficient
