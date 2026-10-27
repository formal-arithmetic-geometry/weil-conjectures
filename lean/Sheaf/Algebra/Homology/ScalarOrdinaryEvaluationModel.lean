/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q78
-/
module

public import Sheaf.Algebra.Homology.ScalarInternalHomData
public import Sheaf.Algebra.Homology.StrictScalarHomChain
import all Sheaf.Algebra.Homology.StrictScalarHomChain
import all Sheaf.Algebra.Homology.ScalarHomTensorCoherence
import all Sheaf.Algebra.Homology.RingedDerivedTensorHomAdjunction

/-! # Flat scalar evaluation on an arbitrary first complex

Source: Stacks Project, sites-cohomology.tex, Tags 07A4, 08J9 and 06YP;
the one-K-flat-factor scalar evaluation refinement recorded in the DAG, rather
than a verbatim assertion of these tags
(blueprint: lem-sfb-ordinary-scalar-evaluation-model).

All tensors, Hom products, sections and localization functors below are the
recorded constructions. The data asserted to exist are fixed by generator
formulas and the K-flat normalization; no representative is chosen arbitrarily.
-/

@[expose] public noncomputable section
set_option autoImplicit false
-- Avoid re-synthesizing the site-universe instances in the section-variable linter.
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward false
universe c v r w
open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules WeilConjectures

attribute [local irreducible] CategoryTheory.Preadditive.preadditiveHasZeroMorphisms

attribute [local irreducible] derivedInternalHomOfUniverses
  CoefficientClosedStructure.tensor
  Functor.mapHomologicalComplexUpToQuasiIso Functor.mapHomologicalComplexUpToQuasiIsoFactors

attribute [local irreducible] homComplex homComplexπ
  RingedDerivedNative.chainEquiv

attribute [local irreducible] coefficientTotalTensor coefficientTensorGenerator
  scalarPairComplexComparison CoefficientTensorModels.iso
  SheafOfModules.monoidalCategory homComplexFunctor


namespace CategoryTheory.ScalarOrdinaryEvaluation

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})]
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]


/-- Ordinary scalar evaluation interface. Source: Stacks 07A4 and 08J9
(blueprint: lem-sfb-ordinary-scalar-evaluation-model). -/
structure Scalars where
  E : ∀ {R S : Sheaf J CommRingCat.{max c v r}} (_a : R ⟶ S),
    scalarModules J R ⥤ scalarModules J S
  additive : ∀ {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S), (E a).Additive
  obj_eq : ∀ {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S) X,
    (E a).obj X = changeOfRings a X
  map_eq : ∀ {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S)
    {X Y : scalarModules J R} (f : X ⟶ Y), (E a).map f =
      eqToHom (obj_eq a X) ≫ changeOfRingsHom a X f ≫ eqToHom (obj_eq a Y).symm
  adj : ∀ {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S),
    E a ⊣ scalarRestriction a
  unit_pure : ∀ {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S)
    (X : scalarModules J R) (V : Cᵒᵖ) (x : X.val.obj V),
    (eqToHom (obj_eq a X)).val.app V (((adj a).unit.app X).val.app V x) =
      scalarExtensionSection a X V 1 x

attribute [local instance] Scalars.additive

/-- Ordinary scalar evaluation interface. Source: Stacks 07A4 and 08J9
(blueprint: lem-sfb-ordinary-scalar-evaluation-model). -/
abbrev extension (O : Scalars.{c, v, r} (J := J))
    {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S) :=
  scalarComplex (O.E a) (O.additive a)

/-- Ordinary scalar evaluation interface. Source: Stacks 07A4 and 08J9
(blueprint: lem-sfb-ordinary-scalar-evaluation-model). -/
def unitSection (O : Scalars.{c, v, r} (J := J))
    {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S)
    (X : scalarModules J R) (V : Cᵒᵖ) (x : X.val.obj V) :
    ((O.E a).obj X).val.obj V :=
  ((O.adj a).unit.app X).val.app V x

/-- Ordinary scalar evaluation interface. Source: Stacks 07A4 and 08J9
(blueprint: lem-sfb-ordinary-scalar-evaluation-model). -/
def extensionSection (O : Scalars.{c, v, r} (J := J))
    {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S)
    (D : StrictScalarHom.Complex.{c, v, r} R) (n : ℤ) (V : Cᵒᵖ)
    (s : S.obj.obj V) (x : (D.X n).val.obj V) :
    (((extension O a).obj D).X n).val.obj V :=
  s • unitSection O a (D.X n) V x

/-- Ordinary scalar evaluation interface. Source: Stacks 07A4 and 08J9
(blueprint: lem-sfb-ordinary-scalar-evaluation-model). -/
def chainAdj (O : Scalars.{c, v, r} (J := J))
    {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S) :
    extension O a ⊣ StrictScalarHom.restriction.{c, v, r} a :=
  (O.adj a).mapHomologicalComplex (.up ℤ)


/-- Ordinary scalar evaluation interface. Source: Stacks 07A4 and 08J9
(blueprint: lem-sfb-ordinary-scalar-evaluation-model). -/
structure Tensor (O : Scalars.{c, v, r} (J := J))
    {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S) where
  complexIso : ∀ (D P : StrictScalarHom.Complex.{c, v, r} R),
    (extension O a).obj ((coefficientTotalTensor.{r, c, v} J R).obj (D, P)) ≅
      (coefficientTotalTensor.{r, c, v} J S).obj
        ((extension O a).obj D, (extension O a).obj P)
  generators : ∀ (D P : StrictScalarHom.Complex.{c, v, r} R)
    (n i k : ℤ) (h : n + i = k) (V : Cᵒᵖ)
    (x : (D.X n).val.obj V) (p : (P.X i).val.obj V),
    (((complexIso D P).hom.f k).val.app V)
      (unitSection O a _ V (coefficientTensorGenerator.{r, c, v} J R D P n i k h V x p)) =
    coefficientTensorGenerator.{r, c, v} J S
      ((extension O a).obj D) ((extension O a).obj P) n i k h V
      (unitSection O a _ V x) (unitSection O a _ V p)

/-- Ordinary scalar evaluation interface. Source: Stacks 07A4 and 08J9
(blueprint: lem-sfb-ordinary-scalar-evaluation-model). -/
structure Presentation (O : Scalars.{c, v, r} (J := J)) where
  chainData : ∀ {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S),
    StrictScalarHom.Data.{c, v, r} a
  chainIso : ∀ {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S),
    (chainData a).extension.complex ≅ extension O a
  chainIso_pure : ∀ {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S)
    (D : StrictScalarHom.Complex.{c, v, r} R) (n : ℤ) (V : Cᵒᵖ)
    (s : S.obj.obj V) (x : (D.X n).val.obj V),
    ((((chainIso a).hom.app D).f n).val.app V)
      ((chainData a).extension.section D n V s x) = extensionSection O a D n V s x

/-- Ordinary scalar evaluation interface. Source: Stacks 07A4 and 08J9
(blueprint: lem-sfb-ordinary-scalar-evaluation-model). -/
structure Evaluation (O : Scalars.{c, v, r} (J := J)) where
  scalarEvaluate : ∀ {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S)
    (P I D : StrictScalarHom.Complex.{c, v, r} R) (_b : D ⟶ homComplex (R := R) P I),
    (coefficientTotalTensor.{r, c, v} J R).obj
      ((StrictScalarHom.tensor.{c, v, r} a).obj D, P) ⟶
      (StrictScalarHom.restriction.{c, v, r} a).obj ((extension O a).obj I)
  scalarEvaluate_pure : ∀ {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S)
    (P I D : StrictScalarHom.Complex.{c, v, r} R) (b : D ⟶ homComplex (R := R) P I)
    (n i k : ℤ) (h : n + i = k) (h' : i + n = k) (V : Cᵒᵖ)
    (s : S.obj.obj V) (x : (D.X n).val.obj V) (p : (P.X i).val.obj V),
    ((scalarEvaluate a P I D b).f k).val.app V
      (coefficientTensorGenerator.{r, c, v} J R
        ((StrictScalarHom.tensor.{c, v, r} a).obj D) P n i k h V
        (StrictScalarHom.tensorSection.{c, v, r} a D n V s x) p) =
      extensionSection O a I k V s
        (StrictScalarHom.evaluate.{c, v, r} P I n i k h' V ((b.f n).val.app V x) p)

variable (O : Scalars.{c, v, r} (J := J))
  (μ : ∀ {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S), Tensor O a)



/-- Ordinary scalar evaluation interface. Source: Stacks 07A4 and 08J9
(blueprint: lem-sfb-ordinary-scalar-evaluation-model). -/
def Nu (O : Scalars.{c, v, r} (J := J)) :=
  ∀ {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S),
    StrictScalarHom.tensor.{c, v, r} a ≅
      extension.{c, v, r} (J := J) O a ⋙ StrictScalarHom.restriction.{c, v, r} a

/-- The recorded representative clause `nu_pure`. 
Ordinary scalar evaluation interface. Source: Stacks 07A4 and 08J9
(blueprint: lem-sfb-ordinary-scalar-evaluation-model). -/
def NuPure (O : Scalars.{c, v, r} (J := J)) (nu : Nu.{c, v, r} (J := J) O) : Prop :=
  ∀ {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S)
    (D : StrictScalarHom.Complex.{c, v, r} R) (n : ℤ) (V : Cᵒᵖ)
    (s : S.obj.obj V) (x : (D.X n).val.obj V),
    (((nu a).hom.app D).f n).val.app V
      (StrictScalarHom.tensorSection.{c, v, r} a D n V s x) =
        extensionSection.{c, v, r} (J := J) O a D n V s x


/-- Ordinary scalar evaluation interface. Source: Stacks 07A4 and 08J9
(blueprint: lem-sfb-ordinary-scalar-evaluation-model). -/
def Evaluate :=
  ∀ {R : Sheaf J CommRingCat.{max c v r}} (P I D : StrictScalarHom.Complex.{c, v, r} R)
    (_b : D ⟶ homComplex (R := R) P I),
    (coefficientTotalTensor.{r, c, v} J R).obj (D, P) ⟶ I

/-- The recorded representative clause `evaluate_pure`. 
Ordinary scalar evaluation interface. Source: Stacks 07A4 and 08J9
(blueprint: lem-sfb-ordinary-scalar-evaluation-model). -/
def EvaluatePure (evaluate : Evaluate.{c, v, r} (J := J)) : Prop :=
  ∀ {R : Sheaf J CommRingCat.{max c v r}}
    (P I D : StrictScalarHom.Complex.{c, v, r} R)
    (b : D ⟶ homComplex (R := R) P I) (n i k : ℤ) (h : n + i = k) (h' : i + n = k)
    (V : Cᵒᵖ) (x : (D.X n).val.obj V) (p : (P.X i).val.obj V),
    ((evaluate P I D b).f k).val.app V
      (coefficientTensorGenerator.{r, c, v} J R D P n i k h V x p) =
        StrictScalarHom.evaluate.{c, v, r} P I n i k h' V ((b.f n).val.app V x) p

/-- The recorded representative clause `scalarEvaluate`. 
Ordinary scalar evaluation interface. Source: Stacks 07A4 and 08J9
(blueprint: lem-sfb-ordinary-scalar-evaluation-model). -/
def Scalarevaluate (O : Scalars.{c, v, r} (J := J)) :=
  ∀ {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S)
    (P I D : StrictScalarHom.Complex.{c, v, r} R) (_b : D ⟶ homComplex (R := R) P I),
    (coefficientTotalTensor.{r, c, v} J R).obj
      ((StrictScalarHom.tensor.{c, v, r} a).obj D, P) ⟶
        (StrictScalarHom.restriction.{c, v, r} a).obj ((extension.{c, v, r} (J := J) O a).obj I)

/-- The recorded representative clause `scalarEvaluate_pure`. 
Ordinary scalar evaluation interface. Source: Stacks 07A4 and 08J9
(blueprint: lem-sfb-ordinary-scalar-evaluation-model). -/
def ScalarevaluatePure (O : Scalars.{c, v, r} (J := J)) (scalarEvaluate : Scalarevaluate.{c, v, r}
  (J := J) O) : Prop :=
  ∀ {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S)
    (P I D : StrictScalarHom.Complex.{c, v, r} R) (b : D ⟶ homComplex (R := R) P I)
    (n i k : ℤ) (h : n + i = k) (h' : i + n = k) (V : Cᵒᵖ)
    (s : S.obj.obj V) (x : (D.X n).val.obj V) (p : (P.X i).val.obj V),
    ((scalarEvaluate a P I D b).f k).val.app V
      (coefficientTensorGenerator.{r, c, v} J R
        ((StrictScalarHom.tensor.{c, v, r} a).obj D) P n i k h V
        (StrictScalarHom.tensorSection.{c, v, r} a D n V s x) p) =
      extensionSection.{c, v, r} (J := J) O a I k V s
        (StrictScalarHom.evaluate.{c, v, r} P I n i k h' V ((b.f n).val.app V x) p)

/-- The recorded representative clause `chainUnitTensor`. 
Ordinary scalar evaluation interface. Source: Stacks 07A4 and 08J9
(blueprint: lem-sfb-ordinary-scalar-evaluation-model). -/
def Chainunittensor (O : Scalars.{c, v, r} (J := J)) :=
  ∀ {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S)
    (V P : StrictScalarHom.Complex.{c, v, r} R),
    (coefficientTotalTensor.{r, c, v} J R).obj
      ((StrictScalarHom.restriction.{c, v, r} a).obj ((extension.{c, v, r} (J := J) O a).obj V),
        P) ⟶
    (StrictScalarHom.restriction.{c, v, r} a).obj
      ((coefficientTotalTensor.{r, c, v} J S).obj
        ((extension.{c, v, r} (J := J) O a).obj V, (extension.{c, v, r} (J := J) O a).obj P))

/-- The recorded representative clause `chainUnitTensor_pure`. 
Ordinary scalar evaluation interface. Source: Stacks 07A4 and 08J9
(blueprint: lem-sfb-ordinary-scalar-evaluation-model). -/
def ChainunittensorPure (O : Scalars.{c, v, r} (J := J)) (chainUnitTensor : Chainunittensor.{c, v,
  r} (J := J) O) : Prop :=
  ∀ {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S)
    (D P : StrictScalarHom.Complex.{c, v, r} R) (n i k : ℤ) (h : n + i = k) (V : Cᵒᵖ)
    (y : (((extension.{c, v, r} (J := J) O a).obj D).X n).val.obj V) (p : (P.X i).val.obj V),
    ((chainUnitTensor a D P).f k).val.app V
      (coefficientTensorGenerator.{r, c, v} J R
        ((StrictScalarHom.restriction.{c, v, r} a).obj ((extension.{c, v, r} (J := J) O a).obj D)) P
        n i k h V y p) =
      coefficientTensorGenerator.{r, c, v} J S ((extension.{c, v, r} (J := J) O a).obj D)
        ((extension.{c, v, r} (J := J) O a).obj P) n i k h V y (extensionSection.{c, v, r} (J :=
          J) O a P i V 1 p)




private structure OrdinaryScalarExtension
    {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S) where
  functor : scalarModules J R ⥤ scalarModules J S
  additive : functor.Additive
  obj_eq : ∀ X, functor.obj X = changeOfRings a X
  map_eq : ∀ {X Y} (f : X ⟶ Y), functor.map f =
    eqToHom (obj_eq X) ≫ changeOfRingsHom a X f ≫ eqToHom (obj_eq Y).symm
  unit : 𝟭 (scalarModules J R) ⟶ functor ⋙ scalarRestriction a
  unit_pure : ∀ (X : scalarModules J R) (V : Cᵒᵖ) (x : X.val.obj V),
    (eqToHom (obj_eq X)).val.app V ((unit.app X).val.app V x) =
      scalarExtensionSection a X V 1 x

private def ordinarySection {R S : Sheaf J CommRingCat.{max c v r}}
    (a : R ⟶ S) (O : OrdinaryScalarExtension.{c, v, r} (J := J) a) (X : scalarModules J R)
    (V : Cᵒᵖ) (x : X.val.obj V) : (O.functor.obj X).val.obj V :=
  (O.unit.app X).val.app V x

@[no_expose] private def ordinaryModel (O : Scalars.{c, v, r} (J := J)) {R S : Sheaf J
  CommRingCat.{max c v r}}
    (a : R ⟶ S) : OrdinaryScalarExtension.{c, v, r} (J := J) a where
  functor := (O.E a)
  additive := (O.additive a)
  obj_eq := (O.obj_eq a)
  map_eq := (O.map_eq a)
  unit := (O.adj a).unit
  unit_pure := (O.unit_pure a)

@[no_expose] private def ordinaryBridge
    {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S) (O : OrdinaryScalarExtension.{c, v, r} (J
      := J) a)
    (D : StrictScalarHom.Data.{c, v, r} a) :
    D.extension.functor ≅ O.functor :=
  NatIso.ofComponents (fun X ↦
    eqToIso ((D.extension.obj_eq X).trans (O.obj_eq X).symm)) (by
      intro X Y f
      dsimp only [eqToIso, Functor.comp_map]
      rw [D.extension.map_eq, O.map_eq]
      simp only [eqToHom_trans, Category.assoc, eqToHom_trans_assoc]
      rfl)

attribute [local instance] OrdinaryScalarExtension.additive

@[no_expose] private def bridge
    {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S) (O : OrdinaryScalarExtension.{c, v, r} (J
      := J) a)
    (D : StrictScalarHom.Data.{c, v, r} a) :
    D.extension.complex ≅ scalarComplex O.functor O.additive :=
  NatIso.mapHomologicalComplex (ordinaryBridge.{c, v, r} a O D) (.up ℤ)

private theorem bridge_pure
    {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S) (O : OrdinaryScalarExtension.{c, v, r} (J
      := J) a)
    (G : StrictScalarHom.Data.{c, v, r} a)
    (D : StrictScalarHom.Complex.{c, v, r} R) (n : ℤ) (V : Cᵒᵖ)
    (s : S.obj.obj V) (x : (D.X n).val.obj V) :
    ((((bridge.{c, v, r} a O G).hom.app D).f n).val.app V)
      (G.extension.section D n V s x) =
        s • ordinarySection.{c, v, r} a O (D.X n) V x := by
  have hu := O.unit_pure (D.X n) V x
  have hu' : (eqToHom (O.obj_eq (D.X n))).val.app V
      (ordinarySection.{c, v, r} a O (D.X n) V x) =
        scalarExtensionSection a (D.X n) V 1 x := by
    exact hu
  have hs := congrArg
    (fun z ↦ (eqToHom (O.obj_eq (D.X n)).symm).val.app V (s • z)) hu'
  simp only [← map_smul, ← ModuleCat.comp_apply, ← PresheafOfModules.comp_app,
    ← SheafOfModules.comp_val, eqToHom_trans, eqToHom_refl,
    SheafOfModules.id_val, PresheafOfModules.id_app, ModuleCat.id_apply] at hs
  have hsm := scalarExtensionSection_smul a (D.X n) V s 1 x
  rw [mul_one] at hsm
  rw [hsm] at hs
  dsimp only [bridge, NatIso.mapHomologicalComplex_hom_app_f, ordinaryBridge,
    NatIso.ofComponents_hom_app, StrictScalarHom.Extension.section]
  change ((eqToHom (G.extension.obj_eq (D.X n)).symm ≫
      eqToHom ((G.extension.obj_eq (D.X n)).trans
        (O.obj_eq (D.X n)).symm)).val.app V)
      (scalarExtensionSection a (D.X n) V s x) = _
  rw [eqToHom_trans]
  exact hs.symm


attribute [local irreducible] bridge ordinaryBridge StrictScalarHom.canonicalData

@[no_expose] private def chainBridge (O : Scalars.{c, v, r} (J := J))
    {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S) :
    (StrictScalarHom.canonicalData.{c, v, r} a).extension.complex ≅ extension.{c, v, r} (J := J) O
      a :=
  bridge.{c, v, r} a (ordinaryModel.{c, v, r} (J := J) O a) (StrictScalarHom.canonicalData.{c, v,
    r} a)

attribute [local irreducible] chainBridge

private theorem chainBridge_pure (O : Scalars.{c, v, r} (J := J)) {R S : Sheaf J CommRingCat.{max
  c v r}} (a : R ⟶ S)
    (D : StrictScalarHom.Complex.{c, v, r} R) (n : ℤ) (V : Cᵒᵖ)
    (s : S.obj.obj V) (x : (D.X n).val.obj V) :
    ((((chainBridge.{c, v, r} (J := J) O a).hom.app D).f n).val.app V)
      ((StrictScalarHom.canonicalData.{c, v, r} a).extension.section D n V s x) =
        extensionSection.{c, v, r} (J := J) O a D n V s x := by
  unfold chainBridge
  exact bridge_pure.{c, v, r} a (ordinaryModel.{c, v, r} (J := J) O a) _ D n V s x

@[no_expose] private def chainPresentation (O : Scalars.{c, v, r} (J := J)) : Presentation.{c, v,
  r} (J := J) O where
  chainData := fun a ↦ StrictScalarHom.canonicalData.{c, v, r} a
  chainIso := chainBridge.{c, v, r} (J := J) O
  chainIso_pure := chainBridge_pure.{c, v, r} (J := J) O

@[no_expose] private def normalizedNu (O : Scalars.{c, v, r} (J := J)) : Nu.{c, v, r} (J := J) O
  := by
  intro R S a
  exact
  (StrictScalarHom.canonicalData.{c, v, r} a).nu ≪≫
    Functor.isoWhiskerRight (chainBridge.{c, v, r} (J := J) O a) (StrictScalarHom.restriction.{c,
      v, r} a)

attribute [local irreducible] normalizedNu

private theorem normalizedNu_pure (O : Scalars.{c, v, r} (J := J)) : NuPure.{c, v, r} (J := J) O
  (normalizedNu.{c, v, r} (J := J) O) := by
  intro R S a D n V s x
  unfold normalizedNu
  change (((chainBridge.{c, v, r} (J := J) O a).hom.app D).f n).val.app V
    (((((StrictScalarHom.canonicalData.{c, v, r} a).nu).hom.app D).f n).val.app V
      (StrictScalarHom.tensorSection.{c, v, r} a D n V s x)) = _
  exact (congrArg (fun y ↦ (((chainBridge.{c, v, r} (J := J) O a).hom.app D).f n).val.app V y)
    ((StrictScalarHom.canonicalData.{c, v, r} a).nu_pure D n V s x)).trans
      (chainBridge_pure.{c, v, r} (J := J) O a D n V s x)

@[no_expose] private def chainEvaluation : Evaluate.{c, v, r} (J := J) := by
  intro R P I D b
  let (R : Sheaf J CommRingCat.{max c v r}) :
      HasDerivedCategory (scalarModules J R) := HasDerivedCategory.standard _
  exact
  (RingedDerivedNative.chainEquiv.{c, v, r} J R D P I).symm b

attribute [local irreducible] chainEvaluation

private theorem chainEvaluation_pure : EvaluatePure.{c, v, r} (J := J) (chainEvaluation.{c, v, r}
  (J := J)) := by
  intro R P I D b n i k h h' V x p
  let (R : Sheaf J CommRingCat.{max c v r}) :
      HasDerivedCategory (scalarModules J R) := HasDerivedCategory.standard _
  unfold chainEvaluation
  exact RingedDerivedNative.chainEquiv_symm_pure.{c, v, r} J R D P I b n i k h h' V x p

@[no_expose] private def chainUnit (O : Scalars.{c, v, r} (J := J))
    (μ : ∀ {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S), Tensor O a) : Chainunittensor.{c,
      v, r} (J := J) O := by
  intro R S a D P
  exact
  (chainAdj.{c, v, r} (J := J) O a).unit.app _ ≫
    (StrictScalarHom.restriction.{c, v, r} a).map
      (((μ a).complexIso _ P).hom ≫
        (coefficientTotalTensor.{r, c, v} J S).map
          (Prod.mkHom ((chainAdj.{c, v, r} (J := J) O a).counit.app ((extension.{c, v, r} (J := J)
            O a).obj D))
            (𝟙 ((extension.{c, v, r} (J := J) O a).obj P))))

attribute [local irreducible] chainUnit

private theorem chainUnit_pure (O : Scalars.{c, v, r} (J := J))
    (μ : ∀ {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S), Tensor O a) :
      ChainunittensorPure.{c, v, r} (J := J) O (chainUnit.{c, v, r} (J := J) O μ) := by
  intro R S a D P n i k h V y p
  unfold chainUnit
  have ht := (chainAdj.{c, v, r} (J := J) O a).right_triangle_components
    ((extension.{c, v, r} (J := J) O a).obj D)
  have ht' := congrArg (fun f ↦ (f.f n).val.app V y) ht
  change (((chainAdj.{c, v, r} (J := J) O a).counit.app ((extension.{c, v, r} (J := J) O a).obj
    D)).f n).val.app V
    (unitSection.{c, v, r} (J := J) O a _ V y) = y at ht'
  change (((coefficientTotalTensor.{r, c, v} J S).map
      (Prod.mkHom ((chainAdj.{c, v, r} (J := J) O a).counit.app ((extension.{c, v, r} (J := J) O
        a).obj D))
        (𝟙 ((extension.{c, v, r} (J := J) O a).obj P)))).f k).val.app V
    ((((μ a).complexIso _ P).hom.f k).val.app V
      (unitSection.{c, v, r} (J := J) O a _ V
        (coefficientTensorGenerator.{r, c, v} J R
          ((StrictScalarHom.restriction.{c, v, r} a).obj ((extension.{c, v, r} (J := J) O a).obj
            D)) P
          n i k h V y p))) = _
  erw [(μ a).generators, ScalarHomTensor.tensor_generator_map, ht']
  simp only [HomologicalComplex.id_f, SheafOfModules.id_val, PresheafOfModules.id_app,
    ModuleCat.id_apply, extensionSection, one_smul]
  rfl

private theorem extensionSection_map (O : Scalars.{c, v, r} (J := J)) {R S : Sheaf J
  CommRingCat.{max c v r}}
    (a : R ⟶ S) {D I : StrictScalarHom.Complex.{c, v, r} R} (f : D ⟶ I)
    (n : ℤ) (V : Cᵒᵖ) (s : S.obj.obj V) (x : (D.X n).val.obj V) :
    (((extension.{c, v, r} (J := J) O a).map f).f n).val.app V (extensionSection.{c, v, r} (J :=
      J) O a D n V s x) =
      extensionSection.{c, v, r} (J := J) O a I n V s ((f.f n).val.app V x) := by
  have hn := congrArg (fun z ↦ z.val.app V x)
    ((O.adj a).unit.naturality (f.f n)).symm
  change (((extension.{c, v, r} (J := J) O a).map f).f n).val.app V
    (unitSection.{c, v, r} (J := J) O a (D.X n) V x) =
      unitSection.{c, v, r} (J := J) O a (I.X n) V ((f.f n).val.app V x) at hn
  change (((extension.{c, v, r} (J := J) O a).map f).f n).val.app V
    (s • unitSection.{c, v, r} (J := J) O a (D.X n) V x) = _
  rw [map_smul, hn]
  rfl

private theorem generator_smul_left {R : Sheaf J CommRingCat.{max c v r}}
    (D P : StrictScalarHom.Complex.{c, v, r} R) (n i k : ℤ) (h : n + i = k)
    (V : Cᵒᵖ) (s : R.obj.obj V) (x : (D.X n).val.obj V) (p : (P.X i).val.obj V) :
    coefficientTensorGenerator.{r, c, v} J R D P n i k h V (s • x) p =
      s • coefficientTensorGenerator.{r, c, v} J R D P n i k h V x p := by
  delta coefficientTotalTensor coefficientTensorGenerator
  simp only [← TensorProduct.smul_tmul', _root_.map_smul]

private theorem tensorComparison_inv_pure (O : Scalars.{c, v, r} (J := J))
    (μ : ∀ {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S), Tensor O a) {R S : Sheaf J
      CommRingCat.{max c v r}}
    (a : R ⟶ S) (D P : StrictScalarHom.Complex.{c, v, r} R)
    (n i k : ℤ) (h : n + i = k) (V : Cᵒᵖ)
    (s : S.obj.obj V) (x : (D.X n).val.obj V) (p : (P.X i).val.obj V) :
    (((μ a).complexIso D P).inv.f k).val.app V
      (coefficientTensorGenerator.{r, c, v} J S ((extension.{c, v, r} (J := J) O a).obj D)
        ((extension.{c, v, r} (J := J) O a).obj P) n i k h V
        (extensionSection.{c, v, r} (J := J) O a D n V s x) (extensionSection.{c, v, r} (J := J) O
          a P i V 1 p)) =
      extensionSection.{c, v, r} (J := J) O a ((coefficientTotalTensor.{r, c, v} J R).obj (D, P))
        k V s
        (coefficientTensorGenerator.{r, c, v} J R D P n i k h V x p) := by
  have he := congrArg (fun f ↦ (f.f k).val.app V
    (unitSection.{c, v, r} (J := J) O a _ V
      (coefficientTensorGenerator.{r, c, v} J R D P n i k h V x p)))
    ((μ a).complexIso D P).hom_inv_id
  change (((μ a).complexIso D P).inv.f k).val.app V
    ((((μ a).complexIso D P).hom.f k).val.app V
      (unitSection.{c, v, r} (J := J) O a _ V
        (coefficientTensorGenerator.{r, c, v} J R D P n i k h V x p))) = _ at he
  rw [(μ a).generators] at he
  simp only [HomologicalComplex.id_f, SheafOfModules.id_val, PresheafOfModules.id_app,
    ModuleCat.id_apply] at he
  simp only [extensionSection, one_smul]
  erw [generator_smul_left, _root_.map_smul]
  exact congrArg (fun z ↦ s • z) he


@[no_expose] private def scalarChainEvaluation (O : Scalars.{c, v, r} (J := J))
    (μ : ∀ {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S), Tensor O a) : Scalarevaluate.{c,
      v, r} (J := J) O := by
  intro R S a P I D b
  exact
  (coefficientTotalTensor.{r, c, v} J R).map
      (Prod.mkHom ((normalizedNu.{c, v, r} (J := J) O a).hom.app D) (𝟙 P)) ≫
    chainUnit.{c, v, r} (J := J) O μ a D P ≫
    (StrictScalarHom.restriction.{c, v, r} a).map ((μ a).complexIso D P).inv ≫
    (StrictScalarHom.restriction.{c, v, r} a).map
      ((extension.{c, v, r} (J := J) O a).map (chainEvaluation P I D b))

attribute [local irreducible] scalarChainEvaluation

private theorem scalarChainEvaluation_pure (O : Scalars.{c, v, r} (J := J))
    (μ : ∀ {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S), Tensor O a) :
      ScalarevaluatePure.{c, v, r} (J := J) O (scalarChainEvaluation.{c, v, r} (J := J) O μ) := by
  intro R S a P I D b n i k h h' V s x p
  unfold scalarChainEvaluation
  change (((extension.{c, v, r} (J := J) O a).map (chainEvaluation P I D b)).f k).val.app V
    ((((μ a).complexIso D P).inv.f k).val.app V
      (((chainUnit.{c, v, r} (J := J) O μ a D P).f k).val.app V
        ((((coefficientTotalTensor.{r, c, v} J R).map
          (Prod.mkHom ((normalizedNu.{c, v, r} (J := J) O a).hom.app D) (𝟙 P))).f k).val.app V
          (coefficientTensorGenerator.{r, c, v} J R _ P n i k h V
            (StrictScalarHom.tensorSection.{c, v, r} a D n V s x) p)))) = _
  erw [ScalarHomTensor.tensor_generator_map, normalizedNu_pure]
  simp only [HomologicalComplex.id_f, SheafOfModules.id_val, PresheafOfModules.id_app,
    ModuleCat.id_apply]
  erw [chainUnit_pure, tensorComparison_inv_pure, extensionSection_map,
    chainEvaluation_pure P I D b n i k h h']



/-- Normalized chain evaluation data, independent of any derived-category choice.
Source: Stacks 07A4 and 08J9
(blueprint: lem-sfb-ordinary-scalar-evaluation-model). -/
structure RepresentativeData (O : Scalars.{c, v, r} (J := J)) where
  nu : Nu.{c, v, r} (J := J) O
  nu_pure : NuPure.{c, v, r} (J := J) O nu
  evaluate : Evaluate.{c, v, r} (J := J)
  evaluate_pure : EvaluatePure.{c, v, r} (J := J) evaluate
  scalarEvaluate : Scalarevaluate.{c, v, r} (J := J) O
  scalarEvaluate_pure : ScalarevaluatePure.{c, v, r} (J := J) O scalarEvaluate
  chainUnitTensor : Chainunittensor.{c, v, r} (J := J) O
  chainUnitTensor_pure : ChainunittensorPure.{c, v, r} (J := J) O chainUnitTensor
/-- The ordinary chain representatives with a strict coefficient presentation.
Source: Stacks 07A4 and 08J9 (blueprint: lem-sfb-ordinary-scalar-evaluation-model). -/
structure Construction (O : Scalars.{c, v, r} (J := J))
    extends RepresentativeData.{c, v, r} (J := J) O where
  presentation : Presentation.{c, v, r} (J := J) O
  coefficientSquares : ∀ {R S R' S' : Sheaf J CommRingCat.{max c v r}}
    (φ : R ⟶ S) (a : R ⟶ R') (d : S ⟶ S') (φ' : R' ⟶ S')
    (_h : φ ≫ d = a ≫ φ'),
    ∃ Q : StrictScalarHom.CoefficientSquare (presentation.chainData φ)
      (presentation.chainData a) (presentation.chainData d) (presentation.chainData φ'),
      StrictScalarHom.CoefficientCompatibility Q

/-- Ordinary scalar evaluation and its scalar-unit tensor map on arbitrary complexes.
Source: Stacks Project, sites-cohomology.tex, Tags 07A4 and 08J9;
ordinary chain calculation in steps 2--4 of flat scalar evaluation
(blueprint: lem-sfb-ordinary-scalar-evaluation-model).

Proof: compare each normalized ordinary extension with the canonical strict
extension by its object and map equations. Map this comparison to complexes;
the specified unit identifies its generator formula. Compose the strict nu with
this comparison. Chain tensor-Hom transposition constructs evaluation. The
ordinary scalar adjunction and the tensor comparison construct the chain-unit
map; its formula follows from the triangle identity. Compose nu, the chain-unit
map, inverse tensor comparison, and extended evaluation. On tensor generators
the intermediate factors cancel and give s tensor b(x)(p). The resulting maps
and formulas require neither derived categories nor flatness of any input. -/
theorem construction_exists
    (μ : ∀ {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S), Tensor.{c, v, r} (J := J) O a) :
      Nonempty (Construction.{c, v, r} (J := J) O) := by
  exact ⟨{
    nu := normalizedNu.{c, v, r} (J := J) O
    nu_pure := normalizedNu_pure.{c, v, r} (J := J) O
    evaluate := chainEvaluation.{c, v, r} (J := J)
    evaluate_pure := chainEvaluation_pure.{c, v, r} (J := J)
    scalarEvaluate := scalarChainEvaluation.{c, v, r} (J := J) O μ
    scalarEvaluate_pure := scalarChainEvaluation_pure.{c, v, r} (J := J) O μ
    chainUnitTensor := chainUnit.{c, v, r} (J := J) O μ
    chainUnitTensor_pure := chainUnit_pure.{c, v, r} (J := J) O μ
    presentation := chainPresentation.{c, v, r} (J := J) O
    coefficientSquares := by
      intro R S R' S' φ a d φ' h
      let Q := StrictScalarHom.canonicalSquare.{c, v, r} h
      refine ⟨Q, ?_⟩
      exact StrictScalarHom.coefficientCompatibility_generic.{c, v, r}
        (StrictScalarHom.canonicalData.{c, v, r} φ)
        (StrictScalarHom.canonicalData.{c, v, r} a)
        (StrictScalarHom.canonicalData.{c, v, r} d)
        (StrictScalarHom.canonicalData.{c, v, r} φ') Q }⟩

end CategoryTheory.ScalarOrdinaryEvaluation
