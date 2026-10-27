# WeilConjectures.ZlDiagramStage and the finite Weil-diagram interface

## Reason

Separate the existing data from its theorem so that new proof-step modules can import
its types without creating an import cycle. This is a dependency-layout change, with
all existing declaration signatures and definition bodies preserved verbatim.
The source module publicly re-exports the new data module.

## Old

The following declarations lived in Sheaf.Paper.ClassicalFiniteWeilDiagramRealization.
Their complete original signatures and bodies follow verbatim.

```lean
/-- A typed multiplicative word in the arrows, Weil maps, inverses and Frobenius.
An endpoint `(i,n)` denotes the actual n-fold pullback of vertex i.
Source: the finite-word clause of the node, Weil II (1.1.1)b--d
(blueprint: lem-zl-classical-finite-weil-diagram-realization). -/
inductive ZlWeilWord (I : Type v) (A : Type w) (s t : A → I) :
    I × ℕ → I × ℕ → Type (max v w)
  | id (x : I × ℕ) : ZlWeilWord I A s t x x
  | arrow (a : A) : ZlWeilWord I A s t (s a, 0) (t a, 0)
  | weil (i : I) : ZlWeilWord I A s t (i, 1) (i, 0)
  | inverse (i : I) : ZlWeilWord I A s t (i, 0) (i, 1)
  | comp {x y z : I × ℕ} :
      ZlWeilWord I A s t x y → ZlWeilWord I A s t y z → ZlWeilWord I A s t x z
  | pull {x y : I × ℕ} : ZlWeilWord I A s t x y →
      ZlWeilWord I A s t (x.1, x.2 + 1) (y.1, y.2 + 1)

/-- The literal iterated pullback object, including its zeroth iterate.
Source: the node's Frobenius-word convention
(blueprint: lem-zl-classical-finite-weil-diagram-realization). -/
def zlWordObject {C : Type c} [Category.{h} C] (F : C ⥤ C)
    {I : Type v} (M : I → IsoAlgebra F) (i : I) : ℕ → C
  | 0 => (M i).carrier
  | n + 1 => F.obj (zlWordObject F M i n)

/-- Interpret a word using actual functorial pullback and both maps of each Weil iso.
Source: Weil II (1.1.1)b--d; node proof steps 2, 7--8
(blueprint: lem-zl-classical-finite-weil-diagram-realization). -/
def ZlWeilWord.eval {I : Type v} {A : Type w} {s t : A → I}
    {C : Type c} [Category.{h} C] (F : C ⥤ C) (M : I → IsoAlgebra F)
    (a : ∀ j : A, M (s j) ⟶ M (t j)) :
    ∀ {x y : I × ℕ}, ZlWeilWord I A s t x y →
      (zlWordObject F M x.1 x.2 ⟶ zlWordObject F M y.1 y.2)
  | _, _, .id _ => 𝟙 _
  | _, _, .arrow j => (IsoAlgebra.forget F).map (a j)
  | _, _, .weil i => (M i).str.hom
  | _, _, .inverse i => (M i).str.inv
  | _, _, .comp f g => f.eval F M a ≫ g.eval F M a
  | _, _, .pull f => F.map (f.eval F M a)

/-- A finite additive word, with zero represented by the empty list.
Source: the node's finite additive composite clause, distributed into signed words
(blueprint: lem-zl-classical-finite-weil-diagram-realization). -/
abbrev ZlWeilExpression {I : Type v} {A : Type w} (s t : A → I) (x y : I × ℕ) :=
  List (ℤ × ZlWeilWord I A s t x y)

/-- Evaluate an additive expression after a specified additive realization.
This also avoids imposing a second additive structure on the classical localization.
Source: normalized Hom formula in BS 6.8.4(4), 6.8.14(2)
(blueprint: lem-zl-classical-finite-weil-diagram-realization). -/
def zlExpressionValue {I : Type v} {A : Type w} {s t : A → I}
    {C : Type c} [Category.{h} C] {B : Type b} [Category B]
    [∀ X Y : B, AddCommGroup (X ⟶ Y)] (F : C ⥤ C) (M : I → IsoAlgebra F)
    (a : ∀ j : A, M (s j) ⟶ M (t j)) (T : C ⥤ B)
    {x y : I × ℕ} (e : ZlWeilExpression s t x y) :
    T.obj (zlWordObject F M x.1 x.2) ⟶ T.obj (zlWordObject F M y.1 y.2) :=
  (e.map (fun b ↦ b.1 • T.map (b.2.eval F M a))).sum

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type (u + 1)) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
  [IsSeparated Y₀.hom]

-- This inherited unit fact supplies existing interfaces without adding a hypothesis.
/-- The derived stalk-unit fact, with no extra geometric assumption.
Source: the finite-field coefficient convention
(blueprint: lem-zl-classical-finite-weil-diagram-realization). -/
abbrev zlDiagramUnits : Fact (∀ x : (D.geometricFiber Y₀).left,
    IsUnit (l : (D.geometricFiber Y₀).left.presheaf.stalk x)) :=
  ⟨fun x ↦ @isUnit_of_invertible _ _ _ (zlClassicalStalkInvertible D l hl Y₀ x)⟩

variable [Fact (∀ x : (D.geometricFiber Y₀).left,
  IsUnit (l : (D.geometricFiber Y₀).left.presheaf.stalk x))]

/-- A displayed witness of the finite-stage pinning in ZlClassicalPullbackStage.
Unlike a bare existence proposition, this retains the very systems used by the diagram.
The unit fields and final equality are the defining squares of the recorded datum.
R is fixed, but these finite witnesses may be chosen: their realization and Along data
can be normalized to one Family without changing the finite functor or R's pinning.
Source: BS 6.8.4(1),(4), 6.8.15; node proof steps 4--6
(blueprint: lem-zl-classical-finite-weil-diagram-realization). -/
structure ZlDiagramStage (R : ZlClassicalRealization D l hl Ω Y₀)
    (E : Padic.FiniteCoefficientFields l Ω)
    extends ZlClassicalPullbackModels D l hl Ω Y₀ E where
  finite_pullback : finite ⋙ LisseRealization.pull D l hl (Coefficient.{u} l Ω E)
      (X := zlRealizationBase D l hl Y₀) (Y := zlRealizationBase D l hl Y₀)
      (D.geometricFrobenius Y₀).hom ≅ operation.raw ⋙ finite
  ordinary_unit : ∀ (F : AlgebraicGeometry.ProEtale.CompletedLisse.RawRational l
      (zlCompletedBase D l Ω Y₀ E)) (U : (D.geometricFiber Y₀).left.ProEt)
    (s : ((realization.sheaf D l hl (Coefficient.{u} l Ω E)).obj
      (finite.obj F)).val.obj (op U)),
    ((sheaf.hom.app (operation.raw.obj F)).hom.app
        (op ((proEtaleBaseChange (D.geometricFrobenius Y₀).hom).obj U)))
      (((realization.sheaf D l hl (Coefficient.{u} l Ω E)).map
          (finite_pullback.hom.app F)).val.app
        (op ((proEtaleBaseChange (D.geometricFrobenius Y₀).hom).obj U))
        (((along.comparison (finite.obj F) (lisse F)).inv).val.app
          (op ((proEtaleBaseChange (D.geometricFrobenius Y₀).hom).obj U))
          (ContinuousRational.moduleUnit (D.geometricFrobenius Y₀).hom
            (LisseRealization.coefficientPull l (Coefficient.{u} l Ω E)
              (D.geometricFrobenius Y₀).hom)
            ((realization.sheaf D l hl (Coefficient.{u} l Ω E)).obj (finite.obj F)) U s))) =
    (operation.rational.hom.app F).hom.val.app
      (op ((proEtaleBaseChange (D.geometricFrobenius Y₀).hom).obj U))
      ((operation.modules.rationalUnit l (completed.rationalRealization.obj F)).hom.app
        (op U) ((sheaf.hom.app F).hom.app (op U) s))
  classical_objects : ∀ F,
    lisseAlgebraicOfModel l (D.geometricFiber Y₀).left Ω E (operation.raw.obj F).obj =
      (lisseAlgebraicAutomorphismPullback (D.geometricFrobenius Y₀) l Ω).obj
        (lisseAlgebraicOfModel l (D.geometricFiber Y₀).left Ω E F.obj)
  finite_unit : ∀ F (m : ℕ),
    HEq (operation.etale.unit l ⟨F.obj.integral, F.property⟩ m ≫
      (Etale.lowerStar AddCommGrpCat.{u + 1} (D.geometricFrobenius Y₀).hom).map
        ((sheafCompose _ (forget₂ (ModuleCat.{u + 1}
          (Padic.coefficientExtensionIntegers l E.val)) AddCommGrpCat)).map
            (((operation.rawIntegral F).inv).hom.app (op m))))
      (zlClassicalFiniteUnit D l Ω Y₀ E (F.obj.integral.obj.obj (op m)))
  stage : zlClassicalModel D l Ω Y₀ E ⋙ R.functor ≅
    finite ⋙ GeneralAlgebraicallyClosedCoefficients.inclusion E
  stage_pullback_objects : ∀ K,
    (sfCommonStageWeilFrobeniusPullback D l hl Y₀ Ω).obj
        ((GeneralAlgebraicallyClosedCoefficients.inclusion E).obj K) =
      (GeneralAlgebraicallyClosedCoefficients.inclusion E).obj
        ((LisseRealization.pull D l hl (Coefficient.{u} l Ω E)
          (X := zlRealizationBase D l hl Y₀) (Y := zlRealizationBase D l hl Y₀)
          (D.geometricFrobenius Y₀).hom).obj K)
  pinning : ∀ F,
    R.pullback.hom.app (lisseAlgebraicOfModel l (D.geometricFiber Y₀).left Ω E F.obj) =
      (sfCommonStageWeilFrobeniusPullback D l hl Y₀ Ω).map (stage.hom.app F) ≫
        eqToHom (stage_pullback_objects (finite.obj F)) ≫
        (GeneralAlgebraicallyClosedCoefficients.inclusion E).map
          (finite_pullback.hom.app F) ≫
        stage.inv.app (operation.raw.obj F) ≫ R.functor.map (eqToHom (classical_objects F))
  classical : zlClassicalModel D l Ω Y₀ E ⋙
      lisseAlgebraicAutomorphismPullback (D.geometricFrobenius Y₀) l Ω ≅
    operation.raw ⋙ zlClassicalModel D l Ω Y₀ E
  classical_values : ∀ F, classical.hom.app F = eqToHom (classical_objects F).symm
  finite_fullyFaithful : finite.FullyFaithful
  finite_add : ∀ (F G : AlgebraicGeometry.ProEtale.CompletedLisse.RawRational l
      (zlCompletedBase D l Ω Y₀ E)) (f g : F ⟶ G),
    finite.map ⟨f.hom + g.hom⟩ = finite.map f + finite.map g

/-- The finite rational Weil models, on the actual normalized free-system category.
Source: Weil II (1.1.1)c); BS 6.8.4(4)
(blueprint: lem-zl-classical-finite-weil-diagram-realization). -/
abbrev ZlDiagramStage.Weil {R : ZlClassicalRealization D l hl Ω Y₀}
    {E : Padic.FiniteCoefficientFields l Ω} (P : ZlDiagramStage D l hl Ω Y₀ R E) :=
  IsoAlgebra P.operation.raw

/-- Include both Weil maps of a finite model into the classical algebraic category.
Source: Weil II (1.1.1)d); node proof steps 2 and 7
(blueprint: lem-zl-classical-finite-weil-diagram-realization). -/
def ZlDiagramStage.classicalWeil {R : ZlClassicalRealization D l hl Ω Y₀}
    {E : Padic.FiniteCoefficientFields l Ω} (P : ZlDiagramStage D l hl Ω Y₀ R E) :
    P.Weil D l hl Ω Y₀ ⥤ ZlClassicalWeil D l Ω Y₀ :=
  IsoAlgebra.mapOfNatIso P.classical

/-- The finite heart Weil model, whose pullback uses the pinned finite comparison.
Source: BS 6.8.14(2), 6.8.15; node proof step 7
(blueprint: lem-zl-classical-finite-weil-diagram-realization). -/
def ZlDiagramStage.heartWeil {R : ZlClassicalRealization D l hl Ω Y₀}
    {E : Padic.FiniteCoefficientFields l Ω} (P : ZlDiagramStage D l hl Ω Y₀ R E) :
    P.Weil D l hl Ω Y₀ ⥤ sfWeilSheaf D l hl Y₀ (Coefficient.{u} l Ω E) :=
  ObjectProperty.lift _ (IsoAlgebra.mapOfNatIso P.finite_pullback)
    (fun F ↦ (P.lisse F.carrier).1)

/-- The ordinary-module Weil isomorphism of a lisse finite heart object. The inverse
of the normalized pullback comparison fixes its source, so it uses the actual unit.
Source: BS 6.8.14(2), 6.8.15; node proof steps 7 and 9
(blueprint: lem-zl-classical-finite-weil-diagram-realization). -/
def zlDiagramModuleWeil {R : ZlClassicalRealization D l hl Ω Y₀}
    {E : Padic.FiniteCoefficientFields l Ω} (P : ZlDiagramStage D l hl Ω Y₀ R E)
    (K : sfWeilComplex D l hl Y₀ (Coefficient.{u} l Ω E))
    (hK : LisseRealization.Lisse D l hl (Coefficient.{u} l Ω E)
      (zlRealizationBase D l hl Y₀) K.carrier) :
    (LisseRealization.ordinaryPull l (Coefficient.{u} l Ω E)
        (D.geometricFrobenius Y₀).hom).obj
      ((P.realization.sheaf D l hl (Coefficient.{u} l Ω E)).obj K.carrier) ≅
      (P.realization.sheaf D l hl (Coefficient.{u} l Ω E)).obj K.carrier :=
  (P.along.comparison K.carrier hK).symm ≪≫
    (P.realization.sheaf D l hl (Coefficient.{u} l Ω E)).mapIso K.str

/-- A prescribed module identification lifts uniquely, with its finite representative
and its common-stage arrow fixed. The finite stage is universally quantified, so an
identification appearing only after a coefficient enlargement is included. The target
heart object is arbitrary; its displayed finite representative need not be classical.
Source: BS 6.8.14(2), 6.8.15; node proof step 9
(blueprint: lem-zl-classical-finite-weil-diagram-realization). -/
def ZlPrescribedWeilLifts (R : ZlClassicalRealization D l hl Ω Y₀)
    (M : ZlClassicalWeil D l Ω Y₀) : Prop :=
  ∀ (E : Padic.FiniteCoefficientFields l Ω) (P : ZlDiagramStage D l hl Ω Y₀ R E)
    (N : P.Weil D l hl Ω Y₀) (β : (P.classicalWeil D l hl Ω Y₀).obj N ≅ M)
    (H : sfWeilSheaf D l hl Y₀ (Coefficient.{u} l Ω E))
    (hH : LisseRealization.Lisse D l hl (Coefficient.{u} l Ω E)
      (zlRealizationBase D l hl Y₀) H.obj.carrier)
    (K : sfCommonStageWeilSheaf D l hl Y₀ Ω)
    (η : sfWeilStageObject D l hl Y₀ Ω E H.obj ≅ K.obj)
    (ξ : (P.realization.sheaf D l hl (Coefficient.{u} l Ω E)).obj
        (P.finite.obj N.carrier) ≅
      (P.realization.sheaf D l hl (Coefficient.{u} l Ω E)).obj H.obj.carrier),
    (LisseRealization.ordinaryPull l (Coefficient.{u} l Ω E)
        (D.geometricFrobenius Y₀).hom).map ξ.hom ≫
      (zlDiagramModuleWeil D l hl Ω Y₀ P H.obj hH).hom =
    (zlDiagramModuleWeil D l hl Ω Y₀ P
      ((P.heartWeil D l hl Ω Y₀).obj N).obj (P.lisse N.carrier)).hom ≫ ξ.hom →
    ∃! B : (R.weil D l hl Ω Y₀).obj M ≅ K,
      ∃ ψ : (P.heartWeil D l hl Ω Y₀).obj N ≅ H,
        ((ObjectProperty.ι _ ⋙ sfWeilForget D l hl Y₀ (Coefficient.{u} l Ω E)) ⋙
          P.realization.sheaf D l hl (Coefficient.{u} l Ω E)).mapIso ψ = ξ ∧
        (sfCommonStageWeilForget D l hl Y₀ Ω).map B.hom.hom =
          R.functor.map ((IsoAlgebra.forget
            (lisseAlgebraicAutomorphismPullback (D.geometricFrobenius Y₀) l Ω)).map β.inv) ≫
          P.stage.hom.app N.carrier ≫
          (GeneralAlgebraicallyClosedCoefficients.inclusion E).map
            ((sfWeilForget D l hl Y₀ (Coefficient.{u} l Ω E)).map ψ.hom.hom) ≫
          (sfCommonStageWeilForget D l hl Y₀ Ω).map η.hom

/-- Coherence under finite coefficient extension is expressed by the recorded normalized
realization family, including its identity, composition and mixed pullback equations.
Its finite realizations are exactly those used by the diagram stage witnesses.
The stage witnesses are chosen existentially for the given R; no equality between
R itself and a separately chosen global realization is required.
Source: BS 6.8.15; node proof step 8
(blueprint: lem-zl-classical-finite-weil-diagram-realization). -/
def ZlDiagramCoefficientCoherence (R : ZlClassicalRealization D l hl Ω Y₀)
    (P : ∀ E : Padic.FiniteCoefficientFields l Ω, ZlDiagramStage D l hl Ω Y₀ R E) : Prop :=
  ∃ a : LisseRealization.Family D l hl,
    (∀ E : Padic.FiniteCoefficientFields l Ω,
      (P E).realization = a.realization (Coefficient.{u} l Ω E)
        (zlRealizationBase D l hl Y₀)) ∧
    (∀ E : Padic.FiniteCoefficientFields l Ω,
      HEq (P E).along (a.along (Coefficient.{u} l Ω E)
        (X := zlRealizationBase D l hl Y₀) (Y := zlRealizationBase D l hl Y₀)
        (D.geometricFrobenius Y₀).hom)) ∧
    (∀ (E E' : Padic.FiniteCoefficientFields l Ω) (i : E ≤ E'),
      Nonempty (LisseRealization.FieldNormalized D l hl
        (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω E')
        (coefficientInclusion l Ω E E' i) (zlRealizationBase D l hl Y₀)
        (a.realization (Coefficient.{u} l Ω E) (zlRealizationBase D l hl Y₀))
        (a.realization (Coefficient.{u} l Ω E') (zlRealizationBase D l hl Y₀))
        (a.fieldChange (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω E')
          (coefficientInclusion l Ω E E' i) (zlRealizationBase D l hl Y₀))))

/-- On the actual algebraic category, an additive equation is tested on all classical
geometric fibres. This uses the existing finite-model fibre functors, and is equivalent
to equality of sheaf maps, without choosing an additive structure on a localization.
Source: Weil II (1.1.1), (1.1.6); node proof steps 2 and 8
(blueprint: lem-zl-classical-finite-weil-diagram-realization). -/
def zlClassicalEquation {I : Type v} {A : Type w} {s t : A → I}
    (M : I → ZlClassicalWeil D l Ω Y₀) (a : ∀ j : A, M (s j) ⟶ M (t j))
    {x y : I × ℕ} (e f : ZlWeilExpression s t x y) : Prop :=
  ∀ (κ : Type u) [Field κ] [IsAlgClosed κ] (b : Spec (.of κ) ⟶ (D.geometricFiber Y₀).left),
    zlExpressionValue (lisseAlgebraicAutomorphismPullback (D.geometricFrobenius Y₀) l Ω)
        M a (lisseAlgebraicFiberFunctor l (D.geometricFiber Y₀).left b Ω) e =
      zlExpressionValue (lisseAlgebraicAutomorphismPullback (D.geometricFrobenius Y₀) l Ω)
        M a (lisseAlgebraicFiberFunctor l (D.geometricFiber Y₀).left b Ω) f

```

## New

The exact same Lean text above now lives in
Sheaf.Paper.ClassicalFiniteWeilDiagramData, with the original public imports and
settings. The original module has:

```lean
public import Sheaf.Paper.ClassicalFiniteWeilDiagramData
```

All declaration names, universes, visibility, signatures and definition bodies are
identical. No new mathematical definition replaces an old one. There is no target
statement change, nor any change to the meaning of definitions used by a target.
The supporting proof lemmas are private and proved. Three new public theorem modules
isolate source steps; each has a DAG node and a complete natural-language proof.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ClassicalFiniteWeilDiagramRealization | C3 | Re-exports the unchanged data and proves the original theorem from smaller steps. |
| Sheaf.Paper.ClassicalFiniteWeilDiagramData | new, C3 | Holds the verbatim data interface. |
| Sheaf.Paper.ClassicalWeilCoherentDiagramStages | new, C3 | Imports the data to state coherent stages. |
| Sheaf.Paper.ClassicalWeilFiniteDiagramDescent | new, C3 | Imports the data to state finite descent. |
| Sheaf.Paper.ClassicalWeilPrescribedIsomorphismLifts | new, C3 | Imports the data to state prescribed lifts. |

The current source has no external Lean importer or declaration user of the original
module (checked using tools/downstream.py and rg). Unfinished DAG parents retain their
attachment to the original theorem, whose signature is unchanged. No consumer repair
is required.

## Status

landed 20261025T122605-L-1788533 2026-10-25 (merge of deliver/C3/Sheaf.Paper.ClassicalFiniteWeilDiagramRealization)
