/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q37
-/
module

public import Sheaf.RingTheory.CotangentResolutionCoherence
public import Sheaf.CategoryTheory.DerivedColimitBar
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.InducedCategory
public import Mathlib.SetTheory.Cardinal.Basic
import Sheaf.AlgebraicTopology.SurjectiveQuasiIsoTrivialKan
import Sheaf.Paper.TrivialKanHomotopyEquivalence

/-!
# The polynomial-presentation sheaf model of the cotangent complex

Source: Stacks Project, Cotangent Complex, Tags 08PS, 08PT, 08PU, 08QI and 08QL
(blueprint: lem-trf-cotangent-sheaf-model).

A fixed infinite set bounds the variables. Subsets of that set give a small
category equivalent to the category of polynomial presentations within the bound.
The topology is the identity-cover topology. The records specify the constructions
by their polynomial and differential formulas; nothing is chosen from a postponed
existence theorem.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open scoped ChangeOfRings

namespace Algebra.CotangentSheaf

/-- A polynomial algebra with variables in the fixed bound and an augmentation to `B`.
Source: Stacks 08PS (blueprint: lem-trf-cotangent-sheaf-model). -/
structure Presentation (f : Arrow CommRingCat.{u}) (κ : Type u) where
  vars : Set κ
  values : vars → f.right

/-- The target ring with its specified `A`-algebra structure.
Source: Stacks 08PS (blueprint: lem-trf-cotangent-sheaf-model). -/
def target (f : Arrow CommRingCat.{u}) : CommAlgCat.{u} f.left :=
  letI := f.hom.hom.toAlgebra
  CommAlgCat.of f.left f.right

/-- The actual augmented polynomial algebra; morphisms in its over category are
all algebra maps commuting with augmentations. Source: Stacks 08PS
(blueprint: lem-trf-cotangent-sheaf-model). -/
def presentationObject {f : Arrow CommRingCat.{u}} {κ : Type u} (p : Presentation f κ) :
    Over (target f) :=
  letI := f.hom.hom.toAlgebra
  Over.mk (CommAlgCat.ofHom (MvPolynomial.aeval (R := f.left) (S₁ := target f) p.values))

/-- A small model for the polynomial-presentation category before taking opposites.
No surjectivity is required of its objects. Source: Stacks 08PS
(blueprint: lem-trf-cotangent-sheaf-model). -/
abbrev Presentations (f : Arrow CommRingCat.{u}) (κ : Type u) :=
  InducedCategory (Over (target f)) (@presentationObject f κ)

/-- The structure presheaf, written covariantly on the opposite of the site.
Source: Stacks 08PS (blueprint: lem-trf-cotangent-sheaf-model). -/
def rings (f : Arrow CommRingCat.{u}) (κ : Type u) :
    Presentations f κ ⥤ CommRingCat.{u} :=
  inducedFunctor (@presentationObject f κ) ⋙ Over.forget (target f) ⋙
    forget₂ (CommAlgCat.{u} f.left) CommRingCat

/-- Coefficient inclusion in a presentation. Source: Stacks 08PS
(blueprint: lem-trf-cotangent-sheaf-model). -/
def base {f : Arrow CommRingCat.{u}} {κ : Type u} (p : Presentations f κ) :
    f.left ⟶ (rings f κ).obj p := CommRingCat.ofHom MvPolynomial.C

/-- The augmentation of a presentation. Source: Stacks 08PS
(blueprint: lem-trf-cotangent-sheaf-model). -/
def augmentation {f : Arrow CommRingCat.{u}} {κ : Type u} (p : Presentations f κ) :
    (rings f κ).obj p ⟶ f.right :=
  CommRingCat.ofHom (MvPolynomial.eval₂Hom f.hom.hom p.values)

/-- The actual coefficient module `B ⊗_P Ω[P/A]`, with tensor factors reversed
by the usual symmetry from the source. Source: Stacks 08PU
(blueprint: lem-trf-cotangent-sheaf-model). -/
def coefficientTerm {f : Arrow CommRingCat.{u}} {κ : Type u} (p : Presentations f κ) :
    ModuleCat.{u} f.right :=
  (ModuleCat.extendScalars (augmentation p).hom).obj (CommRingCat.KaehlerDifferential (base p))

/-- The generating differential tensor. Source: Stacks 08PU and 08QL
(blueprint: lem-trf-cotangent-sheaf-model). -/
def generator {f : Arrow CommRingCat.{u}} {κ : Type u} (p : Presentations f κ)
    (b : f.right) (x : (rings f κ).obj p) : coefficientTerm p :=
  b ⊗ₜ[_, (augmentation p).hom] CommRingCat.KaehlerDifferential.d x

/-- The coefficient presheaf, including the universal differential formula for every
restriction. Source: Stacks 08PU (blueprint: lem-trf-cotangent-sheaf-model). -/
structure Coefficients (f : Arrow CommRingCat.{u}) (κ : Type u) where
  functor : Presentations f κ ⥤ ModuleCat.{u} f.right
  terms : ∀ p : Presentations f κ, functor.obj p ≅ coefficientTerm p
  formula : ∀ {p r : Presentations f κ} (h : p ⟶ r) (b : f.right)
    (x : (rings f κ).obj p),
    (terms r).hom (functor.map h ((terms p).inv (generator p b x))) =
      generator r b ((rings f κ).map h x)

/-- The sheaf of coefficients as a module presheaf on the opposite presentation site.
The identity-cover topology identifies such presheaves with sheaves through the
bar model's `CategoryColimitPoint.modules`. Source: Stacks 08PU
(blueprint: lem-trf-cotangent-sheaf-model). -/
def presheaf {f : Arrow CommRingCat.{u}} {κ : Type u} (F : Coefficients f κ) :
    (Presentations f κ)ᵒᵖᵒᵖ ⥤ ModuleCat.{u} f.right :=
  unopUnop (Presentations f κ) ⋙ F.functor

/-- A resolution transported to the chosen small presentation category, with its
actual algebra, base map and augmentation identified. Source: Stacks 08PS and 08QI
(blueprint: lem-trf-cotangent-sheaf-model). -/
structure ResolutionLift {f : Arrow CommRingCat.{u}} (κ : Type u)
    (P : CotangentResolution.Augmentation f) where
  diagram : SimplicialObject (Presentations f κ)
  ringIso : diagram ⋙ rings f κ ≅ P.algebra
  base_eq : ∀ n : ℕ, base (diagram.obj (op ⦋n⦌)) ≫ ringIso.hom.app (op ⦋n⦌) =
    P.base.app (op ⦋n⦌)
  augmentation_eq : ∀ n : ℕ,
    ringIso.hom.app (op ⦋n⦌) ≫ P.augmentation.app (op ⦋n⦌) =
      augmentation (diagram.obj (op ⦋n⦌))

/-- A resolution lies within the common variable bound precisely when each term
has a polynomial presentation within that bound. Source: Stacks 08PS and the size
convention (blueprint: lem-trf-cotangent-sheaf-model). -/
def FitsBound {f : Arrow CommRingCat.{u}} (κ : Type u)
    (P : CotangentResolution.Augmentation f) : Prop :=
  ∀ n : ℕ, ∃ (p : Presentations f κ) (e : (rings f κ).obj p ≅ P.algebra.obj (op ⦋n⦌)),
    base p ≫ e.hom = P.base.app (op ⦋n⦌) ∧
      e.hom ≫ P.augmentation.app (op ⦋n⦌) = augmentation p

/-- Evaluation on the augmented resolution, followed by the alternating differential
and extension by zero to positive cohomological degrees. Source: Stacks 08PS and 08QI
(blueprint: lem-trf-cotangent-sheaf-model). -/
def evaluation {f : Arrow CommRingCat.{u}} {κ : Type u}
    {P : CotangentResolution.Augmentation f} (L : ResolutionLift κ P) :
    ((Presentations f κ)ᵒᵖᵒᵖ ⥤ ModuleCat.{u} f.right) ⥤
      CochainComplex (ModuleCat.{u} f.right) ℤ :=
  (Functor.whiskeringLeft SimplexCategoryᵒᵖ (Presentations f κ)ᵒᵖᵒᵖ
    (ModuleCat.{u} f.right)).obj (L.diagram ⋙ opOp (Presentations f κ)) ⋙
      CotangentResolution.negativeComplex (ModuleCat.{u} f.right)

/-- Evaluation and the alternating complex are additive, by the existing Mathlib
instances for precomposition, alternating complexes and extension by zero.
Source: Stacks 08PS (blueprint: lem-trf-cotangent-sheaf-model). -/
instance evaluation_additive {f : Arrow CommRingCat.{u}} {κ : Type u}
    {P : CotangentResolution.Augmentation f} (L : ResolutionLift κ P) :
    (evaluation L).Additive :=
  inferInstanceAs (((Functor.whiskeringLeft SimplexCategoryᵒᵖ (Presentations f κ)ᵒᵖᵒᵖ
    (ModuleCat.{u} f.right)).obj (L.diagram ⋙ opOp (Presentations f κ)) ⋙
      (AlgebraicTopology.alternatingFaceMapComplex (ModuleCat.{u} f.right) ⋙
        ComplexShape.embeddingDownNat.extendFunctor (ModuleCat.{u} f.right))).Additive)

/-- An element of degree `-n` in the evaluated alternating complex. Source: Stacks
08PS (blueprint: lem-trf-cotangent-sheaf-model). -/
def evaluationElement {f : Arrow CommRingCat.{u}} {κ : Type u}
    {P : CotangentResolution.Augmentation f} (L : ResolutionLift κ P)
    (F : (Presentations f κ)ᵒᵖᵒᵖ ⥤ ModuleCat.{u} f.right) (n : ℕ)
    (x : F.obj (op (op (L.diagram.obj (op ⦋n⦌))))) :
    ((evaluation L).obj F).X (-(n : ℤ)) :=
  (((AlgebraicTopology.alternatingFaceMapComplex _).obj
    (L.diagram ⋙ opOp (Presentations f κ) ⋙ F)).extendXIso
      ComplexShape.embeddingDownNat (i := n) rfl).inv x

/-- The map on evaluated complexes induced by a map of augmented resolutions in
the presentation category. Source: Stacks 08QI
(blueprint: lem-trf-cotangent-sheaf-model). -/
def evaluationMap {f : Arrow CommRingCat.{u}} {κ : Type u}
    {P Q : CotangentResolution.Augmentation f}
    (L : ResolutionLift κ P) (N : ResolutionLift κ Q) (h : L.diagram ⟶ N.diagram)
    (F : (Presentations f κ)ᵒᵖᵒᵖ ⥤ ModuleCat.{u} f.right) :
    (evaluation L).obj F ⟶ (evaluation N).obj F :=
  (CotangentResolution.negativeComplex (ModuleCat.{u} f.right)).map
    (Functor.whiskerRight (Functor.whiskerRight h (opOp (Presentations f κ))) F)

/-- Derived lower shriek on presheaves in degree zero, using exactly the bar
system's derived colimit. Source: Stacks 08PS
(blueprint: lem-trf-cotangent-sheaf-model). -/
def lowerShriek (S : CategoryColimitBarSystem.{u}) (f : Arrow CommRingCat.{u}) (κ : Type u) :=
  CochainComplex.singleFunctor ((Presentations f κ)ᵒᵖᵒᵖ ⥤ ModuleCat.{u} f.right) 0 ⋙
    DerivedCategory.Q ⋙ (S.models (Presentations f κ)ᵒᵖ f.right).derived

/-- Normalization by the augmentation to ordinary colimits, compared with the
universal derived-colimit transformation. Source: Stacks 08PS and 08PG
(blueprint: lem-trf-cotangent-sheaf-model). -/
def IsNormalized (S : CategoryColimitBarSystem.{u})
    {f : Arrow CommRingCat.{u}} {κ : Type u}
    {P : CotangentResolution.Augmentation f} (L : ResolutionLift κ P)
    (iso : lowerShriek S f κ ≅ evaluation L ⋙ DerivedCategory.Q)
    (augmentation : ∀ F : (Presentations f κ)ᵒᵖᵒᵖ ⥤ ModuleCat.{u} f.right,
      (evaluation L).obj F ⟶
        (CochainComplex.singleFunctor (ModuleCat.{u} f.right) 0).obj (colimit F)) : Prop :=
  ∀ F : (Presentations f κ)ᵒᵖᵒᵖ ⥤ ModuleCat.{u} f.right,
    iso.hom.app F ≫ DerivedCategory.Q.map (augmentation F) ≫
      DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex
          (colim : ((Presentations f κ)ᵒᵖᵒᵖ ⥤ ModuleCat.{u} f.right) ⥤ _) (.up ℤ) 0).inv.app F) =
      (S.models (Presentations f κ)ᵒᵖ f.right).comparison.app
        ((CochainComplex.singleFunctor _ 0).obj F)

/-- Compatibility with the connecting morphisms of short exact sequences, so
the normalized comparison is the canonical map of derived homological functors.
Source: Stacks 08PS and 08Q9 (blueprint: lem-trf-cotangent-sheaf-model). -/
def PreservesBoundary (S : CategoryColimitBarSystem.{u})
    {f : Arrow CommRingCat.{u}} {κ : Type u}
    {P : CotangentResolution.Augmentation f} (L : ResolutionLift κ P)
    (iso : lowerShriek S f κ ≅ evaluation L ⋙ DerivedCategory.Q)
    (hExact : ∀ T : ShortComplex ((Presentations f κ)ᵒᵖᵒᵖ ⥤ ModuleCat.{u} f.right),
      T.ShortExact → (T.map (evaluation L)).ShortExact) : Prop :=
  ∀ (T : ShortComplex ((Presentations f κ)ᵒᵖᵒᵖ ⥤ ModuleCat.{u} f.right))
    (hT : T.ShortExact)
    (hobj : ∀ V : (Presentations f κ)ᵒᵖᵒᵖ,
      (T.map ((CategoryTheory.evaluation _ _).obj V)).ShortExact),
    (S.models (Presentations f κ)ᵒᵖ f.right).derived.map
        (DerivedCategory.triangleOfSESδ
          ((S.models (Presentations f κ)ᵒᵖ f.right).singleExact T hobj)) ≫
      ((S.models (Presentations f κ)ᵒᵖ f.right).derived.commShiftIso (1 : ℤ)).hom.app
        (DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj T.X₁)) ≫
      (iso.hom.app T.X₁)⟦(1 : ℤ)⟧' =
      iso.hom.app T.X₃ ≫ DerivedCategory.triangleOfSESδ (hExact T hT)

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- The normalized resolution comparison for one transported resolution. The
augmentation extends the ordinary colimit cocone and the boundary law fixes the
morphism of derived homological functors. Source: Stacks 08PS and 08QI
(blueprint: lem-trf-cotangent-sheaf-model). -/
structure ResolutionComparison (S : CategoryColimitBarSystem.{u})
    {f : Arrow CommRingCat.{u}} {κ : Type u}
    {P : CotangentResolution.Augmentation f} (L : ResolutionLift κ P) where
  iso : lowerShriek S f κ ≅ evaluation L ⋙ DerivedCategory.Q
  augmentation : ∀ F : (Presentations f κ)ᵒᵖᵒᵖ ⥤ ModuleCat.{u} f.right,
    (evaluation L).obj F ⟶
      (CochainComplex.singleFunctor (ModuleCat.{u} f.right) 0).obj (colimit F)
  augmentation_formula : ∀ (F : (Presentations f κ)ᵒᵖᵒᵖ ⥤ ModuleCat.{u} f.right)
    (x : F.obj (op (op (L.diagram.obj (op ⦋0⦌))))),
    (augmentation F).f 0 (evaluationElement L F 0 x) =
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (colimit F)).inv
        (colimit.ι F (op (op (L.diagram.obj (op ⦋0⦌)))) x)
  normalization : IsNormalized S L iso augmentation
  exact : ∀ T : ShortComplex ((Presentations f κ)ᵒᵖᵒᵖ ⥤ ModuleCat.{u} f.right),
    T.ShortExact → (T.map (evaluation L)).ShortExact
  boundary : PreservesBoundary S L iso exact

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- The coefficient sheaf and all canonical resolution comparisons, including
agreement with the recorded standard cotangent-resolution comparisons.
Source: Stacks 08PS, 08PT, 08PU and 08QI
(blueprint: lem-trf-cotangent-sheaf-model). -/
structure Model (C : CotangentResolution.Coherence.{u}) (S : CategoryColimitBarSystem.{u})
    (f : Arrow CommRingCat.{u}) (κ : Type u) where
  coefficients : Coefficients f κ
  standardFits : FitsBound κ (C.standard f)
  lift : ∀ (P : CotangentResolution.Augmentation f), FitsBound κ P → ResolutionLift κ P
  comparison : ∀ {P : CotangentResolution.Augmentation f}
    (_hP : CotangentResolution.IsPolynomialResolution P) (L : ResolutionLift κ P),
    ResolutionComparison S L
  natural_resolution : ∀ {P Q : CotangentResolution.Augmentation f}
    (hP : CotangentResolution.IsPolynomialResolution P)
    (hQ : CotangentResolution.IsPolynomialResolution Q)
    (L : ResolutionLift κ P) (N : ResolutionLift κ Q) (h : L.diagram ⟶ N.diagram)
    (F : (Presentations f κ)ᵒᵖᵒᵖ ⥤ ModuleCat.{u} f.right),
    (comparison hP L).iso.hom.app F ≫ DerivedCategory.Q.map (evaluationMap L N h F) =
      (comparison hQ N).iso.hom.app F
  differentialIso : ∀ {P : CotangentResolution.Augmentation f} (L : ResolutionLift κ P),
    (evaluation L).obj (presheaf coefficients) ≅
      CotangentResolution.differentialComplex (C.differentials P)
  differential_formula : ∀ {P : CotangentResolution.Augmentation f}
    (L : ResolutionLift κ P) (n : ℕ) (b : f.right)
    (x : (rings f κ).obj (L.diagram.obj (op ⦋n⦌))),
    (differentialIso L).hom.f (-(n : ℤ))
      (evaluationElement L (presheaf coefficients) n
        ((coefficients.terms (L.diagram.obj (op ⦋n⦌))).inv
          (generator (L.diagram.obj (op ⦋n⦌)) b x))) =
      CotangentResolution.complexGenerator (C.differentials P) n b
        (L.ringIso.hom.app (op ⦋n⦌) x)
  agrees : ∀ {P : CotangentResolution.Augmentation f}
    (hP : CotangentResolution.IsPolynomialResolution P) (L : ResolutionLift κ P),
    (comparison hP L).iso.hom.app (presheaf coefficients) ≫
        DerivedCategory.Q.map (differentialIso L).hom ≫ (C.comparison P hP).hom =
      (comparison (C.standard_resolution f) (lift (C.standard f) standardFits)).iso.hom.app
          (presheaf coefficients) ≫
        DerivedCategory.Q.map (differentialIso (lift (C.standard f) standardFits)).hom

/-- The canonical sheaf-to-standard-cotangent comparison: evaluate on the standard
resolution and apply the prescribed differential identification. Source: Stacks
08PT and 08PU (blueprint: lem-trf-cotangent-sheaf-model). -/
def theta {C : CotangentResolution.Coherence.{u}} {S : CategoryColimitBarSystem.{u}}
    {f : Arrow CommRingCat.{u}} {κ : Type u} (M : Model C S f κ) :
    (lowerShriek S f κ).obj (presheaf M.coefficients) ≅ CotangentResolution.cotangentComplex C f :=
  (M.comparison (C.standard_resolution f) (M.lift (C.standard f) M.standardFits)).iso.app
      (presheaf M.coefficients) ≪≫
    DerivedCategory.Q.mapIso (M.differentialIso (M.lift (C.standard f) M.standardFits))

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- Base change of a polynomial presentation is the polynomial algebra on the same
variables over `A'`, canonically `P ⊗_A A'`. The insertion is coefficientwise
`MvPolynomial.map`, hence sends `p` to `p ⊗ 1`. Its naturality specifies base
change on all presentation maps. The coefficient map has exactly the prescribed
semilinear differential-tensor formula. Source: Stacks 08QL
(blueprint: lem-trf-cotangent-sheaf-model). -/
structure BaseChange {f g : Arrow CommRingCat.{u}} {κ : Type u} (q : f ⟶ g)
    (F : Coefficients f κ) (G : Coefficients g κ) where
  functor : Presentations f κ ⥤ Presentations g κ
  objects : ∀ p : Presentations f κ,
    functor.obj p = ⟨p.vars, fun e ↦ q.right (p.values e)⟩
  insertion : rings f κ ⟶ functor ⋙ rings g κ
  insertion_formula : ∀ p : Presentations f κ,
    HEq (insertion.app p)
      (CommRingCat.ofHom (MvPolynomial.map q.left.hom) :
        CommRingCat.of (MvPolynomial p.vars f.left) ⟶
          CommRingCat.of (MvPolynomial p.vars g.left))
  coefficientMap : F.functor ⟶ functor ⋙ G.functor ⋙ ModuleCat.restrictScalars q.right.hom
  formula : ∀ (p : Presentations f κ) (b : f.right) (x : (rings f κ).obj p),
    (G.terms (functor.obj p)).hom
      (coefficientMap.app p ((F.terms p).inv (generator p b x))) =
      generator (functor.obj p) (q.right b) (insertion.app p x)

/-- The semilinear transformation as a map of module presheaves on the opposite
sites. Source: Stacks 08QL (blueprint: lem-trf-cotangent-sheaf-model). -/
def barCoefficientMap {f g : Arrow CommRingCat.{u}} {κ : Type u} {q : f ⟶ g}
    {F : Coefficients f κ} {G : Coefficients g κ} (V : BaseChange q F G) :
    presheaf F ⟶ V.functor.op.op ⋙ presheaf G ⋙ ModuleCat.restrictScalars q.right.hom :=
  Functor.whiskerLeft (unopUnop (Presentations f κ)) V.coefficientMap

/-- The canonical map `T = Lπ_!(u,t)`, using precisely the bar-chain map of
`lem-trf-derived-colimit-bar`, transported through that node's canonical models
and the exact scalar-restriction localization comparison. Source: Stacks 08QL
and Cohomology on Sites 08PH (blueprint: lem-trf-cotangent-sheaf-model). -/
def sheafMap {C : CotangentResolution.Coherence.{u}} {S : CategoryColimitBarSystem.{u}}
    {f g : Arrow CommRingCat.{u}} {κ : Type u} {q : f ⟶ g}
    (M : Model C S f κ) (N : Model C S g κ)
    (V : BaseChange q M.coefficients N.coefficients) :
    (lowerShriek S f κ).obj (presheaf M.coefficients) ⟶
      (ModuleCat.restrictScalars q.right.hom).mapDerivedCategory.obj
        ((lowerShriek S g κ).obj (presheaf N.coefficients)) :=
  (S.models (Presentations f κ)ᵒᵖ f.right).model.hom.app (presheaf M.coefficients) ≫
    DerivedCategory.Q.map (S.map V.functor.op q.right.hom (barCoefficientMap V)) ≫
    (ModuleCat.restrictScalars q.right.hom).mapDerivedCategoryFactors.inv.app
      ((S.models (Presentations g κ)ᵒᵖ g.right).bar.obj (presheaf N.coefficients)) ≫
    (ModuleCat.restrictScalars q.right.hom).mapDerivedCategory.map
      ((S.models (Presentations g κ)ᵒᵖ g.right).model.inv.app (presheaf N.coefficients))

/-- A common infinite variable bound containing both coefficient rings. Together
with `FitsBound` this makes precise the stipulated common size convention, without
restricting the universe of any ring or imposing a finiteness condition.
Source: Stacks, Cotangent Complex, size conventions before 08PS
(blueprint: lem-trf-cotangent-sheaf-model). -/
def ContainsRings (κ : Type u) (f : Arrow CommRingCat.{u}) : Prop :=
  Cardinal.mk f.left ≤ Cardinal.mk κ ∧ Cardinal.mk f.right ≤ Cardinal.mk κ

/-- The cotangent sheaf model, its comparison on every polynomial resolution, and
its agreement with standard-resolution functoriality for every ring square.
Source: Stacks 08PS, 08PT, 08PU, 08QI and 08QL, including the omitted agreement
in 08QL (blueprint: lem-trf-cotangent-sheaf-model).

Proof, following the DAG:
1. Put D = Cᵒᵖ, the small category of augmented polynomial algebras within the
common bound. A module presheaf is a covariant functor on D. The bar complexes
of lem-trf-derived-colimit-bar and lem-trf-simplicial-derived-colimit-computation
have reversed face orders. Multiplication in degree -n by
(-1)^(n(n+1)/2) identifies them, since λ_n = (-1)^n λ_(n-1). This is the identity
in degree zero and commutes with every coefficient and reindexing map.
2. Each polynomial resolution is termwise surjective and its additive
augmentation is a quasi-isomorphism by lem-trf-cotangent-resolution-coherence.
The constant simplicial additive group's alternating complex has differential
zero in odd degrees and identity in positive even degrees. Two-out-of-three
therefore makes the map to the constant simplicial group a quasi-isomorphism.
Apply lem-trf-surjective-qis-simplicial-group-trivial-kan (Stacks 08P1).
3. Maps from A[E] into the resolution are choices of lifts of each generator
with its prescribed augmentation. Boundary fillers from step 2, chosen for
all generators, extend uniquely to algebra maps; this includes the empty and
infinite generator sets. Apply lem-weil-pbc-trivial-kan-homotopy-equivalence
using def-weil-pbc-trivial-kan-fibration. Thus the representable simplicial sets
are contractible, and the same is true after transport to our small model.
4. Apply lem-trf-simplicial-derived-colimit-computation to obtain the canonical
resolution comparison for every module presheaf, naturally in the presheaf
and in augmented resolution maps. Step 1 converts its bar model to the bar
system used here. The augmentation is the ordinary colimit cocone in degree
zero; its derived comparison respects short exact sequences and connecting
maps. No flatness or exactness is required of the presheaf.
5. The universal differential relations of def-weil-pbc-kahler-differentials
construct the coefficient functor, with the displayed tensor restriction
formula. Evaluation identifies it with the differential complex of
lem-trf-cotangent-resolution-coherence. Evaluate on the standard resolution
to define theta; its comparison for any other resolution is obtained through
the same derived colimit and agrees with that node's canonical comparison.
6. For a ring square base change sends A[E] to A'[E]; its augmentation sends
e to b(ε(e)). Coefficientwise polynomial mapping is the insertion p ↦ p ⊗ 1.
The differential and tensor relations give the semilinear coefficient map
b₀ ⊗ dp ↦ b(b₀) ⊗ d(p ⊗ 1). These maps are natural on all presentations.
7. Extend the standard semilinear resolution map h across base change by
p ⊗ a' ↦ h(p)a'. Composing with the coefficient map gives exactly
b₀ ⊗ dp ↦ b(b₀) ⊗ d(h(p)), hence the standard cotangent-complex map.
8. Reindexing naturality of lem-trf-simplicial-derived-colimit-computation
identifies this map with the bar-chain map of lem-trf-derived-colimit-bar.
Cancel the standard comparison isomorphisms to obtain the displayed equality
with cotangentMap, after exact restriction of scalars. Step 1's signs commute
with these bar maps. The base-changed resolution is never assumed to be a
resolution: no injectivity or flatness of either ring map is used.

The quantified models expand the constructions and their formulas, and are
not hypotheses assuming the desired comparison. No object is selected by a
definition from this postponed existence theorem. -/
theorem exists_model (C : CotangentResolution.Coherence.{u}) (S : CategoryColimitBarSystem.{u})
    (κ : Type u) [Infinite κ] :
    ∃ M : ∀ (f : Arrow CommRingCat.{u}), ContainsRings κ f → Model C S f κ,
      ∀ (f g : Arrow CommRingCat.{u}) (hf : ContainsRings κ f) (hg : ContainsRings κ g)
        (q : f ⟶ g),
        ∃ V : BaseChange q (M f hf).coefficients (M g hg).coefficients,
          sheafMap (M f hf) (M g hg) V ≫
              (ModuleCat.restrictScalars q.right.hom).mapDerivedCategory.map
                (theta (M g hg)).hom =
            (theta (M f hf)).hom ≫ CotangentResolution.cotangentMap C q := by
  sorry

end Algebra.CotangentSheaf
