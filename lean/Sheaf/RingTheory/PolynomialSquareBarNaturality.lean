/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q20
-/
module

public import Sheaf.RingTheory.PolynomialPresentationHomology
public import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
public import Sheaf.RingTheory.CotangentDifferentialPresheafSes
public import Mathlib.Algebra.Category.ModuleCat.Ulift
import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-! # Ring squares and polynomial bar comparisons

Source: Stacks Project, Cotangent Complex, Tag 08QL; Cohomology on Sites,
Tags 08PD and 08Q9 (blueprint: lem-trf-polynomial-square-bar-naturality).

All comparison maps are the recorded, projective-roof-normalized comparisons.
The tensor order is `A' ⊗[A] T` and `B ⊗[T] Ω[T/A]`, using tensor symmetry.
The data are specified on all pure tensors; no construction selects data from
an unproved existence theorem. The containing universe is `max (u + 1) v`.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u v

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open CategoryTheory.SimplicialDerivedColimit
open scoped ChangeOfRings TensorProduct

namespace Algebra.PolynomialSquareBar

/-- Forget the harmless size lift and pass to the recorded full polynomial site.
Source: Stacks 08PS and 08QL (blueprint: lem-trf-polynomial-square-bar-naturality). -/
def site {A B : CommRingCat.{u}} (f : A ⟶ B) :
    PolynomialHomology.Category.{u, v} f ⥤ (CotangentSites.Site f)ᵒᵖ :=
  AsSmall.down ⋙ opOp _ ⋙ AsSmall.up.op

/-- The recorded differential coefficients, transported to the containing universe.
Source: Stacks 08PU and 08QL (blueprint: lem-trf-polynomial-square-bar-naturality). -/
def coefficients {A B : CommRingCat.{u}} {f : A ⟶ B}
    (F : CotangentSheaf.SiteCoefficients f) :
    (PolynomialHomology.Category.{u, v} f)ᵒᵖᵒᵖ ⥤
      ModuleCat.{max (u + 1) v} (ULift.{max (u + 1) v} B) :=
  unopUnop _ ⋙ site f ⋙ F.functor ⋙
    ModuleCat.uliftFunctor.{max (u + 1) v, u, u} B ⋙
      ModuleCat.restrictScalars
        (ULift.ringEquiv : ULift.{max (u + 1) v} B ≃+* B).toRingHom

/-- The differential tensor in these coefficients, in the symmetric tensor order.
Source: Stacks 08PU and 08QL (blueprint: lem-trf-polynomial-square-bar-naturality). -/
def generator {A B : CommRingCat.{u}} {f : A ⟶ B}
    (F : CotangentSheaf.SiteCoefficients f) (T : PolynomialHomology.Category.{u, v} f)
    (b : B) (x : (PolynomialHomology.rings f).obj T) :
    (coefficients.{u, v} F).obj (op (op T)) :=
  ULift.up ((F.terms ((site f).obj T)).inv
    (CotangentSheaf.tensorD ((PolynomialHomology.diagram f).obj T).left.hom
      ((PolynomialHomology.diagram f).obj T).hom.right b x))

/-- The actual tensor algebra for base change; its scalar structures are the supplied maps.
Source: Stacks 08QL (blueprint: lem-trf-polynomial-square-bar-naturality). -/
def tensorRing {f g : Arrow CommRingCat.{u}} (q : f ⟶ g)
    (T : PolynomialHomology.Category.{u, v} f.hom) : CommRingCat.{u} :=
  letI := q.left.hom.toAlgebra
  letI : Algebra f.left ((PolynomialHomology.rings f.hom).obj T) :=
    ((PolynomialHomology.diagram f.hom).obj T).left.hom.hom.toAlgebra
  CommRingCat.of (g.left ⊗[f.left] (PolynomialHomology.rings f.hom).obj T)

/-- A pure tensor, with the scalar in the first position.
Source: Stacks 08QL (blueprint: lem-trf-polynomial-square-bar-naturality). -/
def tensorElement {f g : Arrow CommRingCat.{u}} (q : f ⟶ g)
    (T : PolynomialHomology.Category.{u, v} f.hom) (a : g.left)
    (x : (PolynomialHomology.rings f.hom).obj T) : tensorRing q T :=
  letI := q.left.hom.toAlgebra
  letI : Algebra f.left ((PolynomialHomology.rings f.hom).obj T) :=
    ((PolynomialHomology.diagram f.hom).obj T).left.hom.hom.toAlgebra
  a ⊗ₜ[f.left] x

/-- Regard a simplicial polynomial presentation as the recorded augmented algebra.
Source: Stacks 08QI and 08QL (blueprint: lem-trf-polynomial-square-bar-naturality). -/
def augmented {A B : CommRingCat.{u}} {f : A ⟶ B}
    (Q : SimplicialObject (PolynomialHomology.Category.{u, v} f)) :
    CotangentResolution.Augmentation (Arrow.mk f) where
  algebra := Q ⋙ PolynomialHomology.rings f
  base := Functor.whiskerLeft (Q ⋙ PolynomialHomology.diagram f ⋙ Over.forget _)
    (Under.forgetCone A).π
  augmentation := Functor.whiskerRight
    (Functor.whiskerLeft (Q ⋙ PolynomialHomology.diagram f)
      (Over.forgetCocone (Under.mk f)).ι) (Under.forget A)
  triangle n := Under.w ((PolynomialHomology.diagram f).obj (Q.obj (op ⦋n⦌))).hom

/-- A coefficient tensor in cochain degree `-n`; the evaluation complex has alternating
faces and zero positive terms. Source: Stacks 08PN and 08Q9
(blueprint: lem-trf-polynomial-square-bar-naturality). -/
def complexGenerator {A B : CommRingCat.{u}} {f : A ⟶ B}
    (F : CotangentSheaf.SiteCoefficients f)
    (Q : SimplicialObject (PolynomialHomology.Category.{u, v} f)) (n : ℕ) (b : B)
    (x : (PolynomialHomology.rings f).obj (Q.obj (op ⦋n⦌))) :
    ((evaluationComplex (Q ⋙ opOp _)).obj (coefficients F)).X (-↑n) :=
  (evaluationTerm (Q ⋙ opOp _) (coefficients F) n).inv
    (generator F (Q.obj (op ⦋n⦌)) b x)

-- The independent containing-universe lift appears only through `max (u + 1) v`.
set_option linter.checkUnivs false in
set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- The standard simplicial resolutions and their explicitly recursive square maps.
Source: Stacks 08PM and 08QL (blueprint: lem-trf-polynomial-square-bar-naturality). -/
structure StandardData where
  standard : ∀ f : Arrow CommRingCat.{u},
    SimplicialObject (PolynomialHomology.Category.{u, v} f.hom)
  standard_spec : ∀ f : Arrow CommRingCat.{u},
    CotangentResolution.IsStandard (augmented (standard f))
  standard_trivial : ∀ f : Arrow CommRingCat.{u},
    SSet.modelCategoryQuillen.I.rlp (PolynomialHomology.augmentation (standard f))
  standardMap : ∀ {f g : Arrow CommRingCat.{u}} (q : f ⟶ g),
    CotangentResolution.AugmentedMap q (augmented (standard f)) (augmented (standard g))
  standard_formula : ∀ {f g : Arrow CommRingCat.{u}} (q : f ⟶ g) (n : ℕ),
    HEq ((standardMap q).map.app (op ⦋n⦌)) (CotangentResolution.standardSquareMap q n)
  standard_id : ∀ f : Arrow CommRingCat.{u}, (standardMap (𝟙 f)).map = 𝟙 _
  standard_comp : ∀ {f g j : Arrow CommRingCat.{u}} (q : f ⟶ g) (r : g ⟶ j),
    (standardMap (q ≫ r)).map = (standardMap q).map ≫ (standardMap r).map
-- The independent containing-universe lift appears only through `max (u + 1) v`.
set_option linter.checkUnivs false in
set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- Base change on the full polynomial category, fixed on all pure tensors.
Source: Stacks 08QL (blueprint: lem-trf-polynomial-square-bar-naturality). -/
structure TensorData where
  baseChange : ∀ {f g : Arrow CommRingCat.{u}} (_q : f ⟶ g),
    PolynomialHomology.Category.{u, v} f.hom ⥤ PolynomialHomology.Category.{u, v} g.hom
  tensorIso : ∀ {f g : Arrow CommRingCat.{u}} (q : f ⟶ g)
    (T : PolynomialHomology.Category.{u, v} f.hom),
    (PolynomialHomology.rings g.hom).obj ((baseChange q).obj T) ≅ tensorRing q T
  tensor_base : ∀ {f g : Arrow CommRingCat.{u}} (q : f ⟶ g)
    (T : PolynomialHomology.Category.{u, v} f.hom) (a : g.left),
    (tensorIso q T).hom
      (((PolynomialHomology.diagram g.hom).obj ((baseChange q).obj T)).left.hom a) =
        tensorElement q T a 1
  tensor_aug : ∀ {f g : Arrow CommRingCat.{u}} (q : f ⟶ g)
    (T : PolynomialHomology.Category.{u, v} f.hom) (a : g.left)
    (x : (PolynomialHomology.rings f.hom).obj T),
    ((PolynomialHomology.diagram g.hom).obj ((baseChange q).obj T)).hom.right
      ((tensorIso q T).inv (tensorElement q T a x)) =
        q.right (((PolynomialHomology.diagram f.hom).obj T).hom.right x) * g.hom a
  tensor_map : ∀ {f g : Arrow CommRingCat.{u}} (q : f ⟶ g)
    {T S : PolynomialHomology.Category.{u, v} f.hom} (z : T ⟶ S) (a : g.left)
    (x : (PolynomialHomology.rings f.hom).obj T),
    (tensorIso q S).hom ((PolynomialHomology.rings g.hom).map ((baseChange q).map z)
      ((tensorIso q T).inv (tensorElement q T a x))) =
        tensorElement q S a ((PolynomialHomology.rings f.hom).map z x)
set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- The coefficient transformation, its simplicial factorization, and the induced
chain maps, fixed on differential tensors. The two component records are part of
the conclusion. Source: Stacks 08QL (blueprint: lem-trf-polynomial-square-bar-naturality). -/
structure Maps (F : ∀ f : Arrow CommRingCat.{u}, CotangentSheaf.SiteCoefficients f.hom) where
  S : StandardData.{u, v}
  tensor : TensorData.{u, v}
  theta : ∀ {f g : Arrow CommRingCat.{u}} (q : f ⟶ g),
    coefficients (F f) ⟶ (tensor.baseChange q).op.op ⋙ coefficients (F g) ⋙
      ModuleCat.restrictScalars (RingHom.ulift.{max (u + 1) v, max (u + 1) v} q.right.hom)
  theta_formula : ∀ {f g : Arrow CommRingCat.{u}} (q : f ⟶ g)
    (T : PolynomialHomology.Category.{u, v} f.hom) (b : f.right)
    (x : (PolynomialHomology.rings f.hom).obj T),
    (theta q).app (op (op T)) (generator (F f) T b x) =
      generator (F g) ((tensor.baseChange q).obj T) (q.right b)
        ((tensor.tensorIso q T).inv (tensorElement q T 1 x))
  factor : ∀ {f g : Arrow CommRingCat.{u}} (q : f ⟶ g)
    {Q : SimplicialObject (PolynomialHomology.Category.{u, v} f.hom)}
    {Q' : SimplicialObject (PolynomialHomology.Category.{u, v} g.hom)}
    (_h : CotangentResolution.AugmentedMap q (augmented Q) (augmented Q')),
    Q ⋙ tensor.baseChange q ⟶ Q'
  factor_formula : ∀ {f g : Arrow CommRingCat.{u}} (q : f ⟶ g)
    {Q : SimplicialObject (PolynomialHomology.Category.{u, v} f.hom)}
    {Q' : SimplicialObject (PolynomialHomology.Category.{u, v} g.hom)}
    (h : CotangentResolution.AugmentedMap q (augmented Q) (augmented Q'))
    (n : ℕ) (a : g.left) (x : (PolynomialHomology.rings f.hom).obj (Q.obj (op ⦋n⦌))),
    (PolynomialHomology.rings g.hom).map ((factor q h).app (op ⦋n⦌))
      ((tensor.tensorIso q (Q.obj (op ⦋n⦌))).inv
        (tensorElement q (Q.obj (op ⦋n⦌)) a x)) =
      h.map.app (op ⦋n⦌) x * (augmented Q').base.app (op ⦋n⦌) a
  chainMap : ∀ {f g : Arrow CommRingCat.{u}} (q : f ⟶ g)
    {Q : SimplicialObject (PolynomialHomology.Category.{u, v} f.hom)}
    {Q' : SimplicialObject (PolynomialHomology.Category.{u, v} g.hom)}
    (_h : CotangentResolution.AugmentedMap q (augmented Q) (augmented Q')),
    (evaluationComplex (Q ⋙ opOp _)).obj (coefficients (F f)) ⟶
      ((ModuleCat.restrictScalars
        (RingHom.ulift.{max (u + 1) v, max (u + 1) v} q.right.hom)).mapHomologicalComplex
          (.up ℤ)).obj ((evaluationComplex (Q' ⋙ opOp _)).obj (coefficients (F g)))
  chain_formula : ∀ {f g : Arrow CommRingCat.{u}} (q : f ⟶ g)
    {Q : SimplicialObject (PolynomialHomology.Category.{u, v} f.hom)}
    {Q' : SimplicialObject (PolynomialHomology.Category.{u, v} g.hom)}
    (h : CotangentResolution.AugmentedMap q (augmented Q) (augmented Q'))
    (n : ℕ) (b : f.right) (x : (PolynomialHomology.rings f.hom).obj (Q.obj (op ⦋n⦌))),
    (chainMap q h).f (-↑n) (complexGenerator (F f) Q n b x) =
      complexGenerator (F g) Q' n (q.right b) (h.map.app (op ⦋n⦌) x)
  chain_id : ∀ (f : Arrow CommRingCat.{u}) (i : ℤ)
    (x : ((evaluationComplex (S.standard f ⋙ opOp _)).obj (coefficients (F f))).X i),
    (chainMap (𝟙 f) (S.standardMap (𝟙 f))).f i x = x
  chain_comp : ∀ {f g j : Arrow CommRingCat.{u}} (q : f ⟶ g) (r : g ⟶ j) (i : ℤ)
    (x : ((evaluationComplex (S.standard f ⋙ opOp _)).obj (coefficients (F f))).X i),
    (chainMap (q ≫ r) (S.standardMap (q ≫ r))).f i x =
      (chainMap r (S.standardMap r)).f i ((chainMap q (S.standardMap q)).f i x)
/-- All constructions and their canonical bar comparison equation. The parameters `D`
are the recorded normalized polynomial comparisons, and `F` are the recorded differential
coefficient functors. Source: Stacks 08QL, 08PD and 08Q9
(blueprint: lem-trf-polynomial-square-bar-naturality). -/
def Data (bar : CategoryColimitBarSystem.{max (u + 1) v}) (C : Computation bar)
    (D : ∀ f : Arrow CommRingCat.{u}, PolynomialHomology.ComputationData f.hom bar C)
    (F : ∀ f : Arrow CommRingCat.{u}, CotangentSheaf.SiteCoefficients f.hom) : Prop :=
  ∃ M : Maps.{u, v} F, ∀ {f g : Arrow CommRingCat.{u}} (q : f ⟶ g)
    {Q : SimplicialObject (PolynomialHomology.Category.{u, v} f.hom)}
    {Q' : SimplicialObject (PolynomialHomology.Category.{u, v} g.hom)}
    (hQ : SSet.modelCategoryQuillen.I.rlp (PolynomialHomology.augmentation Q))
    (hQ' : SSet.modelCategoryQuillen.I.rlp (PolynomialHomology.augmentation Q'))
    (h : CotangentResolution.AugmentedMap q (augmented Q) (augmented Q')),
    DerivedCategory.Q.map (M.chainMap q h) ≫
      (ModuleCat.restrictScalars
        (RingHom.ulift.{max (u + 1) v, max (u + 1) v}
          q.right.hom)).mapDerivedCategoryFactors.inv.app
          ((evaluationComplex (Q' ⋙ opOp _)).obj (coefficients (F g))) ≫
      (ModuleCat.restrictScalars
        (RingHom.ulift.{max (u + 1) v, max (u + 1) v} q.right.hom)).mapDerivedCategory.map
          (((D g).comparison Q' hQ' (ULift.{max (u + 1) v} g.right)).hom.app
            (coefficients (F g))) =
      ((D f).comparison Q hQ (ULift.{max (u + 1) v} f.right)).hom.app (coefficients (F f)) ≫
        derivedMap bar (M.tensor.baseChange q).op
          (RingHom.ulift.{max (u + 1) v, max (u + 1) v} q.right.hom) (M.theta q)

/-- Explicit standard ring-square maps and base-change bar naturality exist, with every
map fixed by its polynomial or differential-tensor formula.
Source: Stacks Project, Tag 08QL; Cohomology on Sites, Tags 08PD and 08Q9
(blueprint: lem-trf-polynomial-square-bar-naturality).

Proof:
1. Use the existing recursive `standardSquareMap`: coefficients go through alpha and
   variables through the preceding map, starting with beta in degree -1. Evaluation
   and unit insertion commute with substitution on coefficients and generators.
   This proves semilinear augmented simpliciality and strict identity/composition.
   The standard augmentation is trivial Kan by polynomial-augmentation-boundary.
2. Tensor an augmented polynomial algebra with A'. The augmentation is
   a' tensor x |-> beta(epsilon(x)) a', and arrows apply their map to x.
   These are balanced by the ring-square equation. The polynomial tensor equivalence
   `MvPolynomial.algebraTensorAlgEquiv` shows the result is polynomial for every
   variable set, including empty and infinite sets. All rings remain U-small.
3. Universal differential relations define theta by dx tensor b |->
   d(x tensor 1) tensor beta(b). Additivity, Leibniz, base constants and balancing
   prove well-definedness; on these generators the naturality square commutes.
4. Extend h over A' by x tensor a' |-> h(x)a'. Balancing uses semilinearity,
   augmentation compatibility uses the equation for h, and simpliciality follows
   on pure tensors. Differential relations give the specified chainMap; alternating
   faces commute because h is simplicial. Generator formulas prove the strict
   standard chain identity and composition laws.
5. Polynomial-presentation-homology supplies representable contractibility for Q
   and Q' and its comparisons are normalized to C. Apply the naturality clause of
   simplicial-derived-colimit-computation with u, theta and factor. Its evaluation
   map is chainMap by the generator formula. Its signed first-vertex bar map sends
   a string to its u-image and x to theta(x), giving exactly the displayed equation.
6. Apply this to the standard endpoints using standard_trivial. No contractibility
   of uQ is used, and substitutions and balanced tensors require no flatness or
   injectivity of either vertical ring map. Coefficient ULift and restriction
   preserve every displayed formula, including the localization comparison. -/
theorem data_nonempty (bar : CategoryColimitBarSystem.{max (u + 1) v}) (C : Computation bar)
    (D : ∀ f : Arrow CommRingCat.{u}, PolynomialHomology.ComputationData f.hom bar C)
    (F : ∀ f : Arrow CommRingCat.{u}, CotangentSheaf.SiteCoefficients f.hom) :
    Data bar C D F := by
  sorry

end Algebra.PolynomialSquareBar
