/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NC
-/
module

public import Sheaf.SixFunctors.RingedDerivedAdjointLift
public import Sheaf.SixFunctors.RingedDerivedComparisonData
public import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Homology.BifunctorShift
import Sheaf.SixFunctors.RingedDerivedTensorLift
import Sheaf.Paper.RingedTopoiDerivedPullback
import Sheaf.Algebra.Homology.RingedDerivedTensorHomAdjunction
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses

/-! # Evaluation-defined Hom comparison for ringed pullback

Source: Stacks Project, Cohomology on Sites, Tags 07A4, 08J9 and 0A98;
agent evaluation-mate calculation, steps 1-8
(blueprint: lem-coef-ringed-pullback-hom-evaluation-comparison).

## Main definitions and statement

* `pullbackHomTensorModel` restricts the fixed tensor model to flat-term K-flats.
* `ringedPullbackHomComparison` is the transpose of pulled-back evaluation.
* `RingedHomSignedRepresentatives` specifies evaluation and composition on the actual
  signed total tensor and product Hom complexes.
* `ringedPullbackHomEvaluationComparison` states naturality and compatibility with
  evaluation, arbitrary tensor-Hom transposition and internal composition.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures SheafOfModules

namespace CategoryTheory.RingedDerivedComparisons

/-- The already fixed derived internal Hom, with only its site arguments abbreviated.
Source: Stacks 08J9 (blueprint: lem-coef-ringed-pullback-hom-evaluation-comparison). -/
abbrev pullbackHomFunctor (X : Site.{u, w}) : X.Dᵒᵖ × X.D ⥤ X.D :=
  derivedInternalHomOfUniverses.{u, u, u, w} X.J X.A

/-- Restriction of the site's fixed tensor comparison to flat-term K-flat representatives.
This constructs the data directly; it does not choose an arbitrary tensor comparison.
Source: Stacks 07A4 (blueprint: lem-coef-ringed-pullback-hom-evaluation-comparison). -/
def pullbackHomTensorModel (X : Site.{u, w}) : RingedTensorModel X.corner :=
  { representative := Functor.isoWhiskerLeft
      (({
        obj := fun P ↦ ⟨P.obj,
          (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P.obj).2 P.property.1⟩
        map := fun a ↦ ObjectProperty.homMk a.hom } :
        ObjectProperty.FullSubcategory X.corner.mateFlat ⥤
          ObjectProperty.FullSubcategory
            (CochainComplex.IsKFlatIndependentCoefficients.{u, u, u}
              (J := X.J) (R := X.A))).prod
        ({
        obj := fun P ↦ ⟨P.obj,
          (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P.obj).2 P.property.1⟩
        map := fun a ↦ ObjectProperty.homMk a.hom } :
        ObjectProperty.FullSubcategory X.corner.mateFlat ⥤
          ObjectProperty.FullSubcategory
            (CochainComplex.IsKFlatIndependentCoefficients.{u, u, u}
              (J := X.J) (R := X.A)))) X.model.comparison }

/-- The canonical comparison in the direction FX tensor FY to F(X tensor Y).
Source: Stacks 07A4 (blueprint: lem-coef-ringed-pullback-hom-evaluation-comparison). -/
def pullbackHomTensorator {X Y : Site.{u, w}} {f : Morphism X Y}
    (l : AdjointLift f) (P Q : Y.D) :
    X.closed.tensor.obj (l.edge.left.obj P, l.edge.left.obj Q) ⟶
      l.edge.left.obj (Y.closed.tensor.obj (P, Q)) :=
  (l.edge.tensorComparison (pullbackHomTensorModel Y) (pullbackHomTensorModel X)).inv.app
    (P, Q)

/-- Transpose of canonical tensor comparison followed by pulled-back evaluation.
No invertibility of this map is part of the construction.
Source: Stacks 07A4, 08J9 (blueprint: lem-coef-ringed-pullback-hom-evaluation-comparison). -/
def ringedPullbackHomComparison {X Y : Site.{u, w}} {f : Morphism X Y}
    (l : AdjointLift f) (P Q : Y.D) :
    l.edge.left.obj ((pullbackHomFunctor Y).obj (op P, Q)) ⟶
      (pullbackHomFunctor X).obj (op (l.edge.left.obj P), l.edge.left.obj Q) :=
  X.closed.transpose _ (l.edge.left.obj P) (l.edge.left.obj Q)
    (pullbackHomTensorator l ((pullbackHomFunctor Y).obj (op P, Q)) P ≫
      l.edge.left.map (Y.closed.evaluation P Q))

/-- Apply a degree-n Hom section through its actual product projection.
Source: Stacks 0A8X (blueprint: lem-coef-ringed-pullback-hom-evaluation-comparison). -/
def ringedHomSectionApply (X : Site.{u, w}) (L M : CochainComplex X.modules ℤ)
    (n p q : ℤ) (h : p + n = q) (U : X.Cᵒᵖ)
    (a : ((homComplex (R := X.A) L M).X n).val.obj U)
    (x : (L.X p).val.obj U) : (M.X q).val.obj U :=
  ((((coefficientHomComponent.{u, u, u} X.J X.A L M n p q h).val.app U a).app
    (op (Over.mk (𝟙 U.unop)))).hom) x

/-- The representative maps have no sign on evaluation or composition; their chain-map
conditions use the signed total tensor and d(h)=d h-(-1)^degree(h) h d.
Source: Stacks 0A8X, 0A90, 0A91, 0A98
(blueprint: lem-coef-ringed-pullback-hom-evaluation-comparison). -/
def RingedHomSignedRepresentatives (X : Site.{u, w}) : Prop :=
  ∀ L M N : CochainComplex X.modules ℤ,
    ∃ (e : (coefficientTotalTensor.{u, u, u} X.J X.A).obj
        (homComplex (R := X.A) L M, L) ⟶ M)
      (m : (coefficientTotalTensor.{u, u, u} X.J X.A).obj
        (homComplex (R := X.A) M N, homComplex (R := X.A) L M) ⟶
          homComplex (R := X.A) L N),
      (∀ (r p k : ℤ) (h : r + p = k) (h' : p + r = k) (U : X.Cᵒᵖ)
        (a : ((homComplex (R := X.A) L M).X r).val.obj U)
        (x : (L.X p).val.obj U),
        (e.f k).val.app U
          (coefficientTensorGenerator.{u, u, u} X.J X.A
            (homComplex (R := X.A) L M) L r p k h U a x) =
          ringedHomSectionApply X L M r p k h' U a x) ∧
      (∀ (s r k p q t : ℤ) (h : s + r = k) (hq : p + r = q)
        (ht : q + s = t) (ht' : p + k = t) (U : X.Cᵒᵖ)
        (a : ((homComplex (R := X.A) M N).X s).val.obj U)
        (b : ((homComplex (R := X.A) L M).X r).val.obj U)
        (x : (L.X p).val.obj U),
        ringedHomSectionApply X L N k p t ht' U
          ((m.f k).val.app U
            (coefficientTensorGenerator.{u, u, u} X.J X.A
              (homComplex (R := X.A) M N) (homComplex (R := X.A) L M)
              s r k h U a b)) x =
          ringedHomSectionApply X M N s q t ht U a
            (ringedHomSectionApply X L M r p q hq U b x))

/-- Evaluation mates for arbitrary small ringed-topos morphisms, on the fixed unbounded
module derived categories. The supplied `AdjointLift` presents Lf*, not an additional
flatness or closed-functor hypothesis.
Source: Stacks 07A4, 08J9, 0A98 and the agent's evaluation-mate coherence calculation
(blueprint: lem-coef-ringed-pullback-hom-evaluation-comparison).

Proof:
1. Use the ringed derived pullback and closed symmetric monoidal theorems to obtain
   F=Lf*, the closed adjunctions and evaluations (`lem-weil-pbc-ringed-topoi-derived-pullback`,
   `lem-sf-ringed-derived-closed-symmetric-monoidal`). The restricted tensor models above
   are the fixed simultaneous K-flat models, with their very same comparison maps.
2. Apply `lem-sfb-ringed-derived-tensor-lift` to the edge of the normalized adjoint lift
   (`lem-sfb-ringed-derived-adjoint-lift`, `def-sfb-ringed-derived-comparison-data`). Its
   inverse tensorator is the canonical comparison of
   `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`, so c respects associators.
3. Define beta=transpose(c followed by F(evaluation)). Inverse transposition gives
   evaluation after beta tensor identity equal to c followed by F(evaluation).
4. Untranspose the two naturality composites. Evaluation naturality and naturality of c
   reduce both to c followed by F((identity tensor a) followed by evaluation followed by b).
   Injectivity of transposition proves naturality, contravariantly in the first input.
5. For t:T tensor P to Q, untranspose F(transpose(t)) followed by beta. Naturality of c
   and inverse transposition give c followed by F(t), proving the transposition equation.
6. Internal composition is the recorded transpose of two evaluations and the associator.
7. Untranspose the composition identity. Substitute step 3 twice and use step 2; both
   sides become iterated pulled-back evaluation with the same canonical associator.
8. On Hom product projections and total-tensor summands evaluation sends h tensor x to
   h(x), and composition sends g tensor h to gh. Expand d(h)=d h-(-1)^r h d to get
   (dh)(x)+(-1)^r h(dx)=d(h(x)) and d(gh)=(dg)h+(-1)^s g(dh).
   The actual signed complexes (`def-pur-hom-complex`, `def-pc-tensor-complex-sheaves`)
   therefore give the representative chain maps. The componentwise uncurrying equation
   in `lem-sf-ringed-derived-tensor-hom-adjunction` identifies their evaluations with the
   fixed closed evaluations. K-flat resolutions (`lem-pc-kflat-resolution`) of the Hom
   factors and the fixed Hom localization (`def-pur-derived-internal-hom`) identify the
   iterated evaluations with derived composition. No inverse of beta is used. -/
theorem ringedPullbackHomEvaluationComparison {X Y : Site.{u, w}} {f : Morphism X Y}
    (l : AdjointLift f) :
    (∀ (P P' Q Q' : Y.D) (a : P' ⟶ P) (b : Q ⟶ Q'),
      l.edge.left.map ((pullbackHomFunctor Y).map (Prod.mkHom a.op b)) ≫
          ringedPullbackHomComparison l P' Q' =
        ringedPullbackHomComparison l P Q ≫
          (pullbackHomFunctor X).map
            (Prod.mkHom (l.edge.left.map a).op (l.edge.left.map b))) ∧
    (∀ P Q : Y.D,
      X.closed.tensor.map
          (X := (l.edge.left.obj ((pullbackHomFunctor Y).obj (op P, Q)), l.edge.left.obj P))
          (Y := ((pullbackHomFunctor X).obj (op (l.edge.left.obj P), l.edge.left.obj Q),
            l.edge.left.obj P))
          (Prod.mkHom (ringedPullbackHomComparison l P Q) (𝟙 (l.edge.left.obj P))) ≫
          X.closed.evaluation (l.edge.left.obj P) (l.edge.left.obj Q) =
        pullbackHomTensorator l ((pullbackHomFunctor Y).obj (op P, Q)) P ≫
          l.edge.left.map (Y.closed.evaluation P Q)) ∧
    (∀ (T P Q : Y.D) (t : Y.closed.tensor.obj (T, P) ⟶ Q),
      l.edge.left.map (Y.closed.transpose T P Q t) ≫ ringedPullbackHomComparison l P Q =
        X.closed.transpose (l.edge.left.obj T) (l.edge.left.obj P) (l.edge.left.obj Q)
          (pullbackHomTensorator l T P ≫ l.edge.left.map t)) ∧
    (∀ P Q T : Y.D,
      pullbackHomTensorator l ((pullbackHomFunctor Y).obj (op Q, T))
          ((pullbackHomFunctor Y).obj (op P, Q)) ≫
          l.edge.left.map (Y.closed.composition P Q T) ≫
          ringedPullbackHomComparison l P T =
        X.closed.tensor.map
          (X := (l.edge.left.obj ((pullbackHomFunctor Y).obj (op Q, T)),
            l.edge.left.obj ((pullbackHomFunctor Y).obj (op P, Q))))
          (Y := ((pullbackHomFunctor X).obj (op (l.edge.left.obj Q), l.edge.left.obj T),
            (pullbackHomFunctor X).obj (op (l.edge.left.obj P), l.edge.left.obj Q)))
          (Prod.mkHom (ringedPullbackHomComparison l Q T) (ringedPullbackHomComparison l P Q)) ≫
          X.closed.composition (l.edge.left.obj P) (l.edge.left.obj Q) (l.edge.left.obj T)) ∧
    RingedHomSignedRepresentatives X ∧ RingedHomSignedRepresentatives Y := by
  sorry

end CategoryTheory.RingedDerivedComparisons
