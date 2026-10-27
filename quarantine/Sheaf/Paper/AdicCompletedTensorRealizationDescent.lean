/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q159
-/
module

public import Sheaf.Paper.NativeAdicFiniteNormalization
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Paper.CompletedCondensedCoefficients
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.Paper.IntegralOperationsPreserveConstructible
import Sheaf.Paper.CompletedPrimitiveCounitComparison
import Sheaf.Paper.NormalizedDVREffectivity
import Sheaf.Paper.NormalizedTensorConstraintTransport
import Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence
import Sheaf.Paper.IntegralAmbientOperationModels
import Sheaf.SixFunctors.RingedDerivedMonoidalComparisons
import Sheaf.Paper.IntegralOperationsScalarComparisons
import Sheaf.Paper.FiniteFreeCompletedScalarComparison
import Sheaf.Paper.ScalarExtensionTowerCoherence
import Sheaf.CategoryTheory.ScalarLocalizationMonoidal

/-! # Descent of the normalized completed tensor through realization

Source: Bhatt--Scholze, Definition 3.4.10 and Remark 6.8.15;
Hemo--Richarz--Scholbach, Lemma 7.9; the specified quotient-augmentation argument
(blueprint: lem-sf-adic-completed-tensor-realization-descent).

The finite comparison uses the published ordinary-to-completed tensor map, including
its zero shifted Roos coordinate. The common-stage comparison is normalized at every
finite field. No internal-Hom invertibility assertion is included in this tensor result.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false

attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
namespace WeilConjectures.AdicQbarRealization
variable (l : ℕ) [Fact l.Prime] (X : Scheme.{u})

/-- The tensor part of realization descent: ordinary K-flat tensor models and the
actual completed common-stage constraints. The ambient coherence fixes reassociation,
both coefficient actions and Koszul symmetry on total complexes, so these equations
compare the specified constraints, including re-resolved inner tensor expressions.
Source: BS Definition 3.4.10, Remark 6.8.15; HRS Lemma 7.9
(blueprint: lem-sf-adic-completed-tensor-realization-descent). -/
structure CompletedTensorRealization (R : LocallyFiniteAdicRealization.Realization l X)
    [∀ x : X, Invertible (l : X.residueField x)] where
  closed : CoefficientClosedStructure (ambientHom l X R)
  models : CoefficientTensorModels.{u + 1, u + 1, u} (ProEt.topology X) (ring l X R) closed
  symmetry : @SymmetricCategory _ _ closed.monoidal
  coherence : RingedDerivedTensorCoherence.{u + 1, u, u + 1}
    (ProEt.topology X) (ring l X R) closed models symmetry
  tensor : ((ordinary l X R).prod (ordinary l X R)) ⋙ closed.tensor ≅
    commonStageDerivedTensor l (PadicAlgCl l) X ⋙ ordinary l X R
  unit : closed.monoidal.tensorUnit ≅
    (ordinary l X R).obj (pullbackTensorCommonUnit l (PadicAlgCl l) X)
  associative : ∀ A B C : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) X,
    closed.tensor.map (Prod.mkHom (tensor.hom.app (A, B)) (𝟙 _)) ≫
        tensor.hom.app ((commonStageDerivedTensor l (PadicAlgCl l) X).obj (A, B), C) ≫
        (ordinary l X R).map (pullbackTensorCommonAssociator l (PadicAlgCl l) X A B C).hom =
      (closed.monoidal.associator ((ordinary l X R).obj A) ((ordinary l X R).obj B)
        ((ordinary l X R).obj C)).hom ≫
        closed.tensor.map (Prod.mkHom (𝟙 _) (tensor.hom.app (B, C))) ≫
        tensor.hom.app (A, (commonStageDerivedTensor l (PadicAlgCl l) X).obj (B, C))
  left_unit : ∀ A : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) X,
    closed.tensor.map (Prod.mkHom unit.hom (𝟙 _)) ≫
        tensor.hom.app (pullbackTensorCommonUnit l (PadicAlgCl l) X, A) ≫
        (ordinary l X R).map (pullbackTensorCommonLeftUnitor l (PadicAlgCl l) X A).hom =
      (closed.monoidal.leftUnitor ((ordinary l X R).obj A)).hom
  right_unit : ∀ A : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) X,
    closed.tensor.map (Prod.mkHom (𝟙 _) unit.hom) ≫
        tensor.hom.app (A, pullbackTensorCommonUnit l (PadicAlgCl l) X) ≫
        (ordinary l X R).map (pullbackTensorCommonRightUnitor l (PadicAlgCl l) X A).hom =
      (closed.monoidal.rightUnitor ((ordinary l X R).obj A)).hom
  symmetric : ∀ A B : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) X,
    tensor.hom.app (A, B) ≫
        (ordinary l X R).map (pullbackTensorCommonBraiding l (PadicAlgCl l) X A B).hom =
      (symmetry.braiding ((ordinary l X R).obj A) ((ordinary l X R).obj B)).hom ≫
        tensor.hom.app (B, A)

/-- The published raw localization at a finite field, followed by its actual
common-stage inclusion. This is a composite of existing functors, not a new category.
Source: BS Remark 6.8.15
(blueprint: lem-sf-adic-completed-tensor-realization-descent). -/
def tensorStage (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l)) :
    sfIntegralConstructibleCategory l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X ⥤
    generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) X :=
  sfRationalConstructibleLocalization l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X ⋙
    GeneralAlgebraicallyClosedCoefficients.inclusion
      (l := l) (Ω := PadicAlgCl l) (Y := X) E

/-- The recorded object equality between rational tensor on integral objects and
localization of their completed tensor. All maps are the existing operations.
Source: BS Definition 3.4.10 and Remark 6.8.15
(blueprint: lem-sf-adic-completed-tensor-realization-descent). -/
def tensorIntegralObjectIso [∀ x : X, Invertible (l : X.residueField x)]
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (K L : sfIntegralConstructibleCategory l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X) :
    (rationalDerivedTensor l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X).obj
      ((sfRationalConstructibleLocalization l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X).obj K,
       (sfRationalConstructibleLocalization l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X).obj L) ≅
    (sfRationalConstructibleLocalization l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X).obj
      ((constructibleIntegralTensor l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X).obj (K, L)) :=
  eqToIso ((rationalDerivedTensor_existsUnique l
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X).exists.choose_spec.1
    ((sfRationalConstructibleLocalization l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X).obj K,
     (sfRationalConstructibleLocalization l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X).obj L))

/-- Invert precisely the recorded quotient-completion map on constructible pairs.
The four normalization clauses in the presentation fix its entire chain representative.
Source: BS Definition 3.4.10 and Lemma 6.5.5
(blueprint: lem-sf-adic-completed-tensor-realization-descent). -/
def tensorQuotientIso
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (C : ConstructibleTensorCompletionPresentation l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X)
    (K L : sfIntegralConstructibleCategory l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X) :
    C.tensor.obj (K.obj, L.obj) ≅
    (integralCompletedTensor l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X).obj
      (K.obj, L.obj) :=
  @asIso _ _ _ _ (C.comparison.app (K.obj, L.obj))
    (C.normalized.2.2.2 K.obj L.obj K.property L.property).2

/-- The representative normalization equation for tensor descent, using the existing
balanced scalar, completion and stage comparisons.
Source: BS Definition 3.4.10, Remark 6.8.15; HRS Lemma 7.9
(blueprint: lem-sf-adic-completed-tensor-realization-descent). -/
def tensorDescentFiniteBalanceSections (R : LocallyFiniteAdicRealization.Realization l X)
    [∀ x : X, Invertible (l : X.residueField x)] (_A : CompletedTensorRealization l X R)
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (balance : constructibleTensorTotal l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X ⋙
        integralComplex l X R E ≅
    ((integralComplex l X R E).prod (integralComplex l X R E)) ⋙
      coefficientTotalTensor.{u + 1, u + 1, u} (ProEt.topology X) (ring l X R)) : Prop :=
  ∀ (P Q : CochainComplex (integralTowerModules l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X) ℤ)
      (p q : ℤ) (U : X.ProEtᵒᵖ) (s : (ring l X R).obj.obj U)
      (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U),
    ((balance.hom.app (P, Q)).f (p + q)).val.app U
      (pbcTensorSection (coefficientMap l X R E)
        (((constructibleTensorTotal l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X).obj
            (P, Q)).X (p + q)) U s
        (constructibleTensorTotalSection l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X P Q p q U x y)) =
      coefficientTensorGenerator.{u + 1, u + 1, u} (ProEt.topology X) (ring l X R)
        ((integralComplex l X R E).obj P) ((integralComplex l X R E).obj Q)
        p q (p + q) rfl U
        (pbcTensorSection (coefficientMap l X R E) (P.X p) U s x)
        (pbcTensorSection (coefficientMap l X R E) (Q.X q) U 1 y)

/-- The representative normalization equation for tensor descent, using the existing
balanced scalar, completion and stage comparisons.
Source: BS Definition 3.4.10, Remark 6.8.15; HRS Lemma 7.9
(blueprint: lem-sf-adic-completed-tensor-realization-descent). -/
def tensorDescentFiniteRepresentative (R : LocallyFiniteAdicRealization.Realization l X)
    [∀ x : X, Invertible (l : X.residueField x)] (A : CompletedTensorRealization l X R)
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (completion : ConstructibleTensorCompletionPresentation l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X)
    (balance : constructibleTensorTotal l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X ⋙
        integralComplex l X R E ≅
    ((integralComplex l X R E).prod (integralComplex l X R E)) ⋙
      coefficientTotalTensor.{u + 1, u + 1, u} (ProEt.topology X) (ring l X R))
    (kflat : ∀ P : (integralOperationsGoodComplex l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X).FullSubcategory,
    CochainComplex.IsKFlatIndependentCoefficients (J := ProEt.topology X) (R := ring l X R)
      ((integralComplex l X R E).obj P.obj))
    (ordinary : completion.tensor ⋙ pbcDerivedExtend (coefficientMap l X R E) ≅
    ((pbcDerivedExtend (coefficientMap l X R E)).prod
      (pbcDerivedExtend (coefficientMap l X R E))) ⋙ A.closed.tensor) : Prop :=
  ∀ P Q : (integralOperationsGoodComplex l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X).FullSubcategory,
    (pbcDerivedExtend (coefficientMap l X R E)).map
        (completion.model.hom.app (P, Q)) ≫
      ordinary.hom.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) ≫
      A.closed.tensor.map (Prod.mkHom
        (pbcComplexCounit (coefficientMap l X R E) P.obj)
        (pbcComplexCounit (coefficientMap l X R E) Q.obj)) =
    pbcComplexCounit (coefficientMap l X R E)
        ((constructibleTensorTotal l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X).obj
            (P.obj, Q.obj)) ≫
      DerivedCategory.Q.map (balance.hom.app (P.obj, Q.obj)) ≫
      (A.models.iso _ _ _ _ _ (kflat P) (kflat Q)).hom

/-- The representative normalization equation for tensor descent, using the existing
balanced scalar, completion and stage comparisons.
Source: BS Definition 3.4.10, Remark 6.8.15; HRS Lemma 7.9
(blueprint: lem-sf-adic-completed-tensor-realization-descent). -/
def tensorDescentFiniteTensorAgreement (R : LocallyFiniteAdicRealization.Realization l X)
    [∀ x : X, Invertible (l : X.residueField x)] (A : CompletedTensorRealization l X R)
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (completion : ConstructibleTensorCompletionPresentation l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X)
    (comparison : completion.tensor ⋙ pbcDerivedExtend (coefficientMap l X R E) ≅
      ((pbcDerivedExtend (coefficientMap l X R E)).prod
        (pbcDerivedExtend (coefficientMap l X R E))) ⋙ A.closed.tensor) : Prop :=
  ∀ K L : sfIntegralConstructibleCategory l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X,
    HEq (A.tensor.hom.app ((tensorStage l X E).obj K, (tensorStage l X E).obj L))
    (A.closed.tensor.map (Prod.mkHom ((R.integral E).hom.app K) ((R.integral E).hom.app L)) ≫
      comparison.inv.app (K.obj, L.obj) ≫
      (pbcDerivedExtend (coefficientMap l X R E)).map (tensorQuotientIso l X E completion K L).hom ≫
      (R.integral E).inv.app ((constructibleIntegralTensor l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X).obj (K, L)) ≫
      (AdicQbarRealization.ordinary l X R).map ((GeneralAlgebraicallyClosedCoefficients.inclusion
        (l := l) (Ω := PadicAlgCl l) (Y := X) E).map (tensorIntegralObjectIso l X E K L).inv) ≫
      (AdicQbarRealization.ordinary l X R).map
        (stageTensor l X (PadicAlgCl l) E
          ((sfRationalConstructibleLocalization l
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X).obj K)
          ((sfRationalConstructibleLocalization l
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X).obj L)).hom)

/-- Finite-stage normalization of the descended tensorator. The ordinary comparison
is fixed by balanced pure sections and its derived K-flat counit equation; the final
field says mu is balanced multiplication followed by J(chi), transported by the
specified integral realization and common-stage inclusion tensorator.
Source: BS Definition 3.4.10, Remark 6.8.15; HRS Lemma 7.9
(blueprint: lem-sf-adic-completed-tensor-realization-descent). -/
structure CompletedTensorFiniteNormalization (R : LocallyFiniteAdicRealization.Realization l X)
    [∀ x : X, Invertible (l : X.residueField x)] (A : CompletedTensorRealization l X R)
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l)) where
  completion : ConstructibleTensorCompletionPresentation l
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X
  balance : constructibleTensorTotal l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X ⋙
        integralComplex l X R E ≅
    ((integralComplex l X R E).prod (integralComplex l X R E)) ⋙
      coefficientTotalTensor.{u + 1, u + 1, u} (ProEt.topology X) (ring l X R)
  balance_sections : tensorDescentFiniteBalanceSections l X R A E balance
  kflat : ∀ P : (integralOperationsGoodComplex l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X).FullSubcategory,
    CochainComplex.IsKFlatIndependentCoefficients (J := ProEt.topology X) (R := ring l X R)
      ((integralComplex l X R E).obj P.obj)
  ordinary : completion.tensor ⋙ pbcDerivedExtend (coefficientMap l X R E) ≅
    ((pbcDerivedExtend (coefficientMap l X R E)).prod
      (pbcDerivedExtend (coefficientMap l X R E))) ⋙ A.closed.tensor
  representative : tensorDescentFiniteRepresentative l X R A E completion balance kflat ordinary
  integral_tensor : tensorDescentFiniteTensorAgreement l X R A E completion ordinary

/-- The common-stage tensorator with its finite representative normalization.
The common tensorator is natural on the actual Hom colimit; normalization at every
finite field identifies its components with balanced multiplication followed by the
specified completion comparison, using the fixed integral and inclusion comparisons.
Source: BS Remark 6.8.15; HRS Lemma 7.9
(blueprint: lem-sf-adic-completed-tensor-realization-descent). -/
structure CompletedTensorRealizationDescent (R : LocallyFiniteAdicRealization.Realization l X)
    where
  [units : ∀ x : X, Invertible (l : X.residueField x)]
  common : CompletedTensorRealization l X R
  normalization : ∀ E, CompletedTensorFiniteNormalization l X R common E

/-- Specified completed tensor comparisons descend through raw rationalization and
common finite fields to the symmetric strong monoidal continuous realization.
The closure is the fixed PadicAlgCl model of the source's chosen algebraic closure;
all finite fields occur through the existing Index and Coefficient presentations.
Source: BS Definition 3.4.10 and Remark 6.8.15; HRS Lemma 7.9
(blueprint: lem-sf-adic-completed-tensor-realization-descent).

Proof:
1. The finite-realization cocone identifies the integral constructible categories,
reductions and rationalizations. For the same representatives apply
lem-fix-constructible-tensor-completion: chi is the natural quotient augmentation,
with zero shifted Roos coordinate, and is invertible on constructible pairs.
Ordinary derived scalar extension is monoidal by
lem-weil-pbc-ringed-topoi-derived-tensor-pullback and
lem-pur-cochain-pullback-tensor-coherence. Its balanced multiplication followed by
J(chi) is mu. Constructibility follows from
lem-pur-integral-operations-preserve-constructible.
2. Apply lem-pur-completed-primitive-counit-comparison and
lem-coef-normalized-dvr-effectivity to the normalized coherent reductions.
lem-pur-normalized-tensor-constraint-transport compares the entire systems by beta
and gamma, for reassociation, both action unitors and signed swap. These same
comparisons cover iterated tensors with re-resolved inner expressions.
3. lem-pur-integral-ambient-operation-models identifies chi with the actual quotient
augmentation. The squares are therefore the whole-system balanced total-complex
squares, not unrelated levelwise isomorphisms. Apply
lem-sfb-ringed-derived-monoidal-comparisons to obtain the four constraint equations.
4. For E contained in F, insert the specified inverse completion comparison from
lem-weil-finite-free-completed-scalar-comparison and use
lem-pur-integral-operations-scalar-extension. By
lem-pur-scalar-extension-tower-coherence its tensor square is the strict balanced
quotient-tower square. Both routes multiply the same coefficient scalars, including
identity extensions, ramification and successive field extensions. The ordinary
scalar-composition maps are monoidal, including their unit normalization.
5. Localize the integral Hom modules using def-weil-rationalization-karoubi and
lem-sf-scalar-localization-monoidal. Pure rational arrows multiply coefficients;
both naturality routes are ab times the integral square. Additivity and balancing
give all rational arrows, and the inverse comparisons descend too.
6. For two common-stage objects choose one finite field containing both stages.
Extend its tensorator to the native coefficient sheaf and conjugate by the fixed
integral/scalar and inclusion comparisons. Step 4 identifies this map after any
further extension; two choices agree at a common further field. Do the same for
arrows and inverse components. Thus the result is natural and independent of every
object-stage and arrow representative in the actual Hom colimit.
7. Every constraint diagram uses finitely many objects and arrows, hence is represented
at one finite field. Steps 3--5 make it commute there, so it commutes after extension.
Naturality includes the fixed finite scalar comparisons and their identity/tower
maps. On the coefficient unit the map is multiplication r tensor e to re; its inverse
inserts one. The two unitor equations with the fixed tensorator characterize this
unit comparison uniquely. -/
theorem adic_completed_tensor_realization_descent
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (T : Over (Spec (CommRingCat.of D.k)))
    [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] [IsSeparated T.hom]
    (R : LocallyFiniteAdicRealization.Realization l T.left) :
    Nonempty (CompletedTensorRealizationDescent l T.left R) := by
  sorry

end WeilConjectures.AdicQbarRealization
