/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q55
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.IntegralScalarExtensionUniverses
public import Sheaf.Algebra.Homology.KFlat
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Algebra.Homology.ChangeOfRingsKFlat
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import Mathlib.Algebra.Homology.BifunctorShift
public import Sheaf.Paper.NormalizedDVRTower
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.Paper.SfDerivedComplete
public import Sheaf.Paper.CoefficientExtensionReductionModel
public import Sheaf.Paper.IntegralComparisonRealizationModels
public import Sheaf.Paper.IntegralOperationsScalarComparisons
public import Sheaf.Paper.CompletedOperationTowerSubstitution
public import Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence
import all Sheaf.Paper.ScalarExtensionTensorUnit
import Sheaf.Paper.ScalarExtensionQuotientAssociation
import all Sheaf.Paper.CoefficientExtensionOrdinaryStrictTensor
import Sheaf.Paper.TensorPullbackRepresentativeDescent
import Sheaf.Paper.ResolvingRepresentativeWhiskering
import Sheaf.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses

public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Paper.ScalarExtensionTowerComparisonData
public import Sheaf.Paper.ScalarExtensionTowerComposition
import all Sheaf.Paper.ScalarExtensionTowerComparisonData

/-! # Scalar extension on strict quotient models

Source: main-20261015 blueprint, def-weil-derived-pullback-tensor-hom, integral operations;
Stacks Tags 03EL and 07A4 (blueprint: lem-pur-scalar-extension-tower-coherence).

## Main definitions

* `Comparisons`: the pure-tensor-normalized comparisons on whole quotient systems.
* `TensorModel`: the representative-normalized completed tensor realization.

## Main statements

* `square`, `unit`, `composition`: strict tower coherence before localization.
* `quotientModels`: the actual quotient representatives and their association formula.
* `scalarExtensionTowerCoherence`: their identification with the canonical integral maps.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option genSizeOf false
set_option genCtorIdx false
set_option genInjectivity false
set_option genSizeOfSpec false
attribute [local irreducible] CategoryTheory.Functor.leftAdjoint
  CategoryTheory.Functor.mapDerivedCategory
  WeilConjectures.coefficientTotalTensor
  SheafOfModules.monoidalCategory
  WeilConjectures.coefficientSequenceCommRingSheaf
  WeilConjectures.coefficientSequenceCommRingPresheaf
  WeilConjectures.integralComparisonSequenceScalarModel
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [-instance] WeilConjectures.coefficientSequenceEssentiallySmall
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped ChangeOfRings
namespace WeilConjectures.ScalarExtensionTower

variable (l : ℕ) [Fact l.Prime]
variable (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

attribute [local irreducible] scalar_adj comparisons
  integralComparisonSequenceTensorSection integralComparisonSequenceScalarUnit

set_option maxHeartbeats 800000 in
-- Check all three normalized maps on homogeneous tensor generators.
/-- Equality before localization, hence for both directions and all quotient transitions.
Source: blueprint integral operations; Stacks 03EL, 07A4
(blueprint: lem-pur-scalar-extension-tower-coherence).
Proof: expand the specified scalar association and the two tensor comparisons on
b tensor (x tensor y). Both composites give (b tensor x) tensor (1 tensor y).
The coefficient square commutes on constant sections, hence after sheafification.
Balancing extends the equality to arbitrary scalars in either factor. Homogeneous
tensors generate each summand and the direct sum total, proving equality of chain
maps. Their inverses are equal because the two maps are isomorphisms. Every map
is a sequence-site module map, so this equality and its inverse retain every
horizontal quotient transition, as well as vertical restrictions. -/
theorem square {X Y : Scheme.{u}} (f : X ⟶ Y) :
    leftRoute l E L ι f = rightRoute l E L ι f := by
  apply Iso.ext
  apply NatTrans.ext
  funext Z
  rcases Z with ⟨P, Q⟩
  apply HomologicalComplex.hom_ext
  intro n
  apply ((scalar_adj l E L ι X).homEquiv _ _).injective
  apply ((Adjunction.ofIsRightAdjoint
    (integralComparisonSequenceDirectImage.{u, u} l E f)).homEquiv _ _).injective
  apply WeilConjectures.total_tensor_sections_ext l E Y P Q n
  intro p q hpq V
  rcases V with ⟨m, U⟩
  intro x y
  subst n
  change
    (((scalar_adj l E L ι X).homEquiv _ _)
      (((leftRoute l E L ι f).hom.app (P, Q)).f (p + q))).val.app
        (op (m, (Scheme.proEtaleBaseChange f).obj U))
        (pullSection l E f _ m U (generator l E Y P Q p q (op (m, U)) x y)) =
    (((scalar_adj l E L ι X).homEquiv _ _)
      (((rightRoute l E L ι f).hom.app (P, Q)).f (p + q))).val.app
        (op (m, (Scheme.proEtaleBaseChange f).obj U))
        (pullSection l E f _ m U (generator l E Y P Q p q (op (m, U)) x y))
  refine (scalar_transpose_section l E L ι X
    ((integralComparisonSequencePullback.{u, u} l E f).obj
      (((tensor l E Y).obj (P, Q)).X (p + q))) _ _
    (op (m, (Scheme.proEtaleBaseChange f).obj U))
    (pullSection l E f _ m U (generator l E Y P Q p q (op (m, U)) x y))).trans ?_
  refine Eq.trans ?_ (scalar_transpose_section l E L ι X
    ((integralComparisonSequencePullback.{u, u} l E f).obj
      (((tensor l E Y).obj (P, Q)).X (p + q))) _ _
    (op (m, (Scheme.proEtaleBaseChange f).obj U))
    (pullSection l E f _ m U (generator l E Y P Q p q (op (m, U)) x y))).symm
  simp only [leftRoute, rightRoute, leftRouteCore, rightRouteCore, Iso.trans_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, NatTrans.comp_app,
    HomologicalComplex.comp_f,
    SheafOfModules.comp_val,
    PresheafOfModules.comp_app, ModuleCat.comp_apply]
  erw [scalar_pull_section l E L ι f
    (((tensor l E Y).obj (P, Q)).X (p + q)) m U
    (generator l E Y P Q p q (op (m, U)) x y)]
  erw [pull_section_naturality l L f
    ((((comparisons l).sigma E L ι Y).hom.app (P, Q)).f (p + q))]
  erw [(comparisons l).sigma_formula E L ι Y P Q p q (op (m, U)) 1 x y]
  erw [pull_tensor_section l L f ((scalar l E L ι Y).obj P)
    ((scalar l E L ι Y).obj Q) p q m U]
  erw [scalar_section_naturality l E L ι X
    ((((comparisons l).c E f).hom.app (P, Q)).f (p + q))]
  erw [pull_tensor_section l E f P Q p q m U x y]
  erw [(comparisons l).sigma_formula E L ι X
    ((pull l E f).obj P) ((pull l E f).obj Q) p q
    (op (m, (Scheme.proEtaleBaseChange f).obj U)) 1
    (pullSection l E f (P.X p) m U x) (pullSection l E f (Q.X q) m U y)]
  erw [WeilConjectures.generator_map]
  erw [scalar_pull_section l E L ι f (P.X p) m U x,
    scalar_pull_section l E L ι f (Q.X q) m U y]
  rfl

/-- Identity extension is the identity under the actual scalar action unitors.
Source: node proof step 7; Stacks 03EL
(blueprint: lem-pur-scalar-extension-tower-coherence).
Proof: at identity coefficients the scalar-association map multiplies the inserted
coefficient, exactly the action unitor. On x tensor y the tensor comparison inserts
one in the second factor. Applying the two action unitors gives x tensor y again.
These formulas commute with every quotient and restriction, giving the displayed
identities as strict-system equations. -/
theorem unit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    UnitSquare (pull l E f) (scalar l E E (AlgHom.id ℚ_[l] E) Y)
      (scalar l E E (AlgHom.id ℚ_[l] E) X) (kappa l E E (AlgHom.id ℚ_[l] E) f)
      (scalarUnit l E Y) (scalarUnit l E X) ∧
    TensorUnitSquare (tensor l E Y) (scalar l E E (AlgHom.id ℚ_[l] E) Y)
      ((comparisons l).sigma E E (AlgHom.id ℚ_[l] E) Y) (scalarUnit l E Y) := by
  unfold UnitSquare TensorUnitSquare
  constructor
  · exact map_unit_square _ _ _ _ _ _ (scalar_pull_unit l E f)
  · exact scalarExtensionTensorUnit l E Y
      ((comparisons l).sigma E E (AlgHom.id ℚ_[l] E) Y)
      (fun P Q p q V x y ↦
        (comparisons l).sigma_formula E E (AlgHom.id ℚ_[l] E) Y P Q p q V 1 x y)

/-- A generator read in the legacy restricted finite-tensor tower's exact section type.
Source: Stacks 07A4 (blueprint: lem-pur-scalar-extension-tower-coherence). -/
def integralTensorGenerator (W : Scheme.{u})
    (P Q : CochainComplex (integralTowerModules.{u, u} l E W) ℤ)
    (n : ℕ) (p r : ℤ) (U : W.ProEtᵒᵖ)
    (x : (((unrestrictedIntegralFiniteComplex.{u, u} l E W n).obj P).X p).val.obj U)
    (y : (((unrestrictedIntegralFiniteComplex.{u, u} l E W n).obj Q).X r).val.obj U) :
    ((((integralOperationsTensorTowerFunctor.{u, u} l E W).obj (P, Q)).obj
      (op n)).X (p + r)).val.obj U :=
  integralOperationsTotalTensorSection.{u, u} l E W n P Q p r U x y

/-- Representative normalization of the completed tensor realization, including its
local tensor formula and its specified Roos comparison.
Source: Stacks 06YS, 07A4, 0941 (blueprint: lem-pur-scalar-extension-tower-coherence). -/
def IsTensorModelNormalized (W : Scheme.{u})
    (S : CoefficientDerivedSystemCalculus.{u, u} l E W)
    (ρ : IntegralComparisonRoosModel.{u, u} l E W)
    (realization : integralCompletedTensor.{u, u} l E W ≅ S.reduction.prod S.reduction ⋙
      S.systemClosed.tensor ⋙ coefficientSequenceLimit.{u, u} l E W) : Prop :=
  ∀ (P Q : (integralOperationsGoodComplex.{u, u} l E W).FullSubcategory)
    (C D : Complex l E W)
    (eC : S.reduction.obj (DerivedCategory.Q.obj P.obj) ≅ DerivedCategory.Q.obj C)
    (eD : S.reduction.obj (DerivedCategory.Q.obj Q.obj) ≅ DerivedCategory.Q.obj D)
    (κC : ∀ n : ℕ,
      ((coefficientSequenceEvaluation.{u, u} l E W n).mapHomologicalComplex (.up ℤ)).obj C ≅
        (unrestrictedIntegralFiniteComplex.{u, u} l E W n).obj P.obj)
    (κD : ∀ n : ℕ,
      ((coefficientSequenceEvaluation.{u, u} l E W n).mapHomologicalComplex (.up ℤ)).obj D ≅
        (unrestrictedIntegralFiniteComplex.{u, u} l E W n).obj Q.obj)
    (hC : CochainComplex.IsKFlatIndependentCoefficients
      (R := coefficientSequenceCommRingSheaf.{u, u} l E W) C)
    (hD : CochainComplex.IsKFlatIndependentCoefficients
      (R := coefficientSequenceCommRingSheaf.{u, u} l E W) D),
    CoefficientReductionPresentation.{u, u} l E W S.toCoefficientDerivedSystemReduction
      P.obj P.property.1 C eC κC →
    CoefficientReductionPresentation.{u, u} l E W S.toCoefficientDerivedSystemReduction
      Q.obj Q.property.1 D eD κD →
    ∃ q : (((coefficientSequenceRestriction.{u, u} l E W).mapHomologicalComplex (.up ℤ)).obj
        ((tensor l E W).obj (C, D))).asFunctor ≅
      (integralOperationsTensorTowerFunctor.{u, u} l E W).obj (P.obj, Q.obj),
      (∀ (n : ℕ) (p r : ℤ) (U : W.ProEtᵒᵖ)
        (x : (C.X p).val.obj (op (n, U.unop)))
        (y : (D.X r).val.obj (op (n, U.unop))),
        ((q.hom.app (op n)).f (p + r)).val.app U
          (integralComparisonRestrictedSection.{u, u} l E W
            (((tensor l E W).obj (C, D)).X (p + r)) n U
            (generator l E W C D p r (op (n, U.unop)) x y)) =
          integralTensorGenerator l E W P.obj Q.obj n p r U
            (((κC n).hom.f p).val.app U (coefficientEvaluationSection.{u, u} l E W (C.X p) n U x))
            (((κD n).hom.f r).val.app U
              (coefficientEvaluationSection.{u, u} l E W (D.X r) n U y))) ∧
      FiveStepEquation
        (realization.hom.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj))
        ((coefficientSequenceLimit.{u, u} l E W).map
          (S.systemClosed.tensor.map (Prod.mkHom eC.hom eD.hom)))
        ((coefficientSequenceLimit.{u, u} l E W).map
          ((S.systemTensorModel.iso _ _ _ C D hC hD).inv))
        ((integralComparisonRoosBridge.{u, u} l E W ρ
          ((tensor l E W).obj (C, D))).hom)
        (DerivedCategory.Q.map (integralOperationsRoosFunctor.map q.hom))
        ((integralCompletedTensorComparison.{u, u} l E W).hom.app (P, Q))


attribute [local irreducible] IsTensorModelNormalized

/-- A normalized presentation of the named completed tensor by whole quotient systems.
Source: node proof steps 1, 4, 8; Stacks 06YS, 07A4 and 0941
(blueprint: lem-pur-scalar-extension-tower-coherence). -/
structure TensorModel (W : Scheme.{u})
    (S : CoefficientDerivedSystemCalculus.{u, u} l E W)
    (ρ : IntegralComparisonRoosModel.{u, u} l E W) where
  /-- The named completed tensor, realized by the specified system closed tensor. -/
  realization : integralCompletedTensor.{u, u} l E W ≅ S.reduction.prod S.reduction ⋙
    S.systemClosed.tensor ⋙ coefficientSequenceLimit.{u, u} l E W
  /-- Normalization at every simultaneous good quotient presentation. -/
  normalization : IsTensorModelNormalized l E W S ρ realization

/-- The actual reduction of a completed pullback, followed by the coherent counit.
Source: node proof step 8 (blueprint: lem-pur-scalar-extension-tower-coherence). -/
def pullbackReduction (W : Bool → Scheme.{u}) (M : CompletedOperations.Models.{u, u} l E W)
    (f : W true ⟶ W false) (K : DerivedCategory (scalarReductionSource.{u, u} l E (W false))) :
    (M.calculus true).reduction.obj ((integralDerivedPullback.{u, u} l E f).obj K) ⟶
      (integralComparisonDerivedSequencePullback.{u, u} l E f).obj
        ((M.calculus false).reduction.obj K) :=
  (M.calculus true).reduction.map ((M.pullback f).realization.hom.app K) ≫
    (M.calculus true).adjunction.counit.app _

/-- The actual coherent scalar-reduction comparison, obtained from its normalized
realization and the coherent counit, with no arbitrary quotient identification.
Source: node proof step 8 (blueprint: lem-pur-scalar-extension-tower-coherence). -/
def scalarReduction (W : Scheme.{u})
    (SE : CoefficientDerivedSystemCalculus.{u, u} l E W)
    (SL : CoefficientDerivedSystemCalculus.{u, u} l L W)
    (ρ : IntegralComparisonRoosModel.{u, u} l L W)
    (M : IntegralComparisonScalarModel.{u, u} l E L ι W SE ρ)
    (K : DerivedCategory (scalarReductionSource.{u, u} l E W)) :
    SL.reduction.obj ((integralScalarExtension.{u} l E L ι W).obj K) ⟶
      (integralComparisonDerivedSequenceScalar.{u, u} l E L ι W).obj (SE.reduction.obj K) :=
  SL.reduction.map (M.realization.hom.app K) ≫ SL.adjunction.counit.app _

/-- The completed tensor's actual quotient comparison, followed by the coherent counit.
Source: node proof step 8 (blueprint: lem-pur-scalar-extension-tower-coherence). -/
def tensorReduction (W : Scheme.{u}) (S : CoefficientDerivedSystemCalculus.{u, u} l E W)
    (ρ : IntegralComparisonRoosModel.{u, u} l E W) (M : TensorModel l E W S ρ)
    (K N : DerivedCategory (scalarReductionSource.{u, u} l E W)) :
    S.reduction.obj ((integralCompletedTensor.{u, u} l E W).obj (K, N)) ⟶
      S.systemClosed.tensor.obj (S.reduction.obj K, S.reduction.obj N) :=
  S.reduction.map (M.realization.hom.app (K, N)) ≫ S.adjunction.counit.app _

/-- The flat-term K-flat class used for scalar/tensor descent on the sequence site.
Source: Stacks 06YS, 0G7E (blueprint: lem-pur-scalar-extension-tower-coherence). -/
def Good (W : Scheme.{u}) (P : Complex l E W) : Prop :=
  CochainComplex.IsKFlatIndependentCoefficients
    (R := coefficientSequenceCommRingSheaf.{u, u} l E W) P ∧
  ∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
    (J := coefficientSequenceTopology (Scheme.ProEt.topology W))
    (R := coefficientSequenceCommRingSheaf.{u, u} l E W) (P.X n)

/-- Cochain normalization of the system derived scalar/tensor comparison.
Source: node proof steps 1, 4, 8; Stacks 06YS, 07A4
(blueprint: lem-pur-scalar-extension-tower-coherence). -/
def DerivedSigmaModel (W : Scheme.{u})
    (SE : CoefficientDerivedSystemCalculus.{u, u} l E W)
    (SL : CoefficientDerivedSystemCalculus.{u, u} l L W)
    (α : SE.systemClosed.tensor ⋙ integralComparisonDerivedSequenceScalar.{u, u} l E L ι W ≅
      (integralComparisonDerivedSequenceScalar.{u, u} l E L ι W).prod
        (integralComparisonDerivedSequenceScalar.{u, u} l E L ι W) ⋙ SL.systemClosed.tensor) :
    Prop :=
  ∀ (P Q : Complex l E W) (hP : Good l E W P) (hQ : Good l E W Q),
    ∃ (hsP : Good l L W ((scalar l E L ι W).obj P))
      (hsQ : Good l L W ((scalar l E L ι W).obj Q)),
    (integralComparisonDerivedSequenceScalar.{u, u} l E L ι W).map
        ((SE.systemTensorModel.iso _ _ _ P Q hP.1 hQ.1).hom) ≫
      α.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
      SL.systemClosed.tensor.map (Prod.mkHom
        ((integralComparisonSequenceScalarModel.{u, u} l E L ι W).ε.app P)
        ((integralComparisonSequenceScalarModel.{u, u} l E L ι W).ε.app Q)) =
    (integralComparisonSequenceScalarModel.{u, u} l E L ι W).ε.app
        ((tensor l E W).obj (P, Q)) ≫
      DerivedCategory.Q.map (((comparisons l).sigma E L ι W).hom.app (P, Q)) ≫
      (SL.systemTensorModel.iso _ _ _ _ _ hsP.1 hsQ.1).hom

attribute [local irreducible] DerivedSigmaModel

private theorem scalar_good (W : Scheme.{u}) (P : Complex l E W) (hP : Good l E W P) :
    Good l L W ((scalar l E L ι W).obj P) := by
  unfold Good at hP ⊢
  have h := SheafOfModules.changeOfRings_isKFlat_of_flat_terms_independentCoefficients
    (integralComparisonSequenceScalarMap.{u, u} l E L ι W) P
    (integralComparisonSequenceScalarModel.{u, u} l E L ι W).E
    (integralComparisonSequenceScalarModel.{u, u} l E L ι W).obj_eq
    (integralComparisonSequenceScalarModel.{u, u} l E L ι W).map_eq hP.1
    (fun n ↦ (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso.{u + 1, u, u + 1}
        (coefficientSequenceCommRingSheaf.{u, u} l E W) (P.X n)) (hP.2 n))
  refine ⟨h.1, fun n ↦ ?_⟩
  exact (exactFunctor _ _).prop_of_iso
    (SheafOfModules.siteSheafTensorRightIso.{u + 1, u, u + 1}
      (coefficientSequenceCommRingSheaf.{u, u} l L W)
      (((scalar l E L ι W).obj P).X n)).symm (h.2 n)


set_option maxHeartbeats 800000 in
-- Compare the restricted tensor models and counits simultaneously.

/-- The derived comparison is determined by the same strict sigma on good representatives.
Source: node proof steps 1, 4, 8; Stacks 06YS, 07A4
(blueprint: lem-pur-scalar-extension-tower-coherence).
Proof: flat-term K-flat change of rings works without flatness of the ring map.
It preserves Good and computes scalar derived extension by its universal counit.
Localize sigma on the two resolving subcategories, inserting the normalized tensor
models and scalar counits. Simultaneous K-flat resolutions give naturality on roofs
and independence of resolutions. The localization universal property gives uniqueness
with this cochain model equation. -/
theorem derivedSigma_existsUnique (W : Scheme.{u})
    (SE : CoefficientDerivedSystemCalculus.{u, u} l E W)
    (SL : CoefficientDerivedSystemCalculus.{u, u} l L W) :
    ∃! α : SE.systemClosed.tensor ⋙ integralComparisonDerivedSequenceScalar.{u, u} l E L ι W ≅
      (integralComparisonDerivedSequenceScalar.{u, u} l E L ι W).prod
        (integralComparisonDerivedSequenceScalar.{u, u} l E L ι W) ⋙ SL.systemClosed.tensor,
      DerivedSigmaModel l E L ι W SE SL α := by
  unfold DerivedSigmaModel
  let A := coefficientSequenceModules.{u, u} l E W
  let B := coefficientSequenceModules.{u, u} l L W
  let P : ObjectProperty (CochainComplex A ℤ) := Good l E W
  let S : ObjectProperty (CochainComplex B ℤ) := Good l L W
  let H : ObjectProperty (HomotopyCategory A (.up ℤ)) := fun X ↦ P X.as
  have hres : ∀ X : HomotopyCategory A (.up ℤ),
      ∃ (Y : H.FullSubcategory) (f : Y.obj ⟶ X), HomotopyCategory.quasiIso A (.up ℤ) f := by
    intro X
    obtain ⟨K, f, hK, hflat, hf, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients
        (R := coefficientSequenceCommRingSheaf.{u, u} l E W) X.as
    have hs : ∀ n, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
        (R := coefficientSequenceCommRingSheaf.{u, u} l E W) (K.X n) := fun n ↦
      (exactFunctor _ _).prop_of_iso (SheafOfModules.siteSheafTensorRightIso.{u + 1, u, u + 1}
        (coefficientSequenceCommRingSheaf.{u, u} l E W) (K.X n)).symm (hflat n)
    refine ⟨⟨(HomotopyCategory.quotient A (.up ℤ)).obj K, hK, hs⟩,
      (HomotopyCategory.quotient A (.up ℤ)).map f, ?_⟩
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff f).2 hf
  obtain ⟨ff⟩ := resolvingRepresentativesFullyFaithfulWhiskering (DerivedCategory B)
    (HomotopyCategory.quotient A (.up ℤ)) HomotopyCategory.quotient_obj_surjective
    (HomotopyCategory.quasiIso A (.up ℤ)) DerivedCategory.Qh P H (fun _ ↦ Iff.rfl) hres
  let ff' := ff.ofIso ((Functor.whiskeringLeft _ _ (DerivedCategory B)).mapIso
    (NatIso.prod (Functor.isoWhiskerLeft P.ι (DerivedCategory.quotientCompQhIso A))
      (Functor.isoWhiskerLeft P.ι (DerivedCategory.quotientCompQhIso A))))
  let PE : ObjectProperty (CochainComplex A ℤ) :=
    CochainComplex.IsKFlatIndependentCoefficients
      (R := coefficientSequenceCommRingSheaf.{u, u} l E W)
  let PL : ObjectProperty (CochainComplex B ℤ) :=
    CochainComplex.IsKFlatIndependentCoefficients
      (R := coefficientSequenceCommRingSheaf.{u, u} l L W)
  let iE : P.FullSubcategory ⥤ PE.FullSubcategory :=
    ObjectProperty.lift _ P.ι (fun X ↦ X.property.1)
  let iL : S.FullSubcategory ⥤ PL.FullSubcategory :=
    ObjectProperty.lift _ S.ι (fun X ↦ X.property.1)
  let r := Functor.isoWhiskerLeft (iE.prod iE) SE.systemTensorModel.comparison
  let r' := Functor.isoWhiskerLeft (iL.prod iL) SL.systemTensorModel.comparison
  obtain ⟨α, hα, huniq⟩ := tensorComparisonDescent
    DerivedCategory.Q DerivedCategory.Q (scalar l E L ι W)
    (integralComparisonDerivedSequenceScalar.{u, u} l E L ι W)
    (integralComparisonSequenceScalarModel.{u, u} l E L ι W).ε P S
    (fun X hX ↦ scalar_good l E L ι W X hX) ff' (tensor l E W) (tensor l L W)
    SE.systemClosed.tensor SL.systemClosed.tensor r r'
    ((comparisons l).sigma E L ι W)
    (fun X hX ↦ (integralComparisonSequenceScalarModel.{u, u} l E L ι W).computes X hX.1)
    (fun X Y hX hY ↦ (integralComparisonSequenceScalarModel.{u, u} l E L ι W).computes _
      (coefficientTotalTensor_isKFlat.{u, u + 1, u} _ _ X Y hX.1 hY.1))
  refine ⟨α, ?_, ?_⟩
  · intro X Y hX hY
    exact ⟨scalar_good l E L ι W X hX, scalar_good l E L ι W Y hY, hα X Y hX hY⟩
  · intro β hβ
    apply huniq β
    intro X Y hX hY
    obtain ⟨hX', hY', h⟩ := hβ X Y hX hY
    exact h

/-- The representative-normalized derived tensor scalar comparison on coherent systems.
Source: Stacks 07A4 (blueprint: lem-pur-scalar-extension-tower-coherence). -/
def derivedSigma (W : Scheme.{u})
    (SE : CoefficientDerivedSystemCalculus.{u, u} l E W)
    (SL : CoefficientDerivedSystemCalculus.{u, u} l L W) :=
  (derivedSigma_existsUnique l E L ι W SE SL).exists.choose

attribute [local irreducible] integralScalarExtension integralScalarExtensionOfUniverses
  integralCompletedTensor integralDerivedPullback
  integralComparisonDerivedSequenceScalar integralComparisonDerivedSequencePullback
  pullbackReduction scalarReduction tensorReduction derivedSigma

/-- The normalized realization models exist for the named completed tensor and scalar functors.
Source: node proof step 8; Stacks 06YS, 07A4, 0941
(blueprint: lem-pur-scalar-extension-tower-coherence).
Proof: form the strict quotients of one good representative. For tensor take their
signed total tensor; for scalar use the actual quotient inclusions. K-flat change
of rings and closure under total tensor identify these ordinary complexes with
the derived systems. The coefficient-extension reduction model supplies its
normalized coherent counit. Completed-operation substitution identifies the tensor
limit; scalar extension is its defining strict Roos limit. The K-injective-normalized
Roos bridge identifies these with total derived limit. The generator formulas fix
all tower identifications. Universal localization gives the displayed realizations
and their normalization on every simultaneous presentation. -/
theorem realizationModels (W : Bool → Scheme.{u})
    (ME : CompletedOperations.Models.{u, u} l E W) (ML : CompletedOperations.Models.{u, u} l L W) :
    ∀ a : Bool, Nonempty (TensorModel l E (W a) (ME.calculus a) (ME.roos a)) ∧
      Nonempty (IntegralComparisonScalarModel.{u, u} l E L ι (W a)
        (ME.calculus a) (ML.roos a)) := by
  sorry

/-- The coherent quotient representatives of the canonical completed comparisons.
Together with square, unit, composition and the normalized cochain definitions, this
identifies the actual strict quotient maps and their derived limits, including ramification.
The displayed equations are in the derived category of whole quotient systems;
applying total derived limit gives exactly the two stated integral comparisons.
Source: main-20261015 blueprint, def-weil-derived-pullback-tensor-hom, integral clause;
Stacks 03EL, 07A4 (blueprint: lem-pur-scalar-extension-tower-coherence).
Proof:
1. Use flat-term K-flat representatives P,Q and K-flat change of rings to form
   P_m,Q_m and their scalar extensions. Total tensor and finite pullback preserve
   this representative class; no flatness of A_m to B_m is used.
2. The balanced association (x tensor a) tensor b maps to x tensor iota(a)*b.
   Its inverse inserts one. The coefficient-extension reduction model identifies
   these simultaneously with P tensor B_m,Q tensor B_m, including every transition,
   and makes their coherent systems normalized.
3. Scalar association defines kappa. Tensor balancing gives its inverse; the
   constant coefficient square commutes on constant sections and on sheafification.
4. The signed total tensor comparison defines sigma and c. They preserve each
   bidegree, so preserve the factor (-1)^p in the second differential summand.
5. Both routes on b tensor (x tensor y) give (b tensor x) tensor (1 tensor y).
   Tensor generators, sheafification and direct sums prove the strict square.
6. Reduction preserves multiplication and one. Thus every map and inverse respects
   every quotient transition, and these are equations of strict systems.
7. For identity coefficients multiplication is the action unitor. For E to L to F,
   the direct coefficient map is the composite. Both successive and direct formulas
   multiply d*j(b), so the unit and transitivity equations hold strictly.
8. Apply coefficient-extension reduction and completed-operation tower substitution
   to these normalized systems. Their defining realizations and the canonical
   coherent counits are precisely pullbackReduction, scalarReduction and
   tensorReduction below. The cochain-normalized derivedSigma and the recorded
   derived kappa are the localizations of the same strict chain maps. Their coherent
   counit squares give the two equations, with the specified completed comparisons.
9. Apply total derived limit. Functoriality preserves the square, inverse, units
   and successive-extension equations. The normalized realizations identify the
   limit maps with the canonical scalarPullbackCompleted and scalarTensorCompleted;
   no interchange with arbitrary inverse limits or uniqueness of arbitrary isos is used.
-/
theorem scalarExtensionTowerCoherence (W : Bool → Scheme.{u})
    (ME : CompletedOperations.Models.{u, u} l E W) (ML : CompletedOperations.Models.{u, u} l L W)
    (SX : IntegralComparisonScalarModel.{u, u} l E L ι (W true) (ME.calculus true) (ML.roos true))
    (SY : IntegralComparisonScalarModel.{u, u} l E L ι (W false)
      (ME.calculus false) (ML.roos false))
    (TE : TensorModel l E (W false) (ME.calculus false) (ME.roos false))
    (TL : TensorModel l L (W false) (ML.calculus false) (ML.roos false))
    (f : W true ⟶ W false)
    (_hX : IsUnit (l : Γ(W true, ⊤))) (_hY : IsUnit (l : Γ(W false, ⊤)))
    (M N : sfIntegralConstructibleCategory l E (W false)) :
    ∃ (hF : IsSfDerivedComplete l E (W true) ((integralDerivedPullback.{u, u} l E f).obj M.obj))
      (hT : IsSfDerivedComplete l E (W false)
        ((integralCompletedTensor.{u, u} l E (W false)).obj (M.obj, N.obj))),
    ((ML.calculus true).reduction.map
        (scalarPullbackCompleted l E L ι f M.obj M.property.1 hF).hom ≫
      pullbackReduction l L W ML f ((integralScalarExtension.{u} l E L ι (W false)).obj M.obj) ≫
      (integralComparisonDerivedSequencePullback.{u, u} l L f).map
        (scalarReduction l E L ι (W false) (ME.calculus false) (ML.calculus false)
          (ML.roos false) SY M.obj) =
      scalarReduction l E L ι (W true) (ME.calculus true) (ML.calculus true)
          (ML.roos true) SX ((integralDerivedPullback.{u, u} l E f).obj M.obj) ≫
        (integralComparisonDerivedSequenceScalar.{u, u} l E L ι (W true)).map
          (pullbackReduction l E W ME f M.obj) ≫
        (integralComparisonSystemScalarPullback.{u, u} l E L ι f).hom.app
          ((ME.calculus false).reduction.obj M.obj)) ∧
    ((ML.calculus false).reduction.map
        (scalarTensorCompleted l E L ι (W false) M.obj N.obj M.property.1 N.property.1 hT).hom ≫
      tensorReduction l L (W false) (ML.calculus false) (ML.roos false) TL
        ((integralScalarExtension.{u} l E L ι (W false)).obj M.obj)
        ((integralScalarExtension.{u} l E L ι (W false)).obj N.obj) ≫
      (ML.calculus false).systemClosed.tensor.map (Prod.mkHom
        (scalarReduction l E L ι (W false) (ME.calculus false) (ML.calculus false)
          (ML.roos false) SY M.obj)
        (scalarReduction l E L ι (W false) (ME.calculus false) (ML.calculus false)
          (ML.roos false) SY N.obj)) =
      scalarReduction l E L ι (W false) (ME.calculus false) (ML.calculus false)
          (ML.roos false) SY ((integralCompletedTensor.{u, u} l E (W false)).obj (M.obj, N.obj)) ≫
        (integralComparisonDerivedSequenceScalar.{u, u} l E L ι (W false)).map
          (tensorReduction l E (W false) (ME.calculus false) (ME.roos false) TE M.obj N.obj) ≫
        (derivedSigma l E L ι (W false) (ME.calculus false) (ML.calculus false)).hom.app
          ((ME.calculus false).reduction.obj M.obj, (ME.calculus false).reduction.obj N.obj)) := by
  sorry

attribute [local semireducible] coefficientSequenceCommRingSheaf
  coefficientSequenceCommRingPresheaf

/-- The actual local section of a strict quotient model specified by its evaluation iso.
Source: node proof step 2 (blueprint: lem-pur-scalar-extension-tower-coherence). -/
def modelSection (W : Scheme.{u})
    (SE : CoefficientDerivedSystemCalculus.{u, u} l E W)
    (SL : CoefficientDerivedSystemCalculus.{u, u} l L W)
    (A : CoefficientExtensionSystems.{u, u} l E L ι W)
    (d : CoefficientExtensionReductionData.{u, u} l E L ι W SE SL A)
    (P : (integralOperationsGoodComplex.{u, u} l E W).FullSubcategory)
    (n : ℕ) (i : ℤ) (U : W.ProEtᵒᵖ)
    (b : (coefficientSequenceCommRingSheaf l L W).obj.obj (op (n, U.unop)))
    (x : (P.obj.X i).val.obj U) :
    ((d.direct.obj P).X i).val.obj (op (n, U.unop)) :=
  integralComparisonSequenceSection.{u, u} l L W ((d.direct.obj P).X i) n U
    ((((d.directEvaluation n).inv.app P).f i).val.app U
      (integralScalarTensorSection.{u, u} l E L ι W n (P.obj.X i) U b x))

private theorem modelSection_hom_ext (W : Scheme.{u})
    (SE : CoefficientDerivedSystemCalculus.{u, u} l E W)
    (SL : CoefficientDerivedSystemCalculus.{u, u} l L W)
    (A : CoefficientExtensionSystems.{u, u} l E L ι W)
    (d : CoefficientExtensionReductionData.{u, u} l E L ι W SE SL A)
    (K : (integralOperationsGoodComplex.{u, u} l E W).FullSubcategory) (i : ℤ)
    {T : coefficientSequenceModules.{u, u} l L W}
    (f g : (d.direct.obj K).X i ⟶ T)
    (h : ∀ (n : ℕ) (U : W.ProEtᵒᵖ)
      (b : (coefficientSequenceCommRingSheaf l L W).obj.obj (op (n, U.unop)))
      (x : (K.obj.X i).val.obj U),
      f.val.app (op (n, U.unop)) (modelSection l E L ι W SE SL A d K n i U b x) =
        g.val.app (op (n, U.unop)) (modelSection l E L ι W SE SL A d K n i U b x)) :
    f = g := by
  have he (n : ℕ) : (coefficientSequenceEvaluation l L W n).map f =
      (coefficientSequenceEvaluation l L W n).map g := by
    apply (cancel_epi (((d.directEvaluation n).inv.app K).f i)).mp
    apply (SheafOfModules.toSheaf _).map_injective
    apply WeilConjectures.scalarTensor_ab_hom_ext l E L ι W n (K.obj.X i)
    intro U b x
    exact h n U b x
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext x
  exact congrArg (fun k ↦ k.val.app (op U.unop.2) x) (he U.unop.1)

/-- Scalar extension of the actual E quotient complex is the actual B quotient complex,
with the balanced association formula and all quotient transitions retained.
Source: node proof steps 1--2, 5--6; Stacks 03EL, 0G7E
(blueprint: lem-pur-scalar-extension-tower-coherence).
Proof: the coefficient-extension reduction model supplies d and d0. Their finite
values are P tensor B_m and P tensor A_m with the actual quotient transitions.
Associate (x tensor a) tensor b to x tensor iota(a)*b; the inverse inserts one.
Balancing proves inverse identities and naturality. These formulas are chain maps
and commute with every quotient transition because coefficient reduction is a ring
map. They therefore glue to the displayed unique strict-system iso. K-flat change
of rings and closure under total tensor justify every derived interpretation.
Apply square to these E quotient representatives. The resulting iso equality is
exactly the stated scalar-extension square, on the actual models, in both directions.
No flatness of A_m to B_m is required, including in ramified extensions. -/
theorem quotientModels {X Y : Scheme.{u}} (f : X ⟶ Y)
    (_hX : IsUnit (l : Γ(X, ⊤))) (_hY : IsUnit (l : Γ(Y, ⊤)))
    (SE : CoefficientDerivedSystemCalculus.{u, u} l E Y)
    (SL : CoefficientDerivedSystemCalculus.{u, u} l L Y)
    (A : CoefficientExtensionSystems.{u, u} l E L ι Y)
    (A0 : CoefficientExtensionSystems.{u, u} l E E (AlgHom.id ℚ_[l] E) Y)
    (M N : sfIntegralConstructibleCategory l E Y)
    (P Q : (integralOperationsGoodComplex.{u, u} l E Y).FullSubcategory)
    (_eP : DerivedCategory.Q.obj P.obj ≅ M.obj) (_eQ : DerivedCategory.Q.obj Q.obj ≅ N.obj) :
    ∃ (d : CoefficientExtensionReductionData.{u, u} l E L ι Y SE SL A)
      (d0 : CoefficientExtensionReductionData.{u, u} l E E (AlgHom.id ℚ_[l] E) Y SE SE A0),
    (∀ K : (integralOperationsGoodComplex.{u, u} l E Y).FullSubcategory,
      ∃! δ : (scalar l E L ι Y).obj (d0.direct.obj K) ≅ d.direct.obj K,
        ∀ (n : ℕ) (i : ℤ) (U : Y.ProEtᵒᵖ)
          (b : (coefficientSequenceCommRingSheaf l L Y).obj.obj (op (n, U.unop)))
          (a : (coefficientSequenceCommRingSheaf l E Y).obj.obj (op (n, U.unop)))
          (x : (K.obj.X i).val.obj U),
          (δ.hom.f i).val.app (op (n, U.unop))
            (integralComparisonSequenceTensorSection l E L ι Y ((d0.direct.obj K).X i)
              (op (n, U.unop)) b
              (modelSection l E E (AlgHom.id ℚ_[l] E) Y SE SE A0 d0 K n i U a x)) =
          modelSection l E L ι Y SE SL A d K n i U
            (((integralComparisonSequenceScalarMap.{u, u} l E L ι Y).hom.app
              (op (n, U.unop))) a * b) x) ∧
    (leftRoute l E L ι f).app (d0.direct.obj P, d0.direct.obj Q) =
      (rightRoute l E L ι f).app (d0.direct.obj P, d0.direct.obj Q) := by
  obtain ⟨d⟩ := coefficientExtensionReductionModel l E L ι Y SE SL A _hY
  obtain ⟨d0⟩ := coefficientExtensionReductionModel l E E (AlgHom.id ℚ_[l] E) Y
    SE SE A0 _hY
  refine ⟨d, d0, ?_, ?_⟩
  · intro K
    obtain ⟨δ, hδ⟩ := quotientAssociation_exists l E L ι Y SE SL A A0 d d0 K
    refine ⟨δ, hδ, ?_⟩
    intro δ' hδ'
    apply Iso.ext
    apply HomologicalComplex.hom_ext
    intro i
    apply ((scalar_adj l E L ι Y).homEquiv _ _).injective
    apply modelSection_hom_ext l E E (AlgHom.id ℚ_[l] E) Y SE SE A0 d0 K i
    intro n U a x
    rw [scalar_transpose_section, scalar_transpose_section]
    exact (hδ' n i U 1 a x).trans (hδ n i U 1 a x).symm
  · exact congrArg (fun e ↦ e.app (d0.direct.obj P, d0.direct.obj Q)) (square l E L ι f)

end WeilConjectures.ScalarExtensionTower
