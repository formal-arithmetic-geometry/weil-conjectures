/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q31
-/
module

public import Sheaf.Paper.IsomorphismDerivedPullback

public import Sheaf.Paper.FiniteFieldFiber

public import Sheaf.Paper.ConstantWeilStructure
public import Sheaf.Paper.LocalFrobeniusTrace
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.AlgebraicGeometry.ProEtale.InverseImagePullbackComparison
public import Sheaf.AlgebraicGeometry.FrobeniusDetailed
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.FiniteCoefficientPoint
public import Sheaf.Paper.FiniteRegularCoefficientComparisons
public import Sheaf.SixFunctors.FrobeniusPointTransport
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.SfRationalizationKaroubi

import all Sheaf.Paper.PointSectionsScalarExtension
import all Sheaf.Paper.CanonicalCoefficientPullbackReduction
import all Sheaf.Paper.ConstantWeilStructure
import WeilConjectures.Algebra.Homology.DerivedCategory.SingleHomology

/-! # Constant geometric stalks and the coefficient unit

Source: main-20261015, sec-zeta-weil/sk-thm-tracetodeterminant,
prop-every-iterate-trace.proof.md, constant-sheaf clause, reviewed expansion step 5
(blueprint: lem-zl-constant-geometric-stalk-unit).

All finite indices denote exponent m+1. The integral coefficient is the completed
ring sheaf. The maps below retain the actual adjunction units and strict Roos model.

## Main statements

* `embeddingPoint_return`: the semilinear return for every allowed embedding.
* `finiteStalkUnit`, `integralStalkUnit`, `rationalStalkUnit`: coefficient-unit coordinates.
* `finiteOperator_unit`, `integralOperator_unit`, `rationalOperator_unit`: identity operators.
* `finiteUnit_reduction`, `integralUnit_projection`, `section_reductions`: actual quotient squares.
* `rationalStalkUnit_existsUnique`, `rationalOperator_scalar`: rationalization squares.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
namespace WeilConjectures.ConstantGeometricStalkUnit

attribute [-instance] coefficientComplexModuleDerived pointScalarModuleDerived
  pointCompletedSheafDerived pointScalarAbSheafify pointScalarAbLocallyBijective
  coefficientComplexIntegralAdditive coefficientComplexIntegralLimits
  coefficientComplexIntegralColimits coefficientComplexRationalAdditive
  coefficientComplexRationalLimits coefficientComplexRationalColimits
  coefficientComplexFieldAdditive coefficientComplexFieldLimits coefficientComplexFieldColimits

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Multiplication on the finite coefficient unit, as the adjoint of the constant section one.
Source: reviewed expansion step 2 (blueprint: lem-zl-constant-geometric-stalk-unit). -/
def finiteUnitHom {X Y : Scheme.{u}} (f : X ⟶ Y) (m : ℕ) :
    (sfIntrinsicPullback (Padic.coefficientExtensionRing l E (m + 1)) f).obj
        (SheafOfModules.unit (integralCoefficientSheaf l E Y m)) ⟶
      SheafOfModules.unit (integralCoefficientSheaf l E X m) :=
  letI := Padic.finite_coefficientExtensionRing l E (m + 1) (Nat.succ_le_succ (Nat.zero_le m))
  ((sfIntrinsicConstantModuleAdjunction f
    (Padic.coefficientExtensionRing l E (m + 1))).homEquiv _ _).symm
      ((SheafOfModules.unitHomEquiv _).symm
        (PresheafOfModules.sectionsMk (fun U ↦ (1 : (integralCoefficientSheaf l E X m).obj.obj
          ((proEtaleBaseChange f).op.obj U)))
          (fun {_ _} a ↦ map_one ((integralCoefficientSheaf l E X m).obj.map
            ((proEtaleBaseChange f).op.map a)).hom)))

/-- Transposing multiplication computes it on every adjunction generator.
Source: reviewed expansion step 2 (blueprint: lem-zl-constant-geometric-stalk-unit). -/
private theorem finiteUnitHom_generator {X Y : Scheme.{u}} (f : X ⟶ Y) (m : ℕ)
    (V : Y.ProEt) (a : (integralCoefficientSheaf l E Y m).obj.obj (op V)) :
    letI := Padic.finite_coefficientExtensionRing l E (m + 1) (by omega)
    (finiteUnitHom l E f m).val.app (op ((proEtaleBaseChange f).obj V))
      (((sfIntrinsicConstantModuleAdjunction f
        (Padic.coefficientExtensionRing l E (m + 1))).unit.app
          (SheafOfModules.unit (integralCoefficientSheaf l E Y m))).val.app (op V) a) =
      ((coefficientProEtaleDirectRingMap.{u, u} f
        (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (m + 1))))).hom.app
          (op V)) a := by
  let := Padic.finite_coefficientExtensionRing l E (m + 1) (by omega)
  let adj := sfIntrinsicConstantModuleAdjunction f
    (Padic.coefficientExtensionRing l E (m + 1))
  have h := (adj.homEquiv
    (SheafOfModules.unit (integralCoefficientSheaf l E Y m))
    (SheafOfModules.unit (integralCoefficientSheaf l E X m))).apply_symm_apply
    ((SheafOfModules.unitHomEquiv
      ((proEtaleConstantModuleDirectImage f
        (Padic.coefficientExtensionRing l E (m + 1))).obj
          (SheafOfModules.unit (integralCoefficientSheaf l E X m)))).symm
      (PresheafOfModules.sectionsMk (fun U ↦
        (1 : (integralCoefficientSheaf l E X m).obj.obj
          ((proEtaleBaseChange f).op.obj U)))
        (fun {_ _} b ↦ map_one ((integralCoefficientSheaf l E X m).obj.map
          ((proEtaleBaseChange f).op.map b)).hom)))
  rw [Adjunction.homEquiv_unit] at h
  have hv := congrArg (fun z ↦ z.val.app (op V) a) h
  let b : (integralCoefficientSheaf l E X m).obj.obj (op ((proEtaleBaseChange f).obj V)) :=
    ((coefficientProEtaleDirectRingMap.{u, u} f
      (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (m + 1))))).hom.app
        (op V)) a
  change (finiteUnitHom l E f m).val.app (op ((proEtaleBaseChange f).obj V))
      ((adj.unit.app (SheafOfModules.unit (integralCoefficientSheaf l E Y m))).val.app
        (op V) a) =
    b * (1 : (integralCoefficientSheaf l E X m).obj.obj
      (op ((proEtaleBaseChange f).obj V))) at hv
  exact hv.trans (mul_one b)

/-- The adjoint constant-section map is natural in its coefficient ring.
Source: reviewed expansion step 5 (blueprint: lem-zl-constant-geometric-stalk-unit). -/
private theorem coefficientDirect_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    {A B : CommRingCat.{u + 1}} (a : A ⟶ B) :
    (constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).map a ≫
        coefficientProEtaleDirectRingMap.{u, u} f B =
      coefficientProEtaleDirectRingMap.{u, u} f A ≫
        ((proEtaleBaseChange f).sheafPushforwardContinuous CommRingCat.{u + 1}
          (ProEt.topology Y) (ProEt.topology X)).map
            ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map a) := by
  let adj := sheafificationAdjunction (ProEt.topology Y) CommRingCat.{u + 1}
  apply (adj.homEquiv _ _).injective
  change adj.homEquiv _ _
    ((presheafToSheaf (ProEt.topology Y) CommRingCat.{u + 1}).map
      ((Functor.const Y.ProEtᵒᵖ).map a) ≫ _) = _
  rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right]
  simp only [coefficientProEtaleDirectRingMap, adj, Equiv.apply_symm_apply]
  ext U x
  exact congrArg (fun z ↦ (z.app ((proEtaleBaseChange f).op.obj U)).hom x)
    (toSheafify_naturality (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).map a))

private theorem finiteUnitHom_tensor {X Y : Scheme.{u}} (f : X ⟶ Y) (m : ℕ) :
    letI := Padic.finite_coefficientExtensionRing l E (m + 1) (by omega)
    let A := CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (m + 1)))
    let φ : integralCoefficientSheaf l E Y m ⟶
        ((proEtaleBaseChange f).sheafPushforwardContinuous RingCat.{u + 1}
          (ProEt.topology Y) (ProEt.topology X)).obj
            (integralCoefficientSheaf l E X m) :=
      ⟨Functor.whiskerRight (coefficientProEtaleDirectRingMap.{u, u} f A).hom
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩
    letI : (SheafOfModules.pushforward.{u + 1} φ).IsRightAdjoint :=
      coefficientProEtaleModuleDirectImage_isRightAdjoint.{u, u} f A
    (inverseImageFiniteIntrinsicPullbackComparison f
      (Padic.coefficientExtensionRing l E (m + 1))).hom.app
        (SheafOfModules.unit (integralCoefficientSheaf l E Y m)) ≫
          finiteUnitHom l E f m = SheafOfModules.pullbackObjUnitToUnit φ := by
  let := Padic.finite_coefficientExtensionRing l E (m + 1) (by omega)
  let A := CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (m + 1)))
  let φ : integralCoefficientSheaf l E Y m ⟶
      ((proEtaleBaseChange f).sheafPushforwardContinuous RingCat.{u + 1}
        (ProEt.topology Y) (ProEt.topology X)).obj
          (integralCoefficientSheaf l E X m) :=
    ⟨Functor.whiskerRight (coefficientProEtaleDirectRingMap.{u, u} f A).hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩
  let : (SheafOfModules.pushforward.{u + 1} φ).IsRightAdjoint :=
    coefficientProEtaleModuleDirectImage_isRightAdjoint.{u, u} f A
  let adj₁ := coefficientProEtaleModuleAdjunction.{u, u} f A
  let adj₂ := sfIntrinsicConstantModuleAdjunction f
    (Padic.coefficientExtensionRing l E (m + 1))
  let e := adj₁.leftAdjointUniq adj₂
  change e.hom.app (SheafOfModules.unit (integralCoefficientSheaf l E Y m)) ≫
    finiteUnitHom l E f m = SheafOfModules.pullbackObjUnitToUnit φ
  apply (adj₁.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc,
    adj₁.unit_leftAdjointUniq_hom_app adj₂]
  change adj₂.homEquiv _ _ (finiteUnitHom l E f m) = _
  rw [finiteUnitHom, Equiv.apply_symm_apply]
  change _ = (SheafOfModules.pullbackPushforwardAdjunction φ).homEquiv _ _
    (SheafOfModules.pullbackObjUnitToUnit φ)
  rw [SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit]
  apply (SheafOfModules.unitHomEquiv _).injective
  simp only [Equiv.apply_symm_apply]
  ext U
  simp only [SheafOfModules.unitHomEquiv_apply_coe]
  change (1 : (integralCoefficientSheaf l E X m).obj.obj
    ((proEtaleBaseChange f).op.obj U)) = φ.hom.app U 1
  exact (map_one _).symm

/-- The finite multiplication is invertible, including the first positive quotient.
Source: reviewed expansion step 2 (blueprint: lem-zl-constant-geometric-stalk-unit).
Proof: in tensor coordinates the map is z tensor b ↦ c_f(z)b; its inverse sends b to
1 tensor b. The balancing relation makes the two composites identities. The intrinsic
realization and adjunction preserve this unit-normalized map. -/
theorem finiteUnitHom_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) (m : ℕ) :
    IsIso (finiteUnitHom l E f m) := by
  let := Padic.finite_coefficientExtensionRing l E (m + 1) (by omega)
  let A := CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (m + 1)))
  let φ : integralCoefficientSheaf l E Y m ⟶
      ((proEtaleBaseChange f).sheafPushforwardContinuous RingCat.{u + 1}
        (ProEt.topology Y) (ProEt.topology X)).obj
          (integralCoefficientSheaf l E X m) :=
    ⟨Functor.whiskerRight (coefficientProEtaleDirectRingMap.{u, u} f A).hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩
  let : (SheafOfModules.pushforward.{u + 1} φ).IsRightAdjoint :=
    coefficientProEtaleModuleDirectImage_isRightAdjoint.{u, u} f A
  let adj₁ := coefficientProEtaleModuleAdjunction.{u, u} f A
  let adj₂ := sfIntrinsicConstantModuleAdjunction f
    (Padic.coefficientExtensionRing l E (m + 1))
  let e := adj₁.leftAdjointUniq adj₂
  have he : e.hom.app (SheafOfModules.unit (integralCoefficientSheaf l E Y m)) ≫
      finiteUnitHom l E f m = SheafOfModules.pullbackObjUnitToUnit φ :=
    finiteUnitHom_tensor l E f m
  have : IsIso (e.hom.app (SheafOfModules.unit (integralCoefficientSheaf l E Y m)) ≫
      finiteUnitHom l E f m) := by
    rw [he]
    infer_instance
  exact IsIso.of_isIso_comp_left
    (e.hom.app (SheafOfModules.unit (integralCoefficientSheaf l E Y m)))
    (finiteUnitHom l E f m)

/-- The finite derived unit comparison, with its exact single-complex comparison.
Source: reviewed expansion step 2 (blueprint: lem-zl-constant-geometric-stalk-unit). -/
def finiteUnit {X Y : Scheme.{u}} (f : X ⟶ Y) (m : ℕ) :
    (finiteDerivedPullback l E m f).obj (finiteConstantCoefficientObject l E Y m) ≅
      finiteConstantCoefficientObject l E X m :=
  letI := Padic.finite_coefficientExtensionRing l E (m + 1) (Nat.succ_le_succ (Nat.zero_le m))
  ((sfIntrinsicPullback
    (Padic.coefficientExtensionRing l E (m + 1)) f).mapDerivedCategorySingleFunctor
      0).app _ ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso
        (@asIso _ _ _ _ (finiteUnitHom l E f m) (finiteUnitHom_isIso l E f m))

section
attribute [local irreducible] unrestrictedIntegralReductionExistence limit
  chainUnitCandidate pullbackUnitProduct pullbackUnitLevel

/-- The normalized strict unit for arbitrary scheme maps, extending the same owning-node
construction used for the Weil automorphism.
Source: reviewed expansion steps 2, 5 and 6
(blueprint: lem-zl-constant-geometric-stalk-unit).
Proof: the compatible finite generators are the adjunction images of 1 tensor 1.
Their product is killed by 1-shift. Use mappingCocone.lift with zero shifted component.
Maps from the regular module are determined by the global section one; the terminal
object is a base-change object. This proves existence and uniqueness with the displayed
normalization, without choosing a filler in a triangulated homotopy limit. -/
theorem integralChainUnit_existsUnique {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃! η : constantWeilIntegralComplex l E X ⟶
        (integralOperationsPullbackComplexFunctor l E f).obj
          (constantWeilIntegralComplex l E Y),
      (∀ (m : ℕ) (V : Y.ProEt),
        ((η.f 0 ≫
          (CochainComplex.mappingCocone.fst
            (constantWeilPullbackRoosEndomorphism l E f)).f 0 ≫
          (Pi.π (fun j ↦ (constantWeilPullbackTower l E f).obj (op j)) m).f 0).val.app
            (op ((proEtaleBaseChange f).obj V)))
          (constantWeilUnitSection l E X ((proEtaleBaseChange f).obj V)) =
        integralOperationsPullbackGenerator l E f m
          (((unrestrictedIntegralFiniteComplex l E Y m).obj
            (constantWeilIntegralComplex l E Y)).X 0) V
          (constantWeilReducedUnitSection l E Y m V)) ∧
      (∀ i : ℤ, η.f i ≫
        (CochainComplex.mappingCocone.snd
          (constantWeilPullbackRoosEndomorphism l E f)).v i (i - 1) (by omega) = 0) := by
  refine ⟨chainUnitCandidate l E f, ⟨?_, ?_⟩, ?_⟩
  · intro m V
    exact chainUnitCandidate_generators l E f m V
  · intro i
    simp only [chainUnitCandidate, CochainComplex.mappingCocone.lift_f_snd_v,
      CochainComplex.HomComplex.Cochain.zero_v]
  · intro η hη
    exact normalized_chainUnit_unique l E f η hη


end

/-- The uniquely specified strict chain map, with real cochain data.
Source: reviewed expansion step 6 (blueprint: lem-zl-constant-geometric-stalk-unit). -/
def integralChainUnit {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (integralChainUnit_existsUnique l E f).exists.choose

/-- The strict coefficient unit is a quasi-isomorphism for arbitrary pullback.
Source: reviewed expansion step 6 (blueprint: lem-zl-constant-geometric-stalk-unit).
Proof: finite multiplication identifies the entire pulled quotient system with the
constant quotient system on X, including its actual transitions. Its surjective tower
has limit the completed ring sheaf. The zero-homotopy map above is its Roos comparison;
the surjective-tower derived-limit theorem makes it a quasi-isomorphism. -/
theorem integralChainUnit_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsIso (DerivedCategory.Q.map (integralChainUnit l E f)) := by
  sorry

/-- The integral unit identification uses the inverse normalized strict-cone map.
Source: reviewed expansion step 6 (blueprint: lem-zl-constant-geometric-stalk-unit). -/
def integralUnit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (integralDerivedPullback l E f).obj (integralConstantCoefficientObject l E Y) ≅
      integralConstantCoefficientObject l E X :=
  (integralDerivedPullbackComparison l E f).app (constantWeilIntegralGood l E Y) ≪≫
    (@asIso _ _ _ _ (DerivedCategory.Q.map (integralChainUnit l E f))
      (integralChainUnit_isIso l E f)).symm



section
attribute [local irreducible] coefficientFinitePullIso canonicalCoefficientFiniteKappaComplex
  canonicalCoefficientFiniteUnit constantSheaf unrestrictedIntegralReductionExistence limit

/-- The intrinsic finite multiplication is exactly c_m composed with lambda_m,
using the canonical unit-preserving comparison of the two pullback presentations.
Source: reviewed expansion steps 2 and 3
(blueprint: lem-zl-constant-geometric-stalk-unit).
Proof: the model comparison is uniqueness of left adjoints preserving their units.
The inverse tensor-unit map lambda_m is multiplication, and c_m acts on each constant
coefficient by that same coefficient. Both sides send every adjunction generator
z tensor b to c_m(z)b. They agree before localization and hence in the derived category. -/
theorem finiteUnit_canonicalWeil {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] (m : ℕ) :
    letI := Padic.finite_coefficientExtensionRing l E (m + 1) (by omega)
    (finiteRegularKappa l E g m).f 0 ≫
      (inverseImageFiniteIntrinsicPullbackComparison g
        (Padic.coefficientExtensionRing l E (m + 1))).hom.app
          ((finiteRegularCoefficientComplex l E Y m).X 0) ≫
        finiteUnitHom l E g m =
      (finiteRegularComparison l E g m).hom.f 0 := by
  let := Padic.finite_coefficientExtensionRing l E (m + 1) (by omega)
  let A := CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (m + 1)))
  let adj₁ := coefficientProEtaleModuleAdjunction.{u, u} g A
  let adj₂ := sfIntrinsicConstantModuleAdjunction g
    (Padic.coefficientExtensionRing l E (m + 1))
  let e := adj₁.leftAdjointUniq adj₂
  have he : e.hom.app (SheafOfModules.unit (integralCoefficientSheaf l E Y m)) ≫
      finiteUnitHom l E g m = (finitePullbackRegularIso l E g m).hom :=
    finiteUnitHom_tensor l E g m
  have hc : finiteRegularKappa l E g m ≫ (coefficientFinitePullIso l E g m).hom =
      (finiteRegularComparison l E g m).hom := by
    rw [finiteRegularKappa, coefficientFiniteKappa_formula]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rfl
  change (finiteRegularKappa l E g m).f 0 ≫
    e.hom.app (SheafOfModules.unit (integralCoefficientSheaf l E Y m)) ≫
      finiteUnitHom l E g m = _
  rw [he]
  have hc₀ := congrArg (fun z ↦ z.f 0) hc
  simp only [coefficientFinitePullIso, Iso.trans_hom, HomologicalComplex.comp_f,
    Functor.mapIso_hom, Iso.app_hom, CochainComplex.singleFunctor,
    CochainComplex.singleFunctors, HomologicalComplex.single_map_f_self,
    HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
    Category.assoc, Iso.inv_hom_id_assoc] at hc₀
  change (finiteRegularKappa l E g m).f 0 ≫
    (integralOperationsLevelPullback l E g m).map
      (𝟙 (SheafOfModules.unit (integralCoefficientSheaf l E Y m))) ≫
        (finitePullbackRegularIso l E g m).hom ≫
          𝟙 (SheafOfModules.unit (integralCoefficientSheaf l E X m)) = _ at hc₀
  have hmap := (integralOperationsLevelPullback l E g m).map_id
    (SheafOfModules.unit (integralCoefficientSheaf l E Y m))
  have h := congrArg (fun z ↦ (finiteRegularKappa l E g m).f 0 ≫
    z ≫ (finitePullbackRegularIso l E g m).hom) hmap
  have hc₁ : (finiteRegularKappa l E g m).f 0 ≫
      (integralOperationsLevelPullback l E g m).map
        (𝟙 (SheafOfModules.unit (integralCoefficientSheaf l E Y m))) ≫
          (finitePullbackRegularIso l E g m).hom =
        (finiteRegularComparison l E g m).hom.f 0 := by
    simpa only [Category.comp_id] using hc₀
  exact (congrArg (fun z ↦ (finiteRegularKappa l E g m).f 0 ≫ z)
    (Category.id_comp (finitePullbackRegularIso l E g m).hom)).symm.trans
      (h.symm.trans hc₁)



end

/-- The generalized strict unit agrees with the recorded canonical integral Weil map.
Source: reviewed expansion steps 6 and 7
(blueprint: lem-zl-constant-geometric-stalk-unit).
Proof: both strict units have the same finite generators and zero shifted component.
The uniqueness clause of constantWeilChainUnit_existsUnique identifies their chain maps.
Their good-representative comparisons coincide, and c composed with lambda cancels
the two inverse coefficient comparisons in constantWeilIntegralTheta. -/
theorem integralUnit_canonicalWeil {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    integralUnit l E g = constantWeilIntegralTheta l E g := by
  simp only [constantWeilIntegralTheta, constantWeilIntegralLambda, Iso.trans_assoc,
    Iso.symm_self_id, Iso.trans_refl]
  rfl

/-- Multiplication respects every finite quotient on every pullback generator.
Source: reviewed expansion steps 2 and 5
(blueprint: lem-zl-constant-geometric-stalk-unit).
Proof: the adjunction unit sends a to a tensor 1, multiplication sends this to the
constant section a, and constant sheafification is natural in the quotient ring map.
These are all generators after the sheafified tensor construction, so the equation
is the actual reduction square, before exact single and section functors are applied. -/
theorem finiteUnit_reduction {X Y : Scheme.{u}} (f : X ⟶ Y) (m : ℕ) (V : Y.ProEt)
    (a : (integralCoefficientSheaf l E Y (m + 1)).obj.obj (op V)) :
    letI := Padic.finite_coefficientExtensionRing l E (m + 2) (by omega)
    letI := Padic.finite_coefficientExtensionRing l E (m + 1) (by omega)
    (integralCoefficientSheafTransition l E X m).hom.app
        (op ((proEtaleBaseChange f).obj V))
      (((finiteUnitHom l E f (m + 1)).val.app
        (op ((proEtaleBaseChange f).obj V)))
          (((sfIntrinsicConstantModuleAdjunction f
            (Padic.coefficientExtensionRing l E (m + 2))).unit.app
              (SheafOfModules.unit (integralCoefficientSheaf l E Y (m + 1)))).val.app
                (op V) a)) =
      (finiteUnitHom l E f m).val.app (op ((proEtaleBaseChange f).obj V))
        (((sfIntrinsicConstantModuleAdjunction f
          (Padic.coefficientExtensionRing l E (m + 1))).unit.app
            (SheafOfModules.unit (integralCoefficientSheaf l E Y m))).val.app (op V)
              ((integralCoefficientSheafTransition l E Y m).hom.app (op V) a)) := by
  let := Padic.finite_coefficientExtensionRing l E (m + 2) (by omega)
  let := Padic.finite_coefficientExtensionRing l E (m + 1) (by omega)
  rw [finiteUnitHom_generator, finiteUnitHom_generator]
  have h := coefficientDirect_naturality f (CommRingCat.ofHom
    ((ULift.ringEquiv : ULift.{u + 1} _ ≃+* _).symm.toRingHom.comp
      ((Padic.coefficientExtensionTransition l E (m + 1)).comp
        (ULift.ringEquiv : ULift.{u + 1} _ ≃+* _).toRingHom)))
  exact (congrArg (fun z ↦ (z.hom.app (op V)) a) h).symm

/-- The strict integral unit's actual nth Roos projection on every regular section.
Source: reviewed expansion steps 5--7 (blueprint: lem-zl-constant-geometric-stalk-unit).
Proof: the regular-module map is linear and its value on one is the normalized
finite generator. Scalar action on the nth restricted tower term factors through
its actual quotient projection. Thus the formula follows for every regular section.
Together with the zero shifted component, this determines the entire strict cone
map and all projections, rather than just its finite isomorphism classes. -/
theorem integralUnit_projection {X Y : Scheme.{u}} (f : X ⟶ Y) (m : ℕ) (V : Y.ProEt)
    (a : (completedIntegralCoefficientSheafUnrestricted l E X).obj.obj
      (op ((proEtaleBaseChange f).obj V))) :
    ((integralChainUnit l E f).f 0 ≫
      (CochainComplex.mappingCocone.fst
        (constantWeilPullbackRoosEndomorphism l E f)).f 0 ≫
      (Pi.π (fun j ↦ (constantWeilPullbackTower l E f).obj (op j)) m).f 0).val.app
        (op ((proEtaleBaseChange f).obj V))
      (((HomologicalComplex.singleObjXSelf (.up ℤ) 0
        (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E X))).inv.val.app
          (op ((proEtaleBaseChange f).obj V))) a) =
      @SMul.smul
        ((integralCoefficientSheaf l E X m).obj.obj
          (op ((proEtaleBaseChange f).obj V)))
        (((integralOperationsLevelPullback l E f m).obj
          (((unrestrictedIntegralFiniteComplex l E Y m).obj
            (constantWeilIntegralComplex l E Y)).X 0)).val.obj
              (op ((proEtaleBaseChange f).obj V))) inferInstance
        ((limit.π (integralCoefficientSheafSystem l E X) (op m)).hom.app
          (op ((proEtaleBaseChange f).obj V)) a)
          (integralOperationsPullbackGenerator l E f m
            (((unrestrictedIntegralFiniteComplex l E Y m).obj
              (constantWeilIntegralComplex l E Y)).X 0) V
            (constantWeilReducedUnitSection l E Y m V)) := by
  let U := op ((proEtaleBaseChange f).obj V)
  let one : (completedIntegralCoefficientSheafUnrestricted l E X).obj.obj U := 1
  let e := HomologicalComplex.singleObjXSelf (V := integralTowerModules l E X) (.up ℤ) 0
    (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E X))
  let F := (((integralChainUnit l E f).f 0 ≫
    (CochainComplex.mappingCocone.fst
      (constantWeilPullbackRoosEndomorphism l E f)).f 0 ≫
    (Pi.π (fun j ↦ (constantWeilPullbackTower l E f).obj (op j)) m).f 0).val.app U).hom
  have h := (integralChainUnit_existsUnique l E f).exists.choose_spec.1 m V
  change F ((e.inv.val.app U).hom one) = _ at h
  have he : (e.inv.val.app U).hom a = a • (e.inv.val.app U).hom one := by
    simpa only [one, smul_eq_mul, mul_one] using (e.inv.val.app U).hom.map_smul a one
  calc
    F ((e.inv.val.app U).hom a) = F (a • (e.inv.val.app U).hom one) := congrArg F he
    _ = a • F ((e.inv.val.app U).hom one) := F.map_smul a _
    _ = _ := congrArg (fun z ↦ a • z) h

variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)

/-- The coefficient-to-section map at the finite point, preserving every constant a.
Source: reviewed expansion step 2 (blueprint: lem-zl-constant-geometric-stalk-unit). -/
def finiteSection (m : ℕ) :
    ModuleCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (m + 1)))
        (ULift.{u + 1} (Padic.coefficientExtensionRing l E (m + 1))) ⟶
      (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (m + 1))).obj
        (SheafOfModules.unit (integralCoefficientSheaf l E (Spec (.of D.k)) m)) :=
  ModuleCat.ofHom
    (Y := (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (m + 1))).obj
      (SheafOfModules.unit (integralCoefficientSheaf l E (Spec (.of D.k)) m)))
    { toFun := pointConstantSectionMap D.k (Padic.coefficientExtensionRing l E (m + 1))
      map_add' := map_add _
      map_smul' := fun a b ↦ by
        change _ = (pointConstantSectionMap D.k
          (Padic.coefficientExtensionRing l E (m + 1)) a) *
            (pointConstantSectionMap D.k (Padic.coefficientExtensionRing l E (m + 1)) b)
        exact map_mul _ a b }

/-- The coefficient-to-section map for completed integral scalars.
Source: reviewed expansion step 6 (blueprint: lem-zl-constant-geometric-stalk-unit). -/
def integralSection :
    ModuleCat.of (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))
        (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) ⟶
      (pointIntegralSections l E D.k).obj
        (SheafOfModules.unit
          (completedIntegralCoefficientSheafUnrestricted l E (Spec (.of D.k)))) :=
  ModuleCat.ofHom
    (Y := (pointIntegralSections l E D.k).obj
      (SheafOfModules.unit
        (completedIntegralCoefficientSheafUnrestricted l E (Spec (.of D.k)))))
    { toFun := pointIntegralSectionMap l E D.k
      map_add' := map_add _
      map_smul' := fun a b ↦ by
        change _ = pointIntegralSectionMap l E D.k a * pointIntegralSectionMap l E D.k b
        exact map_mul _ a b }

/-- Both section maps are invertible with the canonical coefficient actions.
Source: reviewed expansion steps 2 and 6 (blueprint: lem-zl-constant-geometric-stalk-unit).
Proof: Spec k has one point. Finite constant sections are the coefficient ring by
constant functions and evaluation. Limits of sheaves are sectionwise, so completed
sections are lim A_m. Completeness of the coefficient DVR identifies this limit with
O_E via its actual quotient maps; uniqueness follows from separatedness. -/
theorem section_isIso :
    (∀ m : ℕ, IsIso (finiteSection l E D m)) ∧ IsIso (integralSection l E D) := by
  constructor
  · intro m
    apply (ConcreteCategory.isIso_iff_bijective _).2
    exact AlgebraicGeometry.ProEtale.bijective_toSheafify_app_of_iso (Iso.refl _)
      ((Functor.const (Scheme.ProEt (Spec (.of D.k)))ᵒᵖ).obj
        (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (m + 1)))))
  · apply (ConcreteCategory.isIso_iff_bijective _).2
    change Function.Bijective (pointIntegralSectionMap l E D.k)
    have h := pointCompletedConstant_bijective D.k l E
    exact h.comp (ULift.ringEquiv : ULift.{u + 1}
      (Padic.coefficientExtensionIntegers l E) ≃+*
        Padic.coefficientExtensionIntegers l E).bijective

/-- Finite sections identified with the regular coefficient module in degree zero.
Source: reviewed expansion step 2 (blueprint: lem-zl-constant-geometric-stalk-unit). -/
def finiteSectionsUnit (m : ℕ) :
    (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (m + 1))).mapDerivedCategory.obj
        (finiteConstantCoefficientObject l E (Spec (.of D.k)) m) ≅
      (DerivedCategory.singleFunctor _ 0).obj
        (ModuleCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (m + 1)))
          (ULift.{u + 1} (Padic.coefficientExtensionRing l E (m + 1)))) :=
  ((pointFiniteSections D.k
    (Padic.coefficientExtensionRing l E (m + 1))).mapDerivedCategorySingleFunctor
    0).app _ ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso
        (@asIso _ _ _ _ (finiteSection l E D m) ((section_isIso l E D).1 m)).symm

/-- Completed integral sections in coefficient-unit coordinates.
Source: reviewed expansion step 6 (blueprint: lem-zl-constant-geometric-stalk-unit). -/
def integralSectionsUnit :
    (pointFibreIntegralAmbient D l E).obj (integralConstantCoefficientObject l E (Spec (.of D.k))) ≅
      (DerivedCategory.singleFunctor _ 0).obj
        (ModuleCat.of (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))
          (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))) :=
  ((pointIntegralSections l E D.k).mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso
      (@asIso _ _ _ _ (integralSection l E D) (section_isIso l E D).2).symm

/-- The actual section coordinates preserve quotient transitions and completion projections.
Source: reviewed expansion steps 5, 6 and 8
(blueprint: lem-zl-constant-geometric-stalk-unit).
Proof: naturality of constant sheafification gives the first equation. The defining
limit lift of integralConstantToCompletion has the actual quotient cone as its legs,
which gives the second equation after evaluation at the final object. -/
theorem section_reductions (m : ℕ) :
    (∀ a : ULift.{u + 1} (Padic.coefficientExtensionRing l E (m + 2)),
      (integralCoefficientSheafTransition l E (Spec (.of D.k)) m).hom.app
        (op (ProEt.mk (𝟙 (Spec (.of D.k))))) (finiteSection l E D (m + 1) a) =
          finiteSection l E D m (ULift.up
            (Padic.coefficientExtensionTransition l E (m + 1) a.down))) ∧
    (∀ a : ULift.{u + 1} (Padic.coefficientExtensionIntegers l E),
      (limit.π (integralCoefficientSheafSystem l E (Spec (.of D.k))) (op m)).hom.app
        (op (ProEt.mk (𝟙 (Spec (.of D.k))))) (integralSection l E D a) =
          finiteSection l E D m (ULift.up
            (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (m + 1)) a.down))) := by
  let U := op (ProEt.mk (𝟙 (Spec (.of D.k))))
  let : EssentiallySmall.{u + 1} (Scheme.ProEt (Spec (.of D.k))) :=
    essentiallySmallSelf.{u} _
  let : HasSheafify (ProEt.topology (Spec (.of D.k))) CommRingCat.{u + 1} :=
    hasSheafifyEssentiallySmallSite.{u, u + 1, u + 1, u + 2, u + 1} _ _
  let : (sheafToPresheaf (ProEt.topology (Spec (.of D.k)))
      CommRingCat.{u + 1}).IsRightAdjoint :=
    ⟨⟨_, ⟨sheafificationAdjunction _ _⟩⟩⟩
  constructor
  · intro a
    have h := toSheafify_naturality (ProEt.topology (Spec (.of D.k)))
      ((Functor.const (Scheme.ProEt (Spec (.of D.k)))ᵒᵖ).map
        (CommRingCat.ofHom
          ((ULift.ringEquiv : ULift.{u + 1} _ ≃+* _).symm.toRingHom.comp
            ((Padic.coefficientExtensionTransition l E (m + 1)).comp
              (ULift.ringEquiv : ULift.{u + 1} _ ≃+* _).toRingHom))))
    exact congrArg (fun f ↦ (f.app U).hom a) h.symm
  · intro a
    have h := limit.lift_π (integralConstantCoefficientCone l E (Spec (.of D.k))) (op m)
    have h' := congrArg (fun f ↦ (f.hom.app U)
      (pointConstantSectionMap D.k (Padic.coefficientExtensionIntegers l E) a)) h
    have hn := toSheafify_naturality (ProEt.topology (Spec (.of D.k)))
      ((Functor.const (Scheme.ProEt (Spec (.of D.k)))ᵒᵖ).map
        (CommRingCat.ofHom
          ((ULift.ringEquiv : ULift.{u + 1} _ ≃+* _).symm.toRingHom.comp
            ((Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (m + 1))).comp
              (ULift.ringEquiv : ULift.{u + 1} _ ≃+* _).toRingHom))))
    have h'' := congrArg (fun f ↦ (f.app U).hom a) hn.symm
    exact h'.trans h''

variable (Y₀ : Over (Spec (.of D.k₀)))
  [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]

/-- The canonical finite geometric stalk identification, before any Frobenius calculation.
Source: reviewed expansion step 2 (blueprint: lem-zl-constant-geometric-stalk-unit). -/
def finiteStalkUnit (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) (m : ℕ) :=
  (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (m + 1))).mapDerivedCategory.mapIso
    (finiteUnit l E x m) ≪≫ finiteSectionsUnit l E D m

/-- The canonical completed integral geometric stalk identification.
Source: reviewed expansion step 6 (blueprint: lem-zl-constant-geometric-stalk-unit). -/
def integralStalkUnit (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) :=
  (pointFibreIntegralAmbient D l E).mapIso (integralUnit l E x) ≪≫ integralSectionsUnit l E D

/-- Iteration of the actual finite Weil maps with the specified pullback compositors.
Source: reviewed expansion step 3 (blueprint: lem-zl-constant-geometric-stalk-unit). -/
def finiteWeilIterate (m : ℕ) : (r : ℕ) →
    (finiteDerivedPullback l E m (localPositivePower (D.geometricFrobenius Y₀).hom r)).obj
        (finiteConstantCoefficientObject l E (D.geometricFiber Y₀).left m) ≅
      finiteConstantCoefficientObject l E (D.geometricFiber Y₀).left m
  | 0 => finiteUnit l E (D.geometricFrobenius Y₀).hom m
  | r + 1 =>
    (finiteCanonicalPullbackComposition l E (localPositivePower (D.geometricFrobenius Y₀).hom r)
      (D.geometricFrobenius Y₀).hom m).app _ ≪≫
      (finiteDerivedPullback l E m
        (localPositivePower (D.geometricFrobenius Y₀).hom r)).mapIso
          (finiteUnit l E (D.geometricFrobenius Y₀).hom m) ≪≫ finiteWeilIterate m r

/-- Iterate restriction-and-coprojection transport, retaining the actual finite comparisons.
Source: reviewed expansion step 4 (blueprint: lem-zl-constant-geometric-stalk-unit). -/
def finiteTransportIterate (m : ℕ)
    (N : proEtaleDerivedCategory (Spec (.of D.k))
      (Padic.coefficientExtensionRing l E (m + 1))) : (r : ℕ) →
    (pointFiniteSections D.k
      (Padic.coefficientExtensionRing l E (m + 1))).mapDerivedCategory.obj N ⟶
      (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (m + 1))).mapDerivedCategory.obj
        ((finiteDerivedPullback l E m (localPositivePower (frobeniusPointIso D).hom r)).obj N)
  | 0 => frobeniusPointTransportFinite D l hl E m N
  | r + 1 =>
    frobeniusPointTransportFinite D l hl E m N ≫
      finiteTransportIterate m
        ((finiteDerivedPullback l E m (frobeniusPointIso D).hom).obj N) r ≫
      (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (m + 1))).mapDerivedCategory.map
        ((finiteCanonicalPullbackComposition l E (localPositivePower (frobeniusPointIso D).hom r)
          (frobeniusPointIso D).hom m).inv.app N)

/-- The actual local finite operator at a semilinearly returning geometric point.
Source: reviewed expansion step 4 (blueprint: lem-zl-constant-geometric-stalk-unit). -/
def finiteOperator (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) (m r : ℕ)
    (h : x ≫ localPositivePower (D.geometricFrobenius Y₀).hom r =
      localPositivePower (frobeniusPointIso D).hom r ≫ x) :=
  finiteTransportIterate l E D hl m
      ((finiteDerivedPullback l E m x).obj
        (finiteConstantCoefficientObject l E (D.geometricFiber Y₀).left m)) r ≫
    (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (m + 1))).mapDerivedCategory.map
      (((finiteCanonicalPullbackComposition l E
          (localPositivePower (frobeniusPointIso D).hom r) x m).symm.app
          (finiteConstantCoefficientObject l E (D.geometricFiber Y₀).left m) ≪≫
        eqToIso (congrArg (fun (f : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) ↦
          (finiteDerivedPullback l E m f).obj
          (finiteConstantCoefficientObject l E (D.geometricFiber Y₀).left m)) h.symm) ≪≫
        (finiteCanonicalPullbackComposition l E x
          (localPositivePower (D.geometricFrobenius Y₀).hom r) m).app
          (finiteConstantCoefficientObject l E (D.geometricFiber Y₀).left m)).hom) ≫
    (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (m + 1))).mapDerivedCategory.map
      ((finiteDerivedPullback l E m x).map (finiteWeilIterate l E D Y₀ m r).hom)



/-- The integral stalk in the published full constructible category.
Source: reviewed expansion step 6 (blueprint: lem-zl-constant-geometric-stalk-unit). -/
def integralStalk (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) :=
  letI := frobeniusPointPrimeInvertible D l hl
  letI := sfWeilPrimeInvertible D l hl Y₀
  (constructibleIntegralPullback l E x).obj
    (constantWeilIntegralObject l E D hl (D.geometricFiber Y₀).left)

/-- Iterate the published completed integral Weil comparison.
Source: reviewed expansion steps 3 and 7 (blueprint: lem-zl-constant-geometric-stalk-unit). -/
def integralWeilIterate : (r : ℕ) →
    (@constructibleIntegralPullback l _ E _ _ _ _ _
      (localPositivePower (D.geometricFrobenius Y₀).hom r)
      (sfWeilPrimeInvertible D l hl Y₀) (sfWeilPrimeInvertible D l hl Y₀)).obj
        (constantWeilIntegralObject l E D hl (D.geometricFiber Y₀).left) ≅
      constantWeilIntegralObject l E D hl (D.geometricFiber Y₀).left
  | 0 => constantWeilConstructibleIntegralTheta l E D hl Y₀
  | r + 1 =>
    letI := sfWeilPrimeInvertible D l hl Y₀
    ((integralPullbackComposition l E).choose
      (localPositivePower (D.geometricFrobenius Y₀).hom r)
      (D.geometricFrobenius Y₀).hom).app _ ≪≫
      (constructibleIntegralPullback l E
        (localPositivePower (D.geometricFrobenius Y₀).hom r)).mapIso
          (constantWeilConstructibleIntegralTheta l E D hl Y₀) ≪≫
        integralWeilIterate r

/-- Iterate the actual integral point transports, with the specified composition maps.
Source: reviewed expansion step 7 (blueprint: lem-zl-constant-geometric-stalk-unit). -/
def integralTransportIterate (N : sfIntegralConstructibleCategory l E (Spec (.of D.k))) :
    (r : ℕ) →
    ((pointIntegralFibre D l hl E).obj N).obj ⟶
      ((pointIntegralFibre D l hl E).obj
        ((@constructibleIntegralPullback l _ E _ _ _ _ _
          (localPositivePower (frobeniusPointIso D).hom r)
          (frobeniusPointPrimeInvertible D l hl)
          (frobeniusPointPrimeInvertible D l hl)).obj N)).obj
  | 0 => frobeniusPointTransportIntegral D l hl E N.obj
  | r + 1 =>
    letI := frobeniusPointPrimeInvertible D l hl
    frobeniusPointTransportIntegral D l hl E N.obj ≫
      integralTransportIterate
        ((constructibleIntegralPullback l E (frobeniusPointIso D).hom).obj N) r ≫
      (pointFibreIntegralAmbient D l E).map
        (((integralPullbackComposition l E).choose
          (localPositivePower (frobeniusPointIso D).hom r)
          (frobeniusPointIso D).hom).inv.app N).hom

/-- Integral local Frobenius: transport, semilinear return, and the iterated Weil map.
Source: reviewed expansion step 7 (blueprint: lem-zl-constant-geometric-stalk-unit). -/
def integralOperator (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) (r : ℕ)
    (h : x ≫ localPositivePower (D.geometricFrobenius Y₀).hom r =
      localPositivePower (frobeniusPointIso D).hom r ≫ x) :=
  letI := frobeniusPointPrimeInvertible D l hl
  letI := sfWeilPrimeInvertible D l hl Y₀
  integralTransportIterate l E D hl (integralStalk l E D hl Y₀ x) r ≫
    (pointFibreIntegralAmbient D l E).map
      ((((integralPullbackComposition l E).choose
          (localPositivePower (frobeniusPointIso D).hom r) x).symm.app
            (constantWeilIntegralObject l E D hl (D.geometricFiber Y₀).left) ≪≫
        eqToIso (congrArg (fun (f : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) ↦
          (constructibleIntegralPullback l E f).obj
          (constantWeilIntegralObject l E D hl (D.geometricFiber Y₀).left)) h.symm) ≪≫
        ((integralPullbackComposition l E).choose x
          (localPositivePower (D.geometricFrobenius Y₀).hom r)).app
            (constantWeilIntegralObject l E D hl (D.geometricFiber Y₀).left)).hom).hom ≫
    (pointFibreIntegralAmbient D l E).map
      ((constructibleIntegralPullback l E x).map (integralWeilIterate l E D hl Y₀ r).hom).hom

/-- Contravariant Spec sends the positive power to the corresponding field power.
Source: geometric-Frobenius construction (blueprint: def-weil-local-frobenius-trace). -/
private theorem localPointPower_eq (n : ℕ) :
    localPositivePower (frobeniusPointIso D).hom n =
      let := Fintype.ofFinite D.k₀
      Spec.map (CommRingCat.ofHom
        (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k ^ (n + 1)).toRingHom) := by
  let := Fintype.ofFinite D.k₀
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [localPositivePower, ih]
    change Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp]
    congr 1

/-- Iterating the two Galois-map projections preserves the model projection and
iterates the coefficient projection.
Source: geometric-Frobenius construction (blueprint: def-weil-local-frobenius-trace). -/
private theorem localFrobeniusPower_projections (n : ℕ) :
    localPositivePower (D.geometricFrobenius Y₀).hom n ≫
        pullback.fst Y₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) =
      pullback.fst Y₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) ∧
    localPositivePower (D.geometricFrobenius Y₀).hom n ≫
        pullback.snd Y₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) =
      pullback.snd Y₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) ≫
        localPositivePower (frobeniusPointIso D).hom n := by
  let := Fintype.ofFinite D.k₀
  have h := D.galoisMap_projections Y₀.hom
    (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k)
  change (D.geometricFrobenius Y₀).hom ≫ _ = _ ∧
    (D.geometricFrobenius Y₀).hom ≫ _ =
      _ ≫ (frobeniusPointIso D).hom at h
  induction n with
  | zero => exact h
  | succ n ih =>
    constructor
    · rw [localPositivePower, Category.assoc, h.1]
      exact ih.1
    · rw [localPositivePower, Category.assoc, h.2, ← Category.assoc, ih.2,
        Category.assoc]
      rfl

/-- A model map fixed by the point power has the stated semilinear return lift.
Source: pullback uniqueness in the return construction
(blueprint: def-weil-local-frobenius-trace). -/
private theorem localLift_return (n : ℕ) (a : Spec (.of D.k) ⟶ Y₀.left)
    (c : a ≫ Y₀.hom =
      (𝟙 (Spec (.of D.k))) ≫ Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))
    (ha : localPositivePower (frobeniusPointIso D).hom n ≫ a = a) :
    pullback.lift a (𝟙 _) c ≫ localPositivePower (D.geometricFrobenius Y₀).hom n =
      localPositivePower (frobeniusPointIso D).hom n ≫ pullback.lift a (𝟙 _) c := by
  apply pullback.hom_ext
  · rw [Category.assoc, (localFrobeniusPower_projections D Y₀ n).1,
      pullback.lift_fst, Category.assoc, pullback.lift_fst, ha]
  · rw [Category.assoc, (localFrobeniusPower_projections D Y₀ n).2,
      ← Category.assoc, pullback.lift_snd, Category.assoc, pullback.lift_snd,
      Category.id_comp, Category.comp_id]

/-- Compatibility needed to form the lift for any base-field embedding of the
specified finite extension, rather than only the chosen subfield inclusion.
Source: reviewed expansion step 1 (blueprint: lem-zl-constant-geometric-stalk-unit).
Proof: functoriality of Spec turns the base-field compatibility of the embedding
into the required equality; compose with the defining Over-morphism equation of x. -/
theorem embeddingPoint_compatible (n : ℕ) (hn : 1 ≤ n)
    (x : D.extensionPoints Y₀ n hn) (ι : D.extensionSubfield n hn →+* D.k)
    (hι : ι.comp (D.extensionEmbedding n hn) = algebraMap D.k₀ D.k) :
    (Spec.map (CommRingCat.ofHom ι) ≫ x.left) ≫ Y₀.hom =
      (𝟙 (Spec (.of D.k))) ≫ Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)) := by
  rw [Category.assoc, Over.w x, Category.id_comp]
  change Spec.map (CommRingCat.ofHom ι) ≫
    Spec.map (CommRingCat.ofHom (D.extensionEmbedding n hn)) = _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun f ↦ Spec.map (CommRingCat.ofHom f)) hι

/-- The actual geometric point from any allowed finite-field embedding.
Source: reviewed expansion step 1 (blueprint: lem-zl-constant-geometric-stalk-unit). -/
def embeddingPoint (n : ℕ) (hn : 1 ≤ n)
    (x : D.extensionPoints Y₀ n hn) (ι : D.extensionSubfield n hn →+* D.k)
    (hι : ι.comp (D.extensionEmbedding n hn) = algebraMap D.k₀ D.k) :
    Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left :=
  pullback.lift (Spec.map (CommRingCat.ofHom ι) ≫ x.left) (𝟙 _)
    (embeddingPoint_compatible D Y₀ n hn x ι hι)

/-- The semilinear return for every base-field embedding into the closure.
Source: reviewed expansion step 1 (blueprint: lem-zl-constant-geometric-stalk-unit).
Proof: every embedding has image the unique subfield of cardinality q^n. The nth
geometric Frobenius fixes it pointwise. Compare the two projections of the geometric
fiber pullback: the model maps agree by this fixed-field calculation and the closure
maps agree by the geometric Frobenius definition. Pullback uniqueness proves return. -/
theorem embeddingPoint_return (n : ℕ) (hn : 1 ≤ n)
    (x : D.extensionPoints Y₀ n hn) (ι : D.extensionSubfield n hn →+* D.k)
    (hι : ι.comp (D.extensionEmbedding n hn) = algebraMap D.k₀ D.k) :
    embeddingPoint D Y₀ n hn x ι hι ≫
        localPositivePower (D.geometricFrobenius Y₀).hom (n - 1) =
      localPositivePower (frobeniusPointIso D).hom (n - 1) ≫
        embeddingPoint D Y₀ n hn x ι hι := by
  let := Fintype.ofFinite D.k₀
  have hc : Nat.card (D.extensionSubfield n hn) = D.q ^ n :=
    (FiniteField.exists_unique_subfield_of_closure D.p D.a D.q D.prime D.exponent_pos
      D.cardinality_eq D.k₀ D.card_base D.k n hn).choose_spec.2.1
  have hq : 0 < D.q := by
    rw [← D.card_base]
    exact Nat.card_pos
  have : Finite (D.extensionSubfield n hn) :=
    (Nat.card_pos_iff.mp (by rw [hc]; exact pow_pos hq n)).2
  have hc' : Nat.card (D.extensionSubfield n hn) = Fintype.card D.k₀ ^ n := by
    simpa only [← D.card_base, Nat.card_eq_fintype_card] using hc
  apply localLift_return D Y₀ (n - 1)
  rw [← Category.assoc]
  suffices h : localPositivePower (frobeniusPointIso D).hom (n - 1) ≫
      Spec.map (CommRingCat.ofHom ι) = Spec.map (CommRingCat.ofHom ι) by rw [h]
  rw [localPointPower_eq, Nat.sub_add_cancel hn, ← Spec.map_comp]
  congr 1
  ext a
  exact FiniteField.geometricFrobeniusAlgEquivOfAlgebraic_pow_apply_of_card_eq
    D.k₀ D.k n hc' ι a

/-- The finite local operator is the coefficient identity under the canonical stalk iso.
Source: reviewed expansion steps 1--5 (blueprint: lem-zl-constant-geometric-stalk-unit).
Proof: the image of F_(q^n) is the unique subfield of its order, fixed pointwise by
geometric Frobenius to the nth power. Pullback uniqueness gives the semilinear return,
as in localExtensionPoint_return. Finite unit multiplication sends z tensor b to
c(z)b, commutes with the actual pullback compositor, and identifies the iterated
Weil maps with unit multiplication. Restriction, insertion in the inverse-image
colimit and sheafification all preserve a constant a. The tensor unit and multiplication
then send a to a. Naturality repeats the calculation at every transport in the iterate.
The return square has the same coefficient coordinates on both paths. Thus the entire
local composite is identity, including n=1 and m=0 (exponent one). -/
theorem finiteOperator_unit (n : ℕ) (hn : 1 ≤ n) (x : D.extensionPoints Y₀ n hn)
    (ι : D.extensionSubfield n hn →+* D.k)
    (hι : ι.comp (D.extensionEmbedding n hn) = algebraMap D.k₀ D.k) (m : ℕ) :
    finiteOperator l E D hl Y₀ (embeddingPoint D Y₀ n hn x ι hι) m (n - 1)
        (embeddingPoint_return D Y₀ n hn x ι hι) ≫
      (finiteStalkUnit l E D Y₀ (embeddingPoint D Y₀ n hn x ι hι) m).hom =
        (finiteStalkUnit l E D Y₀ (embeddingPoint D Y₀ n hn x ι hι) m).hom := by
  sorry

/-- The completed integral local operator is identity on the whole derived stalk.
Source: reviewed expansion steps 1, 6 and 7 (blueprint: lem-zl-constant-geometric-stalk-unit).
Proof: the integral regular module is a flat-term K-flat model. Its finite reductions
are the regular quotient modules with the actual quotient transitions. The compatible
finite multiplication maps identify its pulled strict tower with the coefficient tower
at s. The zero-shifted-component comparison identifies the whole Roos complex with
the completed integral unit. Sectionwise limits and completeness identify sections
with O_E, and all projections with the quotient maps. The normalized inverse-image
comparison and whole-system point-transport power laws identify the actual integral
local operator with this reconstructed finite identity. This uses equality of strict
system maps and their normalized cone maps, not detection by unrelated finite reductions. -/
theorem integralOperator_unit (n : ℕ) (hn : 1 ≤ n) (x : D.extensionPoints Y₀ n hn)
    (ι : D.extensionSubfield n hn →+* D.k)
    (hι : ι.comp (D.extensionEmbedding n hn) = algebraMap D.k₀ D.k) :
    integralOperator l E D hl Y₀ (embeddingPoint D Y₀ n hn x ι hι) (n - 1)
        (embeddingPoint_return D Y₀ n hn x ι hι) ≫
      (integralStalkUnit l E D Y₀ (embeddingPoint D Y₀ n hn x ι hι)).hom =
        (integralStalkUnit l E D Y₀ (embeddingPoint D Y₀ n hn x ι hι)).hom := by
  sorry



/-- The fraction-field tensor of the regular integral module is the regular field module.
Source: reviewed expansion step 8 (blueprint: lem-zl-constant-geometric-stalk-unit). -/
def rationalRegular :
    (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (pointIntegralToField l E)).obj
        (ModuleCat.of (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))
          (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))) ≅
      ModuleCat.of (ULift.{u + 1} E) (ULift.{u + 1} E) :=
  letI := (pointIntegralToField l E).toAlgebra
  (TensorProduct.AlgebraTensorModule.rid (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))
    (ULift.{u + 1} E) (ULift.{u + 1} E)).toModuleIso

/-- The actual rational stalk lifted to the section universe is the tensor of its
integral stalk; these are the prescribed object identities and size-descent counit.
Source: reviewed expansion step 8 (blueprint: lem-zl-constant-geometric-stalk-unit). -/
def rationalFibreComparison (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) :
    (pointFibreModuleLift E).mapDerivedCategory.obj
        (localPointComplex l E D hl Y₀ (constantWeilRationalComplex l E D hl Y₀) x).obj ≅
      (ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
        (pointIntegralToField l E)).mapDerivedCategory.obj
          ((pointFibreIntegralAmbient D l E).obj (integralStalk l E D hl Y₀ x).obj) :=
  letI := frobeniusPointPrimeInvertible D l hl
  letI := sfWeilPrimeInvertible D l hl Y₀
  letI := pointFibreSizeLift_equivalence E
  (pointFibreModuleLift E).mapDerivedCategory.mapIso
    ((DerivedCategory.pointFiniteDimensional E).ι.mapIso
      ((pointRationalFibre D l hl E).mapIso
        (localPullbackObjectIso l E x
          (constantWeilRationalObject l E D hl (D.geometricFiber Y₀).left)) ≪≫
        pointRationalFibreObjIso D l hl E
          ((sfRationalConstructibleLocalization l E (Spec (.of D.k))).obj
            (integralStalk l E D hl Y₀ x)))) ≪≫
    (DerivedCategory.pointFiniteDimensional (ULift.{u + 1} E)).ι.mapIso
      ((pointFibreSizeLift E).asEquivalence.counitIso.app
        (pointFibreRationalLarge D l hl E (integralStalk l E D hl Y₀ x)))

/-- The canonical large rational unit identification, obtained by tensoring the integral one.
Source: reviewed expansion step 8 (blueprint: lem-zl-constant-geometric-stalk-unit). -/
def rationalStalkUnitLarge (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) :=
  rationalFibreComparison l E D hl Y₀ x ≪≫
    (ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
      (pointIntegralToField l E)).mapDerivedCategory.mapIso (integralStalkUnit l E D Y₀ x) ≪≫
    ((ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
      (pointIntegralToField l E)).mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso (rationalRegular l E) ≪≫
    ((pointFibreModuleLift E).mapDerivedCategorySingleFunctor 0).symm.app (ModuleCat.of E E)

/-- The small rational unit is uniquely determined by its actual scalar-normalization square.
Source: reviewed expansion step 8 (blueprint: lem-zl-constant-geometric-stalk-unit).
Proof: the large map is integral unit multiplication tensor E, with the specified
rational object comparisons and size-descent counit. Its source and target have bounded
finite-dimensional cohomology. The equivalence pointFibreSizeLift is fully faithful
on this subcategory, so the large map and its inverse descend uniquely. Faithfulness
reflects both inverse equations. This gives a unique isomorphism with the displayed
normalization, not an arbitrary choice of a point-unit isomorphism. -/
theorem rationalStalkUnit_existsUnique
    (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) :
    ∃! e : (localPointComplex l E D hl Y₀
        (constantWeilRationalComplex l E D hl Y₀) x).obj ≅
          (DerivedCategory.singleFunctor _ 0).obj (ModuleCat.of E E),
      (pointFibreModuleLift E).mapDerivedCategory.mapIso e =
        rationalStalkUnitLarge l E D hl Y₀ x := by
  classical
  let p := DerivedCategory.pointFiniteDimensional E
  let q := DerivedCategory.pointFiniteDimensional (ULift.{u + 1} E)
  let J := p.ι ⋙ (pointFibreModuleLift E).mapDerivedCategory
  let := pointFibreSizeLift_equivalence E
  let J₀ := pointFibreSizeLift E ⋙ q.ι
  let eJ : J₀ ≅ J :=
    q.liftCompιIso (p.ι ⋙ (pointFibreModuleLift E).mapDerivedCategory)
      (pointFibreModuleLift_mem E)
  have : J₀.Full := by dsimp only [J₀]; infer_instance
  have : J₀.Faithful := by dsimp only [J₀]; infer_instance
  let ff := (Functor.FullyFaithful.ofFullyFaithful J₀).ofIso eJ
  have : J.Full := ff.full
  have : J.Faithful := ff.faithful
  let V := (DerivedCategory.singleFunctor (ModuleCat.{u} E) 0).obj (ModuleCat.of E E)
  have hV : p V := by
    refine ⟨⟨{0}, fun i hi ↦ ?_⟩, fun i ↦ ?_⟩
    · exact DerivedCategory.isZero_homologyFunctor_obj_of_iso_singleFunctor
        (Iso.refl V) (by simpa only [Finset.mem_singleton] using hi)
    · by_cases hi : i = 0
      · subst i
        let e₀ : (DerivedCategory.homologyFunctor (ModuleCat.{u} E) 0).obj V ≅
            ModuleCat.of E E :=
          (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} E) 0).app _
        exact e₀.symm.toLinearEquiv.finiteDimensional
      · have hz := DerivedCategory.isZero_homologyFunctor_obj_of_iso_singleFunctor
          (Iso.refl V) hi
        have := ModuleCat.isZero_iff_subsingleton.mp hz
        infer_instance
  let X : p.FullSubcategory := localPointComplex l E D hl Y₀
    (constantWeilRationalComplex l E D hl Y₀) x
  let Y : p.FullSubcategory := ⟨V, hV⟩
  let a : J.obj X ≅ J.obj Y := rationalStalkUnitLarge l E D hl Y₀ x
  let e : X ≅ Y := J.preimageIso a
  refine ⟨p.ι.mapIso e, ?_, ?_⟩
  · change J.mapIso e = a
    ext
    exact J.map_preimage a.hom
  · intro e' he'
    let b : X ≅ Y := p.ι.preimageIso e'
    have hb : J.mapIso b = a := by
      change (pointFibreModuleLift E).mapDerivedCategory.mapIso (p.ι.mapIso b) = a
      have h : p.ι.mapIso b = e' := by
        ext
        exact p.ι.map_preimage (X := X) (Y := Y) e'.hom
      rw [h]
      exact he'
    have he : J.mapIso e = a := by ext; exact J.map_preimage a.hom
    have hbe : b = e := J.mapIso_injective (hb.trans he.symm)
    calc
      e' = p.ι.mapIso b := by
        ext
        exact (p.ι.map_preimage (X := X) (Y := Y) e'.hom).symm
      _ = p.ι.mapIso e := congrArg (fun t ↦ p.ι.mapIso t) hbe

/-- The rational geometric stalk identification with E[0], normalized by integral tensor.
Source: reviewed expansion step 8 (blueprint: lem-zl-constant-geometric-stalk-unit). -/
def rationalStalkUnit (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) :=
  (rationalStalkUnit_existsUnique l E D hl Y₀ x).exists.choose

/-- The actual rational operator is tensor of the actual integral operator, under
the prescribed rational point comparison, so rationalization respects operator equality.
Source: reviewed expansion step 8 (blueprint: lem-zl-constant-geometric-stalk-unit).
Proof: localPullbackObjectIso identifies the underlying integral objects. The rational
Weil map, composition maps and transport are the localized integral maps. Naturality
of the size-descent counit then identifies each factor of the two local composites.
Exact scalar extension preserves their composition, yielding the displayed square. -/
theorem rationalOperator_scalar (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left)
    (r : ℕ) (h : x ≫ localPositivePower (D.geometricFrobenius Y₀).hom r =
      localPositivePower (frobeniusPointIso D).hom r ≫ x) :
    (pointFibreModuleLift E).mapDerivedCategory.map
        (localFrobeniusOperator l E D hl Y₀
          (constantWeilRationalComplex l E D hl Y₀) x r h).hom ≫
      (rationalFibreComparison l E D hl Y₀ x).hom =
        (rationalFibreComparison l E D hl Y₀ x).hom ≫
          (ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
            (pointIntegralToField l E)).mapDerivedCategory.map
              (integralOperator l E D hl Y₀ x r h) := by
  sorry


/-- The rational local operator is identity in the same canonical coefficient coordinates.
Source: reviewed expansion steps 1 and 8 (blueprint: lem-zl-constant-geometric-stalk-unit).
Proof: theta_E and rational point transport are the images of their integral counterparts
under exact tensor with E, with the recorded boundary comparisons. The rational pullback
compositors are the localized integral ones, so all three factors of localFrobeniusOperator
are the corresponding integral factors after tensor. Apply integralOperator_unit to the
whole-system identity, tensor it with E, and cancel the specified size equivalence. The
normalization of rationalStalkUnit makes its coefficient coordinate exactly E[0]. -/
theorem rationalOperator_unit (n : ℕ) (hn : 1 ≤ n) (x : D.extensionPoints Y₀ n hn)
    (ι : D.extensionSubfield n hn →+* D.k)
    (hι : ι.comp (D.extensionEmbedding n hn) = algebraMap D.k₀ D.k) :
    (localFrobeniusOperator l E D hl Y₀
        (constantWeilRationalComplex l E D hl Y₀)
        (embeddingPoint D Y₀ n hn x ι hι) (n - 1)
        (embeddingPoint_return D Y₀ n hn x ι hι)).hom ≫
      (rationalStalkUnit l E D hl Y₀ (embeddingPoint D Y₀ n hn x ι hι)).hom =
        (rationalStalkUnit l E D hl Y₀ (embeddingPoint D Y₀ n hn x ι hι)).hom := by
  let xbar := embeddingPoint D Y₀ n hn x ι hι
  let hreturn := embeddingPoint_return D Y₀ n hn x ι hι
  have hI : integralOperator l E D hl Y₀ xbar (n - 1) hreturn = 𝟙 _ := by
    apply (cancel_mono (integralStalkUnit l E D Y₀ xbar).hom).mp
    simpa only [Category.id_comp] using integralOperator_unit l E D hl Y₀ n hn x ι hι
  let := pointFibreSizeLift_equivalence E
  have hR : localFrobeniusOperator l E D hl Y₀
      (constantWeilRationalComplex l E D hl Y₀) xbar (n - 1) hreturn = 𝟙 _ := by
    apply (pointFibreSizeLift E).map_injective
    rw [CategoryTheory.Functor.map_id]
    apply ObjectProperty.hom_ext
    change (pointFibreModuleLift E).mapDerivedCategory.map
      (localFrobeniusOperator l E D hl Y₀
        (constantWeilRationalComplex l E D hl Y₀) xbar (n - 1) hreturn).hom = 𝟙 _
    apply (cancel_mono (rationalFibreComparison l E D hl Y₀ xbar).hom).mp
    rw [rationalOperator_scalar, hI]
    simp only [Category.id_comp]
    exact (congrArg (fun t ↦ (rationalFibreComparison l E D hl Y₀ xbar).hom ≫ t)
      ((ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
        (pointIntegralToField l E)).mapDerivedCategory.map_id _)).trans (Category.comp_id _)
  change (localFrobeniusOperator l E D hl Y₀
    (constantWeilRationalComplex l E D hl Y₀) xbar (n - 1) hreturn).hom ≫ _ = _
  rw [hR]
  exact Category.id_comp _


end WeilConjectures.ConstantGeometricStalkUnit

