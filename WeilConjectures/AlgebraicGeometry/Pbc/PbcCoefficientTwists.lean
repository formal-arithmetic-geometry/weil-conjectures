/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.FixedFinitePositiveCoefficientTwist
public import WeilConjectures.SmoothPurity.Supporting.Coefficient.IntrinsicCoefficientTwists
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcCohomologySheaves
import all WeilConjectures.Algebra.Homology.LineEvaluation.LineEvaluationInversePair
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients

/-! # The recorded Tate twists in the PBC finite-stage coordinates

Source: blueprint definition-tate-twists, signed powers and tensor with a complex;
Bhatt--Scholze, Section 6.8 (blueprint: definition-tate-twists).
All roots, signed powers and coefficient identifications are the published ones.
The only new construction is their transport to the PBC completed coefficient ring.
The original finite, integral, rational and intrinsic Qbar interfaces remain imported.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u w v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped TensorProduct
open WeilConjectures
namespace AlgebraicGeometry.Scheme

variable (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
  [hInv : Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]

variable (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

variable (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  [IsNoetherian X]
  [hDim : Fact (∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞))]

/-- The recorded signed root line, transported along the fixed coefficient isomorphism.
Source: blueprint signed-power definition
(blueprint: definition-tate-twists). -/
def pbcTateLineSheaf (m : ℤ) : pbcModules X (pbcAdicCompletion X (pbcIntegralDatum l E)) :=
  (pbcRestrict (purCoefficientIso l E X).hom).obj
    (coefficientTwistLine X
      (R := completedIntegralCommRingSheafUnrestricted l E X) (purTwistIntegralModule X l E) m)

/-- Ordinary sheaf tensor by the same line, in the actual PBC module category.
Source: blueprint tensor-twist definition
(blueprint: definition-tate-twists). -/
def pbcTateSheafTensor (m : ℤ) :
    pbcModules X (pbcAdicCompletion X (pbcIntegralDatum l E)) ⥤
      pbcModules X (pbcAdicCompletion X (pbcIntegralDatum l E)) :=
  purOrdinaryCoefficientModel l E X ⋙ integralSheafTwist l E X m ⋙
    pbcRestrict (purCoefficientIso l E X).hom

omit [IsNoetherian X] hDim in
/-- The ordinary tensor twist is additive and exact.
Source: blueprint tensor-twist definition
(blueprint: definition-tate-twists).
Proof: both coefficient restrictions are exact, and tensor with the rank-one root
line is exact because l is invertible on every residue field. -/
theorem pbcTateSheafTensor_exact (m : ℤ) :
    (pbcTateSheafTensor l X E m).Additive ∧
      PreservesFiniteLimits (pbcTateSheafTensor l X E m) ∧
      PreservesFiniteColimits (pbcTateSheafTensor l X E m) := by
  let : ∀ x : X, Invertible (l : X.residueField x) := fun x ↦
    (show IsUnit (l : X.residueField x) from
      map_natCast (X.residue x).hom l ▸ (hInv.out x).map (X.residue x).hom).invertible
  have : (purOrdinaryCoefficientModel l E X).Additive := pbcRestrict_additive _
  have : (pbcRestrict (purCoefficientIso l E X).hom).Additive := pbcRestrict_additive _
  have : PreservesFiniteLimits (purOrdinaryCoefficientModel l E X) := pbcRestrict_limits _
  have : PreservesFiniteLimits (pbcRestrict (purCoefficientIso l E X).hom) :=
    pbcRestrict_limits _
  have : PreservesFiniteColimits (purOrdinaryCoefficientModel l E X) := pbcRestrict_colimits _
  have : PreservesFiniteColimits (pbcRestrict (purCoefficientIso l E X).hom) :=
    pbcRestrict_colimits _
  unfold pbcTateSheafTensor
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- Additivity of the ordinary tensor twist.
Source: blueprint tensor-twist definition
(blueprint: definition-tate-twists). -/
instance pbcTateSheafTensor_additive (m : ℤ) : (pbcTateSheafTensor l X E m).Additive :=
  (pbcTateSheafTensor_exact l X E m).1

/-- The ordinary tensor twist preserves finite limits.
Source: blueprint tensor-twist definition
(blueprint: definition-tate-twists). -/
instance pbcTateSheafTensor_finiteLimits (m : ℤ) :
    PreservesFiniteLimits (pbcTateSheafTensor l X E m) :=
  (pbcTateSheafTensor_exact l X E m).2.1

/-- The ordinary tensor twist preserves finite colimits.
Source: blueprint tensor-twist definition
(blueprint: definition-tate-twists). -/
instance pbcTateSheafTensor_finiteColimits (m : ℤ) :
    PreservesFiniteColimits (pbcTateSheafTensor l X E m) :=
  (pbcTateSheafTensor_exact l X E m).2.2

/-- The actual derived tensor: flatness permits termwise tensor on every complex.
Source: blueprint tensor-twist definition
(blueprint: definition-tate-twists). -/
def pbcTateAmbient (m : ℤ) :
    PbcCompletedDerived X (pbcIntegralDatum l E) ⥤
      PbcCompletedDerived X (pbcIntegralDatum l E) :=
  (pbcTateSheafTensor l X E m).mapDerivedCategory

omit hInv [IsNoetherian X] hDim in
set_option backward.isDefEq.respectTransparency.types false in
/-- The ordinary tensor twist commutes with the constant coefficient action.
Source: blueprint tensor-twist definition
(blueprint: definition-tate-twists).
Proof: transport the constant section through the coefficient isomorphism. Tensor
with the line commutes with multiplication by every global section, and both
coefficient restrictions leave sections and the transported action unchanged. -/
theorem pbcTateSheafTensor_linear (m : ℤ) :
    (pbcTateSheafTensor l X E m).Linear (PbcIntegralRing l E) := by
  let A := completedIntegralCommRingSheafUnrestricted l E X
  let J := ProEt.topology X
  let d := pbcIntegralDatum l E
  let e := purCoefficientIso l E X
  let : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let : MonoidalCategory (integralTowerModules l E X) :=
    @SheafOfModules.cochainModulesMonoidal.{u + 1, u, u + 1}
      X.ProEt inferInstance (essentiallySmallSelf.{0, u, u + 1} _) J inferInstance A
  let P := coefficientTwistLine X (R := A) (purTwistIntegralModule X l E) m
  let S := RingCat.sectionsSubring (A.obj ⋙ forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  let : Linear S (integralTowerModules l E X) :=
    SheafOfModules.homLinear A.obj
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A).property
  have ht : (MonoidalCategory.tensorRight P).Linear S :=
    @SheafOfModules.LineEvaluation.tensor_linear.{u + 1, u, u}
      X.ProEt inferInstance J (essentiallySmallSelf.{0, u, u + 1} _)
      (inferInstance : J.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})) A P
  have hs : (integralSheafTwist l E X m).Linear S :=
    Functor.linear_of_iso S (SheafOfModules.siteSheafTensorRightIso.{u + 1, u, u + 1} A P).symm
  constructor
  intro M N f a
  let s : S := ⟨fun U ↦ e.hom.hom.app U (pbcCompletedSection X d U a), fun {U V} g ↦ by
    change A.obj.map g (e.hom.hom.app U (pbcCompletedSection X d U a)) =
      e.hom.hom.app V (pbcCompletedSection X d V a)
    rw [← pbcCompletedSection_naturality X d U V g a]
    exact (ConcreteCategory.congr_hom (e.hom.hom.naturality g) _).symm⟩
  have h1 : (purOrdinaryCoefficientModel l E X).map (a • f) =
      s • (purOrdinaryCoefficientModel l E X).map f := by
    apply SheafOfModules.hom_ext
    ext U x
    change ((a • f).val.app U) x = _
    change _ = (e.inv.hom.app U (s.1 U)) • ((f.val.app U) x)
    change pbcCompletedSection X d U a • f.val.app U x = _
    have hc : e.inv.hom.app U (s.1 U) = pbcCompletedSection X d U a :=
      ConcreteCategory.congr_hom (congrArg (fun k ↦ k.hom.app U) e.hom_inv_id) _
    rw [hc]
  have h2 := hs.map_smul ((purOrdinaryCoefficientModel l E X).map f) s
  apply SheafOfModules.hom_ext
  ext U y
  change ((integralSheafTwist l E X m).map
    ((purOrdinaryCoefficientModel l E X).map (a • f))).val.app U y = _
  rw [h1, h2]
  rfl

omit [IsNoetherian X] hDim in
attribute [local instance] pbcTateSheafTensor_linear in
/-- Additivity and constant-coefficient linearity of the derived tensor twist.
Source: blueprint tensor-twist definition
(blueprint: definition-tate-twists).
Proof: the twist is exact and linear on sheaves, and derived localization preserves
both properties. -/
theorem pbcTateAmbient_linear (m : ℤ) :
    (pbcTateAmbient l X E m).Additive ∧
      (pbcTateAmbient l X E m).Linear (PbcIntegralRing l E) := by
  let F := pbcTateSheafTensor l X E m
  let C := pbcModules X (pbcAdicCompletion X (pbcIntegralDatum l E))
  refine ⟨by unfold pbcTateAmbient; infer_instance, ?_⟩
  unfold pbcTateAmbient
  have : Localization.Lifting DerivedCategory.Q (HomologicalComplex.quasiIso C (.up ℤ))
      (F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) F.mapDerivedCategory :=
    ⟨F.mapDerivedCategoryFactors⟩
  change F.mapDerivedCategory.Linear (PbcIntegralRing l E)
  rw [← Localization.functor_linear_iff DerivedCategory.Q
    (HomologicalComplex.quasiIso C (.up ℤ)) (PbcIntegralRing l E)
    (F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) F.mapDerivedCategory]
  infer_instance

/-- Additivity of the derived tensor twist.
Source: blueprint tensor-twist definition
(blueprint: definition-tate-twists). -/
instance pbcTateAmbient_additive (m : ℤ) : (pbcTateAmbient l X E m).Additive :=
  (pbcTateAmbient_linear l X E m).1

/-- Constant-coefficient linearity of the derived tensor twist.
Source: blueprint tensor-twist definition
(blueprint: definition-tate-twists). -/
instance pbcTateAmbient_isLinear (m : ℤ) :
    (pbcTateAmbient l X E m).Linear (PbcIntegralRing l E) :=
  (pbcTateAmbient_linear l X E m).2

omit [IsNoetherian X] in
/-- Tensor by the root line preserves the three defining integral conditions.
Source: blueprint integral tensor-twist definition
(blueprint: definition-tate-twists).
Proof: locally trivialize the root line on its compatible primitive-root covers.
Its positive powers, the unit, and its dual powers are invertible lines. Tensor
is locally the identity, commutes with each finite reduction, and preserves the
common bounded interval, stratification and normalized etale-origin witnesses.
It also preserves the completion comparison: a finite projective factor commutes
with the reduction tower and its derived limit. Descend along these covers and
transport through the finite-projection-normalized coefficient isomorphism. -/
theorem pbcTateAmbient_mem [IsNoetherian X]
    (_hDim : ∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞))
    (m : ℤ) (K : PbcBoundedConstructibleComplete X (pbcIntegralDatum l E)) :
    PbcIsBoundedConstructibleComplete X (pbcIntegralDatum l E)
      ((pbcTateAmbient l X E m).obj K.obj) := by
  sorry

/-- Rational tensor by the actual signed line at the specified finite field.
Source: blueprint rational tensor-twist definition
(blueprint: definition-tate-twists). -/
def pbcTateRational (F : Padic.FiniteCoefficientFields l Ω) (m : ℤ) :
    pbcStageCategory l Ω X F ⥤ pbcStageCategory l Ω X F :=
  pbcConditionalRational (pbcStageDatum.{u} l Ω F)
    (pbcTateAmbient l X (pbcFiniteField.{u} l Ω F) m)
    (pbcTateAmbient_mem l X (pbcFiniteField.{u} l Ω F) hDim.out m)
    (pbcStageUniformizer.{u} l Ω F)

end AlgebraicGeometry.Scheme
