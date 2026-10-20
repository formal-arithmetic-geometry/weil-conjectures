/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q151
-/
module

public import Sheaf.Paper.FixedFinitePositiveCoefficientTwist
public import Sheaf.Paper.IntrinsicCoefficientTwists
public import Sheaf.Paper.PbcCohomologySheaves

/-! # The recorded Tate twists in the PBC finite-stage coordinates

Source: blueprint def-coefficient-twists-detailed, signed powers and tensor with a complex;
Bhatt--Scholze, Section 6.8 (blueprint: def-coefficient-twists-detailed).
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

/-- Ordinary tensor of vector-space morphisms, with independent module/coefficient sizes.
Source: blueprint fibre tensor convention
(blueprint: def-coefficient-twists-detailed). -/
def pbcFibreTensorMap (R : Type w) [CommRing R]
    {V W : ModuleCat.{v} R} (f : V ⟶ W) (L : ModuleCat.{v} R) :
    ModuleCat.of R (V ⊗[R] L) ⟶ ModuleCat.of R (W ⊗[R] L) :=
  ModuleCat.ofHom (f.hom.rTensor L)

/-- Functor laws for ordinary tensor, without equating ring and module universes.
Source: blueprint fibre tensor convention
(blueprint: def-coefficient-twists-detailed).
Proof: on a pure tensor v tensor z the map is f(v) tensor z. The identity map
therefore fixes every pure tensor, and the two composite maps send it to
 g(f(v)) tensor z. Pure tensors generate, so the maps are equal. -/
theorem pbcFibreTensor_laws (R : Type w) [CommRing R] (L : ModuleCat.{v} R) :
    (∀ V : ModuleCat.{v} R,
      pbcFibreTensorMap R (𝟙 V) L = 𝟙 (ModuleCat.of R (V ⊗[R] L))) ∧
    (∀ (V W Z : ModuleCat.{v} R) (f : V ⟶ W) (g : W ⟶ Z),
      pbcFibreTensorMap R (f ≫ g) L =
        pbcFibreTensorMap R f L ≫ pbcFibreTensorMap R g L) := by
  sorry

/-- Ordinary tensor with the given fibre line. This uses TensorProduct itself;
no monoidal unit or equality of coefficient and module universes is required.
Source: blueprint fibre tensor convention
(blueprint: def-coefficient-twists-detailed). -/
def pbcFibreTensorRight (R : Type w) [CommRing R] (L : ModuleCat.{v} R) :
    ModuleCat.{v} R ⥤ ModuleCat.{v} R where
  obj V := ModuleCat.of R (V ⊗[R] L)
  map f := pbcFibreTensorMap R f L
  map_id V := (pbcFibreTensor_laws R L).1 V
  map_comp f g := (pbcFibreTensor_laws R L).2 _ _ _ f g

variable (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
  [hInv : Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]

/-- Invertibility in the local rings gives invertibility in every residue field.
Source: blueprint coefficient convention
(blueprint: def-coefficient-twists-detailed).
Proof: apply the local-ring-to-residue-field homomorphism to the given inverse;
its product equations remain the product equations for the image of l. -/
theorem pbcTwistResidueUnit (x : X) : IsUnit (l : X.residueField x) := by
  sorry

/-- The inverse required by the published root-line construction.
Source: blueprint coefficient convention
(blueprint: def-coefficient-twists-detailed). -/
instance pbcTwistResidueInvertible (x : X) : Invertible (l : X.residueField x) :=
  (pbcTwistResidueUnit l X x).invertible

variable (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The recorded signed root line, transported along the fixed coefficient isomorphism.
Source: blueprint signed-power definition
(blueprint: def-coefficient-twists-detailed). -/
def pbcTateLineSheaf (m : ℤ) : pbcModules X (pbcAdicCompletion X (pbcIntegralDatum l E)) :=
  (pbcRestrict (purCoefficientIso l E X).hom).obj
    (coefficientTwistLine X
      (R := completedIntegralCommRingSheafUnrestricted l E X) (purTwistIntegralModule X l E) m)

/-- Ordinary sheaf tensor by the same line, in the actual PBC module category.
Source: blueprint tensor-twist definition
(blueprint: def-coefficient-twists-detailed). -/
def pbcTateSheafTensor (m : ℤ) :
    pbcModules X (pbcAdicCompletion X (pbcIntegralDatum l E)) ⥤
      pbcModules X (pbcAdicCompletion X (pbcIntegralDatum l E)) :=
  purOrdinaryCoefficientModel l E X ⋙ integralSheafTwist l E X m ⋙
    pbcRestrict (purCoefficientIso l E X).hom

/-- The transported tensor is additive.
Source: blueprint flat rank-one line
(blueprint: def-coefficient-twists-detailed). -/
instance pbcTateSheafTensor_additive (m : ℤ) : (pbcTateSheafTensor l X E m).Additive := by
  unfold pbcTateSheafTensor
  infer_instance

/-- The transported tensor preserves kernels and finite products.
Source: blueprint flat rank-one line
(blueprint: def-coefficient-twists-detailed). -/
instance pbcTateSheafTensor_limits (m : ℤ) :
    PreservesFiniteLimits (pbcTateSheafTensor l X E m) := by
  have : PreservesFiniteLimits (pbcRestrict (purCoefficientIso l E X).hom) :=
    pbcRestrict_limits _
  have := comp_preservesFiniteLimits (integralSheafTwist l E X m)
    (pbcRestrict (purCoefficientIso l E X).hom)
  exact comp_preservesFiniteLimits (purOrdinaryCoefficientModel l E X)
    (integralSheafTwist l E X m ⋙ pbcRestrict (purCoefficientIso l E X).hom)

/-- The transported tensor preserves cokernels and finite coproducts.
Source: blueprint flat rank-one line
(blueprint: def-coefficient-twists-detailed). -/
instance pbcTateSheafTensor_colimits (m : ℤ) :
    PreservesFiniteColimits (pbcTateSheafTensor l X E m) := by
  have : PreservesFiniteColimits (pbcRestrict (purCoefficientIso l E X).hom) :=
    pbcRestrict_colimits _
  have := comp_preservesFiniteColimits (integralSheafTwist l E X m)
    (pbcRestrict (purCoefficientIso l E X).hom)
  exact comp_preservesFiniteColimits (purOrdinaryCoefficientModel l E X)
    (integralSheafTwist l E X m ⋙ pbcRestrict (purCoefficientIso l E X).hom)

/-- The actual derived tensor: flatness permits termwise tensor on every complex.
Source: blueprint tensor-twist definition
(blueprint: def-coefficient-twists-detailed). -/
def pbcTateAmbient (m : ℤ) :
    PbcCompletedDerived X (pbcIntegralDatum l E) ⥤
      PbcCompletedDerived X (pbcIntegralDatum l E) :=
  (pbcTateSheafTensor l X E m).mapDerivedCategory

/-- Additivity of the exact derived tensor.
Source: blueprint tensor-twist definition
(blueprint: def-coefficient-twists-detailed). -/
instance pbcTateAmbient_additive (m : ℤ) : (pbcTateAmbient l X E m).Additive := by
  unfold pbcTateAmbient
  infer_instance

/-- Derived tensor is linear for the canonical constant-section action.
Source: blueprint tensor-twist definition
(blueprint: def-coefficient-twists-detailed).
Proof: tensor balancing moves a constant coefficient through a pure tensor. Both
coefficient restrictions preserve that same constant by their finite-projection
normalization. The equation holds termwise and therefore on derived roofs. -/
theorem pbcTateAmbient_linear (m : ℤ) :
    (pbcTateAmbient l X E m).Linear (PbcIntegralRing l E) := by
  sorry

/-- Linearity of the actual derived tensor.
Source: blueprint tensor-twist definition
(blueprint: def-coefficient-twists-detailed). -/
instance pbcTateAmbient_linearInstance (m : ℤ) :
    (pbcTateAmbient l X E m).Linear (PbcIntegralRing l E) :=
  pbcTateAmbient_linear l X E m

/-- Tensor by the root line preserves the three defining integral conditions.
Source: blueprint integral tensor-twist definition
(blueprint: def-coefficient-twists-detailed).
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

variable (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  [IsNoetherian X]
  [hDim : Fact (∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞))]

/-- Rational tensor by the actual signed line at the specified finite field.
Source: blueprint rational tensor-twist definition
(blueprint: def-coefficient-twists-detailed). -/
def pbcTateRational (F : Padic.FiniteCoefficientFields l Ω) (m : ℤ) :
    pbcStageCategory l Ω X F ⥤ pbcStageCategory l Ω X F :=
  pbcConditionalRational (pbcStageDatum.{u} l Ω F)
    (pbcTateAmbient l X (pbcFiniteField.{u} l Ω F) m)
    (pbcTateAmbient_mem l X (pbcFiniteField.{u} l Ω F) hDim.out m)
    (pbcStageUniformizer.{u} l Ω F)

/-- The Qbar twist is formed on its actual integral representative and rationalized
at the same finite stage, exactly as prescribed in the coefficient definition.
Its codomain records that it is still a bounded constructible Qbar complex.
Source: blueprint common-stage tensor-twist definition
(blueprint: def-coefficient-twists-detailed). -/
def pbcTateTwist (M : pbcQbarCategory l Ω X) (m : ℤ) : pbcQbarCategory l Ω X :=
  ⟨M.stage, (pbcTateRational l X Ω M.stage m).obj M.obj⟩

/-- The same signed coefficient line evaluated at a geometric point and extended
to Qbar. It is placed in degree zero before taking the completed geometric fibre.
Source: blueprint coefficient-line convention
(blueprint: def-coefficient-twists-detailed). -/
def pbcTateLineFibre (F : Padic.FiniteCoefficientFields l Ω) (m : ℤ)
    (κ : Type u) [Field κ] [IsAlgClosed κ] (x : Spec (.of κ) ⟶ X) :
    ModuleCat.{max (u + 1) w} Ω :=
  (pbcStageCohomologyFibre l Ω X F κ x 0).obj
    ((DerivedCategory.singleFunctor _ 0).obj
      (pbcTateLineSheaf l X (pbcFiniteField.{u} l Ω F) m))

/-- The two integral sides of the cohomology-tensor comparison, before localization.
Source: blueprint tensor-twist definition and exact ordinary tensor
(blueprint: def-coefficient-twists-detailed). -/
def pbcTateCohomologyLeft (F : Padic.FiniteCoefficientFields l Ω) (m a : ℤ) :
    pbcIntegralStage l Ω X F ⥤ pbcStageModules l Ω X F :=
  pbcStageInclusion l Ω X F ⋙ pbcTateAmbient l X (pbcFiniteField.{u} l Ω F) m ⋙
    DerivedCategory.homologyFunctor _ a

/-- Ordinary sheaf tensor of the integral cohomology sheaf with the line.
Source: blueprint tensor-twist definition
(blueprint: def-coefficient-twists-detailed). -/
def pbcTateCohomologyRight (F : Padic.FiniteCoefficientFields l Ω) (m a : ℤ) :
    pbcIntegralStage l Ω X F ⥤ pbcStageModules l Ω X F :=
  pbcStageCohomology l Ω X F a ⋙ pbcTateSheafTensor l X (pbcFiniteField.{u} l Ω F) m

/-- Both sides are additive and linear, so their canonical comparison descends to
all rational morphisms, not only integral arrows.
Source: blueprint tensor-twist definition
(blueprint: def-coefficient-twists-detailed).
Proof: cohomology is additive and coefficient-linear on kernels modulo images.
Tensor has the same properties by balancing and the fixed coefficient transport.
Composition retains both identities. They extend to fractions after inverting
the same uniformizer, since every Hom is the displayed scalar tensor module. -/
theorem pbcTateCohomology_linear (F : Padic.FiniteCoefficientFields l Ω) (m a : ℤ) :
    (pbcTateCohomologyLeft l X Ω F m a).Additive ∧
    (pbcTateCohomologyLeft l X Ω F m a).Linear
      (PbcIntegralRing l (pbcFiniteField.{u} l Ω F)) ∧
    (pbcTateCohomologyRight l X Ω F m a).Additive ∧
    (pbcTateCohomologyRight l X Ω F m a).Linear
      (PbcIntegralRing l (pbcFiniteField.{u} l Ω F)) := by
  sorry

/-- Additivity on the left of the comparison.
Source: blueprint tensor-twist definition (blueprint: def-coefficient-twists-detailed). -/
instance pbcTateCohomologyLeft_additive (F : Padic.FiniteCoefficientFields l Ω) (m a : ℤ) :
    (pbcTateCohomologyLeft l X Ω F m a).Additive :=
  (pbcTateCohomology_linear l X Ω F m a).1

/-- Linearity on the left of the comparison.
Source: blueprint tensor-twist definition (blueprint: def-coefficient-twists-detailed). -/
instance pbcTateCohomologyLeft_linear (F : Padic.FiniteCoefficientFields l Ω) (m a : ℤ) :
    (pbcTateCohomologyLeft l X Ω F m a).Linear
      (PbcIntegralRing l (pbcFiniteField.{u} l Ω F)) :=
  (pbcTateCohomology_linear l X Ω F m a).2.1

/-- Additivity on the right of the comparison.
Source: blueprint tensor-twist definition (blueprint: def-coefficient-twists-detailed). -/
instance pbcTateCohomologyRight_additive (F : Padic.FiniteCoefficientFields l Ω) (m a : ℤ) :
    (pbcTateCohomologyRight l X Ω F m a).Additive :=
  (pbcTateCohomology_linear l X Ω F m a).2.2.1

/-- Linearity on the right of the comparison.
Source: blueprint tensor-twist definition (blueprint: def-coefficient-twists-detailed). -/
instance pbcTateCohomologyRight_linear (F : Padic.FiniteCoefficientFields l Ω) (m a : ℤ) :
    (pbcTateCohomologyRight l X Ω F m a).Linear
      (PbcIntegralRing l (pbcFiniteField.{u} l Ω F)) :=
  (pbcTateCohomology_linear l X Ω F m a).2.2.2

/-- The canonical cohomology-tensor comparison on the rational finite stage. It is
natural for every rationalized arrow by transportNat, including denominators.
Source: blueprint cohomology convention and flat Tate tensor
(blueprint: def-coefficient-twists-detailed). -/
def pbcTateCohomologyMap (F : Padic.FiniteCoefficientFields l Ω) (m a : ℤ) :
    ScalarLocalization.transport (PbcIntegralRing l (pbcFiniteField.{u} l Ω F))
        (pbcStageUniformizer.{u} l Ω F) (pbcTateCohomologyLeft l X Ω F m a) ⟶
      ScalarLocalization.transport (PbcIntegralRing l (pbcFiniteField.{u} l Ω F))
        (pbcStageUniformizer.{u} l Ω F) (pbcTateCohomologyRight l X Ω F m a) :=
  ScalarLocalization.transportNat (PbcIntegralRing l (pbcFiniteField.{u} l Ω F))
    (pbcStageUniformizer.{u} l Ω F)
    (Functor.whiskerLeft (pbcStageInclusion l Ω X F)
      (Functor.mapDerivedCategoryHomologyFunctorIso
        (pbcTateSheafTensor l X (pbcFiniteField.{u} l Ω F) m) a).inv)

end AlgebraicGeometry.Scheme
