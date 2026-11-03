/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProductComparisons.NativeSixFunctorKunnethMaps
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SFDualizableBiduality
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.ProEtaleFiniteLocallyProjective

import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.ProEtaleFiniteProjectiveDualizable
import WeilConjectures.CategoryTheory.DerivedCategory.SingleDualPairing.SingleDualPairing
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.KVGenerator.KVHomEvaluationFactorization

/-! # The generator comparison and its evaluation transpose

Source: `literature/blueprint/latest/blueprint/sec-six-functors/sk-thm-sf-kunneth-verdier/`,
`sk-thm-sf-kunneth-verdier.proof.md`, “Internal Hom and Verdier duals”, and
`prop-trf-external-hom.proof.md`, the displayed generator composite
(blueprint: lem-sf-kv-generator-evaluation).

All objects are in the ordinary derived category of internal modules over the
pulled-back condensed ring. The comparison to internal Hom is defined by its
uncurried evaluation, including the ordinary and exceptional counits. Its
invertibility is asserted below, separately from its definition. The product
comparison is the existing signed evaluation transpose, never a chosen arrow.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing.KVGenerator

open CompactificationReindexing RelativeKunneth ProductComparisons

variable (Λ : ScalarSixRing.{u})

/-- Coefficient evaluation tensored with the exceptional inverse-image target.
Source: generator calculation, step 1 (blueprint: lem-sf-kv-generator-evaluation). -/
def evaluate (X : Scheme.{u}) (K Q : D Λ.X X) :
    K ⊗ (coefficientDual Λ.X X K ⊗ Q) ⟶ Q :=
  (α_ _ _ _).inv ≫ (coefficientDualEvaluation Λ.X X K ▷ Q) ≫ (λ_ Q).hom

/-- The generator comparison, oriented from the ordinary pushforward to internal Hom.
Its transpose is exactly projection, ordinary counit, coefficient evaluation, and
exceptional counit, in that order.
Source: generator calculation, step 1 (blueprint: lem-sf-kv-generator-evaluation). -/
def homMap {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    (S : SixOperationsLocalizingAdjunction Λ.X c)
    (K : ConstantModelConstructibleFiniteTor Λ.X X)
    (L : ConstantModelConstructibleFiniteTor Λ.X Y) :
    (R Λ.X f).obj (coefficientDual Λ.X X K.obj ⊗
      ((exceptional Λ S).obj L).obj) ⟶
        (ihom ((lower Λ S).obj K).obj).obj L.obj :=
  MonoidalClosed.curry
    (pf Λ.X c K.obj _ ≫
      (F Λ.X c).map
        ((K.obj ◁ (derivedUpperStarLowerStarAdjunction Λ.X f).counit.app _) ≫
          evaluate Λ X K.obj ((exceptional Λ S).obj L).obj) ≫
      ((adjunction Λ S).counit.app L).hom)

/-- The actual uncurried factor evaluation, with the supplied two counits.
Source: generator calculation, steps 1 and 5
(blueprint: lem-sf-kv-comparison-normal-form). -/
def factorEvaluation {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    (S : SixOperationsLocalizingAdjunction Λ.X c)
    (K : ConstantModelConstructibleFiniteTor Λ.X X)
    (L : ConstantModelConstructibleFiniteTor Λ.X Y) :=
  pf Λ.X c K.obj _ ≫
    (F Λ.X c).map
      ((K.obj ◁ (derivedUpperStarLowerStarAdjunction Λ.X f).counit.app _) ≫
        evaluate Λ X K.obj ((exceptional Λ S).obj L).obj) ≫
    ((adjunction Λ S).counit.app L).hom

/-- The coefficient-dual tensor comparison factors through the ordinary tensor-Hom mate.
Source: generator calculation, step 1
(blueprint: lem-sf-kv-hom-evaluation-factorization).
Proof: apply projection naturality in the ordinary direct-image input, followed by
ordinary counit naturality and the defining transpose of ihomUnitTensorToIhom. -/
theorem homMap_factorization {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c : Compactification f} (S : SixOperationsLocalizingAdjunction Λ.X c)
    (K : ConstantModelConstructibleFiniteTor Λ.X X)
    (L : ConstantModelConstructibleFiniteTor Λ.X Y) :
    homMap Λ S K L =
      (R Λ.X f).map
        (MonoidalClosed.ihomUnitTensorToIhom K.obj ((exceptional Λ S).obj L).obj) ≫
      MonoidalClosed.curry
        (pf Λ.X c K.obj _ ≫
          (F Λ.X c).map
            ((K.obj ◁ (derivedUpperStarLowerStarAdjunction Λ.X f).counit.app _) ≫
              (ihom.ev K.obj).app ((exceptional Λ S).obj L).obj) ≫
          ((adjunction Λ S).counit.app L).hom) := by
  exact evaluation_comparison_factorization (F Λ.X c) (P Λ.X f) (R Λ.X f)
    (derivedUpperStarLowerStarAdjunction Λ.X f) (fun K N ↦ pf Λ.X c K N)
    (by
      intro K N N' b
      simpa only [pf] using
        exceptionalProjectionMorphismOfCompactification_natural_right Λ.X c K b)
    K.obj ((exceptional Λ S).obj L).obj L.obj ((adjunction Λ S).counit.app L).hom

/-- For a dualizable input, invertibility reduces to the normalized tensor-Hom mate.
Source: generator calculation, step 1
(blueprint: lem-sf-kv-hom-evaluation-factorization).
Proof: the dual-tensor-to-internal-Hom comparison is invertible by the exact pairing.
Ordinary direct image preserves this inverse. Use homMap_factorization. -/
theorem homMap_isIso_of_exchange {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c : Compactification f} (S : SixOperationsLocalizingAdjunction Λ.X c)
    (K : ConstantModelConstructibleFiniteTor Λ.X X)
    (L : ConstantModelConstructibleFiniteTor Λ.X Y) (hK : IsDualizable K.obj)
    (hex : IsIso (MonoidalClosed.curry
      (pf Λ.X c K.obj _ ≫
        (F Λ.X c).map
          ((K.obj ◁ (derivedUpperStarLowerStarAdjunction Λ.X f).counit.app _) ≫
            (ihom.ev K.obj).app ((exceptional Λ S).obj L).obj) ≫
        ((adjunction Λ S).counit.app L).hom))) :
    IsIso (homMap Λ S K L) := by
  have : IsIso
      (MonoidalClosed.ihomUnitTensorToIhom K.obj ((exceptional Λ S).obj L).obj) :=
    (dualizable_biduality Λ.X X K.obj hK).2.2 _
  have := hex
  rw [homMap_factorization]
  infer_instance

/-- The native ordinary external comparison is the adjunct of the tensor product
of the two pulled-back ordinary counits. This is the internal-module presentation
of Ku_* in sk-lem-sf-kunneth-star, without any invertibility assumption.
Source: generator calculation, step 3 (blueprint: lem-sf-kv-generator-evaluation). -/
def ordinary {k : Type u} [Field k] (G : Geometry k)
    (T₁ : D Λ.X G.X₁.obj.left) (T₂ : D Λ.X G.X₂.obj.left) :
    exterior Λ G.target ((R Λ.X G.f₁.hom.left).obj T₁)
      ((R Λ.X G.f₂.hom.left).obj T₂) ⟶
    (R Λ.X (G.q.hom.left ≫ G.v.hom.left)).obj (exterior Λ G.source T₁ T₂) :=
  let sq₁ : CommSq G.r₁.hom.left (G.q.hom.left ≫ G.v.hom.left)
      G.f₁.hom.left G.t₁.hom.left := ⟨by
    rw [← G.path₁]
    simp only [Category.assoc]
    rw [G.exchange₁.w]
    rw [← Category.assoc, G.relativeProduct.w]
    simp only [Category.assoc]⟩
  let sq₂ : CommSq G.r₂.hom.left (G.q.hom.left ≫ G.v.hom.left)
      G.f₂.hom.left G.t₂.hom.left :=
    ⟨by rw [← G.path₂]; simp only [Category.assoc]; rw [G.exchange₂.w]⟩
  (derivedUpperStarLowerStarAdjunction Λ.X (G.q.hom.left ≫ G.v.hom.left)).homEquiv _ _
    ((pullTensor Λ (G.q.hom.left ≫ G.v.hom.left) _ _).hom ≫
      (((pullbackSquareComparison Λ.X sq₁).hom.app _ ≫
          (P Λ.X G.r₁.hom.left).map
            ((derivedUpperStarLowerStarAdjunction Λ.X G.f₁.hom.left).counit.app T₁)) ⊗ₘ
        ((pullbackSquareComparison Λ.X sq₂).hom.app _ ≫
          (P Λ.X G.r₂.hom.left).map
            ((derivedUpperStarLowerStarAdjunction Λ.X G.f₂.hom.left).counit.app T₂))))

/-- The canonical product of coefficient duals, from the signed external Hom map
at the two coefficient units, followed by their strong monoidal unit identifications.
Source: generator calculation, step 2 (blueprint: lem-sf-kv-generator-evaluation). -/
def dualMap {k : Type u} [Field k] (G : Geometry k)
    (K₁ : D Λ.X G.X₁.obj.left) (K₂ : D Λ.X G.X₂.obj.left) :
    exterior Λ G.source (coefficientDual Λ.X G.X₁.obj.left K₁)
      (coefficientDual Λ.X G.X₂.obj.left K₂) ⟶
    coefficientDual Λ.X G.W.obj.left (exterior Λ G.source K₁ K₂) :=
  beta Λ G.r₁.hom.left G.r₂.hom.left K₁ (𝟙_ _) K₂ (𝟙_ _) ≫
    (ihom (exterior Λ G.source K₁ K₂)).map
      (((leftDerivedUpperStarUnitIso Λ.X G.r₁.hom.left).hom ⊗ₘ
        (leftDerivedUpperStarUnitIso Λ.X G.r₂.hom.left).hom) ≫ (λ_ _).hom)

set_option maxHeartbeats 1200000 in
-- Native derived functors require extra definitional comparisons in this specialization.
/-- The product-dual map preserves the signed product of the two evaluations.
Source: generator calculation, step 2
(blueprint: lem-sf-kv-generator-evaluation).
Proof: internal Hom carries the unit comparisons covariantly. Uncurrying its
composition with beta gives the middle-four interchange followed by the two
pullbacks of evaluation and the two unit comparisons. -/
theorem dualMap_evaluation {k : Type u} [Field k] (G : Geometry k)
    (K₁ : D Λ.X G.X₁.obj.left) (K₂ : D Λ.X G.X₂.obj.left) :
    let := DerivedCategory.braidedCategory'
      (Mod (Sheaf (ProEt.topology G.W.obj.left) Ab.{u + 1})
        (condensedRingObj Λ.X G.W.obj.left))
    MonoidalClosed.uncurry (dualMap Λ G K₁ K₂) =
      tensorμ _ _ _ _ ≫
        ((Functor.LaxMonoidal.μ (P Λ.X G.r₁.hom.left) _ _ ≫
          (P Λ.X G.r₁.hom.left).map
            (coefficientDualEvaluation Λ.X G.X₁.obj.left K₁)) ⊗ₘ
          (Functor.LaxMonoidal.μ (P Λ.X G.r₂.hom.left) _ _ ≫
            (P Λ.X G.r₂.hom.left).map
              (coefficientDualEvaluation Λ.X G.X₂.obj.left K₂))) ≫
        (((leftDerivedUpperStarUnitIso Λ.X G.r₁.hom.left).hom ⊗ₘ
          (leftDerivedUpperStarUnitIso Λ.X G.r₂.hom.left).hom) ≫ (λ_ _).hom) := by
  let := DerivedCategory.braidedCategory'
    (Mod (Sheaf (ProEt.topology G.W.obj.left) Ab.{u + 1})
      (condensedRingObj Λ.X G.W.obj.left))
  change _ = _
  unfold dualMap
  rw [MonoidalClosed.uncurry_natural_right]
  change MonoidalClosed.uncurry
    (MonoidalClosed.externalIhomMap (P Λ.X G.r₁.hom.left) (P Λ.X G.r₂.hom.left)
      K₁ (𝟙_ _) K₂ (𝟙_ _)) ≫ _ = _
  rw [MonoidalClosed.uncurry_externalIhomMap]
  simp only [Category.assoc]
  rfl

/-- Degree-zero finite locally projective modules retain their duals in the derived category.
Source: generator calculation, step 1; Stacks Project, Tag 08JJ
(blueprint: lem-sf-kv-generator-evaluation).
Proof: use the finite-projective sheaf dual, swap its exact pairing, and transport
that pairing through the degree-zero functor on flat objects. -/
theorem single_isDualizable (X : Scheme.{u}) (M : supportModules Λ.X X)
    (hM : IsFiniteLocallyProjective Λ.X X M) :
    IsDualizable ((DerivedCategory.singleFunctor _ 0).obj M) := by
  let := DerivedCategory.braidedCategory' (supportModules Λ.X X)
  obtain ⟨hdual⟩ := finiteLocallyProjective_isDualizable Λ.X X M hM
  let := hdual
  let : ExactPairing Mᘁ M := BraidedCategory.exactPairing_swap M Mᘁ
  obtain ⟨ep, _⟩ := DerivedCategory.SingleDualPairing.singleFunctor_exactPairing M Mᘁ
  let := ep
  exact ⟨{
    rightDual := (DerivedCategory.singleFunctor _ 0).obj Mᘁ
    exact := BraidedCategory.exactPairing_swap _ _ }⟩

/-- The specified product-dual comparison is invertible on dualizable inputs.
Source: generator calculation, step 2
(blueprint: lem-sf-kv-generator-evaluation).
Proof: the external internal-Hom comparison is invertible on exact dual pairs.
The remaining map applies internal Hom to the two monoidal unit comparisons,
which are isomorphisms. This includes the zero objects. -/
theorem dualMap_isIso {k : Type u} [Field k] (G : Geometry k)
    (K₁ : D Λ.X G.X₁.obj.left) (K₂ : D Λ.X G.X₂.obj.left)
    (hK₁ : IsDualizable K₁) (hK₂ : IsDualizable K₂) :
    IsIso (dualMap Λ G K₁ K₂) := by
  let := DerivedCategory.braidedCategory'
    (Mod (Sheaf (ProEt.topology G.W.obj.left) Ab.{u + 1})
      (condensedRingObj Λ.X G.W.obj.left))
  let := DerivedCategory.braidedCategory'
    (Mod (Sheaf (ProEt.topology G.X₁.obj.left) Ab.{u + 1})
      (condensedRingObj Λ.X G.X₁.obj.left))
  let := DerivedCategory.braidedCategory'
    (Mod (Sheaf (ProEt.topology G.X₂.obj.left) Ab.{u + 1})
      (condensedRingObj Λ.X G.X₂.obj.left))
  obtain ⟨d₁⟩ := hK₁
  obtain ⟨d₂⟩ := hK₂
  let := d₁
  let := d₂
  let : ExactPairing K₁ᘁ K₁ := BraidedCategory.exactPairing_swap K₁ K₁ᘁ
  let : ExactPairing K₂ᘁ K₂ := BraidedCategory.exactPairing_swap K₂ K₂ᘁ
  have : IsIso (beta Λ G.r₁.hom.left G.r₂.hom.left K₁ (𝟙_ _) K₂ (𝟙_ _)) := by
    exact MonoidalClosed.isIso_externalIhomMap_of_exactPairing
      (P Λ.X G.r₁.hom.left) (P Λ.X G.r₂.hom.left) K₁ᘁ K₁ (𝟙_ _) K₂ᘁ K₂ (𝟙_ _)
  unfold dualMap
  infer_instance

/-- The shuffle in the displayed generator composite. Its middle-four interchange
uses the native derived braiding, so it retains the Koszul sign.
Source: generator calculation, steps 2--3 (blueprint: lem-sf-kv-generator-evaluation). -/
def shuffle {k : Type u} [Field k] (G : Geometry k)
    (K₁ Q₁ : D Λ.X G.X₁.obj.left) (K₂ Q₂ : D Λ.X G.X₂.obj.left) :
    exterior Λ G.source (coefficientDual Λ.X G.X₁.obj.left K₁ ⊗ Q₁)
      (coefficientDual Λ.X G.X₂.obj.left K₂ ⊗ Q₂) ⟶
    coefficientDual Λ.X G.W.obj.left (exterior Λ G.source K₁ K₂) ⊗
      exterior Λ G.source Q₁ Q₂ :=
  letI := DerivedCategory.braidedCategory'
    (Mod (Sheaf (ProEt.topology G.W.obj.left) Ab.{u + 1})
      (condensedRingObj Λ.X G.W.obj.left))
  ((pullTensor Λ G.r₁.hom.left _ _).hom ⊗ₘ
    (pullTensor Λ G.r₂.hom.left _ _).hom) ≫
    tensorμ (C := D Λ.X G.W.obj.left) _ _ _ _ ≫ (dualMap Λ G K₁ K₂ ▷ exterior Λ G.source Q₁ Q₂)

set_option maxHeartbeats 1200000 in
-- Native derived functors require extra definitional comparisons in this specialization.
set_option maxHeartbeats 1200000 in
-- Native derived functors require extra definitional comparisons in this specialization.
set_option maxHeartbeats 1200000 in
-- Native derived functors require extra definitional comparisons in this specialization.
/-- The formal uncurrying of beta after the two generator comparisons.
Source: generator calculation, step 5
(blueprint: lem-sf-kv-comparison-normal-form).
Proof: specialize uncurry_external_after to the product pullbacks and the two
homMap morphisms. Their uncurrying is the defining factorEvaluation. -/
theorem uncurry_factor_beta {k : Type u} [Field k]
    (G : Geometry k) (c : ProductComparisons.Models G)
    (S₁ : SixOperationsLocalizingAdjunction Λ.X c.f₁)
    (S₂ : SixOperationsLocalizingAdjunction Λ.X c.f₂)
    (K₁ : ConstantModelConstructibleFiniteTor Λ.X G.X₁.obj.left)
    (K₂ : ConstantModelConstructibleFiniteTor Λ.X G.X₂.obj.left)
    (L₁ : ConstantModelConstructibleFiniteTor Λ.X G.Y₁.obj.left)
    (L₂ : ConstantModelConstructibleFiniteTor Λ.X G.Y₂.obj.left) :
    let := DerivedCategory.braidedCategory'
      (Mod (Sheaf (ProEt.topology G.T.obj.left) Ab.{u + 1})
        (condensedRingObj Λ.X G.T.obj.left))
    MonoidalClosed.uncurry
      (((P Λ.X G.t₁.hom.left).map (homMap Λ S₁ K₁ L₁) ⊗ₘ
        (P Λ.X G.t₂.hom.left).map (homMap Λ S₂ K₂ L₂)) ≫
        beta Λ G.t₁.hom.left G.t₂.hom.left
          ((lower Λ S₁).obj K₁).obj L₁.obj ((lower Λ S₂).obj K₂).obj L₂.obj) =
    tensorμ _ _ _ _ ≫
      ((Functor.LaxMonoidal.μ (P Λ.X G.t₁.hom.left) _ _ ≫
          (P Λ.X G.t₁.hom.left).map (factorEvaluation Λ S₁ K₁ L₁)) ⊗ₘ
        (Functor.LaxMonoidal.μ (P Λ.X G.t₂.hom.left) _ _ ≫
          (P Λ.X G.t₂.hom.left).map (factorEvaluation Λ S₂ K₂ L₂))) := by
  let := DerivedCategory.braidedCategory'
    (Mod (Sheaf (ProEt.topology G.T.obj.left) Ab.{u + 1})
      (condensedRingObj Λ.X G.T.obj.left))
  change MonoidalClosed.uncurry
    ((_ ⊗ₘ _) ≫ MonoidalClosed.externalIhomMap
      (P Λ.X G.t₁.hom.left) (P Λ.X G.t₂.hom.left) _ _ _ _) = _
  rw [uncurry_external_after]
  simp only [homMap, MonoidalClosed.uncurry_curry, factorEvaluation]
  rfl

namespace NaturalityProof

variable {C : Type*} [Category C] [MonoidalCategory C] [MonoidalClosed C]
  {D : Type*} [Category D] [MonoidalCategory D] [MonoidalClosed D]

private def evaluation (K Q : C) : K ⊗ ((ihom K).obj (𝟙_ C) ⊗ Q) ⟶ Q :=
  (α_ _ _ _).inv ≫ ((ihom.ev K).app (𝟙_ C) ▷ Q) ≫ (λ_ Q).hom

private theorem evaluation_natural {K K' Q Q' : C} (a : K' ⟶ K) (b : Q ⟶ Q') :
    (K' ◁ ((MonoidalClosed.pre a).app (𝟙_ C) ⊗ₘ b)) ≫ evaluation K' Q' =
      (a ▷ ((ihom K).obj (𝟙_ C) ⊗ Q)) ≫ evaluation K Q ≫ b := by
  simp only [evaluation, MonoidalCategory.tensorHom_def, whiskerLeft_comp, Category.assoc]
  rw [associator_inv_naturality_right_assoc,
    associator_inv_naturality_middle_assoc, whisker_exchange_assoc,
    ← comp_whiskerRight_assoc, MonoidalClosed.id_tensor_pre_app_comp_ev,
    comp_whiskerRight_assoc]
  simp only [Functor.id_obj, leftUnitor_naturality]
  rw [← associator_inv_naturality_left_assoc]

private def comparison (F : C ⥤ D) (P : D ⥤ C) (R : C ⥤ D) (adj : P ⊣ R)
    (pf : ∀ (K : C) (L : D), F.obj K ⊗ L ⟶ F.obj (K ⊗ P.obj L))
    (K Q : C) {L : D} (c : F.obj Q ⟶ L) :
    R.obj ((ihom K).obj (𝟙_ C) ⊗ Q) ⟶ (ihom (F.obj K)).obj L :=
  MonoidalClosed.curry (pf K _ ≫
    F.map ((K ◁ adj.counit.app _) ≫ evaluation K Q) ≫ c)

private theorem comparison_natural
    (F : C ⥤ D) (P : D ⥤ C) (R : C ⥤ D) (adj : P ⊣ R)
    (pf : ∀ (K : C) (L : D), F.obj K ⊗ L ⟶ F.obj (K ⊗ P.obj L))
    (hpfL : ∀ {K K' : C} (a : K' ⟶ K) (L : D),
      F.map a ▷ L ≫ pf K L = pf K' L ≫ F.map (a ▷ P.obj L))
    (hpfR : ∀ (K : C) {L L' : D} (b : L ⟶ L'),
      F.obj K ◁ b ≫ pf K L' = pf K L ≫ F.map (K ◁ P.map b))
    {K K' Q Q' : C} {L L' : D} (a : K' ⟶ K) (q : Q ⟶ Q') (b : L ⟶ L')
    (c : F.obj Q ⟶ L) (c' : F.obj Q' ⟶ L') (hc : F.map q ≫ c' = c ≫ b) :
    R.map ((MonoidalClosed.pre a).app (𝟙_ C) ⊗ₘ q) ≫
        comparison F P R adj pf K' Q' c' =
      comparison F P R adj pf K Q c ≫ (MonoidalClosed.pre (F.map a)).app L ≫
        (ihom (F.obj K')).map b := by
  apply MonoidalClosed.uncurry_injective
  rw [← Category.assoc, MonoidalClosed.uncurry_natural_right,
    MonoidalClosed.uncurry_pre_app, MonoidalClosed.uncurry_natural_left]
  simp only [comparison, MonoidalClosed.uncurry_curry, Category.assoc]
  let T := (ihom K).obj (𝟙_ C) ⊗ Q
  let T' := (ihom K').obj (𝟙_ C) ⊗ Q'
  let t : T ⟶ T' := (MonoidalClosed.pre a).app (𝟙_ C) ⊗ₘ q
  change (F.obj K' ◁ R.map t) ≫ pf K' (R.obj T') ≫
      F.map ((K' ◁ adj.counit.app T') ≫ evaluation K' Q') ≫ c' =
    F.map a ▷ R.obj T ≫ pf K (R.obj T) ≫
      F.map ((K ◁ adj.counit.app T) ≫ evaluation K Q) ≫ c ≫ b
  rw [reassoc_of% (hpfR K' (R.map t)), ← F.map_comp_assoc]
  have ht : (K' ◁ P.map (R.map t)) ≫ (K' ◁ adj.counit.app T') ≫
      evaluation K' Q' =
    (a ▷ P.obj (R.obj T)) ≫ (K ◁ adj.counit.app T) ≫ evaluation K Q ≫ q := by
    rw [← whiskerLeft_comp_assoc]
    have hn : P.map (R.map t) ≫ adj.counit.app T' = adj.counit.app T ≫ t := by
      simpa only [Functor.comp_map, Functor.id_map] using adj.counit.naturality t
    rw [hn]
    rw [whiskerLeft_comp_assoc]
    rw [evaluation_natural a q]
    simpa only [Functor.comp_obj, Functor.id_obj, Category.assoc] using
      congrArg (fun z ↦ z ≫ evaluation K Q ≫ q) (whisker_exchange a (adj.counit.app T))
  rw [ht, F.map_comp, F.map_comp, F.map_comp]
  simp only [Category.assoc]
  rw [hc]
  simp only [← Category.assoc, F.map_comp]
  rw [← hpfL]

end NaturalityProof

/-- The canonical generator map is natural contravariantly in the generator and
covariantly in the target. Source: final naturality sentence of the generator
calculation (blueprint: lem-sf-kv-generator-evaluation).

Proof: expand homMap and uncurry. Naturality of projection moves the support-image
map to its input; naturality of the ordinary counit moves the direct-image map to
its input; naturality of coefficient evaluation and of the exceptional counit gives
the displayed equality. Injectivity of the tensor--Hom adjunction finishes. -/
theorem homMap_naturality {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    (S : SixOperationsLocalizingAdjunction Λ.X c)
    (K K' : ConstantModelConstructibleFiniteTor Λ.X X)
    (L L' : ConstantModelConstructibleFiniteTor Λ.X Y) (a : K' ⟶ K) (b : L ⟶ L') :
    (R Λ.X f).map
        (((MonoidalClosed.pre a.hom).app (𝟙_ _)) ⊗ₘ
          ((exceptional Λ S).map b).hom) ≫ homMap Λ S K' L' =
      homMap Λ S K L ≫
        (MonoidalClosed.pre ((lower Λ S).map a).hom).app L.obj ≫
        (ihom ((lower Λ S).obj K').obj).map b.hom := by
  have hpL : ∀ {B B' : D Λ.X X} (a : B' ⟶ B) (N : D Λ.X Y),
      (F Λ.X c).map a ▷ N ≫ pf Λ.X c B N =
        pf Λ.X c B' N ≫ (F Λ.X c).map (a ▷ (P Λ.X f).obj N) := by
    intro B B' a N
    simpa only [pf] using
      exceptionalProjectionMorphismOfCompactification_natural_left Λ.X c a N
  have hpR : ∀ (B : D Λ.X X) {N N' : D Λ.X Y} (b : N ⟶ N'),
      (F Λ.X c).obj B ◁ b ≫ pf Λ.X c B N' =
        pf Λ.X c B N ≫ (F Λ.X c).map (B ◁ (P Λ.X f).map b) := by
    intro B N N' b
    simpa only [pf] using
      exceptionalProjectionMorphismOfCompactification_natural_right Λ.X c B b
  have hc := congrArg (fun z ↦ z.hom) ((adjunction Λ S).counit.naturality b)
  change (F Λ.X c).map ((exceptional Λ S).map b).hom ≫
      ((adjunction Λ S).counit.app L').hom =
    ((adjunction Λ S).counit.app L).hom ≫ b.hom at hc
  exact NaturalityProof.comparison_natural (F Λ.X c) (P Λ.X f) (R Λ.X f)
    (derivedUpperStarLowerStarAdjunction Λ.X f) (pf Λ.X c) hpL hpR
    a.hom ((exceptional Λ S).map b).hom b.hom
    ((adjunction Λ S).counit.app L).hom ((adjunction Λ S).counit.app L').hom hc

end AlgebraicGeometry.ProEtale.CondensedRing.KVGenerator
