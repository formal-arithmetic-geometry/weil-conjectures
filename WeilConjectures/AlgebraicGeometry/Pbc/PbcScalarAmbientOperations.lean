/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarStages
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarTensor
import WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarCompletedObjectComplete
import WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarCoefficientFiniteFree
import WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarRestrictionComplete
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
import WeilConjectures.AlgebraicGeometry.FiniteFreeDirectImage.FiniteFreeDirectImageCoherence
import Mathlib.CategoryTheory.Preadditive.Biproducts
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsComapBiproduct

/-! # Ambient operation comparisons for finite scalar extension

Source: blueprint proper base change, order 1307; Milne, Section 19.
Existing declarations extracted from `PbcScalarExtension` to bound compilation cost.
(blueprint: lem-pbc-scalar-ambient-operation-comparisons)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open scoped TensorProduct
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [local irreducible] AlgebraicGeometry.Scheme.pbcRationalCoefficientEquiv
namespace AlgebraicGeometry.Scheme
section AmbientOperations

variable (l : ℕ) [Fact l.Prime]
    (E F : Type u) [Field E] [Field F] [Algebra ℚ_[l] E] [Algebra ℚ_[l] F]
    [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] F] (i : E →ₐ[ℚ_[l]] F)
variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The ambient ordinary-pullback comparison is the normalized derived tensor comparison.
Source: blueprint order 1307 (blueprint: lem-pbc-scalar-ambient-operation-comparisons). -/
@[irreducible] def pbcScalarOrdinaryPullIso :
    pbcEmbeddingAmbientTensor l E F i Y ⋙
        pbcActualDerivedPull g (pbcIntegralDatum l F) ≅
      pbcActualDerivedPull g (pbcIntegralDatum l E) ⋙
        pbcEmbeddingAmbientTensor l E F i X :=
  pbcActualScalarDerivedPullIso g (pbcIntegralDatum l E) (pbcIntegralDatum l F)
    (pbcScalarCoefficientMap l E F i Y) (pbcScalarCoefficientMap l E F i X)
    (pbcScalarCoefficientStructureSquare l E F i g)

/-- The direct-image comparison is the actual mate, rather than a selected isomorphism.
Source: blueprint order 1307 (blueprint: lem-pbc-scalar-ambient-operation-comparisons). -/
@[irreducible] def pbcScalarDirectImageMap :
    pbcActualDerivedPush g (pbcIntegralDatum l E) ⋙
        pbcEmbeddingAmbientTensor l E F i Y ⟶
      pbcEmbeddingAmbientTensor l E F i X ⋙
        pbcActualDerivedPush g (pbcIntegralDatum l F) :=
  pbcActualScalarDirectImageMap g (pbcIntegralDatum l E) (pbcIntegralDatum l F)
    (pbcScalarCoefficientMap l E F i Y) (pbcScalarCoefficientMap l E F i X)
    (pbcScalarCoefficientStructureSquare l E F i g)

-- Counit of a derived adjunction from its unit normalization on a representative.

-- The diagram chase computing a mate from normalized units, counits and comparisons.

-- Naturality of a universal derived counit written on cochain representatives.

-- Two naturality squares of the derived-functor factorization.

-- The factorization chase for the termwise restriction/pullback comparison.

-- The final diagram chase, over an abstract category.

-- Natural transformations out of a derived category agree once they agree on a
-- resolving class of complexes.

-- Mates are unchanged when the left adjoints are replaced through conjugates of identities.

/-- The canonical scalar/direct-image mate is invertible for finite coefficient extensions.
Source: blueprint order 1307 (blueprint: lem-pbc-scalar-ambient-operation-comparisons).
Proof: the target valuation ring is finite free over the source. Locally choose a
finite free basis. Scalar extension is then a finite sum, and derived direct image
commutes with finite sums. The resulting identification has the same ordinary
tensor formula as the mate, so descends independently of that basis. Equivalently
use the finite perfect projection formula and the tensor-unit normalization. -/
@[instance] theorem pbcScalarDirectImageMap_isIso :
    IsIso (pbcScalarDirectImageMap l E F i g) := by
  classical
  obtain ⟨d, ⟨b⟩⟩ := pbcScalarCoefficient_finiteFree l E F i Y
  let RE := (adicLisseForget Y).obj (pbcAdicCompletion Y (pbcIntegralDatum l E))
  let N := SheafOfModules.unit RE
  let : HasBiproduct (fun _ : Fin d ↦ N) := HasBiproduct.of_hasProduct _
  let e : (∏ᶜ fun _ : Fin d ↦ N) ≅
      SheafOfModules.free (R := RE) (ULift.{u + 1} (Fin d)) :=
    (biproduct.isoProduct (fun _ : Fin d ↦ N)).symm ≪≫
      biproduct.isoCoproduct (fun _ : Fin d ↦ N) ≪≫
        Sigma.whiskerEquiv (Equiv.ulift.{u + 1, 0}).symm (fun _ ↦ Iso.refl N)
  let R' : FiniteFreeDirectImage.Coefficients g :=
    ⟨pbcAdicCompletion Y (pbcIntegralDatum l E), pbcAdicCompletion X (pbcIntegralDatum l E),
      pbcCompletedCoefficientIso g (pbcIntegralDatum l E)⟩
  let S' : FiniteFreeDirectImage.Coefficients g :=
    ⟨pbcAdicCompletion Y (pbcIntegralDatum l F), pbcAdicCompletion X (pbcIntegralDatum l F),
      pbcCompletedCoefficientIso g (pbcIntegralDatum l F)⟩
  let a' : FiniteFreeDirectImage.CoefficientMap R' S' :=
    ⟨pbcScalarCoefficientMap l E F i Y, pbcScalarCoefficientMap l E F i X,
      pbcScalarCoefficientInverseSquare l E F i g⟩
  obtain ⟨sY, sX, _, _, hi, _⟩ := FiniteFreeDirectImage.finiteFreeDirectImageCoherence g
  have : IsIso (FiniteFreeDirectImage.comparison sY sX a') := (hi R' S' a' d ⟨b ≪≫ e⟩).1
  let δ := pbcScalarRestrictionDirectImage l E F i g
  have hm : (mateEquiv (sX.adjunction a'.source) (sY.adjunction a'.target)
      (TwoSquare.mk _ _ _ _ (FiniteFreeDirectImage.comparison sY sX a'))).natTrans =
      δ.inv := by
    rw [FiniteFreeDirectImage.comparison, iterated_mateEquiv_conjugateEquiv]
    exact (conjugateEquiv _ _).apply_symm_apply δ.inv
  have he : ((mateEquiv (sX.adjunction a'.source) (sY.adjunction a'.target)).symm
      (TwoSquare.mk _ _ _ _ δ.inv)).natTrans =
        FiniteFreeDirectImage.comparison sY sX a' := by
    apply congrArg TwoSquare.natTrans
    apply (mateEquiv (sX.adjunction a'.source) (sY.adjunction a'.target)).injective
    rw [Equiv.apply_symm_apply]
    ext K
    exact (NatTrans.congr_app hm K).symm
  have : IsIso (((mateEquiv (sX.adjunction a'.source)
      (sY.adjunction a'.target)).symm (TwoSquare.mk _ _ _ _ δ.inv)).natTrans) := by
    rw [he]
    infer_instance
  have hiso := scalarInverseMate_isIso_of_isIso
    (pbcDerivedScalarAdjunction (pbcScalarCoefficientMap l E F i X))
    (pbcDerivedScalarAdjunction (pbcScalarCoefficientMap l E F i Y))
    (sX.adjunction a'.source) (sY.adjunction a'.target) (TwoSquare.mk _ _ _ _ δ.inv) this
  have hs : mateEquiv (pbcDerivedScalarAdjunction (pbcScalarCoefficientMap l E F i X))
      (pbcDerivedScalarAdjunction (pbcScalarCoefficientMap l E F i Y))
      (TwoSquare.mk _ _ _ _ (pbcScalarDirectImageMap l E F i g)) =
        TwoSquare.mk _ _ _ _ δ.inv := by
    ext K
    exact NatTrans.congr_app (pbcScalarDirectImageMap_scalarMate l E F i g) K
  have hμ := congrArg TwoSquare.natTrans (((mateEquiv
    (pbcDerivedScalarAdjunction (pbcScalarCoefficientMap l E F i X))
    (pbcDerivedScalarAdjunction (pbcScalarCoefficientMap l E F i Y))).eq_symm_apply).2 hs)
  change IsIso (TwoSquare.mk _ _ _ _ (pbcScalarDirectImageMap l E F i g)).natTrans
  rw [hμ]
  exact hiso

/-- The canonical invertible direct-image comparison, with its mate definition retained.
Source: blueprint order 1307 (blueprint: lem-pbc-scalar-ambient-operation-comparisons). -/
@[irreducible] def pbcScalarDirectImageIso :
    pbcActualDerivedPush g (pbcIntegralDatum l E) ⋙
        pbcEmbeddingAmbientTensor l E F i Y ≅
      pbcEmbeddingAmbientTensor l E F i X ⋙
        pbcActualDerivedPush g (pbcIntegralDatum l F) :=
  asIso (pbcScalarDirectImageMap l E F i g)

-- Construct both arrows from the two reflection Hom bijections. Scalar restriction
-- lets the source reflection compute maps into complete target-coefficient objects.

/-- The unique completion comparison preserving the specified quotient unit.
Source: blueprint order 1307 (blueprint: lem-pbc-scalar-ambient-operation-comparisons). -/
@[irreducible] def pbcScalarCompletionIso (W : Scheme.{u}) :
    pbcEmbeddingAmbientTensor l E F i W ⋙
        pbcActualCompletion (pbcIntegralDatum l F) W ≅
      pbcActualCompletion (pbcIntegralDatum l E) W ⋙
        pbcEmbeddingAmbientTensor l E F i W :=
  (pbcScalarCompletionIso_exists l E F i W).exists.choose

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Completed scalar/pullback is the ordinary comparison followed by the canonical
completion comparisons. Source: blueprint order 1307
(blueprint: lem-pbc-scalar-ambient-operation-comparisons). -/
@[irreducible] def pbcScalarCompletedPullIso :
    pbcEmbeddingAmbientTensor l E F i Y ⋙
        pbcActualCompletedPull g (pbcIntegralDatum l F) ≅
      pbcActualCompletedPull g (pbcIntegralDatum l E) ⋙
        pbcEmbeddingAmbientTensor l E F i X :=
  NatIso.ofComponents
    (F := pbcEmbeddingAmbientTensor l E F i Y ⋙
      pbcActualCompletedPull g (pbcIntegralDatum l F))
    (G := pbcActualCompletedPull g (pbcIntegralDatum l E) ⋙
      pbcEmbeddingAmbientTensor l E F i X) (fun K ↦
    (pbcActualCompletion (pbcIntegralDatum l F) X).mapIso
        ((pbcScalarOrdinaryPullIso l E F i g).app K) ≪≫
      (pbcScalarCompletionIso l E F i X).app
        ((pbcActualDerivedPull g (pbcIntegralDatum l E)).obj K)) (fun {K L} f ↦ by
    have he := (pbcScalarOrdinaryPullIso l E F i g).hom.naturality f
    have hc := (pbcScalarCompletionIso l E F i X).hom.naturality
      ((pbcActualDerivedPull g (pbcIntegralDatum l E)).map f)
    dsimp only [CategoryTheory.Functor.comp_map] at he hc
    dsimp only [pbcActualCompletedPull, CategoryTheory.Functor.comp_map, Iso.trans_hom,
      CategoryTheory.Functor.mapIso_hom, Iso.app_hom]
    rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, he,
      CategoryTheory.Functor.map_comp, Category.assoc, hc, Category.assoc])

variable {X' Y' : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {a : Y' ⟶ Y} (sq : ChosenCartesianSquare g' f' f a)

end AmbientOperations
end AlgebraicGeometry.Scheme
