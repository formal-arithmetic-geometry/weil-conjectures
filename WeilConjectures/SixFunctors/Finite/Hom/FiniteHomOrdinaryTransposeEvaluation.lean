/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.EtaleFiniteCoefficientHomArrow
public import WeilConjectures.AlgebraicGeometry.CoefficientPairingChange.InternalAdjunctionPairingChange
import WeilConjectures.SixFunctors.Finite.Hom.FiniteHomClosedNormalization
import WeilConjectures.SixFunctors.Finite.Hom.FiniteHomNativeEvaluation
import WeilConjectures.SixFunctors.Finite.Hom.FiniteHomScalarTensorNormalization

/-! # Evaluation characterization of the ordinary finite Hom transpose
Source: blueprint thm-coef-finite-hom, evaluation paragraph
(blueprint: lem-coef-finite-hom-ordinary-transpose-evaluation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u a b c d
open CategoryTheory AlgebraicGeometry CategoryTheory.MonoidalCategory Opposite
namespace WeilConjectures

attribute [local irreducible] HasDerivedCategory.standard

-- Retain named tensor fields instead of expanding the derived bifunctor.
set_option allowUnsafeReducibility true in
attribute [local irreducible] DerivedMonoidal.tensorObjAux
  DerivedMonoidal.whiskerLeftAux DerivedMonoidal.whiskerRightAux

-- Use the coefficient and sheaf braidings fixed in the ordinary derived tensor.
attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000]
  GrothendieckTopology.braidedCategory_sheaf_of_essentiallySmall

-- Match the native instance arguments already fixed inside derivedTensor and derivedHom.

attribute [local implicit_reducible] CategoryTheory.uniformProd
  Etale.sheafMonoidalCategory Etale.sheafBraidedCategory Etale.sheafMonoidalClosed
  ModuleCat.MonoidalCategory.symmetricCategory SymmetricCategory.ofFaithful

attribute [local implicit_reducible]
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory

attribute [local implicit_reducible]
  DerivedCategory.monoidalClosed_of_hasFunctorialFlatResolution

-- Keep the faithful-transfer construction atomic after exposing the symmetric parent.
attribute [local irreducible] ModuleCat.MonoidalCategory.instBraidedCategory

attribute [local irreducible] DerivedCategory.monoidalClosed

set_option maxHeartbeats 1600000 in
-- Transport compares the full derived-instance arguments.
end WeilConjectures

namespace WeilConjectures

private theorem tensor_uncurry {C : Type a} [Category.{b} C] [MonoidalCategory C] :
    tensor C = Functor.uncurry.obj (curriedTensor C) := by
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro P Q f
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id, tensor_map,
    Functor.uncurry_obj_map, curriedTensor_map_app, curriedTensor_obj_map] using
      (MonoidalCategory.tensorHom_def f.1 f.2)

private theorem inverseApp_heq {J : Type a} [Category.{b} J]
    {C : Type c} [Category.{d} C] {F G F' G' : J ⥤ C}
    (hF : F = F') (hG : G = G') (α : F ≅ G) (β : F' ≅ G')
    (h : HEq α β) (x : J) : HEq (α.inv.app x) (β.inv.app x) := by
  cases hF
  cases hG
  cases h
  rfl

private theorem evaluationTransport
    {C : Type a} [Category.{b} C] {D : Type c} [Category.{d} D]
    {H : Cᵒᵖ × C ⥤ C} {H' : Dᵒᵖ × D ⥤ D}
    (CA CA' : CoefficientClosedStructure H) (CB CB' : CoefficientClosedStructure H')
    (F : C ⥤ D) (K M : C)
    (v : F.obj (H.obj (op K, M)) ⟶ H'.obj (op (F.obj K), F.obj M))
    (μ : CA.tensor ⋙ F ≅ F.prod F ⋙ CB.tensor)
    (e : CB'.tensor.obj (F.obj (H.obj (op K, M)), F.obj K) ⟶
      F.obj (CA'.tensor.obj (H.obj (op K, M), K)))
    (hCA : CA = CA') (hCB : CB = CB')
    (hμ : HEq (μ.inv.app (H.obj (op K, M), K)) e)
    (he : CB'.tensor.map (Prod.mkHom v (𝟙 (F.obj K))) ≫
      CB'.evaluation (F.obj K) (F.obj M) = e ≫ F.map (CA'.evaluation K M)) :
    CB.tensor.map (Prod.mkHom v (𝟙 (F.obj K))) ≫ CB.evaluation (F.obj K) (F.obj M) =
      μ.inv.app (H.obj (op K, M), K) ≫ F.map (CA.evaluation K M) := by
  cases hCA
  cases hCB
  rw [eq_of_heq hμ]
  exact he

private theorem quotientEvaluation {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (X : Scheme.{u}) (K M : Etale.DerivedCategoryModule A X)
    (CA : CoefficientClosedStructure (finiteHomEtaleInternalHomGeneral (ModuleCat A) X))
    (CB : CoefficientClosedStructure (finiteHomEtaleInternalHomGeneral (ModuleCat B) X))
    (μ : CA.tensor ⋙ Etale.scalarExtension φ X ≅
      (Etale.scalarExtension φ X).prod (Etale.scalarExtension φ X) ⋙ CB.tensor)
    (hCA : CA = finiteHomEtaleClosedGeneral (ModuleCat A) X)
    (hCB : CB = finiteHomEtaleClosedGeneral (ModuleCat B) X)
    (hμ : HEq μ (Etale.ExceptionalCoefficients.tensorIso φ X)) :
    CB.tensor.map
        (Prod.mkHom (Etale.CoefficientPairingChange.evaluationComparison φ X K M)
          (𝟙 ((Etale.scalarExtension φ X).obj K))) ≫
      CB.evaluation ((Etale.scalarExtension φ X).obj K)
        ((Etale.scalarExtension φ X).obj M) =
      μ.inv.app ((finiteHomEtaleInternalHomGeneral (ModuleCat A) X).obj (op K, M), K) ≫
        (Etale.scalarExtension φ X).map (CA.evaluation K M) := by
  let SA := finiteHomNativeDerivedClosed (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
  let SB := finiteHomNativeDerivedClosed (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))
  have hA : CA = SA := hCA.trans (finiteHom_etale_closed_normalization (ModuleCat A) X)
  have hB : CB = SB := hCB.trans (finiteHom_etale_closed_normalization (ModuleCat B) X)
  have hsrc : CA.tensor = Functor.uncurry.obj (Etale.derivedTensor (ModuleCat A) X) :=
    (congrArg CoefficientClosedStructure.tensor hA).trans tensor_uncurry
  have htgt : CB.tensor = Functor.uncurry.obj (Etale.derivedTensor (ModuleCat B) X) :=
    (congrArg CoefficientClosedStructure.tensor hB).trans tensor_uncurry
  have happ := inverseApp_heq
    (congrArg (fun T ↦ T ⋙ Etale.scalarExtension φ X) hsrc)
    (congrArg (fun T ↦ (Etale.scalarExtension φ X).prod
      (Etale.scalarExtension φ X) ⋙ T) htgt)
    μ (Etale.ExceptionalCoefficients.tensorIso φ X) hμ
    ((finiteHomEtaleInternalHomGeneral (ModuleCat A) X).obj (op K, M), K)
  exact evaluationTransport CA SA CB SB (Etale.scalarExtension φ X) K M
    (Etale.CoefficientPairingChange.evaluationComparison φ X K M) μ
    (Etale.etaleHomTensorComparison X φ
      (((Etale.derivedHom (ModuleCat A) X).obj (op K)).obj M) K).hom hA hB
    (happ.trans (heq_of_eq (finiteHom_scalar_tensor_normalization φ X _ K)))
    (finiteHom_native_evaluation φ X K M)

/-- The ordinary evaluation comparison satisfies the reduced evaluation equation.
Source: blueprint thm-coef-finite-hom, proof paragraphs 1--2
(blueprint: lem-coef-finite-hom-ordinary-transpose-evaluation).

Proof: identify the normalized closed tensor and evaluation with the published
ordinary derived tensor and counit. Expand `evaluationComparison` as the
ordinary left-tensor adjunct of the tensor comparison followed by scalar
extension of the counit. Naturality of the braiding transports this left
adjunct to the right-tensor closed record used by `finiteHomEtaleClosed`; the
inverse tensor comparison then cancels the displayed tensorator. The resulting
composite is exactly the reduced evaluation map. This argument is valid for
arbitrary objects and identity quotients; no invertibility of the Hom map is
used. -/
theorem finiteHom_ordinary_transpose_evaluation
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : Scheme.{u}) {n m : ℕ} (h : m ≤ n)
    (K M : finiteHomEtale l E X n) :
    (finiteHomEtaleClosed l E X m).tensor.map
          (Prod.mkHom (Etale.CoefficientPairingChange.evaluationComparison
            (finiteHomQuotient l E h) X K M)
            (𝟙 ((finiteHomEtaleReduction l E X h).obj K))) ≫
        (finiteHomEtaleClosed l E X m).evaluation ((finiteHomEtaleReduction l E X h).obj K)
          ((finiteHomEtaleReduction l E X h).obj M) =
      (finiteHomEtaleTensor l E X h).inv.app
          ((finiteHomEtaleInternalHom l E X n).obj (Opposite.op K, M), K) ≫
        (finiteHomEtaleReduction l E X h).map ((finiteHomEtaleClosed l E X n).evaluation K M) := by
  exact quotientEvaluation (finiteHomQuotient l E h) X K M
    (finiteHomEtaleClosed l E X n) (finiteHomEtaleClosed l E X m)
    (finiteHomEtaleTensor l E X h)
    (eq_of_heq ((finiteHomEtaleData_existsUnique l E X).choose_spec.1.closed n))
    (eq_of_heq ((finiteHomEtaleData_existsUnique l E X).choose_spec.1.closed m))
    ((finiteHomEtaleData_existsUnique l E X).choose_spec.1.tensor n m h)

end WeilConjectures
