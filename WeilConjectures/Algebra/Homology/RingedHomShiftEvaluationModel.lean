/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.RingedHomShiftRepresentatives
import all WeilConjectures.Algebra.Homology.RingedDerivedTensorHomAdjunction
import all WeilConjectures.Algebra.Homology.RingedDerivedTensorNativeSupplement
import all WeilConjectures.Algebra.Homology.KInjectiveHomComplexOfUniverses
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all WeilConjectures.Algebra.Homology.HomComplex
import all Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all WeilConjectures.Algebra.Homology.HomTensorDegreewiseIso
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.RingTheory.Flat.CategoryTheory
import all WeilConjectures.SecSmoothPurity.CochainTensoratorExistence
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
import all WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.AdjunctionRingOperations
import all Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import all Mathlib.CategoryTheory.Adjunction.Basic
import all WeilConjectures.CategoryTheory.GeometricModuleConstruction
import all WeilConjectures.CategoryTheory.RingedToposRingData
import all WeilConjectures.CategoryTheory.RingedToposMorphismSupplement
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.CategoryTheory.GeometricModuleTransport
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all WeilConjectures.Algebra.Homology.InternalHom
import all WeilConjectures.Algebra.Homology.HomComplexComponents
import all WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
import all WeilConjectures.Algebra.Homology.HomotopyCategory.InternalHom
import all WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
import all WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement

/-! # Evaluation on ordinary Hom representatives

Source: Stacks 08J9 and 0A95. This is independent of shifts.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe c v u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite WeilConjectures
open scoped TensorProduct
attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
namespace CategoryTheory.RingedHomShift

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
  (R : Sheaf J CommRingCat.{max c v u})

/-- A chain map is ordinary uncurrying exactly when it evaluates on each tensor generator.
Source: Stacks 0A8X, 08J9
(blueprint: lem-sf-ringed-hom-shift-evaluation-model). -/
def Uncurries (A P I : RingedHomUniverses.Complex.{c, v, u} J R)
    (a : A ⟶ RingedHomUniverses.complexHom.{c, v, u} J R P I)
    (ψ : (coefficientTotalTensor.{u, c, v} J R).obj (A, P) ⟶ I) : Prop :=
  ∀ (p q k : ℤ) (h : p + q = k) (h' : q + p = k) (U : Cᵒᵖ)
    (x : (A.X p).val.obj U) (y : (P.X q).val.obj U),
    (ψ.f k).val.app U (coefficientTensorGenerator.{u, c, v} J R A P p q k h U x y) =
      ((((coefficientHomComponent.{u, c, v} J R P I p q k h').val.app U)
        ((a.f p).val.app U x)).app (op (Over.mk (𝟙 U.unop)))).hom y

private theorem map_pair_comp
    {D₁ D₂ E : Type*} [Category D₁] [Category D₂] [Category E]
    (F : D₁ × D₂ ⥤ E) {X Y Z : D₁} {X' Y' Z' : D₂}
    (f : X ⟶ Y) (g : Y ⟶ Z) (f' : X' ⟶ Y') (g' : Y' ⟶ Z') :
    F.map (Prod.mkHom f f') ≫ F.map (Prod.mkHom g g') =
      F.map (Prod.mkHom (f ≫ g) (f' ≫ g')) :=
  (F.map_comp (Prod.mkHom f f') (Prod.mkHom g g')).symm

private def pure (X Y : RingedHomUniverses.Modules.{c, v, u} J R) (U : Cᵒᵖ)
    (x : X.val.obj U) (y : Y.val.obj U) :
    ((SheafOfModules.monoidalCategory R).tensorObj X Y).val.obj U :=
  (SheafOfModules.tensorObjIsoSheafification (R := R) X Y).inv.val.app U
    (((PresheafOfModules.sheafificationAdjunction
      (𝟙 ((sheafCompose J
        (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj R).obj)).unit.app
        (X.val ⊗ Y.val)).app U (x ⊗ₜ[R.obj.obj U] y))

private theorem pure_hom_ext (X Y Z : RingedHomUniverses.Modules.{c, v, u} J R)
    {f g : (SheafOfModules.monoidalCategory R).tensorObj X Y ⟶ Z}
    (h : ∀ U x y, f.val.app U (pure.{c, v, u} J R X Y U x y) =
      g.val.app U (pure.{c, v, u} J R X Y U x y)) : f = g := by
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj R).obj)
  apply (cancel_epi (SheafOfModules.tensorObjIsoSheafification (R := R) X Y).inv).mp
  apply (adj.homEquiv (X.val ⊗ Y.val) Z).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro x y
  exact h U x y

private theorem total_hom_ext (A P I : RingedHomUniverses.Complex.{c, v, u} J R)
    {f g : (coefficientTotalTensor.{u, c, v} J R).obj (A, P) ⟶ I}
    (h : ∀ (p q k : ℤ) (hpq : p + q = k) (U : Cᵒᵖ)
      (x : (A.X p).val.obj U) (y : (P.X q).val.obj U),
      (f.f k).val.app U (coefficientTensorGenerator.{u, c, v} J R A P p q k hpq U x y) =
        (g.f k).val.app U
          (coefficientTensorGenerator.{u, c, v} J R A P p q k hpq U x y)) : f = g := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  apply HomologicalComplex.hom_ext
  intro k
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  apply pure_hom_ext.{c, v, u} J R (A.X p) (P.X q) (I.X k)
  intro U x y
  exact h p q k hpq U x y

private theorem uncurries_unique (A P I : RingedHomUniverses.Complex.{c, v, u} J R)
    (a : A ⟶ RingedHomUniverses.complexHom.{c, v, u} J R P I)
    {f g : (coefficientTotalTensor.{u, c, v} J R).obj (A, P) ⟶ I}
    (hf : Uncurries.{c, v, u} J R A P I a f)
    (hg : Uncurries.{c, v, u} J R A P I a g) : f = g := by
  apply total_hom_ext.{c, v, u} J R A P I
  intro p q k hpq U x y
  exact (hf p q k hpq (by omega) U x y).trans
    (hg p q k hpq (by omega) U x y).symm

variable [HasDerivedCategory.{w} (RingedTensorModules.{c, v, u} J R)]
  (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, u, w} J R))
  (T : CoefficientTensorModels.{u, c, v, w} J R S)
  (β : @SymmetricCategory (DerivedCategory (RingedTensorModules.{c, v, u} J R))
    _ S.monoidal)
  (hc : RingedDerivedTensorCoherence.{c, v, u, w} J R S T β)

/-- Step 4: evaluation is ordinary uncurrying on K-flat sources and any target complex.
Source: Stacks 08J9, 0A95
(blueprint: lem-sf-ringed-hom-shift-evaluation-model).

Proof: ordinary sheaf tensor-Hom uncurrying defines ψ by the displayed generator formula;
the Hom differential makes it a chain map. Apply T.uncurry_model to a followed by
Hom(P,η_I). Uniqueness on the sheafified pure-tensor generators and naturality of chain
uncurrying identify its uncurry with ψ followed by η_I. The localization inverts η_I,
so the inverse augmentation in the model cancels it. hc.tensorIso_both identifies the
tensor comparison with T.iso. Evaluation naturality in both K and M transports the
square along eK and eM. Neither shifts nor shift compatibility enter this argument. -/
theorem exists_evaluation_model
    {K M : RingedHomUniverses.D.{c, v, u, w} J R}
    (A P I : RingedHomUniverses.Complex.{c, v, u} J R)
    (hA : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) A)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P)
    (eK : DerivedCategory.Q.obj P ≅ K)
    (eM : DerivedCategory.Q.obj I ≅ M)
    (a : A ⟶ RingedHomUniverses.complexHom.{c, v, u} J R P I) :
    ∃ ψ : (coefficientTotalTensor.{u, c, v} J R).obj (A, P) ⟶ I,
      Uncurries.{c, v, u} J R A P I a ψ ∧
      (hc.tensorIso A P (Or.inl hA)).hom ≫
          S.tensor.map (Prod.mkHom
            (DerivedCategory.Q.map a ≫ comparison.{c, v, u, w} J R P I eK eM) eK.hom) ≫
          S.evaluation K M = DerivedCategory.Q.map ψ ≫ eM.hom := by
  classical
  let Q : RingedHomUniverses.Complex.{c, v, u} J R ⥤
      RingedHomUniverses.D.{c, v, u, w} J R := DerivedCategory.Q
  let H := derivedInternalHomOfUniverses.{c, v, u, w} J R
  let : MonoidalCategory (RingedHomUniverses.D.{c, v, u, w} J R) := S.monoidal
  let : IsGrothendieckAbelian.{max c v u} (RingedHomUniverses.Modules.{c, v, u} J R) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c, v, u}
      J R).1
  let η := (ringedSiteHomAugmentation.{c, v, u} J R).app I
  have : QuasiIso η :=
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{max c v u} _ I).2
  have : IsIso (Q.map η) := by infer_instance
  let aη := a ≫ ringedSiteHomComplexMap.{c, v, u} J R (𝟙 P) η
  let ψ := (RingedDerivedNative.chainEquiv.{c, v, u} J R A P I).symm a
  have hψ : Uncurries.{c, v, u} J R A P I a ψ := by
    intro p q k h h' U x y
    exact RingedDerivedNative.chainEquiv_symm_pure.{c, v, u}
      J R A P I a p q k h h' U x y
  obtain ⟨ψ', hψ', he⟩ := T.uncurry_model ⟨A, hA⟩ ⟨P, hP⟩ I aη
  have hψ'eq : ψ' = ψ ≫ η := by
    have hnat := RingedDerivedNative.chainEquiv_symm_naturality.{c, v, u} J R
      A A P P I ((coefficientHomResolution.{u, c, v} J R).obj I) (𝟙 A) (𝟙 P) η a
    have hnat' :
        (RingedDerivedNative.chainEquiv.{c, v, u} J R A P
          ((coefficientHomResolution.{u, c, v} J R).obj I)).symm aη = ψ ≫ η := by
      have hid : (coefficientTotalTensor.{u, c, v} J R).map (𝟙 A, 𝟙 P) =
          𝟙 ((coefficientTotalTensor.{u, c, v} J R).obj (A, P)) :=
        (coefficientTotalTensor.{u, c, v} J R).map_id (A, P)
      simpa only [Category.id_comp, hid, ψ, aη, ringedSiteHomComplexMap] using hnat
    rw [← hnat']
    apply uncurries_unique.{c, v, u} J R A P _ aη
    · exact hψ'
    · intro p q k h h' U x y
      exact RingedDerivedNative.chainEquiv_symm_pure.{c, v, u}
        J R A P _ aη p q k h h' U x y
  have hbase : (hc.tensorIso A P (Or.inl hA)).hom ≫
      S.tensor.map (Prod.mkHom
        (Q.map a ≫ ringedSiteOrdinaryHomComparison.{c, v, u, w} J R P I)
        (𝟙 (Q.obj P))) ≫ S.evaluation (Q.obj P) (Q.obj I) = Q.map ψ := by
    rw [hc.tensorIso_both A P hA hP]
    change T.comparison.hom.app (⟨A, hA⟩, ⟨P, hP⟩) ≫ _ = _
    have hm : Q.map aη ≫ (coefficientHomResolutionIso.{u, c, v, w} J R P I).inv =
        Q.map a ≫ ringedSiteOrdinaryHomComparison.{c, v, u, w} J R P I := by
      simp only [aη, Q.map_comp, ringedSiteOrdinaryHomComparison, η, Category.assoc]
      rfl
    have htr (ξ : Q.obj A ⟶ H.obj (op (Q.obj P), Q.obj I)) :
        (S.transpose (Q.obj A) (Q.obj P) (Q.obj I)).symm ξ =
          S.tensor.map (Prod.mkHom ξ (𝟙 (Q.obj P))) ≫
            S.evaluation (Q.obj P) (Q.obj I) := by
      simpa only [CoefficientClosedStructure.tensor, tensor, tensorRight, tensorLeft,
        curriedTensor, Functor.flip, Functor.comp_obj, Functor.comp_map, Functor.id_obj,
        Functor.id_map, Prod.sectR, tensorHom_id,
        CoefficientClosedStructure.evaluation, CoefficientClosedStructure.transpose]
        using (S.adjunction (Q.obj P)).homEquiv_counit (g := ξ)
    rw [hm, htr] at he
    change T.comparison.hom.app (⟨A, hA⟩, ⟨P, hP⟩) ≫
      S.tensor.map (Prod.mkHom _ (𝟙 (Q.obj P))) ≫ S.evaluation _ _ = _ at he
    rw [he, hψ'eq, Q.map_comp]
    change (Q.map ψ ≫ Q.map η) ≫ inv (Q.map η) = Q.map ψ
    simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have hk₀ := S.evaluation_naturality K (Q.obj P) M eK.hom
  have hk : S.tensor.map (Prod.mkHom (H.map (Prod.mkHom eK.hom.op (𝟙 M)))
      (𝟙 (Q.obj P))) ≫ S.evaluation (Q.obj P) M =
    S.tensor.map (Prod.mkHom (𝟙 (H.obj (op K, M))) eK.hom) ≫ S.evaluation K M := by
    simpa only [CoefficientClosedStructure.tensor, tensor, tensorRight, tensorLeft,
        curriedTensor, Functor.flip, Functor.comp_obj, Functor.comp_map, Functor.id_obj,
        Functor.id_map, Prod.sectR, tensorHom_id, id_tensorHom,
      CoefficientClosedStructure.evaluation] using hk₀
  have hM₀ := (S.adjunction (Q.obj P)).counit.naturality eM.hom
  have hM : S.tensor.map (Prod.mkHom (H.map (Prod.mkHom (𝟙 (op (Q.obj P))) eM.hom))
      (𝟙 (Q.obj P))) ≫ S.evaluation (Q.obj P) M =
    S.evaluation (Q.obj P) (Q.obj I) ≫ eM.hom := by
    simpa only [CoefficientClosedStructure.tensor, tensor, tensorRight, tensorLeft,
        curriedTensor, Functor.flip, Functor.comp_obj, Functor.comp_map, Functor.id_obj,
        Functor.id_map, Prod.sectR, tensorHom_id,
      CoefficientClosedStructure.evaluation] using hM₀
  have hH : H.map (Prod.mkHom eK.inv.op eM.hom) ≫
      H.map (Prod.mkHom eK.hom.op (𝟙 M)) =
      H.map (Prod.mkHom (𝟙 (op (Q.obj P))) eM.hom) := by
    rw [map_pair_comp]
    simp only [← op_comp, Iso.hom_inv_id, op_id, Category.comp_id]
    rfl
  have ht : S.tensor.map (Prod.mkHom (H.map (Prod.mkHom eK.inv.op eM.hom)) eK.hom) ≫
      S.evaluation K M = S.evaluation (Q.obj P) (Q.obj I) ≫ eM.hom := by
    calc
      _ = S.tensor.map (Prod.mkHom (H.map (Prod.mkHom eK.inv.op eM.hom))
            (𝟙 (Q.obj P))) ≫
          S.tensor.map (Prod.mkHom (𝟙 (H.obj (op K, M))) eK.hom) ≫
            S.evaluation K M := by
        rw [← Category.assoc, map_pair_comp]
        simp only [Category.comp_id, Category.id_comp]
      _ = S.tensor.map (Prod.mkHom (H.map (Prod.mkHom eK.inv.op eM.hom))
            (𝟙 (Q.obj P))) ≫
          S.tensor.map (Prod.mkHom (H.map (Prod.mkHom eK.hom.op (𝟙 M)))
            (𝟙 (Q.obj P))) ≫ S.evaluation (Q.obj P) M := by rw [hk]
      _ = _ := by
        rw [← Category.assoc, map_pair_comp]
        simpa only [Category.id_comp, hH] using hM
  refine ⟨ψ, hψ, ?_⟩
  change (hc.tensorIso A P (Or.inl hA)).hom ≫
    S.tensor.map (Prod.mkHom
      (Q.map a ≫ ringedSiteOrdinaryHomComparison.{c, v, u, w} J R P I ≫
        H.map (Prod.mkHom eK.inv.op eM.hom)) eK.hom) ≫ S.evaluation K M = _
  calc
    _ = (hc.tensorIso A P (Or.inl hA)).hom ≫
        S.tensor.map (Prod.mkHom
          (Q.map a ≫ ringedSiteOrdinaryHomComparison.{c, v, u, w} J R P I)
          (𝟙 (Q.obj P))) ≫
        S.tensor.map (Prod.mkHom (H.map (Prod.mkHom eK.inv.op eM.hom)) eK.hom) ≫
          S.evaluation K M := by
      rw [← Category.assoc (S.tensor.map _), map_pair_comp]
      simp only [Category.assoc]
      rw [Category.id_comp]
    _ = _ := by
      rw [ht]
      simpa only [Category.assoc] using congrArg (fun z ↦ z ≫ eM.hom) hbase

end CategoryTheory.RingedHomShift
