/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Weil.NativeWeilClosedModels
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
public import WeilConjectures.CategoryTheory.RingedForgetTensorTransposition.RingedForgetTensorTranspositionData
import WeilConjectures.CategoryTheory.Native.NativeWeilTensorConstraintLifts

/-! # Monoidal coherence on a represented native tensor

This is the constraint-descent part of the equivariant lift of the native tensor.

## Implementation details

The ringed closed symmetric tensor, transported to native complexes through the Frobenius
action-site presentation, is naturally isomorphic to `T`: for each `K` both tensor functors
are left adjoint to `M.weilHom(K, -)`, and the counit equation `ha` makes the isomorphism
natural in `K`. The monoidal constraints, the coefficient unit and the Koszul symmetry are
transported through this bifunctor isomorphism, taking `T` itself as the tensor functor (on
pairs of arrows and on whiskerings), so that pentagon, triangle, symmetry and hexagon follow
from their ringed counterparts by conjugation. The unit-mate formula `hτ`, `hη` and
uniqueness of adjoints identify the supplied `τ` with the ringed forgetful tensor comparison;
the ringed forgetful tensor coherence is applied on summands and descended along the K-flat
localization. No conservativity argument replaces a constraint equation.

## References

* Stacks 06YS, 0FPT
-/

@[expose] public section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
attribute [local instance] uliftCategory
private theorem assemble_tensor_constraints
    {C D : Type v} [Category.{w} C] [Category.{w} D]
    (F : C ⥤ D) (T : C × C ⥤ C) (U : C) (V : D) (ζ : F.obj U ≅ V)
    (n : MonoidalCategory D) (β : @SymmetricCategory D _ n)
    (τ : T ⋙ F ≅ F.prod F ⋙ @MonoidalCategory.tensor D _ n)
    (L : TensorConstraintLifts F T U V ζ n β τ) :
    ∃ m : MonoidalCategory C, ∃ hT : @MonoidalCategory.tensor C _ m = T,
    ∃ γ : @SymmetricCategory C _ m, ∃ δ : m.tensorUnit ≅ U,
    ∃ ε : n.tensorUnit ≅ V,
    ∃ c : RingedForgetTensorTransposition.TensorCoherence m n γ β F
        (eqToIso (congrArg (fun T' ↦ T' ⋙ F) hT) ≪≫ τ),
      c.unit = F.mapIso δ ≪≫ ζ ≪≫ ε.symm := by
  let : L.model.Faithful := L.faithful
  let : MonoidalCategory (ULift.{0} C) := L.modelMonoidal
  let m : MonoidalCategory C :=
    @Monoidal.induced (ULift.{0} C) _ L.modelMonoidal C _ L.candidate.operations
      L.model L.faithful L.modelData
  let em : @Functor.Monoidal C _ m (ULift.{0} C) _ L.modelMonoidal L.model :=
    @Monoidal.fromInducedMonoidal (ULift.{0} C) _ L.modelMonoidal C _ L.candidate.operations
      L.model L.faithful L.modelData
  let br : @BraidedCategory C _ m :=
    @BraidedCategory.ofFaithful C (ULift.{0} C) _ _ m L.modelMonoidal L.model em L.faithful
      L.modelSymmetry.toBraidedCategory L.candidate.braiding L.model_braiding
  let γ : @SymmetricCategory C _ m :=
    { toBraidedCategory := br
      symmetry := by
        intro A B
        apply L.model.map_injective
        apply (cancel_epi (L.modelData.μIso A B).hom).1
        change (L.modelData.μIso A B).hom ≫
            L.model.map ((L.candidate.braiding A B).hom ≫
              (L.candidate.braiding B A).hom) =
          (L.modelData.μIso A B).hom ≫ L.model.map (𝟙 _)
        rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id,
          ← Category.assoc, L.model_braiding, Category.assoc, L.model_braiding,
          ← Category.assoc, L.modelSymmetry.symmetry, Category.id_comp,
          Category.comp_id] }
  have hT : @MonoidalCategory.tensor C _ m = T := rfl
  have hμ (A B : C) : (L.forgetData.μIso A B).inv = τ.hom.app (A, B) :=
    congrArg Iso.hom (L.forget_tensor A B)
  let := m
  let := n
  let core : F.CoreMonoidal :=
    { εIso := L.forgetData.εIso
      μIso := L.forgetData.μIso
      μIso_hom_natural_left := by intros; simp [L.forgetData.whiskerRight_eq]
      μIso_hom_natural_right := by intros; simp [L.forgetData.whiskerLeft_eq]
      associativity := by intros; simp [L.forgetData.associator_eq]
      left_unitality := by intros; simp [L.forgetData.leftUnitor_eq]
      right_unitality := by intros; simp [L.forgetData.rightUnitor_eq] }
  let c : RingedForgetTensorTransposition.TensorCoherence m n γ β F τ :=
    { unit := L.forgetData.εIso.symm
      associativity := by
        intro A B D
        have h := core.toOplaxMonoidal.oplax_associativity A B D
        simpa only [Functor.CoreMonoidal.toOplaxMonoidal_δ, core, hμ,
          MonoidalCategory.tensor_map, MonoidalCategory.tensorHom_id,
          MonoidalCategory.id_tensorHom] using h.symm
      left_unit := by
        intro A
        have h := L.forgetData.leftUnitor_eq A
        simp only [Iso.trans_hom, Iso.symm_hom, MonoidalCategory.tensorIso_hom,
          Iso.refl_hom] at h
        simpa only [hμ, Category.assoc, Iso.symm_hom, Functor.comp_obj,
          MonoidalCategory.tensor_obj, MonoidalCategory.tensor_map,
          MonoidalCategory.tensorHom_id,
          MonoidalCategory.id_tensorHom] using h.symm
      right_unit := by
        intro A
        have h := L.forgetData.rightUnitor_eq A
        simp only [Iso.trans_hom, Iso.symm_hom, MonoidalCategory.tensorIso_hom,
          Iso.refl_hom] at h
        simpa only [hμ, Category.assoc, Iso.symm_hom, Functor.comp_obj,
          MonoidalCategory.tensor_obj, MonoidalCategory.tensor_map,
          MonoidalCategory.tensorHom_id,
          MonoidalCategory.id_tensorHom] using h.symm
      symmetry := L.forget_braiding }
  refine ⟨m, hT, γ, Iso.refl U, L.ordinaryUnit, ?_⟩
  have hc : eqToIso (congrArg (fun T' ↦ T' ⋙ F) hT) ≪≫ τ = τ := by
    simp only [eqToIso_refl, Iso.refl_trans]
  rw [hc]
  refine ⟨c, ?_⟩
  change L.forgetData.εIso.symm = F.mapIso (Iso.refl U) ≪≫ ζ ≪≫ L.ordinaryUnit.symm
  simpa only [Functor.mapIso_refl, Iso.refl_trans] using L.forget_unit

namespace AlgebraicGeometry.ProEtaleWeilSheaf
variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

/-- Extend the native tensor adjoints to a symmetric monoidal structure, preserving
an already specified invertible mate. -/
theorem native_weil_tensor_coherence
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
    (M : NativeClosedHomModels k₀ l X)
    (η : M.weilHom ⋙ nativeForget k₀ l X ≅
      (nativeForget k₀ l X).op.prod (nativeForget k₀ l X) ⋙ M.ordinaryHom)
    (hη : NativeHomRepresentativeCompatibility (ihomBifunctor k₀ l X)
      (ordinaryIhomBifunctor l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
      M.weilHom M.ordinaryHom M.weilRepresentatives M.ordinaryRepresentatives
      (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)) η)
    (S : CoefficientClosedStructure M.ordinaryHom)
    (β : @SymmetricCategory _ _ S.monoidal)
    (hmonoidal : S.monoidal = (inferInstance : MonoidalCategory
      (DerivedCategory (ProEtale.AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber))))
    (hS : NativeOrdinaryTensorModels l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber
      M.ordinaryHom M.ordinaryRepresentatives S β)
    (T : (DerivedCategory (ProEtaleWeilSheaf k₀ l X)) ×
      DerivedCategory (ProEtaleWeilSheaf k₀ l X) ⥤
        DerivedCategory (ProEtaleWeilSheaf k₀ l X))
    (a : ∀ K : DerivedCategory (ProEtaleWeilSheaf k₀ l X),
      Prod.sectL _ K ⋙ T ⊣ Prod.sectR (op K) _ ⋙ M.weilHom)
    (ha : ∀ (K K' L : DerivedCategory (ProEtaleWeilSheaf k₀ l X)) (f : K' ⟶ K),
        T.map (X := (M.weilHom.obj (op K, L), K'))
            (Y := (M.weilHom.obj (op K', L), K'))
            (M.weilHom.map (X := (op K, L)) (Y := (op K', L)) (f.op, 𝟙 L), 𝟙 K') ≫
              (a K').counit.app L =
          T.map (X := (M.weilHom.obj (op K, L), K'))
            (Y := (M.weilHom.obj (op K, L), K))
            (𝟙 (M.weilHom.obj (op K, L)), f) ≫ (a K).counit.app L)
    (τ : T ⋙ nativeForget k₀ l X ≅
        (nativeForget k₀ l X).prod (nativeForget k₀ l X) ⋙ S.tensor)
    (hτ : ∀ A K : DerivedCategory (ProEtaleWeilSheaf k₀ l X),
        τ.inv.app (A, K) =
          (S.transpose ((nativeForget k₀ l X).obj A) ((nativeForget k₀ l X).obj K)
            ((nativeForget k₀ l X).obj (T.obj (A, K)))).symm
              ((nativeForget k₀ l X).map ((a K).unit.app A) ≫
                η.hom.app (op K, T.obj (A, K)))) :
    ∃ m : MonoidalCategory (DerivedCategory (ProEtaleWeilSheaf k₀ l X)),
    ∃ hT : @MonoidalCategory.tensor _ _ m = T,
    ∃ γ : @SymmetricCategory _ _ m,
    ∃ δ : m.tensorUnit ≅ (DerivedCategory.singleFunctor _ 0).obj (adicConstant k₀ l X),
    ∃ ε : S.monoidal.tensorUnit ≅ (DerivedCategory.singleFunctor _ 0).obj
      (ProEtale.AdicSheaf.unit l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber),
    ∃ c : RingedForgetTensorTransposition.TensorCoherence
        m S.monoidal γ β (nativeForget k₀ l X)
        (eqToIso (congrArg (fun T' ↦ T' ⋙ nativeForget k₀ l X) hT) ≪≫ τ),
      c.unit =
        ((nativeForget k₀ l X).mapIso δ ≪≫
          (Functor.mapDerivedCategorySingleFunctor
            (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)) 0).app
              (adicConstant k₀ l X) ≪≫ ε.symm)
:= by
  obtain ⟨L⟩ := native_weil_tensor_constraint_lifts k₀ l X M η hη S β hmonoidal hS
    T a ha τ hτ
  exact assemble_tensor_constraints (nativeForget k₀ l X) T
    ((DerivedCategory.singleFunctor _ 0).obj (adicConstant k₀ l X))
    ((DerivedCategory.singleFunctor _ 0).obj
      (ProEtale.AdicSheaf.unit l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber))
    ((Functor.mapDerivedCategorySingleFunctor
      (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)) 0).app
        (adicConstant k₀ l X)) S.monoidal β τ L

end AlgebraicGeometry.ProEtaleWeilSheaf
