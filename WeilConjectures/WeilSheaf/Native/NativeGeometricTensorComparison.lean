/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.SixFunctors.DerivedWeilTensorOperations
public import WeilConjectures.WeilSheaf.SixFunctors.WeilGeometricHomConstructibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
import WeilConjectures.WeilSheaf.Native.Ordinary.NativeOrdinaryClosedTensorModels
import WeilConjectures.AlgebraicGeometry.Native.NativeScalarForgettingMonoidal
import WeilConjectures.AlgebraicGeometry.Native.NativeScalarForgetting
import WeilConjectures.CategoryTheory.ModuleObjects.MapModMonoidal
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategoryMonoidal

/-! # Tensor comparison for the native geometric realization

The specified native geometric realization preserves the ambient derived tensor. This compares
the two ambient tensor functors and asserts no constructibility.

## Implementation details

Let `F` be forgetting scalar linearity followed by restriction along
`nativeModuleCoefficientIso`; it is an exact equivalence. The relative tensors before and after
`F` represent the same balanced bilinear maps, and the comparison maps on the relative tensor
coequalizers send a pure tensor to the same pure tensor. Applied in each bidegree and to the sum
total complexes, this shows that `F` preserves and reflects K-flatness, so the ordinary native
tensor of `NativeOrdinaryTensorModels` and the condensed `derivedTensor` agree after `F` on
K-flat resolutions; localization gives the natural isomorphism. It is then composed with the
`tensorComparison` of `nativeDerivedClosedComparison`, whiskered by `F.mapDerivedCategory`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite WeilConjectures CategoryTheory.MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtaleWeilSheaf

namespace TensorComparisonProof

universe v w

variable {D : Type v} [Category.{w} D]

private noncomputable def isoOfHomEquiv {A B : D}
    (e : ∀ Z : D, (B ⟶ Z) ≃ (A ⟶ Z))
    (hn : ∀ (Z Z' : D) (a : B ⟶ Z) (b : Z ⟶ Z'),
      e Z' (a ≫ b) = e Z a ≫ b) : A ≅ B where
  hom := e B (𝟙 B)
  inv := (e A).symm (𝟙 A)
  hom_inv_id := by
    rw [← hn B A (𝟙 B) ((e A).symm (𝟙 A)), Category.id_comp,
      Equiv.apply_symm_apply]
  inv_hom_id := by
    apply (e B).injective
    rw [hn A B, Equiv.apply_symm_apply, Category.id_comp]

private theorem tensor_right_map {H : Dᵒᵖ × D ⥤ D}
    (S : CoefficientClosedStructure H) {K K' : D} (f : K ⟶ K') (L : D) :
    (@MonoidalCategory.tensorRight D _ S.monoidal L).map f =
      S.tensor.map (Prod.mkHom f (𝟙 L)) := by
  let := S.monoidal
  exact (MonoidalCategory.tensorHom_id f L).symm

private theorem tensor_left_map {H : Dᵒᵖ × D ⥤ D}
    (S : CoefficientClosedStructure H) (K : D) {L L' : D} (f : L ⟶ L') :
    (@MonoidalCategory.tensorLeft D _ S.monoidal K).map f =
      S.tensor.map (Prod.mkHom (𝟙 K) f) := by
  let := S.monoidal
  exact (MonoidalCategory.id_tensorHom K f).symm

private theorem uncurry_formula {H : Dᵒᵖ × D ⥤ D}
    (S : CoefficientClosedStructure H) (K L M : D) (a : K ⟶ H.obj (op L, M)) :
    (S.transpose K L M).symm a =
      S.tensor.map (Prod.mkHom a (𝟙 L)) ≫ S.evaluation L M := by
  let := S.monoidal
  simp only [CoefficientClosedStructure.transpose,
    CoefficientClosedStructure.tensor, MonoidalCategory.tensor_map,
    MonoidalCategory.tensorHom_id]
  rfl

private theorem uncurry_parameter {H : Dᵒᵖ × D ⥤ D}
    (S : CoefficientClosedStructure H) (K L L' M : D) (g : L' ⟶ L)
    (a : K ⟶ H.obj (op L, M)) :
    (S.transpose K L' M).symm (a ≫ H.map (Prod.mkHom g.op (𝟙 M))) =
      S.tensor.map (Prod.mkHom (𝟙 K) g) ≫ (S.transpose K L M).symm a := by
  rw [uncurry_formula, uncurry_formula]
  have h := S.evaluation_naturality L L' M g
  rw [tensor_right_map, tensor_left_map] at h
  change S.tensor.map (Prod.mkHom (H.map (Prod.mkHom g.op (𝟙 M))) (𝟙 L')) ≫
      S.evaluation L' M =
    S.tensor.map (Prod.mkHom (𝟙 (H.obj (op L, M))) g) ≫ S.evaluation L M at h
  change S.tensor.map (Prod.mkHom (a ≫ H.map (Prod.mkHom g.op (𝟙 M))) (𝟙 L')) ≫
    S.evaluation L' M = _
  have hc : Prod.mkHom (a ≫ H.map (Prod.mkHom g.op (𝟙 M))) (𝟙 L') =
      Prod.mkHom a (𝟙 L') ≫ Prod.mkHom (H.map (Prod.mkHom g.op (𝟙 M))) (𝟙 L') := by
    ext <;> simp
  rw [hc, S.tensor.map_comp, Category.assoc, h, ← Category.assoc,
    ← S.tensor.map_comp]
  have hc' : Prod.mkHom a (𝟙 L') ≫ Prod.mkHom (𝟙 (H.obj (op L, M))) g =
      Prod.mkHom (𝟙 K) g ≫ Prod.mkHom a (𝟙 L) := by
    ext <;> simp
  rw [hc', S.tensor.map_comp, Category.assoc]

private theorem uncurry_both {H : Dᵒᵖ × D ⥤ D}
    (S : CoefficientClosedStructure H) (K K' L L' M : D)
    (f : K ⟶ K') (g : L ⟶ L') (a : K' ⟶ H.obj (op L', M)) :
    (S.transpose K L M).symm
        (f ≫ a ≫ H.map (Prod.mkHom g.op (𝟙 M))) =
      S.tensor.map (Prod.mkHom f g) ≫ (S.transpose K' L' M).symm a := by
  change ((S.adjunction L).homEquiv K M).symm
    (f ≫ (a ≫ H.map (Prod.mkHom g.op (𝟙 M)))) = _
  rw [Adjunction.homEquiv_naturality_left_symm, tensor_right_map]
  change S.tensor.map (Prod.mkHom f (𝟙 L)) ≫
    (S.transpose K' L M).symm (a ≫ H.map (Prod.mkHom g.op (𝟙 M))) = _
  rw [uncurry_parameter, ← Category.assoc, ← S.tensor.map_comp]
  congr 2
  ext <;> simp

-- Images of identities under the common-Hom bijections give the comparison maps.
-- Evaluation naturality makes these maps natural in the second tensor input too.
private noncomputable def closedTensorIso {H : Dᵒᵖ × D ⥤ D}
    (S T : CoefficientClosedStructure H) : S.tensor ≅ T.tensor := by
  let c (x : D × D) (Z : D) :=
    (T.transpose x.1 x.2 Z).trans (S.transpose x.1 x.2 Z).symm
  have hc (x : D × D) (Z Z' : D) (a : T.tensor.obj x ⟶ Z) (b : Z ⟶ Z') :
      c x Z' (a ≫ b) = c x Z a ≫ b := by
    exact (congrArg ((S.adjunction x.2).homEquiv x.1 Z').symm
      ((T.adjunction x.2).homEquiv_naturality_right a b)).trans
        ((S.adjunction x.2).homEquiv_naturality_right_symm _ b)
  refine NatIso.ofComponents (fun x ↦ isoOfHomEquiv (c x) (hc x)) ?_
  intro x y f
  have hi := hc x (T.tensor.obj x) (T.tensor.obj y) (𝟙 _) (T.tensor.map f)
  rw [Category.id_comp] at hi
  change S.tensor.map f ≫ c y _ (𝟙 _) = c x _ (𝟙 _) ≫ T.tensor.map f
  rw [← hi]
  change S.tensor.map f ≫ (S.transpose _ _ _).symm (T.transpose _ _ _ (𝟙 _)) =
    (S.transpose _ _ _).symm (T.transpose _ _ _ (T.tensor.map f))
  have ht := uncurry_both T x.1 y.1 x.2 y.2 (T.tensor.obj y) f.1 f.2
    (T.transpose y.1 y.2 (T.tensor.obj y) (𝟙 _))
  rw [Equiv.symm_apply_apply, Category.comp_id] at ht
  have hf : Prod.mkHom f.1 f.2 = f := by ext <;> rfl
  rw [hf] at ht
  rw [← ht, Equiv.apply_symm_apply]
  exact (uncurry_both S x.1 y.1 x.2 y.2 _ f.1 f.2 _).symm

end TensorComparisonProof

/-- The specified native geometric realization preserves the ambient derived tensor. -/
theorem nativeGeometricForget_tensorComparison
    (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
    [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] :
    Nonempty (nativeDerivedTensor k₀ l X ⋙ nativeGeometricForget k₀ l X ≅
      (nativeGeometricForget k₀ l X).prod (nativeGeometricForget k₀ l X) ⋙
        Functor.uncurry.obj (ProEtale.CondensedRing.derivedTensor
          (Profinite.padicAlgClRingObj l) (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)) := by
  classical
  let Y := (X ↘ Spec (CommRingCat.of k₀)).geometricFiber
  let C := nativeDerivedClosedComparison k₀ l X
  let U := ProEtale.AdicSheaf.forgetAb l Y
  let V := Mod.comap (D := Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
    (ProEtale.nativeModuleCoefficientIso l Y).hom
  obtain ⟨m⟩ := ProEtale.nativeScalarForgetting_monoidal l Y
  let : U.Monoidal := m
  have : U.IsEquivalence := ProEtale.nativeScalarForgetting_isEquivalence l Y
  have : V.IsEquivalence :=
    (Mod.comapEquivalenceOfIsIso
      (ProEtale.nativeModuleCoefficientIso l Y).hom).isEquivalence_functor
  let E := U ⋙ V
  let : E.Monoidal := inferInstanceAs (U ⋙ V).Monoidal
  have : E.IsEquivalence := inferInstance
  have : E.PreservesFlat := Functor.preservesFlat_of_isEquivalence E
  obtain ⟨S, _β, hS, _⟩ := native_ordinary_closed_tensor_models l Y
    C.homModels.ordinaryHom C.homModels.ordinaryRepresentatives
  let e₀ : C.ordinaryClosed.tensor ≅ MonoidalCategory.tensor _ :=
    TensorComparisonProof.closedTensorIso C.ordinaryClosed S ≪≫
      eqToIso (congrArg (fun m ↦ @MonoidalCategory.tensor _ _ m) hS)
  let τ := asIso E.mapDerivedCategoryTensorComparison
  let e₁ : MonoidalCategory.tensor _ ⋙ E.mapDerivedCategory ≅
      E.mapDerivedCategory.prod E.mapDerivedCategory ⋙
        Functor.uncurry.obj (ProEtale.CondensedRing.derivedTensor
          (Profinite.padicAlgClRingObj l) Y) :=
    NatIso.ofComponents (fun x ↦ (τ.app x.1).app x.2) (by
      intro x y f
      have h := (Functor.uncurry.mapIso τ).hom.naturality f
      change E.mapDerivedCategory.map (f.1 ⊗ₘ f.2) ≫ _ = _
      rw [MonoidalCategory.tensorHom_def, Functor.map_comp]
      exact h)
  let e := Functor.isoWhiskerRight e₀ E.mapDerivedCategory ≪≫ e₁
  exact ⟨(Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight C.tensorComparison E.mapDerivedCategory ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft ((nativeForget k₀ l X).prod (nativeForget k₀ l X)) e⟩

end AlgebraicGeometry.ProEtaleWeilSheaf
