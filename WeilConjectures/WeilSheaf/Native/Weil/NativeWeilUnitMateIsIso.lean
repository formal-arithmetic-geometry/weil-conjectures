/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Weil.NativeWeilClosedModels
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
import WeilConjectures.WeilSheaf.Native.Weil.NativeWeilRingedTensorModel
import WeilConjectures.WeilSheaf.Native.NativeHomRepresentativeUniqueness
import Mathlib.CategoryTheory.Adjunction.Unique

/-! # Pointwise invertibility of the native tensor unit mate

## Implementation details

The adjunction is computed on a flat-term K-flat representative on the Frobenius ringed
action site, where the mate is the localized identity comparison of the two total tensors
(the native-to-standard row signs cancel). Uniqueness of left adjoints then extends the
statement to every choice of adjunction, without requiring normalization of that choice.

## References

* Stacks Project, Tags 06YS, 08J9 and 0A97
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures

private theorem unit_mate_isIso_of_tensor_model
    {C D : Type*} [Category* C] [Category* D]
    {H : Cᵒᵖ × C ⥤ C} {H' : Dᵒᵖ × D ⥤ D}
    (W : CoefficientClosedStructure H) (S : CoefficientClosedStructure H')
    (F : C ⥤ D) (χ : H ⋙ F ≅ F.op.prod F ⋙ H')
    (t : W.tensor ⋙ F ≅ F.prod F ⋙ S.tensor)
    (ht : ∀ A K, t.inv.app (A, K) =
      (S.transpose (F.obj A) (F.obj K) (F.obj (W.tensor.obj (A, K)))).symm
        (F.map ((W.adjunction K).unit.app A) ≫ χ.hom.app (op K, W.tensor.obj (A, K))))
    (K : C) (L : C ⥤ C) (a : L ⊣ Prod.sectR (op K) C ⋙ H) (A : C) :
    IsIso ((S.transpose (F.obj A) (F.obj K) (F.obj (L.obj A))).symm
      (F.map (a.unit.app A) ≫ χ.hom.app (op K, L.obj A))) := by
  let e := (W.adjunction K).leftAdjointUniq a
  have hu := (W.adjunction K).unit_leftAdjointUniq_hom_app a A
  change (W.adjunction K).unit.app A ≫
    H.map (Prod.mkHom (𝟙 (op K)) (e.hom.app A)) = a.unit.app A at hu
  have hn := χ.hom.naturality (Prod.mkHom (𝟙 (op K)) (e.hom.app A))
  have hn' :
      F.map
          (H.map (Prod.mkHom (𝟙 (op K)) (e.hom.app A))) ≫
          χ.hom.app (op K, L.obj A) =
        χ.hom.app (op K, W.tensor.obj (A, K)) ≫
          H'.map (Prod.mkHom (𝟙 (op (F.obj K)))
            (F.map (e.hom.app A))) := by
    simpa [CoefficientClosedStructure.tensor] using hn
  have hm :
      (S.transpose (F.obj A) (F.obj K)
        (F.obj (L.obj A))).symm
          (F.map (a.unit.app A) ≫ χ.hom.app (op K, L.obj A)) =
        t.inv.app (A, K) ≫ F.map (e.hom.app A) := by
    rw [← hu, Functor.map_comp, Category.assoc]
    erw [hn']
    rw [← Category.assoc]
    exact ((S.adjunction (F.obj K)).homEquiv_naturality_right_symm
      (F.map ((W.adjunction K).unit.app A) ≫
        χ.hom.app (op K, W.tensor.obj (A, K)))
      (F.map (e.hom.app A))).trans
        (congrArg (fun f ↦ f ≫ F.map (e.hom.app A)) (ht A K).symm)
  rw [hm]
  infer_instance

namespace AlgebraicGeometry.ProEtaleWeilSheaf
variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

/-- For any left adjoint of a fixed-source native derived Hom, the ordinary
transpose of the forgotten unit is invertible. -/
theorem native_weil_unit_mate_isIso
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
    (K : DerivedCategory (ProEtaleWeilSheaf k₀ l X))
    (L : DerivedCategory (ProEtaleWeilSheaf k₀ l X) ⥤
      DerivedCategory (ProEtaleWeilSheaf k₀ l X))
    (a : L ⊣ Prod.sectR (op K) _ ⋙ M.weilHom)
    (A : DerivedCategory (ProEtaleWeilSheaf k₀ l X)) :
    IsIso ((S.transpose ((nativeForget k₀ l X).obj A) ((nativeForget k₀ l X).obj K)
      ((nativeForget k₀ l X).obj (L.obj A))).symm
        ((nativeForget k₀ l X).map (a.unit.app A) ≫ η.hom.app (op K, L.obj A))) := by
  obtain ⟨W, γ, δ, ε, t, χ, c, hc, hχ, ht⟩ :=
    native_weil_ringed_tensor_model k₀ l X M S β hmonoidal hS
  have hηχ := native_hom_representative_unique k₀ l X M η hη χ hχ
  subst η
  exact unit_mate_isIso_of_tensor_model W S (nativeForget k₀ l X) χ t ht K L a A

end AlgebraicGeometry.ProEtaleWeilSheaf
