/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseGerm
public import WeilConjectures.SixFunctors.ProEtale.Adic.StalkIhomDual

/-!
# Tensor powers of sections of lisse sheaves

For a sheaf of `ℚ̄_ℓ,Y`-modules `F` on a scheme `Y`, let `F^{⊗ 0} = ℚ̄_ℓ` and
`F^{⊗ (k + 1)} = 𝓗om(F^∨, F^{⊗ k})` (`AlgebraicGeometry.ProEtale.adicTensorPow`), the underlying
sheaves of the tensor powers of Weil sheaves. A section `σ` of `F` over `W` has tensor powers
`σ^{⊗ 0} = 1` and `σ^{⊗ (k + 1)} = σ ⊗ σ^{⊗ k}`, the image of `σ ⊗ σ^{⊗ k}` under
`F ⊗ F^{⊗ k} ⟶ 𝓗om(F^∨, F^{⊗ k})` (`AlgebraicGeometry.ProEtale.adicTensorPowSection`).

**Lemma.** If `F` is lisse and some tensor power `σ^{⊗ k}` vanishes, then `σ = 0`
(`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.eq_zero_of_adicTensorPowSection_eq_zero`). Indeed
the germ of `σ^{⊗ k}` at a geometric point is the `k`-th tensor power of the germ of `σ`
(`AlgebraicGeometry.ProEtale.germ_adicTensorPowSection_succ`), which is nonzero if the germ of `σ`
is (`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.toIhomDual_stalk_ne_zero`); and a section of a
lisse sheaf with vanishing germs vanishes
(`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.eq_zero_of_germ_eq_zero`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Functor.LaxMonoidal Limits Opposite

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {l : ℕ} [Fact l.Prime] {Y : Scheme.{u}}

/-- The tensor powers `F^{⊗ 0} = ℚ̄_ℓ`, `F^{⊗ (k + 1)} = 𝓗om(F^∨, F^{⊗ k})` of a sheaf of
`ℚ̄_ℓ,Y`-modules. -/
noncomputable def adicTensorPow (F : AdicSheaf l Y) : ℕ → AdicSheaf l Y
  | 0 => AdicSheaf.unit l Y
  | k + 1 => (Mod.ihom ((Mod.ihom F).obj (AdicSheaf.unit l Y))).obj (adicTensorPow F k)

/-- The unit section `1` of `ℚ̄_ℓ,Y` over `W`. -/
noncomputable def adicUnitSection (W : Y.ProEt) :
    ToType ((AdicSheaf.unit l Y).X.obj.obj (op W)) :=
  (MonObj.one (X := adicConstantSheaf l Y)).hom.app (op W)
    ((ε (sheafToPresheaf (ProEt.topology Y) (WeilCoefficients.{u} l))).app (op W)
      (1 : ULift.{u + 1} (PadicAlgCl l)))

/-- The tensor powers `σ^{⊗ 0} = 1`, `σ^{⊗ (k + 1)} = σ ⊗ σ^{⊗ k}` of a section `σ` of `F`. -/
noncomputable def adicTensorPowSection {F : AdicSheaf l Y} {W : Y.ProEt}
    (σ : ToType (F.X.obj.obj (op W))) : (k : ℕ) → ToType ((adicTensorPow F k).X.obj.obj (op W))
  | 0 => adicUnitSection W
  | k + 1 => (Mod.toIhomDual F (adicTensorPow F k)).hom.app (op W)
      ((μ (sheafToPresheaf (ProEt.topology Y) (WeilCoefficients.{u} l)) F.X
        (adicTensorPow F k).X).app (op W) (σ ⊗ₜ adicTensorPowSection σ k))

/-- Tensor powers of sections commute with restriction. -/
lemma map_adicTensorPowSection {F : AdicSheaf l Y} {W W' : Y.ProEt} (f : W' ⟶ W)
    (σ : ToType (F.X.obj.obj (op W))) :
    ∀ k : ℕ, (adicTensorPow F k).X.obj.map f.op (adicTensorPowSection σ k) =
      adicTensorPowSection (F.X.obj.map f.op σ) k
  | 0 => by
    simp only [adicTensorPowSection, adicUnitSection]
    rw [← ConcreteCategory.comp_apply, ← NatTrans.naturality, ConcreteCategory.comp_apply,
      ← ConcreteCategory.comp_apply ((ε _).app _), ← NatTrans.naturality]
    rfl
  | k + 1 => by
    simp only [adicTensorPowSection]
    rw [← ConcreteCategory.comp_apply, ← NatTrans.naturality, ConcreteCategory.comp_apply,
      ← ConcreteCategory.comp_apply ((μ _ _ _).app _), ← NatTrans.naturality,
      ConcreteCategory.comp_apply, ← map_adicTensorPowSection f σ k]
    rfl

variable {K : Type u} [Field K] [IsAlgClosed K]

/-- The germ of the unit section is the unit section of the stalk of `ℚ̄_ℓ`. -/
lemma germ_adicUnitSection (s : Spec (.of K) ⟶ Y) {W : Y.ProEt}
    (t : ProEt.mk (𝟙 _) ⟶ (MorphismProperty.Over.pullback @WeaklyEtale ⊤ s).obj W) :
    germ _ s (AdicSheaf.unit l Y).X t (adicUnitSection W) =
      (unitSection l s).hom (1 : ULift.{u + 1} (PadicAlgCl l)) := by
  have h₁ := congrArg (fun f ↦ f.hom (1 : ULift.{u + 1} (PadicAlgCl l))) (germ_unit (l := l) t)
  have h₂ := congrArg (fun f ↦ f.hom ((ε (sheafToPresheaf (ProEt.topology Y)
    (WeilCoefficients.{u} l))).app (op W) (1 : ULift.{u + 1} (PadicAlgCl l))))
    (germ_naturality (MonObj.one (X := adicConstantSheaf l Y)) t)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h₁ h₂
  rw [unitSection, ModuleCat.hom_comp, LinearMap.comp_apply, h₁]
  exact h₂.symm

/-- The germ of `σ ⊗ τ` under `F ⊗ N ⟶ 𝓗om(F^∨, N)` is the image of the tensor product of the
germs. -/
lemma germ_toIhomDual (F N : AdicSheaf l Y) (s : Spec (.of K) ⟶ Y) {W : Y.ProEt}
    (t : ProEt.mk (𝟙 _) ⟶ (MorphismProperty.Over.pullback @WeaklyEtale ⊤ s).obj W)
    (σ : ToType (F.X.obj.obj (op W))) (τ : ToType (N.X.obj.obj (op W))) :
    germ _ s _ t ((Mod.toIhomDual F N).hom.app (op W)
        ((μ (sheafToPresheaf (ProEt.topology Y) (WeilCoefficients.{u} l)) F.X N.X).app (op W)
          (σ ⊗ₜ τ))) =
      ((stalkFunctor l s).map (Mod.toIhomDual F N)).hom
        ((μ (stalkFunctor l s) F.X N.X).hom (germ _ s _ t σ ⊗ₜ germ _ s _ t τ)) := by
  have h₁ := congrArg (fun f ↦ f.hom (σ ⊗ₜ τ)) (germ_tensor F.X N.X t)
  have h₂ := congrArg (fun f ↦ f.hom ((μ (sheafToPresheaf (ProEt.topology Y)
    (WeilCoefficients.{u} l)) F.X N.X).app (op W) (σ ⊗ₜ τ)))
    (germ_naturality (Mod.toIhomDual F N) t)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply,
    ModuleCat.MonoidalCategory.tensorHom_tmul] at h₁ h₂
  erw [h₂, ← h₁]
  rfl

/-- **Germs of tensor powers of sections are nonzero.** If `F` is lisse and the germ of `σ` at a
geometric point is nonzero, so is the germ of every tensor power `σ^{⊗ k}`. -/
lemma IsAdicLisseSheaf.germ_adicTensorPowSection_ne_zero {F : AdicSheaf l Y}
    (hF : IsAdicLisseSheaf F) (s : Spec (.of K) ⟶ Y) {W : Y.ProEt}
    (t : ProEt.mk (𝟙 _) ⟶ (MorphismProperty.Over.pullback @WeaklyEtale ⊤ s).obj W)
    (σ : ToType (F.X.obj.obj (op W))) (hσ : germ _ s _ t σ ≠ 0) :
    ∀ k : ℕ, germ _ s _ t (adicTensorPowSection σ k) ≠ 0
  | 0 => by
    rw [adicTensorPowSection, germ_adicUnitSection]
    exact unitSection_one_ne_zero s
  | k + 1 => by
    rw [adicTensorPowSection, germ_toIhomDual]
    exact hF.toIhomDual_stalk_ne_zero _ s hσ (germ_adicTensorPowSection_ne_zero hF s t σ hσ k)

/-- **Tensor powers of nonzero sections of lisse sheaves are nonzero.** -/
theorem IsAdicLisseSheaf.eq_zero_of_adicTensorPowSection_eq_zero {F : AdicSheaf l Y}
    (hF : IsAdicLisseSheaf F) {W : Y.ProEt} (σ : ToType (F.X.obj.obj (op W))) (k : ℕ)
    (h : adicTensorPowSection σ k = 0) : σ = 0 := by
  refine hF.eq_zero_of_germ_eq_zero σ fun K _ _ w t ↦ ?_
  by_contra hσ
  exact hF.germ_adicTensorPowSection_ne_zero (w ≫ W.hom) t σ hσ k (by rw [h, map_zero])

end AlgebraicGeometry.ProEtale
