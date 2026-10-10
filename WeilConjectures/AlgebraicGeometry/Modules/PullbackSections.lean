/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.FreeGenerator
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackTilde
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# Sections of pullbacks of modules

We compare sections of pullbacks of `𝒪`-modules along composites, and compute the global
sections of the pullback of a quasi-coherent module along `Spec S ⟶ Spec R`: they are
`S ⊗[R] Γ(N)`, with `1 ⊗ n` corresponding to the image of `n` under the unit of the adjunction.

## Main definitions

- `AlgebraicGeometry.Scheme.Modules.pullbackΓEquiv`: `S ⊗[R] Γ(N) ≃ Γ(f^* N)` for a
  quasi-coherent `N` on `Spec R` and `f = Spec.map φ`.

## Main statements

- `AlgebraicGeometry.Scheme.Modules.pullbackCompOfEq_hom_app_map_pullbackUnit`: the comparison
  `g^* f^* M ≅ fg^* M` on sections, restricted to an open, in the image of the units.
-/

@[expose] public section

universe u

open CategoryTheory Opposite TensorProduct

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y Z : Scheme.{u}}

/-- The unit of `f^* ⊣ f_*` on sections is semilinear along `f.app U`. -/
lemma pullbackUnitApp_smul (f : Y ⟶ X) (M : X.Modules) (U : X.Opens) (a : Γ(X, U))
    (m : Γ(M, U)) :
    pullbackUnitApp f M U (a • m) = f.app U a • pullbackUnitApp f M U m :=
  Hom.app_smul (pullbackUnit f M) a m

/-- The comparison `pullbackCompOfEq` on sections over an open `V` contained in the preimage of
`U`, in the image of the units: `(η_g (η_f m))|_V ↦ (η_fg m)|_V`. -/
lemma pullbackCompOfEq_hom_app_map_pullbackUnit (g : Z ⟶ Y) (f : Y ⟶ X) (fg : Z ⟶ X)
    (h : g ≫ f = fg) (M : X.Modules) {U : X.Opens} (m : Γ(M, U)) {V : Z.Opens}
    (hV₁ : V ≤ g ⁻¹ᵁ f ⁻¹ᵁ U) (hV₂ : V ≤ fg ⁻¹ᵁ U) :
    ((pullbackCompOfEq g f fg h M).hom).app V
      (((pullback g).obj ((pullback f).obj M)).presheaf.map (homOfLE hV₁).op
        (pullbackUnitApp g _ _ (pullbackUnitApp f M U m))) =
      ((pullback fg).obj M).presheaf.map (homOfLE hV₂).op (pullbackUnitApp fg M U m) := by
  subst h
  have h₁ := pullbackUnit_comp_app_apply g f M U m
  have h₂ : (pullbackComp g f).inv.app M ≫ (pullbackCompOfEq g f (g ≫ f) rfl M).hom = 𝟙 _ := by
    simp [pullbackCompOfEq, pullbackCongr]
  have h₁' : pullbackUnitApp g ((pullback f).obj M) (f ⁻¹ᵁ U) (pullbackUnitApp f M U m) =
      ((pullbackComp g f).inv.app M).app ((g ≫ f) ⁻¹ᵁ U) (pullbackUnitApp (g ≫ f) M U m) :=
    h₁.symm
  rw [h₁']
  erw [← Hom.app_presheaf_map]
  change Hom.app ((pullbackComp g f).inv.app M ≫ (pullbackCompOfEq g f (g ≫ f) rfl M).hom) V _ = _
  rw [h₂]
  rfl

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

variable {R S : CommRingCat.{u}} (φ : R ⟶ S)

/-- **Global sections of the pullback of a quasi-coherent module along `Spec S ⟶ Spec R`.**
For a quasi-coherent module `N` on `Spec R`, the global sections of its pullback along
`Spec.map φ` are `S ⊗[R] Γ(N)`. -/
noncomputable def pullbackΓEquiv (N : (Spec R).Modules) [N.IsQuasicoherent] :
    (ModuleCat.extendScalars φ.hom).obj (moduleSpecΓFunctor.obj N) ≃ₗ[S]
      Γ((pullback (Spec.map φ)).obj N, ⊤) :=
  have : IsIso N.fromTildeΓ := isIso_fromTildeΓ_of_isQuasicoherent N
  have : IsIso ((pullback (Spec.map φ)).map N.fromTildeΓ) := Functor.map_isIso _ _
  have : IsIso (((pullback (Spec.map φ)).map N.fromTildeΓ).app ⊤) := inferInstance
  tildePullbackΓEquiv φ (moduleSpecΓFunctor.obj N) ≪≫ₗ
    LinearEquiv.ofBijective (Hom.appSpecₗ ((pullback (Spec.map φ)).map N.fromTildeΓ) ⊤)
      (ConcreteCategory.bijective_of_isIso ((((pullback (Spec.map φ)).map N.fromTildeΓ)).app ⊤))

lemma pullbackΓEquiv_one_tmul (N : (Spec R).Modules) [N.IsQuasicoherent]
    (n : Γ(N, ⊤)) :
    pullbackΓEquiv φ N ((1 : S) ⊗ₜ n) = pullbackUnitApp (Spec.map φ) N ⊤ n := by
  rw [pullbackΓEquiv, LinearEquiv.trans_apply, tildePullbackΓEquiv_one_tmul]
  have h := pullbackUnit_naturality_apply (Spec.map φ) N.fromTildeΓ ⊤
    (tilde.toOpen (moduleSpecΓFunctor.obj N) ⊤ n)
  rw [fromTildeΓ_app_toOpen] at h
  exact h

end AlgebraicGeometry.Scheme.Modules
