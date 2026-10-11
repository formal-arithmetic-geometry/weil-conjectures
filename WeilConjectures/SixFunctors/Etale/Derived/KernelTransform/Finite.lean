/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.AlgebraicGeometry.InvertibleExponent
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Pullback.Assoc
public import WeilConjectures.SixFunctors.Etale.Derived.Composition
public import WeilConjectures.SixFunctors.Etale.Derived.Exchange
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import WeilConjectures.SixFunctors.Etale.Derived.Shift
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
public import WeilConjectures.SixFunctors.Etale.Derived.Triangulated
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal
public import WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition

/-!

# Kernel transforms at finite coefficients

## Main statements

- `AlgebraicGeometry.Etale.nonempty_iso_kernelTransform_comp`: composition of kernel
  transforms, at finite coefficients.
- `AlgebraicGeometry.Etale.nonempty_iso_kernelTransform_diagonal`: the kernel transform of a
  kernel supported on the diagonal is a tensor product.

See `WeilConjectures.SixFunctors.Etale.Derived.KernelTransform` for the implementation notes.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ]
variable {S V V' V'' : Scheme.{u}} (π : V ⟶ S) (π' : V' ⟶ S) (π'' : V'' ⟶ S)

/-- The composite of the kernel transform of `𝒦` with shift `a` and the kernel transform of
`𝒦'` with shift `c` is the kernel transform of the convolution `𝒦' ∗ 𝒦` with shift `a + c`.
The composite is read on the triple product, in the cartesian square

```
    V ×ₛ V' ×ₛ V'' ──r₁₂──▶ V ×ₛ V'
          │                    │
       r₂₃│                    │p₂
          ▼                    ▼
      V' ×ₛ V'' ─────q₁─────▶ V'
```

with `r₁₃ : V ×ₛ V' ×ₛ V'' ⟶ V ×ₛ V''` the remaining projection and
`q₂ : V' ×ₛ V'' ⟶ V''` the second projection.

Class: torsion; decided by compact-support base change and the projection formula for `Rf_!`,
which need `[Finite Λ]`. The composition law of `Rf_!` is applied
to `r₁₃ ≫ s₂ = r₂₃ ≫ q₂`, `s₂ : V ×ₛ V'' ⟶ V''` being the second projection, which is why that
composite is assumed to admit a compactification.
(sketch blueprint: `sk-lem-kernel-composition`; blueprint: `lem-fd-kernel-composition`) -/
theorem nonempty_iso_kernelTransform_comp [Finite Λ]
    [LocallyOfFiniteType π] [QuasiCompact π] [LocallyOfFiniteType π'] [QuasiCompact π']
    [HasCompactification (pullback.tripleProj₁₃ π π' π'')]
    [HasCompactification (pullback.snd π π')] [HasCompactification (pullback.snd π' π'')]
    [HasCompactification (pullback.snd π π'')]
    [HasCompactification (pullback.tripleProj₁₃ π π' π'' ≫ pullback.snd π π'')]
    (𝒦 : DerivedCategory (Sheaf (pullback π π').smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (𝒦' : DerivedCategory (Sheaf (pullback π' π'').smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (a c : ℤ) :
    Nonempty (kernelTransform (ModuleCat.{u + 1} Λ) π π' 𝒦 a ⋙
          kernelTransform (ModuleCat.{u + 1} Λ) π' π'' 𝒦' c ≅
        kernelTransform (ModuleCat.{u + 1} Λ) π π''
          (kernelConvolution (ModuleCat.{u + 1} Λ) π π' π'' 𝒦 𝒦') (a + c)) :=
  have := isIso_rightDerivedLowerShriekBaseChangeMap Λ
    (IsPullback.of_hasPullback (pullback.snd π π') (pullback.fst π' π''))
  nonempty_iso_kernelTransform_comp_of_nonempty_iso (ModuleCat.{u + 1} Λ) π π' π''
    (fun f g _ _ _ _ ↦ nonempty_iso_rightDerivedLowerShriek_comp Λ f g)
    ⟨asIso (rightDerivedLowerShriekBaseChangeMap _
      (IsPullback.of_hasPullback (pullback.snd π π') (pullback.fst π' π'')))⟩
    (fun L ↦ nonempty_iso_rightDerivedLowerShriek_comp_derivedTensorRight _ _ L
      (fun K ↦ hasProjectionFormula_of_finite Λ _ K L))
    (fun K ↦ nonempty_iso_derivedTensor_obj_rightDerivedLowerShriek _ _ K
      (fun L ↦ hasProjectionFormula_of_finite Λ _ K L)) 𝒦 𝒦' a c

/-- `F ⋙ T ⋙ G ⋙ H ≅ M` from `T ≅ P ⋙ M ⋙ Q`, `F ⋙ P ≅ 𝟭`, `Q ⋙ G ≅ 𝟭` and `H ≅ 𝟭`, stated
for abstract functors so that the kernel never unfolds the concrete functors. -/
private lemma _root_.CategoryTheory.Functor.nonempty_iso_comp_comp_comp_of_iso {C D : Type*}
    [Category C] [Category D] (F : C ⥤ D) (T : D ⥤ D) (G : D ⥤ C) (H : C ⥤ C) (P : D ⥤ C)
    (M : C ⥤ C) (Q : C ⥤ D) (t : T ≅ P ⋙ M ⋙ Q) (u : F ⋙ P ≅ 𝟭 C) (c : Q ⋙ G ≅ 𝟭 C)
    (h : H ≅ 𝟭 C) : Nonempty (F ⋙ T ⋙ G ⋙ H ≅ M) :=
  ⟨Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _
      (Functor.isoWhiskerLeft _ h ≪≫ Functor.rightUnitor _)) ≪≫
    Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight t _) ≪≫
    Functor.isoWhiskerLeft _ (Functor.associator _ _ _) ≪≫ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight u _ ≪≫ Functor.leftUnitor _ ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ c ≪≫ Functor.rightUnitor _⟩

/-- `Δ^* p₁^* ≅ 𝟭`, since `Δ ≫ p₁ = 𝟙`. -/
private lemma kt_diagonal_upperStar :
    Nonempty (D((pullback.fst π π)^*[ModuleCat.{u + 1} Λ]) ⋙
      L((pullback.diagonal π)^*[ModuleCat.{u + 1} Λ]) ≅ 𝟭 _) := by
  let A := ModuleCat.{u + 1} Λ
  exact ⟨Functor.isoWhiskerRight (leftDerivedUpperStarIsoMapDerivedCategory A _).symm _ ≪≫
      (leftDerivedUpperStarComp A (pullback.diagonal π) (pullback.fst π π) (𝟙 V)
        (pullback.diagonal_fst π).symm).symm ≪≫
      Functor.leftDerivedFunctorNatIso _ (Etale.upperStarId A _) ≪≫
      (𝟭 _).leftDerivedFunctorIsoMapDerivedCategory ≪≫ Functor.mapDerivedCategoryIdIso _⟩

/-- `Rp₂,! RΔ_! ≅ 𝟭`, by the composition law and `Δ ≫ p₂ = 𝟙`. -/
private lemma kt_diagonal_lowerShriek [Finite Λ] [IsSeparated π]
    [HasCompactification (pullback.snd π π)] :
    Nonempty (R(pullback.diagonal π)_![ModuleCat.{u + 1} Λ] ⋙
      R(pullback.snd π π)_![ModuleCat.{u + 1} Λ] ≅ 𝟭 _) := by
  let A := ModuleCat.{u + 1} Λ
  have h₂ : pullback.diagonal π ≫ pullback.snd π π = 𝟙 V := pullback.diagonal_snd π
  have : HasCompactification (pullback.diagonal π ≫ pullback.snd π π) := .of_eq h₂.symm
  have : QuasiCompact (pullback.diagonal π ≫ pullback.snd π π) := by
    rw [h₂]
    infer_instance
  have hcongr {X Y : Scheme.{u}} {f f' : X ⟶ Y} [HasCompactification f]
      [HasCompactification f'] (h : f = f') : Nonempty (R(f)_![A] ≅ R(f')_![A]) := by
    subst h
    exact ⟨Iso.refl _⟩
  obtain ⟨pid⟩ := nonempty_iso_rightDerivedLowerShriek_rightDerivedLowerStar A (𝟙 V)
  obtain ⟨c⟩ := nonempty_iso_rightDerivedLowerShriek_comp Λ (pullback.diagonal π)
    (pullback.snd π π)
  obtain ⟨cc⟩ := hcongr h₂
  exact ⟨c.symm ≪≫ cc ≪≫ pid ≪≫
    (Etale.lowerStar A (𝟙 V)).rightDerivedFunctorIsoMapDerivedCategory ≪≫
      Functor.mapDerivedCategoryNatIso (Etale.lowerStarId A V) ≪≫
      Functor.mapDerivedCategoryIdIso _⟩

/-- The projection formula `RΔ_! N ⊗ᴸ - ≅ RΔ_!(N ⊗ᴸ Δ^* -)` for the diagonal, natural in the
second factor. -/
private lemma kt_diagonal_projectionFormula [Finite Λ] [IsSeparated π]
    (N : DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Nonempty ((derivedTensor (ModuleCat.{u + 1} Λ) _).obj
        ((R(pullback.diagonal π)_![ModuleCat.{u + 1} Λ]).obj N) ≅
      L((pullback.diagonal π)^*[ModuleCat.{u + 1} Λ]) ⋙
        (derivedTensor (ModuleCat.{u + 1} Λ) V).obj N ⋙
        R(pullback.diagonal π)_![ModuleCat.{u + 1} Λ]) :=
  nonempty_iso_derivedTensor_obj_rightDerivedLowerShriek _ (pullback.diagonal π) N
    (fun L ↦ hasProjectionFormula_of_finite Λ _ N L)

/-- `- ⊗ᴸ RΔ_* N ≅ - ⊗ᴸ RΔ_! N`, the diagonal being proper. -/
private lemma kt_diagonal_lowerStar [IsSeparated π]
    (N : DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Nonempty (derivedTensorRight (ModuleCat.{u + 1} Λ) _
        ((R((pullback.diagonal π)_*[ModuleCat.{u + 1} Λ])).obj N) ≅
      derivedTensorRight (ModuleCat.{u + 1} Λ) _
        ((R(pullback.diagonal π)_![ModuleCat.{u + 1} Λ]).obj N)) := by
  obtain ⟨pz⟩ := nonempty_iso_rightDerivedLowerShriek_rightDerivedLowerStar
    (ModuleCat.{u + 1} Λ) (pullback.diagonal π)
  exact ⟨(derivedTensor (ModuleCat.{u + 1} Λ) _).flip.mapIso (pz.app N).symm⟩

/-- `- ⊗ᴸ N ≅ N ⊗ᴸ -`. -/
private lemma kt_derivedTensorRight_flip (X : Scheme.{u})
    (N : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Nonempty (derivedTensorRight (ModuleCat.{u + 1} Λ) X N ≅
      (derivedTensor (ModuleCat.{u + 1} Λ) X).obj N) := by
  obtain ⟨β⟩ := nonempty_iso_derivedTensor_flip (ModuleCat.{u + 1} Λ) X
  exact ⟨(β.app N).symm⟩

/-- The kernel transform of a kernel `Δ_* N` supported on the diagonal of `V ×_S V`, with
shift `0`, is tensoring with `N`:

`Rp₂,!(p₁^* K ⊗ᴸ Δ_* N) ≅ K ⊗ᴸ N`,

naturally in `K`, where `Δ` is the diagonal of the separated morphism `π`:

```
             Δ
        V ──────▶ V ×ₛ V ──p₂──▶ V
         ╲          │
          ╲ 𝟙       │p₁
           ╲        ▼
            ──────▶ V
```

with `Δ ≫ p₁ = 𝟙 = Δ ≫ p₂`. For `N = Λ` this says that `Δ_* Λ` is the identity kernel.

Class: compactification-dependent; decided by independence of the compactification. The
blueprint proof is formal: the projection formula for the closed immersion `Δ`, `Δ_* = Δ_!`
and `Δ ≫ p₂ = 𝟙`. Here `[Finite Λ]` enters solely through independence of the
compactification (`AlgebraicGeometry.Etale.rightDerivedLowerShriekIso`), since `R(f)_!` is
computed with a chosen compactification. The same comparison is why `[QuasiCompact π]` is
assumed: `AlgebraicGeometry.Etale.rightDerivedLowerShriekIso` compares compactifications of a
quasi-compact morphism, here of `p₂` and of `Δ ≫ p₂ = 𝟙`; `p₂` is quasi-compact as a base
change of `π`. `[IsSeparated π]` makes `Δ` a closed immersion.
(sketch blueprint: `sk-thm-inversion`, proof) -/
theorem nonempty_iso_kernelTransform_diagonal [Finite Λ] [IsSeparated π] [QuasiCompact π]
    [HasCompactification (pullback.snd π π)]
    (N : DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Nonempty (kernelTransform (ModuleCat.{u + 1} Λ) π π
          ((R((pullback.diagonal π)_*[ModuleCat.{u + 1} Λ])).obj N) 0 ≅
        derivedTensorRight (ModuleCat.{u + 1} Λ) V N) := by
  obtain ⟨t₁⟩ := kt_diagonal_projectionFormula Λ π N
  obtain ⟨t₂⟩ := kt_diagonal_lowerStar Λ π N
  obtain ⟨t₃⟩ := kt_derivedTensorRight_flip Λ _
    ((R(pullback.diagonal π)_![ModuleCat.{u + 1} Λ]).obj N)
  obtain ⟨t₄⟩ := kt_derivedTensorRight_flip Λ _ N
  obtain ⟨u⟩ := kt_diagonal_upperStar Λ π
  obtain ⟨c⟩ := kt_diagonal_lowerShriek Λ π
  exact Functor.nonempty_iso_comp_comp_comp_of_iso _ _ _ _ _ _ _
    (t₂ ≪≫ t₃ ≪≫ t₁ ≪≫ Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight t₄.symm _))
    u c (shiftFunctorZero _ ℤ)

end AlgebraicGeometry.Etale
