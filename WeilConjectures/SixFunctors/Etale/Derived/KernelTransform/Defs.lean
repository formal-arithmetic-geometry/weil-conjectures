/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Pullback.Assoc
public import WeilConjectures.SixFunctors.Etale.Derived.Triangulated
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.TriangleShift

/-!

# Kernel transforms: definitions

## Main definitions

- `AlgebraicGeometry.Etale.kernelTransform`: the kernel transform `Φ_𝒦(K) = Rp₂,!(p₁^* K ⊗ᴸ 𝒦)[a]`.
- `AlgebraicGeometry.Etale.kernelConvolution`: the convolution
  `𝒦' ∗ 𝒦 = r₁₃,!(r₁₂^* 𝒦 ⊗ᴸ r₂₃^* 𝒦')`.

## Main statements

- `AlgebraicGeometry.Etale.isTriangulated_kernelTransform`: the kernel transform is a
  triangulated functor.
- `AlgebraicGeometry.Etale.nonempty_iso_kernelTransform_shift`: shifting the kernel shifts the
  kernel transform.

See `WeilConjectures.SixFunctors.Etale.Derived.KernelTransform` for the implementation details.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

section General

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]
variable {S V V' V'' : Scheme.{u}} (π : V ⟶ S) (π' : V' ⟶ S) (π'' : V'' ⟶ S)

/-- The *kernel transform* `Φ_𝒦(K) = Rp₂,!(p₁^* K ⊗ᴸ 𝒦)[a]` attached to a kernel
`𝒦 ∈ D((V ×_S V')_ét)` and a shift `a : ℤ`, where `p₁`, `p₂` are the projections of
`V ×ₛ V'`. -/
noncomputable def kernelTransform [HasCompactification (pullback.snd π π')]
    (𝒦 : DerivedCategory (Sheaf (pullback π π').smallEtaleTopology A)) (a : ℤ) :
    DerivedCategory (Sheaf V.smallEtaleTopology A) ⥤
      DerivedCategory (Sheaf V'.smallEtaleTopology A) :=
  D((pullback.fst π π')^*[A]) ⋙ derivedTensorRight A (pullback π π') 𝒦 ⋙
    R(pullback.snd π π')_![A] ⋙ shiftFunctor _ a

/-- The kernel transform commutes with shifts. -/
noncomputable instance commShiftKernelTransform [HasCompactification (pullback.snd π π')]
    (𝒦 : DerivedCategory (Sheaf (pullback π π').smallEtaleTopology A)) (a : ℤ) :
    (kernelTransform A π π' 𝒦 a).CommShift ℤ :=
  inferInstanceAs ((D((pullback.fst π π')^*[A]) ⋙ derivedTensorRight A (pullback π π') 𝒦 ⋙
    R(pullback.snd π π')_![A] ⋙ shiftFunctor _ a).CommShift ℤ)

/-- The kernel transform is a triangulated functor. -/
instance isTriangulated_kernelTransform [HasCompactification (pullback.snd π π')]
    (𝒦 : DerivedCategory (Sheaf (pullback π π').smallEtaleTopology A)) (a : ℤ) :
    (kernelTransform A π π' 𝒦 a).IsTriangulated :=
  inferInstanceAs ((D((pullback.fst π π')^*[A]) ⋙ derivedTensorRight A (pullback π π') 𝒦 ⋙
    R(pullback.snd π π')_![A] ⋙ shiftFunctor _ a).IsTriangulated)

/-- Shifting the kernel shifts the kernel transform: the kernel transform of `𝒦[a]` with shift
`c` is the kernel transform of `𝒦` with shift `a + c`. -/
theorem nonempty_iso_kernelTransform_shift [HasCompactification (pullback.snd π π')]
    (𝒦 : DerivedCategory (Sheaf (pullback π π').smallEtaleTopology A)) (a c : ℤ) :
    Nonempty (kernelTransform A π π' ((shiftFunctor _ a).obj 𝒦) c ≅
        kernelTransform A π π' 𝒦 (a + c)) := by
  let R := R(pullback.snd π π')_![A]
  let e₁ : derivedTensorRight A (pullback π π') (𝒦⟦a⟧) ⋙ R ⋙ shiftFunctor _ c ≅
      derivedTensorRight A (pullback π π') 𝒦 ⋙ shiftFunctor _ a ⋙ R ⋙ shiftFunctor _ c :=
    Functor.isoWhiskerRight (derivedTensorRightShiftIso A 𝒦 a) _ ≪≫ Functor.associator _ _ _
  let e₂ : shiftFunctor _ a ⋙ R ⋙ shiftFunctor _ c ≅ R ⋙ shiftFunctor _ (a + c) :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (R.commShiftIso a) (shiftFunctor _ c) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft R (shiftFunctorAdd' _ a c (a + c) rfl).symm
  exact ⟨Functor.isoWhiskerLeft D((pullback.fst π π')^*[A])
    (e₁ ≪≫ Functor.isoWhiskerLeft (derivedTensorRight A (pullback π π') 𝒦) e₂)⟩

/-- The convolution `𝒦' ∗ 𝒦 = r₁₃,!(r₁₂^* 𝒦 ⊗ᴸ r₂₃^* 𝒦')` of a kernel `𝒦` on `V ×_S V'`
with a kernel `𝒦'` on `V' ×_S V''`, a kernel on `V ×_S V''`. Here `r₁₂`, `r₂₃`, `r₁₃` are the
projections of the triple product `(V ×_S V') ×_{V'} (V' ×_S V'')`. -/
noncomputable def kernelConvolution
    [HasCompactification (pullback.tripleProj₁₃ π π' π'')]
    (𝒦 : DerivedCategory (Sheaf (pullback π π').smallEtaleTopology A))
    (𝒦' : DerivedCategory (Sheaf (pullback π' π'').smallEtaleTopology A)) :
    DerivedCategory (Sheaf (pullback π π'').smallEtaleTopology A) :=
  (R(pullback.tripleProj₁₃ π π' π'')_![A]).obj
    ((derivedTensorRight A (pullback (pullback.snd π π') (pullback.fst π' π''))
        ((D((pullback.snd (pullback.snd π π') (pullback.fst π' π''))^*[A])).obj 𝒦')).obj
      ((D((pullback.fst (pullback.snd π π') (pullback.fst π' π''))^*[A])).obj 𝒦))

end General

end AlgebraicGeometry.Etale
