/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Hom.EtaleHomNormalizedShift
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.Typing

/-!
# Exactness of the Verdier dual on `Dctf`

For a finite coefficient ring `Λ`, the Verdier dual `𝔻_X = RHom(-, ω_X)` is an exact
contravariant functor: it commutes with the shifts and carries distinguished triangles of
`D(X_ét)ᵒᵖ` to distinguished triangles
(`AlgebraicGeometry.Etale.exists_commShift_isTriangulated_verdierDual`).
Its restriction to the triangulated subcategory `Dctf(X, Λ)`, when it preserves it, is then exact
too, and so is the anti-equivalence `AlgebraicGeometry.Etale.verdierDualEquivalence`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Pretriangulated Pretriangulated.Opposite

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {X S : Scheme.{u}} (a : X ⟶ S)
  [HasCompactification a]

/-- The Verdier dual `𝔻_X = RHom(-, ω_X) : D(X_ét)ᵒᵖ ⥤ D(X_ét)` is exact: it commutes with the
shifts and carries distinguished triangles of `D(X_ét)ᵒᵖ` to distinguished triangles. -/
theorem exists_commShift_isTriangulated_verdierDual :
    ∃ _ : (verdierDual Λ a).CommShift ℤ, (verdierDual Λ a).IsTriangulated := by
  obtain ⟨s, -, h⟩ := etaleHom_normalizedShift_exists (ModuleCat.{u + 1} Λ) X
    (dualizingComplex Λ a)
  exact ⟨s, h⟩

/-- **Exactness of Verdier duality on `Dctf`**. If the Verdier dual `𝔻_X` preserves
`Dctf(X, Λ)`, its restriction `𝔻_X : Dctf(X, Λ)ᵒᵖ ⥤ Dctf(X, Λ)`
(`AlgebraicGeometry.Etale.DerivedCategoryFiniteTor.verdierDual`) is an exact contravariant
functor: it commutes with the shifts and is triangulated. -/
theorem DerivedCategoryFiniteTor.exists_commShift_isTriangulated_verdierDual
    (h : ∀ ⦃K⦄, DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K →
      DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X
        ((Etale.verdierDual Λ a).obj (op K))) :
    ∃ _ : (DerivedCategoryFiniteTor.verdierDual Λ a h).CommShift ℤ,
      (DerivedCategoryFiniteTor.verdierDual Λ a h).IsTriangulated := by
  obtain ⟨_, _⟩ := Etale.exists_commShift_isTriangulated_verdierDual Λ a
  unfold DerivedCategoryFiniteTor.verdierDual DerivedCategoryFiniteTor.ι
  let : (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X).ι.op.CommShift ℤ :=
    inferInstance
  have : (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X).ι.op.IsTriangulated :=
    inferInstance
  have : ((DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X).ι.op ⋙
      Etale.verdierDual Λ a).IsTriangulated :=
    inferInstance
  exact ⟨ObjectProperty.commShiftLift _ _ _, ObjectProperty.isTriangulated_lift _ _ _⟩

/-- **Exactness of Verdier duality on `Dctf`**. For `X` separated of finite type over an
algebraically closed field `k` and a finite `Λ` whose exponent is invertible on `k`, the
anti-equivalence `𝔻_X : Dctf(X, Λ)ᵒᵖ ≌ Dctf(X, Λ)`
(`AlgebraicGeometry.Etale.verdierDualEquivalence`) is exact: its functor commutes with the shifts
and is triangulated. -/
theorem exists_commShift_isTriangulated_verdierDualEquivalence_functor {k : Type u} [Field k]
    [IsAlgClosed k] [HasInvertibleExponent Λ (Spec (.of k))] (aX : X ⟶ Spec (.of k))
    [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX] [HasCompactification aX] :
    ∃ _ : (verdierDualEquivalence Λ aX).functor.CommShift ℤ,
      (verdierDualEquivalence Λ aX).functor.IsTriangulated := by
  obtain ⟨_, _⟩ := DerivedCategoryFiniteTor.exists_commShift_isTriangulated_verdierDual Λ aX
    fun _ hK ↦ constructibleFiniteTor_verdierDual Λ aX hK
  let e := (DerivedCategoryFiniteTor.verdierDualEquivalenceFunctorIso Λ aX).symm
  let := Functor.CommShift.ofIso e ℤ
  have := Functor.CommShift.ofIso_compatibility e ℤ
  exact ⟨inferInstance, Functor.isTriangulated_of_iso e⟩

end Etale

end AlgebraicGeometry
