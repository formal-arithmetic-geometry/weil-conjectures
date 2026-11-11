/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartClosure

/-!
# Constructible sheaves with field coefficients form an abelian category

Let `X` be a noetherian scheme and let `Λ` be the condensed ring `E̲` for a finite extension
`E / ℚ_ℓ`, or `ℚ̲̄_ℓ`. The individual clauses of blueprint `lemma-constructible-sheaves`, read
off from `ProEtale.coefficientHeart_closure`: the constructible `Λ_X`-modules are closed in
`Mod(X_proét, Λ)` under kernels, cokernels and extensions, and form an abelian category.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

variable (ℓ : ℕ) [Fact ℓ.Prime] (Λ : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1})
  [IsCommMonObj (coefficientHeartRingObj Λ)]

/-- **Closure under kernels.** On a noetherian scheme `X`, with coefficients `E̲` (`E / ℚ_ℓ`
finite) or `ℚ̲̄_ℓ`, the kernel in `Mod(X_proét, Λ)` of a morphism of constructible
`Λ_X`-modules is constructible.
(blueprint: lemma-constructible-sheaves--1) -/
theorem isConstantModelConstructible_kernel
    (hΛ : (∃ E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ),
      FiniteDimensional ℚ_[ℓ] E ∧ Λ = Profinite.padicSubfieldCondensedRing ℓ E) ∨
      Λ = Profinite.padicAlgClCondensedRing ℓ)
    (X : Scheme.{u}) [IsNoetherian X]
    {F G : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (coefficientHeartRingObj Λ) X)} (f : F ⟶ G)
    (hF : IsConstantModelConstructible (coefficientHeartRingObj Λ) X F)
    (hG : IsConstantModelConstructible (coefficientHeartRingObj Λ) X G) :
    IsConstantModelConstructible (coefficientHeartRingObj Λ) X (kernel f) :=
  have := ((coefficientHeart_closure ℓ Λ hΛ).2 X).1
  ObjectProperty.prop_kernel _ f hF hG

/-- **Closure under cokernels.** On a noetherian scheme `X`, with coefficients `E̲`
(`E / ℚ_ℓ` finite) or `ℚ̲̄_ℓ`, the cokernel in `Mod(X_proét, Λ)` of a morphism of
constructible `Λ_X`-modules is constructible.
(blueprint: lemma-constructible-sheaves--2) -/
theorem isConstantModelConstructible_cokernel
    (hΛ : (∃ E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ),
      FiniteDimensional ℚ_[ℓ] E ∧ Λ = Profinite.padicSubfieldCondensedRing ℓ E) ∨
      Λ = Profinite.padicAlgClCondensedRing ℓ)
    (X : Scheme.{u}) [IsNoetherian X]
    {F G : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (coefficientHeartRingObj Λ) X)} (f : F ⟶ G)
    (hF : IsConstantModelConstructible (coefficientHeartRingObj Λ) X F)
    (hG : IsConstantModelConstructible (coefficientHeartRingObj Λ) X G) :
    IsConstantModelConstructible (coefficientHeartRingObj Λ) X (cokernel f) :=
  have := ((coefficientHeart_closure ℓ Λ hΛ).2 X).2.1
  ObjectProperty.prop_cokernel _ f hF hG

/-- **Closure under extensions.** On a noetherian scheme `X`, with coefficients `E̲`
(`E / ℚ_ℓ` finite) or `ℚ̲̄_ℓ`, if `0 → F → M → G → 0` is exact in `Mod(X_proét, Λ)` and `F`
and `G` are constructible, then `M` is constructible.
(blueprint: lemma-constructible-sheaves--3) -/
theorem isConstantModelConstructible_of_shortExact
    (hΛ : (∃ E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ),
      FiniteDimensional ℚ_[ℓ] E ∧ Λ = Profinite.padicSubfieldCondensedRing ℓ E) ∨
      Λ = Profinite.padicAlgClCondensedRing ℓ)
    (X : Scheme.{u}) [IsNoetherian X]
    {S : ShortComplex (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (coefficientHeartRingObj Λ) X))} (hS : S.ShortExact)
    (h₁ : IsConstantModelConstructible (coefficientHeartRingObj Λ) X S.X₁)
    (h₃ : IsConstantModelConstructible (coefficientHeartRingObj Λ) X S.X₃) :
    IsConstantModelConstructible (coefficientHeartRingObj Λ) X S.X₂ :=
  have := ((coefficientHeart_closure ℓ Λ hΛ).2 X).2.2.1
  ObjectProperty.prop_X₂_of_shortExact _ hS h₁ h₃

/-- **Abelian structure.** On a noetherian scheme `X`, with coefficients `E̲` (`E / ℚ_ℓ`
finite) or `ℚ̲̄_ℓ`, the full subcategory `Cons(X, Λ)` of constructible `Λ_X`-modules admits
an abelian category structure.
(blueprint: lemma-constructible-sheaves--4) -/
theorem nonempty_abelian_constantModelConstructible
    (hΛ : (∃ E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ),
      FiniteDimensional ℚ_[ℓ] E ∧ Λ = Profinite.padicSubfieldCondensedRing ℓ E) ∨
      Λ = Profinite.padicAlgClCondensedRing ℓ)
    (X : Scheme.{u}) [IsNoetherian X] :
    Nonempty (Abelian (ConstantModelConstructible (coefficientHeartRingObj Λ) X)) :=
  ((coefficientHeart_closure ℓ Λ hΛ).2 X).2.2.2.1

end AlgebraicGeometry.ProEtale
