/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Constructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
public import WeilConjectures.TateTwist.ProEtale

/-!

# Constructibility of the pro-étale Tate twists

Let `ℓ` be a prime and `k` a field of characteristic `p > 0` with `p ≠ ℓ`, and let `Λ` be an
`ℓ`-adic coefficient ring (`𝒪̲_E`, `E̲` or `ℚ̲̄_ℓ`) under `ℤ̲_ℓ` through `φ : ℤ̲_ℓ ⟶ Λ`. For a
separated `k`-scheme `X` of finite type, on which `ℓ` is invertible, the Tate twists `Λ_X(m)`
of `WeilConjectures.TateTwist.ProEtale` are pro-étale locally isomorphic to `Λ_X` (blueprint
`det-def-sp-tate-twist-locally-free`, clause (3)). This file deduces that they are constructible
module objects, and that the shifted twists `Λ_X(m)[n]` are bounded constructible complexes, so
that they are objects of `Dᵇc(X)⟦Λ⟧` (`ProEtale.CondensedRing.boundedConstructibleTateTwist`).

## Main statements

- `ProEtale.CondensedRing.exists_cover_upperStar_tateTwist_iso`: blueprint
  `det-def-sp-tate-twist-locally-free`, clause (3), for the pro-étale `ℓ`-adic twists.
- `ProEtale.CondensedRing.isConstructibleModuleObject_tateTwist`: `Λ_X(m)` is constructible.
- `ProEtale.CondensedRing.boundedConstructible_shiftFunctor_tateTwistDerived`: `Λ_X(m)[n]` is
  bounded constructible.

## Sorried input

The local triviality `exists_cover_upperStar_tateTwist_iso` is `sorry`ed. Its proof needs a
pro-étale cover `X̃ = lim_n X[ζ_{ℓ^n}] ⟶ X` carrying a compatible system of primitive `ℓ^n`-th
roots of unity, on which the inverse system `n ↦ μ_{ℓ^n}` becomes the constant system
`n ↦ ℤ/ℓ^n`, and the compatibility of the pullback `X̃_proét ⟶ X_proét` with the limit defining
`ℤ_ℓ(1)`, with the extension of scalars, and with tensor powers and duals; none of this is
formalized for the pro-étale site. The étale counterpart for finite coefficient rings is proved
(`AlgebraicGeometry.Etale.tateTwistObject_locallyFree`).

-/

@[expose] public section

universe v w u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

/-! ### Free modules of rank one -/

namespace CategoryTheory.Mod

variable {C : Type w} [Category.{v} C] [MonoidalCategory C] [Abelian C] [MonoidalPreadditive C]
  (R : C) [MonObj R] [PreservesFiniteColimits (tensorLeft R)]

/-- The free module object of rank one is the regular module. -/
noncomputable def finiteFreeOneIso : finiteFree R 1 ≅ regular R :=
  biproduct.isoProduct _ ≪≫ productUniqueIso _

/-- The regular module object `R` is finitely presented: it is the cokernel of the zero map
`R^0 ⟶ R^1`. -/
lemma isFinitelyPresented_regular : IsFinitelyPresented R (regular R) :=
  ⟨1, 0, 0, ⟨(finiteFreeOneIso R).symm ≪≫ (cokernelZeroIsoTarget).symm⟩⟩

end CategoryTheory.Mod

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-! ### Local triviality implies constructibility -/

section Local

variable {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]

/-- A module object `N` over `Λ_X` whose pullback `f^* N`, read over `Λ_W`, is finitely presented
is finitely presented when read over `f^* Λ_X`: the two are identified by the isomorphism of ring
objects `α_f : f^* Λ_X ⟶ Λ_W`. -/
lemma isFinitelyPresented_mapMod_of_upperStar {W X : Scheme.{u}} (f : W ⟶ X)
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (h : Mod.IsFinitelyPresented (condensedRingObj Λ W) ((f)^*⟦Λ⟧.obj N)) :
    Mod.IsFinitelyPresented ((f)^*[Ab.{u + 1}].obj (condensedRingObj Λ X))
      (((f)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ X)).obj N) := by
  let α := condensedPullbackHom Λ f
  let e := (Mod.extendScalarsIsoComapInv α).app
    (((f)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ X)).obj N)
  exact Mod.IsFinitelyPresented.of_iso
    ((Mod.comap α).mapIso e ≪≫ (Mod.comapEquivalenceOfIsIso α).counitIso.app _) (h.comap α)

/-- A module object over `Λ_X` which is isomorphic to `Λ` on the members of a pro-étale cover is
pro-étale locally finitely presented. -/
lemma isLocallyFinitelyPresented_of_cover {X : Scheme.{u}}
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage X)
    (h : ∀ i : 𝒰.I₀, Nonempty ((𝒰.f i)^*⟦Λ⟧.obj M ≅ 𝟙_ _)) :
    IsLocallyFinitelyPresented (condensedRingObj Λ X) M :=
  ⟨𝒰, fun i ↦ isFinitelyPresented_mapMod_of_upperStar (𝒰.f i) M
    (Mod.IsFinitelyPresented.of_iso (h i).some.symm (Mod.isFinitelyPresented_regular _))⟩

/-- A pro-étale locally finitely presented module object is constructible, for the trivial
stratification. -/
lemma isConstructibleModuleObject_of_isLocallyFinitelyPresented {X : Scheme.{u}}
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (h : IsLocallyFinitelyPresented (condensedRingObj Λ X) M) :
    IsConstructibleModuleObject (condensedRingObj Λ X) M :=
  ⟨Stratification.trivial X, fun _ ↦ (isLocallyFinitelyPresented_mapMod_iff Λ (𝟙 X) M).2
    (IsLocallyFinitelyPresented.of_iso ((upperStarId Λ X).app M).symm h)⟩

end Local

/-! ### The Tate twists -/

section TateTwist

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ]
  [IsCommMonObj Λ] [IsEllAdicFinitenessCoefficient ℓ Λ]
  (φ : Profinite.continuousMapRingObj.{u} ℤ_[ℓ] ⟶ Λ) [IsMonHom φ]
  (X : Over (Spec (.of k)))

include k in
/-- Blueprint `det-def-sp-tate-twist-locally-free`: Tate twists are well defined and locally free
of rank one, clause (3), for the pro-étale `ℓ`-adic coefficients.

Let `X` be a `k`-scheme, on which `ℓ` is invertible since `ℓ ≠ char k`, and let `Λ` be an
`ℓ`-adic coefficient ring (`𝒪̲_E`, `E̲` or `ℚ̲̄_ℓ`) under `ℤ̲_ℓ` through `φ`. There is a pro-étale
cover `{Uᵢ ⟶ X}` on whose members every Tate twist `Λ_X(m)`, `m ∈ ℤ`, becomes isomorphic to
`Λ_{Uᵢ}`: the twists `Λ_X(1)` are invertible `Λ_X`-modules, and hence so are their tensor
powers `Λ_X(d)` and duals `Λ_X(-d)`. -/
theorem exists_cover_upperStar_tateTwist_iso :
    ∃ 𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage X.left, ∀ (i : 𝒰.I₀) (m : ℤ),
      Nonempty ((𝒰.f i)^*⟦Λ⟧.obj (tateTwist X.left φ m) ≅ 𝟙_ _) :=
  sorry

/-- The Tate twists `Λ_X(m)` are constructible module objects: they are pro-étale locally
isomorphic to `Λ_X` (`exists_cover_upperStar_tateTwist_iso`), hence pro-étale locally finitely
presented. -/
theorem isConstructibleModuleObject_tateTwist (m : ℤ) :
    IsConstructibleModuleObject (condensedRingObj Λ X.left) (tateTwist X.left φ m) := by
  obtain ⟨𝒰, h⟩ := exists_cover_upperStar_tateTwist_iso φ X
  exact isConstructibleModuleObject_of_isLocallyFinitelyPresented
    (isLocallyFinitelyPresented_of_cover _ 𝒰 fun i ↦ h i m)

/-- The shifted Tate twist `Λ_X(m)[n]` is bounded constructible: it is the constructible sheaf
`Λ_X(m)` placed in degree `-n`. -/
theorem boundedConstructible_shiftFunctor_tateTwistDerived (m n : ℤ) :
    boundedConstructible (condensedRingObj Λ X.left)
      ((shiftFunctor _ n).obj (tateTwistDerived X.left φ m)) := by
  let M := tateTwist X.left φ m
  have hM := isConstructibleModuleObject_tateTwist φ X m
  have hS : boundedConstructible (condensedRingObj Λ X.left)
      ((DerivedCategory.singleFunctor _ (-n)).obj M) := by
    refine ⟨⟨⟨-n, inferInstance⟩, ⟨-n, inferInstance⟩⟩, fun i ↦ ?_⟩
    rcases lt_trichotomy i (-n) with hi | rfl | hi
    · exact isConstructibleModuleObject_of_isZero _ (DerivedCategory.isZero_of_isGE _ (-n) i hi)
    · exact IsConstructibleModuleObject.of_iso
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ (-n)).app M).symm hM
    · exact isConstructibleModuleObject_of_isZero _ (DerivedCategory.isZero_of_isLE _ (-n) i hi)
  exact (boundedConstructible _).prop_of_iso
    (((DerivedCategory.singleFunctors _).shiftIso n (-n) 0 (by omega)).app M).symm hS

/-- The shifted Tate twist `Λ_X(m)[n]`, as an object of `Dᵇc(X)⟦Λ⟧`. -/
noncomputable def boundedConstructibleTateTwist (m n : ℤ) : Dᵇc(X.left)⟦Λ⟧ :=
  ⟨(shiftFunctor _ n).obj (tateTwistDerived X.left φ m),
    boundedConstructible_shiftFunctor_tateTwistDerived φ X m n⟩

end TateTwist

end AlgebraicGeometry.ProEtale.CondensedRing
