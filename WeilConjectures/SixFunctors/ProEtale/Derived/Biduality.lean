/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Biduality
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek
public import WeilConjectures.SixFunctors.ProEtale.Derived.ComparisonBraided
public import WeilConjectures.SixFunctors.ProEtale.Derived.HomComparison

/-!
# Verdier biduality on the pro-étale site at a finite stage

Let `k` be an algebraic closure of `𝔽_p`, `Y` a separated scheme of finite type over `k` and `Λ`
a finite ring whose exponent is invertible on `Y`. This file transports Verdier biduality from
the étale site (`AlgebraicGeometry.Etale.isIso_verdierDualDoubleDual_app`) to the small
pro-étale site (blueprint `thm-fix-general-biduality`).

## Main definitions

- `AlgebraicGeometry.ProEtale.verdierDualDoubleDual`: the double-dual morphism
  `δ_K : K ⟶ 𝔻_Y 𝔻_Y K` on `D(Y_proét)`.
- `AlgebraicGeometry.ProEtale.verdierDualEquivalence`: the anti-equivalence
  `𝔻_Y : Dctf(Y_proét, Λ)ᵒᵖ ≌ Dctf(Y_proét, Λ)`.

## Main statements

- `AlgebraicGeometry.ProEtale.constructibleFiniteTor_verdierDual`: `𝔻_Y` preserves
  `Dctf(Y_proét, Λ)`.
- `AlgebraicGeometry.ProEtale.isIso_verdierDualDoubleDual_app`: `δ_K` is an isomorphism on
  `Dctf(Y_proét, Λ)`.
-/

@[expose] public section

universe u' u

open CategoryTheory MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

section General

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

/-- The braiding of the derived tensor product on `D(X_proét)`: the braiding of the sheaf
category with the Koszul sign rule, descended along K-flat resolutions
(`CategoryTheory.DerivedCategory.braidedCategory`). It is used as a local instance. -/
noncomputable abbrev derivedBraidedCategory (X : Scheme.{u}) :
    BraidedCategory (DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :=
  DerivedCategory.braidedCategory _

attribute [local instance] derivedBraidedCategory Etale.derivedBraidedCategory

variable {X Y : Scheme.{u}} (a : X ⟶ Y) [HasCompactification a]
  [Etale.HasBoundedBelowUpperShriek A a]

/-- Blueprint `lem-weil-duality-pairing`, on the pro-étale site: the double-dual morphism
`δ_K : K ⟶ 𝔻_X 𝔻_X K`, natural in `K`, the transpose of the evaluation pairing
`K ⊗ᴸ 𝔻_X K ⟶ ω_X` precomposed with the symmetry. It is
`CategoryTheory.MonoidalClosed.toIhomIhom` for the dualizing complex. -/
noncomputable def verdierDualDoubleDual :
    𝟭 _ ⟶ (verdierDual A a).rightOp ⋙ verdierDual A a :=
  MonoidalClosed.toIhomIhomNatTrans (dualizingComplex A a)

open Functor.LaxMonoidal in
/-- Blueprint `lem-weil-finite-duality-site-comparison`: the site comparison identifies the
double-dual maps. Let `e : Lν^* ω_X ⟶ ω_{X, proét}` be an isomorphism from the pullback of the
étale dualizing complex to the pro-étale one. If the canonical comparison maps
`ν^* RHom(K, ω_X) ⟶ RHom(ν^* K, ν^* ω_X)` and `ν^* RHom(𝔻_X K, ω_X) ⟶ RHom(ν^* 𝔻_X K, ν^* ω_X)`
of the braided functor `Lν^*` are isomorphisms, then `Lν^*` carries the étale double-dual map
`δ_K` to an isomorphism if and only if the pro-étale double-dual map `δ_{Lν^* K}` is an
isomorphism (`CategoryTheory.MonoidalClosed.isIso_map_toIhomIhom_iff_of_isIso_comp`). -/
theorem isIso_leftDerived_map_verdierDualDoubleDual_app_iff
    [(ν^*(X)[A]).PreservesFlat]
    (e : (ν^*(X)[A]).leftDerivedFunctor.obj (Etale.dualizingComplex A a) ⟶ dualizingComplex A a)
    [IsIso e] (K : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (hK : IsIso (leftDerivedComparisonUpperStarIhomComparison A X K (Etale.dualizingComplex A a)))
    (hDK : IsIso (leftDerivedComparisonUpperStarIhomComparison A X
      ((Etale.verdierDual A a).obj (op K)) (Etale.dualizingComplex A a))) :
    IsIso ((ν^*(X)[A]).leftDerivedFunctor.map ((Etale.verdierDualDoubleDual A a).app K)) ↔
      IsIso ((verdierDualDoubleDual A a).app ((ν^*(X)[A]).leftDerivedFunctor.obj K)) := by
  let := leftDerivedComparisonUpperStarBraided A X
  have : IsIso ((ihomComparison (ν^*(X)[A]).leftDerivedFunctor K).natTrans.app
      (Etale.dualizingComplex A a)) := hK
  have : IsIso ((ihomComparison (ν^*(X)[A]).leftDerivedFunctor
      ((ihom K).obj (Etale.dualizingComplex A a))).natTrans.app (Etale.dualizingComplex A a)) :=
    hDK
  exact MonoidalClosed.isIso_map_toIhomIhom_iff_of_isIso_comp _ _ K e

end General

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {k : Type u} [Field k] {p : ℕ}
  [Fact p.Prime] [Algebra (ZMod p) k] [IsAlgClosure (ZMod p) k] {Y : Scheme.{u}}
  (aY : Y ⟶ Spec (.of k)) [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]
  [HasCompactification aY] [HasInvertibleExponent Λ (Spec (.of k))]

include p

/-- Blueprint `thm-fix-general-biduality`: Finite-stage Verdier biduality, on the pro-étale
site: preservation.

For `Y` separated of finite type over `k = 𝔽̄_p` and a finite ring `Λ` whose exponent is
invertible on `Y`, the pro-étale Verdier dual `𝔻_Y = RHom(-, ω_Y)` carries `Dctf(Y_proét, Λ)`
into itself. Every object of `Dctf(Y_proét, Λ)` is the pullback `ν^* K₀` of an étale
`K₀ ∈ Dctf(Y_ét, Λ)`, and `𝔻_Y ν^* K₀ ≅ ν^* 𝔻_Y K₀`
(`lem-weil-finite-duality-site-comparison`), where `𝔻_Y K₀ ∈ Dctf(Y_ét, Λ)`
(`AlgebraicGeometry.Etale.constructibleFiniteTor_verdierDual`). -/
theorem constructibleFiniteTor_verdierDual
    {K : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y K) :
    DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y
      ((verdierDual (ModuleCat.{u + 1} Λ) aY).obj (op K)) :=
  by
  have : HasInvertibleExponent Λ Y := .of_hom aY
  obtain ⟨⟨K₀, hK₀, ⟨e⟩⟩, a, b, hab⟩ := hK
  have hK₀t : Etale.DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) Y a b K₀ :=
    DerivedCategory.torAmplitudeIn_of_mapDerivedCategory Λ
      ((DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) Y a b).prop_of_iso e.symm hab)
  have hD := Etale.constructibleFiniteTor_verdierDual Λ aY ⟨hK₀, a, b, hK₀t⟩
  obtain ⟨⟨e₁⟩, -⟩ :=
    (DerivedCategory.nonempty_iso_mapDerivedCategory_derivedHom_of_isSeparated Λ (p := p) aY).2.2
      ⟨hK₀, a, b, hK₀t⟩
  exact (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y).prop_of_iso
    (e₁ ≪≫ (verdierDual (ModuleCat.{u + 1} Λ) aY).mapIso e.symm.op)
    (DerivedCategory.constructibleFiniteTor_mapDerivedCategory Λ hD)

/-- Blueprint `thm-fix-general-biduality`: Finite-stage Verdier biduality, on the pro-étale
site.

For `Y` separated of finite type over `k = 𝔽̄_p` and a finite ring `Λ` whose exponent is
invertible on `Y`, the double-dual morphism `δ_K : K ⟶ 𝔻_Y 𝔻_Y K` of the pro-étale site is an
isomorphism for every `K ∈ Dctf(Y_proét, Λ)`: the evaluation-compatible site comparison
(`lem-weil-finite-duality-site-comparison`) transports étale biduality
(`AlgebraicGeometry.Etale.isIso_verdierDualDoubleDual_app`). -/
theorem isIso_verdierDualDoubleDual_app
    {K : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y K) :
    IsIso ((verdierDualDoubleDual (ModuleCat.{u + 1} Λ) aY).app K) := by
  have : HasInvertibleExponent Λ Y := .of_hom aY
  have : IsAlgClosed k := IsAlgClosure.isAlgClosed (ZMod p)
  -- `K ≅ ν^* K₀` with `K₀ ∈ Dctf(Y_ét, Λ)`
  obtain ⟨⟨K₀, hK₀, ⟨e⟩⟩, a, b, hab⟩ := hK
  have hK₀' : Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y K₀ :=
    ⟨hK₀, a, b, DerivedCategory.torAmplitudeIn_of_mapDerivedCategory Λ
      ((DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) Y a b).prop_of_iso e.symm hab)⟩
  -- the étale dualizing complex is bounded constructible
  have hunit : Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ)
      (Spec (.of k)) (𝟙_ _) :=
    ⟨(Etale.DerivedCategory.boundedConstructible _ _).prop_of_iso
      (_root_.DerivedCategory.singleFunctorObjUnitIso _)
      (Etale.DerivedCategory.boundedConstructible_singleFunctor_obj _ 0), 0, 0,
      (Etale.DerivedCategory.torAmplitudeIn _ _ 0 0).prop_of_iso
        (_root_.DerivedCategory.singleFunctorObjUnitIso _)
        (_root_.DerivedCategory.torAmplitudeIn_singleFunctor_obj_of_flat
          (ObjectProperty.flat_of_isDualizable isDualizable_unit))⟩
  have hω := (Etale.constructibleFiniteTor_dualizingComplex Λ (𝟙 _) aY hunit).1
  -- the comparison `ν^* ω_Y ≅ ω_{Y, proét}`
  obtain ⟨⟨eω⟩, -⟩ :=
    (DerivedCategory.nonempty_iso_mapDerivedCategory_derivedHom_of_isSeparated Λ (p := p) aY).2
  let i := (ν^*(Y)[ModuleCat.{u + 1} Λ]).leftDerivedFunctorIsoMapDerivedCategory
  have : IsIso (Etale.verdierDualDoubleDual (ModuleCat.{u + 1} Λ) aY |>.app K₀) :=
    Etale.isIso_verdierDualDoubleDual_app Λ aY hK₀'
  have hδ := (isIso_leftDerived_map_verdierDualDoubleDual_app_iff _ aY
    ((i.app _).hom ≫ eω.hom) K₀
    (isIso_leftDerivedComparisonUpperStarIhomComparison Λ (p := p) aY hK₀' hω)
    (isIso_leftDerivedComparisonUpperStarIhomComparison Λ (p := p) aY
      (Etale.constructibleFiniteTor_verdierDual Λ aY hK₀') hω)).1 inferInstance
  exact (NatTrans.isIso_app_iff_of_iso _ (i.app K₀ ≪≫ e)).1 hδ

/-- Blueprint `thm-fix-general-biduality`: Finite-stage Verdier biduality, on the pro-étale
site.

For `Y` separated of finite type over `k = 𝔽̄_p` and a finite ring `Λ` whose exponent is
invertible on `Y`, the pro-étale Verdier dual is a contravariant anti-equivalence
`Dctf(Y_proét, Λ)ᵒᵖ ≌ Dctf(Y_proét, Λ)`, with quasi-inverse `𝔻_Y` itself, the unit and counit
being the double-dual isomorphisms
(`AlgebraicGeometry.ProEtale.isIso_verdierDualDoubleDual_app`). -/
noncomputable def verdierDualEquivalence :
    (DerivedCategoryFiniteTor (ModuleCat.{u + 1} Λ) Y)ᵒᵖ ≌
      DerivedCategoryFiniteTor (ModuleCat.{u + 1} Λ) Y :=
  (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y).liftDualEquivalence
    (verdierDual (ModuleCat.{u + 1} Λ) aY)
    (fun _ hK ↦ constructibleFiniteTor_verdierDual Λ (p := p) aY hK)
    (verdierDualDoubleDual (ModuleCat.{u + 1} Λ) aY)
    (fun _ hK ↦ isIso_verdierDualDoubleDual_app Λ (p := p) aY hK)

end AlgebraicGeometry.ProEtale
