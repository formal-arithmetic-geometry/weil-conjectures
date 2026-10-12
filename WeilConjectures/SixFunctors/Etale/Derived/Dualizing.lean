/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Perfect
public import WeilConjectures.AlgebraicGeometry.InvertibleExponent
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriek
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
public import WeilConjectures.CategoryTheory.ObjectProperty.Duality

/-!

# The dualizing complex and Verdier duality on the étale site

Let `A` be a monoidal Grothendieck abelian coefficient category, let `S` be a base scheme and
let `a : X ⟶ S` be a structure morphism admitting a compactification. The *dualizing complex*
of `X` over `S` is `ω_X = Ra^! Λ_S`, the exceptional inverse image of the monoidal unit, and
the *Verdier dual* is `𝔻_X = RHom_X(-, ω_X)`.

## Main definitions

- `AlgebraicGeometry.Etale.dualizingComplex`: `ω_X = Ra^! Λ_S`.
- `AlgebraicGeometry.Etale.verdierDual`: `𝔻_X = RHom_X(-, ω_X)`.
- `AlgebraicGeometry.Etale.verdierDualEvaluation`, `AlgebraicGeometry.Etale.verdierDualDoubleDual`
  (`lem-weil-duality-pairing`): the evaluation pairing `K ⊗ᴸ 𝔻_X K ⟶ ω_X` and the double-dual
  morphism `δ_K : K ⟶ 𝔻_X 𝔻_X K`, its transpose.
- `AlgebraicGeometry.Etale.verdierDualEquivalence` (`sk-prop-sf-biduality-general`): the
  anti-equivalence `𝔻_X : Dctf(X, Λ)ᵒᵖ ≌ Dctf(X, Λ)`.

## Main statements

- `AlgebraicGeometry.Etale.isIso_verdierDualDoubleDual_app` (`sk-prop-sf-biduality-general`):
  general Verdier biduality, `δ_K` is an isomorphism on `Dctf(X, Λ)`; hence
  `AlgebraicGeometry.Etale.nonempty_iso_verdierDual_verdierDual`.
- `AlgebraicGeometry.Etale.constructibleFiniteTor_verdierDual`,
  `AlgebraicGeometry.Etale.torAmplitudeIn_verdierDual` (`lem-weil-verdier-preservation-strata`):
  `𝔻_X` carries `Dctf(X, Λ)` into itself, sending the Tor interval `[a, b]` to
  `[-b - 2d, -a]` when `dim X ≤ d`.

## Implementation notes

`dualizingComplex` and `verdierDual` are defined relatively, for an arbitrary morphism
`a : X ⟶ S` carrying a compactification and an arbitrary coefficient category `A` for which
`Ra_!` is a left adjoint (`AlgebraicGeometry.Etale.isLeftAdjoint_rightDerivedLowerShriek` for
torsion coefficients).

The two theorems are stated in the setting of the blueprint's `sk-prop-sf-biduality-general`
and of `sk-def-sf-setting`: `X` is a separated scheme of finite type over a field `k`, and the
coefficients are a finite ring `Λ` whose exponent is invertible on `k`. Both hypotheses are
needed. Over a singular base biduality fails already for `a = 𝟙`: on a nodal curve, with
`K = i_* Λ` the skyscraper at the node, `i^! Λ` has rank three, so `𝔻_X 𝔻_X K` has rank nine.
For `p`-torsion coefficients in characteristic `p` the Verdier dual of `j_! Λ` is `Rj_* Λ`,
which is not constructible (Artin–Schreier). At a finite stage every object of `Dctf` is
locally perfect, so no quasi-Frobenius hypothesis on `Λ` is needed.

The statements are for torsion coefficients, finitely generated objects of `A` being finite
(`CategoryTheory.ConcreteCategory.FiniteOfIsFinitelyGenerated`, which holds for `ModuleCat Λ`
with `Λ` finite). With coefficients `ℤ` they fail: for the origin `i` of `𝔸¹` in characteristic
zero, `Ri^!ℤ` has `ℚ/ℤ` in degree `3`, so `𝔻(i_*ℤ)` is not constructible, and
`𝔻𝔻(i_*ℤ) = i_*Ẑ` is not `i_*ℤ`.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

variable {X S : Scheme.{u}} (a : X ⟶ S) [HasCompactification a]

namespace Etale

variable [(R(a)_![A]).IsLeftAdjoint]

/-- The dualizing complex `ω_X = Ra^! Λ_S` of a scheme `X` over a base `S`, the exceptional
inverse image along the structure morphism `a : X ⟶ S` of the monoidal unit `Λ_S`. -/
noncomputable def dualizingComplex : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A) :=
  (R(a)^![A]).obj (𝟙_ _)

/-- Blueprint `def-sf-pf`: Coefficient dual, Verdier dual, and the projection formula.

The Verdier dual `𝔻_X = RHom_X(-, ω_X) : D(X_ét)ᵒᵖ ⥤ D(X_ét)`, the internal hom into the
dualizing complex `AlgebraicGeometry.Etale.dualizingComplex`. The other two items of the
blueprint definition are the coefficient dual `K^∨ = RHom(K, Λ_X)`
(`AlgebraicGeometry.Etale.DerivedCategory.coefficientDual`) and the projection transformation
`PF_{f,K,L}` (`AlgebraicGeometry.Etale.projectionMap`). -/
noncomputable def verdierDual :
    (_root_.DerivedCategory (Sheaf X.smallEtaleTopology A))ᵒᵖ ⥤
      _root_.DerivedCategory (Sheaf X.smallEtaleTopology A) :=
  (RHom(X)[A]).flip.obj (dualizingComplex A a)

/-- The braiding of the derived tensor product on `D(X_ét)`: the braiding of the sheaf category,
with the Koszul sign rule on complexes, descended along K-flat resolutions
(`CategoryTheory.DerivedMonoidal.braidedCategory`). It is the symmetry `K ⊗ᴸ M ≅ M ⊗ᴸ K` of
`AlgebraicGeometry.Etale.nonempty_iso_derivedTensor_flip`, and is used as a local instance. -/
noncomputable abbrev derivedBraidedCategory (X : Scheme.{u}) :
    BraidedCategory (_root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :=
  _root_.DerivedCategory.braidedCategory _

attribute [local instance] derivedBraidedCategory

/-- Blueprint `lem-weil-duality-pairing`: The duality pairing and the double-dual morphism.

The evaluation `ev_K : K ⊗ᴸ 𝔻_X K ⟶ ω_X` of the internal hom, a pairing natural in `K`. No
finiteness of `K` or of `𝔻_X K` is needed. -/
noncomputable def verdierDualEvaluation
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    K ⊗ (verdierDual A a).obj (op K) ⟶ dualizingComplex A a :=
  (ihom.ev K).app (dualizingComplex A a)

/-- Blueprint `lem-weil-duality-pairing`: The duality pairing and the double-dual morphism.

The double-dual morphism `δ_K : K ⟶ 𝔻_X 𝔻_X K`, natural in `K`: the transpose of the
evaluation pairing `AlgebraicGeometry.Etale.verdierDualEvaluation` precomposed with the
symmetry `𝔻_X K ⊗ᴸ K ≅ K ⊗ᴸ 𝔻_X K` (`AlgebraicGeometry.Etale.verdierDualDoubleDual_app`).
It is `CategoryTheory.MonoidalClosed.toIhomIhom` for the dualizing complex. -/
noncomputable def verdierDualDoubleDual :
    𝟭 _ ⟶ (verdierDual A a).rightOp ⋙ verdierDual A a :=
  MonoidalClosed.toIhomIhomNatTrans (dualizingComplex A a)

/-- Blueprint `lem-weil-duality-pairing`: the double-dual morphism `δ_K` is the transpose of
the evaluation `ev_K` composed with the symmetry, `CategoryTheory.MonoidalClosed.toIhomIhom`
(see `CategoryTheory.MonoidalClosed.uncurry_toIhomIhom`). -/
lemma verdierDualDoubleDual_app (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (verdierDualDoubleDual A a).app K = MonoidalClosed.toIhomIhom (dualizingComplex A a) K :=
  rfl

/-- **Verdier biduality for dualizable complexes when `ω_X` is invertible.** If the dualizing
complex `ω_X` is invertible — for instance for `X` smooth over a field, where an orientation
gives `ω_X ≅ Λ_X(d)[2d]` — then the double Verdier dual of a dualizable `K` is `K`:
`𝔻_X 𝔻_X K ≅ K`. This is the duality `[[K, ω], ω] ≅ K` of
`CategoryTheory.nonempty_iso_ihom_obj_ihom_obj_of_isInvertible`, the derived category of étale
sheaves being braided (`AlgebraicGeometry.Etale.derivedBraidedCategory`). -/
theorem nonempty_iso_verdierDual_verdierDual_of_isInvertible
    (hω : IsInvertible (dualizingComplex A a))
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)} (hK : IsDualizable K) :
    Nonempty (K ≅ (verdierDual A a).obj (op ((verdierDual A a).obj (op K)))) := by
  obtain ⟨e⟩ := nonempty_iso_ihom_obj_ihom_obj_of_isInvertible hK hω
  exact ⟨e.symm⟩

section Field

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {k : Type u} [Field k]
  [HasInvertibleExponent Λ (Spec (.of k))] {X : Scheme.{u}} (a : X ⟶ Spec (.of k))
  [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a] [HasCompactification a]

/-- Blueprint `lem-weil-verdier-preservation-strata`: Constructible preservation before
biduality (first half; the subsection `sk-prop-sf-rf-shriek-preservation`).

For `X` separated of finite type over a field `k` and a finite coefficient ring `Λ` whose
exponent is invertible on `k`, the Verdier dual `𝔻_X = RHom(-, ω_X)` carries `Dctf(X, Λ)` into
itself. The Tor-amplitude bound of the same blueprint lemma is
`AlgebraicGeometry.Etale.torAmplitudeIn_verdierDual`. This is the preservation half of the
general Verdier biduality `sk-prop-sf-biduality-general`, whose blueprint proof cites it. -/
theorem constructibleFiniteTor_verdierDual
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K) :
    DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X
      ((verdierDual (ModuleCat.{u + 1} Λ) a).obj (op K)) :=
  sorry

/-- Blueprint `sk-prop-sf-biduality-general`: General Verdier biduality.

For `X` separated of finite type over a field `k` and a finite coefficient ring `Λ` whose
exponent is invertible on `k`, the double-dual morphism `δ_K : K ⟶ 𝔻_X 𝔻_X K`
(`AlgebraicGeometry.Etale.verdierDualDoubleDual`) is an isomorphism for every `K` in
`Dctf(X, Λ)`. Over an algebraically closed field this is the finite-stage étale biduality
`thm-weil-etale-geometric-biduality`. -/
theorem isIso_verdierDualDoubleDual_app
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K) :
    IsIso ((verdierDualDoubleDual (ModuleCat.{u + 1} Λ) a).app K) :=
  sorry

/-- Blueprint `sk-prop-sf-biduality-general`: General Verdier biduality.

For `X` separated of finite type over a field `k` and a finite coefficient ring `Λ` whose
exponent is invertible on `k`, the Verdier dual is a contravariant anti-equivalence of
`Dctf(X, Λ)`: the double-dual morphism `K ⟶ 𝔻_X 𝔻_X K` is an isomorphism for every object `K`
of `Dctf(X, Λ)` (`AlgebraicGeometry.Etale.isIso_verdierDualDoubleDual_app`). -/
theorem nonempty_iso_verdierDual_verdierDual
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K) :
    Nonempty (K ≅ (verdierDual (ModuleCat.{u + 1} Λ) a).obj
      (op ((verdierDual (ModuleCat.{u + 1} Λ) a).obj (op K)))) :=
  have := isIso_verdierDualDoubleDual_app Λ a hK
  ⟨asIso ((verdierDualDoubleDual (ModuleCat.{u + 1} Λ) a).app K)⟩

/-- Blueprint `sk-prop-sf-biduality-general`: General Verdier biduality.

For `X` separated of finite type over a field `k` and a finite coefficient ring `Λ` whose
exponent is invertible on `k`, the Verdier dual `𝔻_X = RHom(-, ω_X)` restricts to a
contravariant anti-equivalence `Dctf(X, Λ)ᵒᵖ ≌ Dctf(X, Λ)`, with quasi-inverse `𝔻_X` itself:
`𝔻_X` preserves `Dctf(X, Λ)` (`AlgebraicGeometry.Etale.constructibleFiniteTor_verdierDual`) and
the unit and the counit are the double-dual isomorphisms `δ_K : K ≅ 𝔻_X 𝔻_X K`
(`AlgebraicGeometry.Etale.isIso_verdierDualDoubleDual_app`). -/
noncomputable def verdierDualEquivalence :
    (DerivedCategoryFiniteTor (ModuleCat.{u + 1} Λ) X)ᵒᵖ ≌
      DerivedCategoryFiniteTor (ModuleCat.{u + 1} Λ) X :=
  (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X).liftDualEquivalence
    (verdierDual (ModuleCat.{u + 1} Λ) a) (fun _ hK ↦ constructibleFiniteTor_verdierDual Λ a hK)
    (verdierDualDoubleDual (ModuleCat.{u + 1} Λ) a)
    (fun _ hK ↦ isIso_verdierDualDoubleDual_app Λ a hK)

end Field

section Preservation

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {k : Type u} [Field k]
  [HasInvertibleExponent Λ (Spec (.of k))]

open _root_.AlgebraicGeometry.Etale.DerivedCategory

/-- Blueprint `lem-weil-verdier-preservation-strata`: Verdier duality preserves `Dctf`.

Let `X` be separated of finite type over `k`, `ω_X = Ra_X^! Λ` and `𝔻_X = RHom(-, ω_X)`. Then
`𝔻_X` carries `Dctf(X, Λ)` into itself, and more precisely, if `dim X ≤ d` and `K ∈ Dctf(X, Λ)`
has Tor amplitude in `[a, b]`, then `𝔻_X K` has Tor amplitude in `[-b - 2d, -a]`. The bound is
independent of the exponent of `Λ`. The first half is
`AlgebraicGeometry.Etale.constructibleFiniteTor_verdierDual`. -/
theorem torAmplitudeIn_verdierDual {X : Scheme.{u}} (aX : X ⟶ Spec (.of k)) [IsSeparated aX]
    [LocallyOfFiniteType aX] [QuasiCompact aX] [HasCompactification aX] (d : ℕ)
    (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) (a b : ℤ)
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : boundedConstructible (ModuleCat.{u + 1} Λ) X K)
    (hKt : torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b K) :
    torAmplitudeIn (ModuleCat.{u + 1} Λ) X (-b - 2 * (d : ℤ)) (-a)
      ((verdierDual (ModuleCat.{u + 1} Λ) aX).obj (op K)) :=
  sorry

end Preservation

end Etale

end AlgebraicGeometry
