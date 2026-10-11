/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import WeilConjectures.Mathlib.AlgebraicGeometry.Group.Affine
public import WeilConjectures.Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra

/-!
# The multiplicative group scheme and the roots of unity

The multiplicative group `𝔾ₘ` over a commutative ring `k` is the affine group scheme
`Spec k[T, T⁻¹]` over `Spec k`, the spectrum of the Hopf algebra of Laurent polynomials, in which
`T` is group-like. Its `R`-points are the units of `R`. For `n : ℕ`, the group scheme `μ_n` of
`n`-th roots of unity is the closed subgroup scheme of `𝔾ₘ` cut out by the Hopf ideal `(T^n - 1)`.

## Main definitions

- `AlgebraicGeometry.MultiplicativeGroup`, notation `𝔾ₘ[k]`: the multiplicative group scheme.
- `AlgebraicGeometry.MultiplicativeGroup.homMulEquiv`: the `R`-points of `𝔾ₘ` are the group `Rˣ`.
- `AlgebraicGeometry.RootsOfUnity`: the group scheme `μ_n = Spec k[T, T⁻¹] ⧸ (T^n - 1)` of
  `n`-th roots of unity, with its closed immersion `rootsOfUnityι` into `𝔾ₘ`, a closed subgroup
  scheme.

## Blueprint

- `def-sc-gm-ga`: the multiplicative group `𝐆_m` and the group scheme `μ_n ⊆ 𝐆_m`.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry WithConv LaurentPolynomial
open scoped MonObj

namespace AlgebraicGeometry

variable (k : Type u) [CommRing k]

/-- Blueprint `def-sc-gm-ga`: The multiplicative group `𝔾ₘ = Spec k[T, T⁻¹]` over a commutative
ring `k`.

It is the affine group scheme over `Spec k` of the Hopf algebra `k[T;T⁻¹]`
(`LaurentPolynomial.instHopfAlgebra`, via `instGrpObjSpecAsOverSpec`), whose comultiplication,
counit and antipode are the algebra homomorphisms with `T ↦ T ⊗ T`, `T ↦ 1` and `T ↦ T⁻¹`
(`LaurentPolynomial.comul_T`, `LaurentPolynomial.counit_T`, `LaurentPolynomial.antipode_T`). Its
`R`-points are the units of `R` (`AlgebraicGeometry.MultiplicativeGroup.homMulEquiv`). -/
noncomputable def MultiplicativeGroup : Over (Spec (.of k)) :=
  (Spec (.of k[T;T⁻¹])).asOver (Spec (.of k))

@[inherit_doc] scoped notation "𝔾ₘ[" k "]" => MultiplicativeGroup k

namespace MultiplicativeGroup

/-- `𝔾ₘ` is a group object in `Over (Spec k)`, by the Hopf algebra structure of `k[T;T⁻¹]`. -/
noncomputable instance : GrpObj 𝔾ₘ[k] :=
  inferInstanceAs (GrpObj ((Spec (.of k[T;T⁻¹])).asOver (Spec (.of k))))

instance : IsAffine (𝔾ₘ[k]).left :=
  inferInstanceAs (IsAffine (Spec (.of k[T;T⁻¹])))

instance : LocallyOfFiniteType (𝔾ₘ[k]).hom :=
  locallyOfFiniteType_specOverSpec

/-- The `R`-points of the multiplicative group `𝔾ₘ` are the units of `R`, as groups: a point
corresponds to the image of `T` under the corresponding algebra homomorphism `k[T;T⁻¹] → R`.
(blueprint: `def-sc-gm-ga`) -/
noncomputable def homMulEquiv (R : Type u) [CommRing R] [Algebra k R] :
    ((Spec (.of R)).asOver (Spec (.of k)) ⟶ 𝔾ₘ[k]) ≃* Rˣ :=
  Spec.mapMulEquiv.symm.trans (algHomMulEquiv k R)

variable {k}

@[simp]
theorem homMulEquiv_mapMulEquiv {R : Type u} [CommRing R] [Algebra k R]
    (ψ : WithConv (k[T;T⁻¹] →ₐ[k] R)) :
    homMulEquiv k R (Spec.mapMulEquiv ψ) = algHomMulEquiv k R ψ := by
  change algHomMulEquiv k R (Spec.mapMulEquiv.symm (Spec.mapMulEquiv ψ)) = _
  rw [MulEquiv.symm_apply_apply]

end MultiplicativeGroup

/-- Blueprint `def-sc-gm-ga`: The group scheme `μ_n` of `n`-th roots of unity.

It is the closed subgroup scheme `Spec (k[T, T⁻¹] ⧸ (T^n - 1))` of `𝔾ₘ` cut out by the Hopf ideal
`(T^n - 1)` (`LaurentPolynomial.isHopfIdeal_span_T_sub_one`), a group scheme by Mathlib's quotient
Hopf algebra structure. Since `T` is invertible modulo `T^n - 1` for `n ≥ 1`, the coordinate ring
`k[T, T⁻¹] ⧸ (T^n - 1)` is the ring `k[t] ⧸ (t^n - 1)` of the blueprint. -/
noncomputable def RootsOfUnity (n : ℕ) : Over (Spec (.of k)) :=
  (Spec (.of (k[T;T⁻¹] ⧸ Ideal.span {(T n - 1 : k[T;T⁻¹])}))).asOver (Spec (.of k))

namespace RootsOfUnity

variable (n : ℕ)

noncomputable instance : GrpObj (RootsOfUnity k n) :=
  inferInstanceAs
    (GrpObj ((Spec (.of (k[T;T⁻¹] ⧸ Ideal.span {(T n - 1 : k[T;T⁻¹])}))).asOver (Spec (.of k))))

instance : IsAffine (RootsOfUnity k n).left :=
  inferInstanceAs (IsAffine (Spec (.of (k[T;T⁻¹] ⧸ Ideal.span {(T n - 1 : k[T;T⁻¹])}))))

end RootsOfUnity

variable (n : ℕ)

/-- Blueprint `def-sc-gm-ga`: The closed immersion `μ_n ⟶ 𝔾ₘ`, the spectrum of the quotient map
`k[T, T⁻¹] → k[T, T⁻¹] ⧸ (T^n - 1)`. It is a homomorphism of group schemes. -/
noncomputable def rootsOfUnityι : RootsOfUnity k n ⟶ 𝔾ₘ[k] :=
  (Spec.map (CommRingCat.ofHom
    (Ideal.Quotient.mkₐ k (Ideal.span {(T n - 1 : k[T;T⁻¹])})).toRingHom)).asOver (Spec (.of k))

instance : IsMonHom (rootsOfUnityι k n) :=
  inferInstanceAs (IsMonHom ((bialgSpec (.of k)).map
    (CommBialgCat.ofHom (Bialgebra.Quotient.mkBialgHom (R := k)
      (Ideal.span {(T n - 1 : k[T;T⁻¹])}))).op).hom)

instance : IsClosedImmersion (rootsOfUnityι k n).left :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

instance : Mono (rootsOfUnityι k n) :=
  Over.mono_of_mono_left _

/-- Over a field, `μ_n ⟶ 𝔾ₘ` is a closed subgroup scheme. (blueprint: `def-sc-gm-ga`) -/
instance {K : Type u} [Field K] : IsClosedSubgroupScheme (rootsOfUnityι K n) where
  toIsSubgroupScheme := .of_mono _
  isClosedImmersion := inferInstance

end AlgebraicGeometry
