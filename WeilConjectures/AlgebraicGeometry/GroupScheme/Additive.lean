/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import WeilConjectures.Mathlib.AlgebraicGeometry.Group.Affine
public import WeilConjectures.RingTheory.HopfAlgebra.Polynomial

/-!
# The additive group scheme and its Frobenius kernel

The additive group `𝔾ₐ` over a commutative ring `k` is the affine group scheme `Spec k[X]` over
`Spec k`, the spectrum of the Hopf algebra `k[X]` in which `X` is primitive
(`Polynomial.instHopfAlgebra`). Its `R`-points are the additive group of `R`. When `k` has prime
characteristic `p`, the Frobenius kernel `α_p` is the closed subgroup scheme of `𝔾ₐ` cut out by
the Hopf ideal `(X^p)`.

## Main definitions

- `AlgebraicGeometry.AdditiveGroup`, notation `𝔾ₐ[k]`: the additive group scheme.
- `AlgebraicGeometry.AdditiveGroup.homMulEquiv`: the `R`-points of `𝔾ₐ` are the additive group
  of `R` (written multiplicatively).
- `AlgebraicGeometry.FrobeniusKernel`: the group scheme `α_p = Spec k[X] ⧸ (X^p)`, with its closed
  immersion `frobeniusKernelι` into `𝔾ₐ`, a closed subgroup scheme.

## Blueprint

- `def-sc-gm-ga`: the additive group `𝐆_a` and its Frobenius kernel `α_p ⊆ 𝐆_a`.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry WithConv Polynomial
open scoped MonObj

namespace AlgebraicGeometry

variable (k : Type u) [CommRing k]

/-- Blueprint `def-sc-gm-ga`: The additive group `𝔾ₐ = Spec k[X]` over a commutative ring `k`.

It is the affine group scheme over `Spec k` of the Hopf algebra `k[X]`
(`Polynomial.instHopfAlgebra`, via `instGrpObjSpecAsOverSpec`), whose comultiplication, counit
and antipode are the algebra homomorphisms with `X ↦ X ⊗ 1 + 1 ⊗ X`, `X ↦ 0` and `X ↦ -X`
(`Polynomial.comul_X`, `Polynomial.counit_X`, `Polynomial.antipode_X`). Its `R`-points are the
additive group of `R` (`AlgebraicGeometry.AdditiveGroup.homMulEquiv`). -/
noncomputable def AdditiveGroup : Over (Spec (.of k)) :=
  (Spec (.of k[X])).asOver (Spec (.of k))

@[inherit_doc] scoped notation "𝔾ₐ[" k "]" => AdditiveGroup k

namespace AdditiveGroup

/-- `𝔾ₐ` is a group object in `Over (Spec k)`, by the Hopf algebra structure of `k[X]`. -/
noncomputable instance : GrpObj 𝔾ₐ[k] :=
  inferInstanceAs (GrpObj ((Spec (.of k[X])).asOver (Spec (.of k))))

instance : IsAffine (𝔾ₐ[k]).left :=
  inferInstanceAs (IsAffine (Spec (.of k[X])))

instance : LocallyOfFiniteType (𝔾ₐ[k]).hom :=
  locallyOfFiniteType_specOverSpec

/-- The `R`-points of the additive group `𝔾ₐ` are the additive group of `R` (written
multiplicatively), as groups: a point corresponds to the image of `X` under the corresponding
algebra homomorphism `k[X] → R`. (blueprint: `def-sc-gm-ga`) -/
noncomputable def homMulEquiv (R : Type u) [CommRing R] [Algebra k R] :
    ((Spec (.of R)).asOver (Spec (.of k)) ⟶ 𝔾ₐ[k]) ≃* Multiplicative R :=
  Spec.mapMulEquiv.symm.trans (Polynomial.algHomMulEquiv k R)

variable {k}

@[simp]
theorem homMulEquiv_mapMulEquiv {R : Type u} [CommRing R] [Algebra k R]
    (ψ : WithConv (k[X] →ₐ[k] R)) :
    homMulEquiv k R (Spec.mapMulEquiv ψ) = Polynomial.algHomMulEquiv k R ψ := by
  change Polynomial.algHomMulEquiv k R (Spec.mapMulEquiv.symm (Spec.mapMulEquiv ψ)) = _
  rw [MulEquiv.symm_apply_apply]

end AdditiveGroup

variable (p : ℕ) [Fact p.Prime] [CharP k p]

/-- Blueprint `def-sc-gm-ga`: The Frobenius kernel `α_p = Spec k[X] ⧸ (X^p)` of `𝔾ₐ`, over a
commutative ring `k` of prime characteristic `p`.

It is the closed subgroup scheme of `𝔾ₐ` cut out by the Hopf ideal `(X^p)`
(`Polynomial.isHopfIdeal_span_X_pow_char`: `X^p` is primitive in characteristic `p`), a group
scheme by Mathlib's quotient Hopf algebra structure. -/
noncomputable def FrobeniusKernel : Over (Spec (.of k)) :=
  (Spec (.of (k[X] ⧸ Ideal.span {(X ^ p : k[X])}))).asOver (Spec (.of k))

namespace FrobeniusKernel

noncomputable instance : GrpObj (FrobeniusKernel k p) :=
  inferInstanceAs
    (GrpObj ((Spec (.of (k[X] ⧸ Ideal.span {(X ^ p : k[X])}))).asOver (Spec (.of k))))

instance : IsAffine (FrobeniusKernel k p).left :=
  inferInstanceAs (IsAffine (Spec (.of (k[X] ⧸ Ideal.span {(X ^ p : k[X])}))))

end FrobeniusKernel

/-- Blueprint `def-sc-gm-ga`: The closed immersion `α_p ⟶ 𝔾ₐ`, the spectrum of the quotient map
`k[X] → k[X] ⧸ (X^p)`. It is a homomorphism of group schemes. -/
noncomputable def frobeniusKernelι : FrobeniusKernel k p ⟶ 𝔾ₐ[k] :=
  (Spec.map (CommRingCat.ofHom
    (Ideal.Quotient.mkₐ k (Ideal.span {(X ^ p : k[X])})).toRingHom)).asOver (Spec (.of k))

instance : IsMonHom (frobeniusKernelι k p) :=
  inferInstanceAs (IsMonHom ((bialgSpec (.of k)).map
    (CommBialgCat.ofHom (Bialgebra.Quotient.mkBialgHom (R := k)
      (Ideal.span {(X ^ p : k[X])}))).op).hom)

instance : IsClosedImmersion (frobeniusKernelι k p).left :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

instance : Mono (frobeniusKernelι k p) :=
  Over.mono_of_mono_left _

/-- Over a field of characteristic `p`, `α_p ⟶ 𝔾ₐ` is a closed subgroup scheme.
(blueprint: `def-sc-gm-ga`) -/
instance {K : Type u} [Field K] [CharP K p] : IsClosedSubgroupScheme (frobeniusKernelι K p) where
  toIsSubgroupScheme := .of_mono _
  isClosedImmersion := inferInstance

end AlgebraicGeometry
