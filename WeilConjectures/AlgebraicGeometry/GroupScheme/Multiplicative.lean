/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.Group.Affine
public import WeilConjectures.RingTheory.HopfAlgebra.LaurentPolynomial

/-!
# The multiplicative group scheme and the group schemes of roots of unity

The multiplicative group `𝔾ₘ` over a commutative ring `k` is the affine group scheme
`Spec k[t, t⁻¹]` over `Spec k`, the spectrum of the Hopf algebra of Laurent polynomials, with
comultiplication `t ↦ t ⊗ t`, counit `t ↦ 1` and antipode `t ↦ t⁻¹`. Mathlib's
`instGrpObjSpecAsOverSpec` makes it a (commutative) group object in `Over (Spec k)`. Its points
with values in a `k`-algebra `R` are the units of `R`.

For `n : ℕ` the group scheme of `n`-th roots of unity is the closed subgroup scheme
`μ_n = Spec k[t, t⁻¹] ⧸ (t ^ n - 1)` of `𝔾ₘ`; its coordinate ring is `k[t] ⧸ (t ^ n - 1)` (in which
`t` is invertible, with inverse `t ^ (n - 1)`). The closed immersion `μ_n ⟶ 𝔾ₘ` is the spectrum
of the quotient map, and is a homomorphism of group objects.

## Main definitions

- `AlgebraicGeometry.MultiplicativeGroup`, notation `𝔾ₘ(k)`: the multiplicative group scheme.
- `AlgebraicGeometry.MultiplicativeGroup.homMulEquiv`: the `R`-points of `𝔾ₘ(k)` are the units
  of `R`, as groups.
- `AlgebraicGeometry.MultiplicativeGroup.RootsOfUnity`: the group scheme `μ_n`, with its closed
  immersion `rootsOfUnityι` into `𝔾ₘ(k)`.

## Blueprint

- `def-sc-gm-ga`: the multiplicative group and its finite subgroups `μ_n`.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry WithConv LaurentPolynomial
open scoped MonObj

namespace AlgebraicGeometry

variable (k : Type u) [CommRing k]

/-- Blueprint `def-sc-gm-ga`: the multiplicative group scheme `𝔾ₘ = Spec k[t, t⁻¹]` over a
commutative ring `k`, the spectrum of the Hopf algebra of Laurent polynomials (comultiplication
`t ↦ t ⊗ t`, counit `t ↦ 1`, antipode `t ↦ t⁻¹`), as a group object in `Over (Spec k)`. The
additive group is `AlgebraicGeometry.AdditiveGroup`, and the finite subgroup schemes `μ_n` and
`α_p` are `AlgebraicGeometry.MultiplicativeGroup.RootsOfUnity` and
`AlgebraicGeometry.AdditiveGroup.FrobeniusKernel`. -/
noncomputable def MultiplicativeGroup : Over (Spec (.of k)) :=
  (Spec (.of k[T;T⁻¹])).asOver (Spec (.of k))

@[inherit_doc] scoped notation "𝔾ₘ(" k ")" => MultiplicativeGroup k

namespace MultiplicativeGroup

/-- `𝔾ₘ(k)` is a commutative group object in `Over (Spec k)`, by the cocommutative Hopf algebra
structure of `k[t, t⁻¹]` (`instCommGrpObjSpecAsOverSpec`). -/
noncomputable instance : CommGrpObj 𝔾ₘ(k) :=
  inferInstanceAs (CommGrpObj ((Spec (.of k[T;T⁻¹])).asOver (Spec (.of k))))

instance : IsAffine (𝔾ₘ(k)).left :=
  inferInstanceAs (IsAffine (Spec (.of k[T;T⁻¹])))

/-- The `R`-points of the group scheme `𝔾ₘ(k)` are the units of `R`, as groups: a point
corresponds to the image of `t`. -/
noncomputable def homMulEquiv (R : Type u) [CommRing R] [Algebra k R] :
    ((Spec (.of R)).asOver (Spec (.of k)) ⟶ 𝔾ₘ(k)) ≃* Rˣ :=
  Spec.mapMulEquiv.symm.trans (algHomMulEquiv k R)

variable {k}

/-- The point of `𝔾ₘ(k)` corresponding to an algebra homomorphism `ψ : k[t, t⁻¹] → R` is the
unit `ψ(t)`. -/
@[simp]
theorem val_homMulEquiv_mapMulEquiv {R : Type u} [CommRing R] [Algebra k R]
    (ψ : WithConv (k[T;T⁻¹] →ₐ[k] R)) :
    (homMulEquiv k R (Spec.mapMulEquiv ψ) : R) = ψ.ofConv (T 1) := by
  change (algHomMulEquiv k R (Spec.mapMulEquiv.symm (Spec.mapMulEquiv ψ)) : R) = _
  rw [MulEquiv.symm_apply_apply, val_algHomMulEquiv]

section RootsOfUnity

variable (k) (n : ℕ)

/-- The group scheme `μ_n = Spec k[t, t⁻¹] ⧸ (t ^ n - 1) ≅ Spec k[t] ⧸ (t ^ n - 1)` of `n`-th roots
of unity over `k`: the closed subgroup scheme of `𝔾ₘ(k)` cut out by the Hopf ideal
`(t ^ n - 1)`, a group object in `Over (Spec k)` by the quotient Hopf algebra structure.
(blueprint: `def-sc-gm-ga`) -/
noncomputable def RootsOfUnity : Over (Spec (.of k)) :=
  (Spec (.of (k[T;T⁻¹] ⧸ rootsOfUnityIdeal k n))).asOver (Spec (.of k))

noncomputable instance : GrpObj (RootsOfUnity k n) :=
  inferInstanceAs (GrpObj ((Spec (.of (k[T;T⁻¹] ⧸ rootsOfUnityIdeal k n))).asOver (Spec (.of k))))

instance : IsAffine (RootsOfUnity k n).left :=
  inferInstanceAs (IsAffine (Spec (.of (k[T;T⁻¹] ⧸ rootsOfUnityIdeal k n))))

/-- The closed immersion `μ_n ⟶ 𝔾ₘ`, the spectrum of the quotient map
`k[t, t⁻¹] → k[t, t⁻¹] ⧸ (t ^ n - 1)`. It is a homomorphism of group schemes.
(blueprint: `def-sc-gm-ga`) -/
noncomputable def rootsOfUnityι : RootsOfUnity k n ⟶ 𝔾ₘ(k) :=
  (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mkₐ k (rootsOfUnityIdeal k n)).toRingHom)).asOver
    (Spec (.of k))

instance : IsMonHom (rootsOfUnityι k n) :=
  inferInstanceAs (IsMonHom ((bialgSpec (.of k)).map
    (CommBialgCat.ofHom (Bialgebra.Quotient.mkBialgHom (R := k) (rootsOfUnityIdeal k n))).op).hom)

instance : IsClosedImmersion (rootsOfUnityι k n).left :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

instance : Mono (rootsOfUnityι k n) :=
  Over.mono_of_mono_left _

end RootsOfUnity

end MultiplicativeGroup

end AlgebraicGeometry
