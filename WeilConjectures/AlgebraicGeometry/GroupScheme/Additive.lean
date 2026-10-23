/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.Group.Affine
public import WeilConjectures.RingTheory.HopfAlgebra.Polynomial

/-!
# The additive group scheme and its Frobenius kernel

The additive group `𝔾ₐ` over a commutative ring `k` is the affine group scheme `Spec k[y]` over
`Spec k`, the spectrum of the Hopf algebra `k[y]` with comultiplication `y ↦ y ⊗ 1 + 1 ⊗ y`,
counit `y ↦ 0` and antipode `y ↦ -y` (`Polynomial.instHopfAlgebra`). Mathlib's
`instGrpObjSpecAsOverSpec` makes it a (commutative) group object in `Over (Spec k)`. Its points
with values in a `k`-algebra `R` are the additive group of `R`.

When `k` is a field of characteristic `p > 0`, the Frobenius kernel `α_p = Spec k[y] ⧸ (y ^ p)` is
a closed subgroup scheme of `𝔾ₐ`: the closed immersion `α_p ⟶ 𝔾ₐ` is the spectrum of the quotient
map, and is a homomorphism of group objects.

## Main definitions

- `AlgebraicGeometry.AdditiveGroup`, notation `𝔾ₐ(k)`: the additive group scheme.
- `AlgebraicGeometry.AdditiveGroup.homMulEquiv`: the `R`-points of `𝔾ₐ(k)` are the additive group
  of `R`.
- `AlgebraicGeometry.AdditiveGroup.FrobeniusKernel`: the group scheme `α_p`, with its closed
  immersion `frobeniusKernelι` into `𝔾ₐ(k)`.

## Blueprint

- `def-sc-gm-ga`: the additive group and its Frobenius kernel `α_p`.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry WithConv Polynomial
open scoped MonObj

namespace AlgebraicGeometry

section CommRing

variable (k : Type u) [CommRing k]

/-- The additive group scheme `𝔾ₐ = Spec k[y]` over a commutative ring `k`, the spectrum of the
Hopf algebra `k[y]` with comultiplication `y ↦ y ⊗ 1 + 1 ⊗ y`, counit `y ↦ 0` and antipode
`y ↦ -y`, as a group object in `Over (Spec k)`. (blueprint: `def-sc-gm-ga`) -/
noncomputable def AdditiveGroup : Over (Spec (.of k)) :=
  (Spec (.of k[X])).asOver (Spec (.of k))

@[inherit_doc] scoped notation "𝔾ₐ(" k ")" => AdditiveGroup k

namespace AdditiveGroup

/-- `𝔾ₐ(k)` is a commutative group object in `Over (Spec k)`, by the cocommutative Hopf algebra
structure of `k[y]` (`instCommGrpObjSpecAsOverSpec`). -/
noncomputable instance : CommGrpObj 𝔾ₐ(k) :=
  inferInstanceAs (CommGrpObj ((Spec (.of k[X])).asOver (Spec (.of k))))

instance : IsAffine (𝔾ₐ(k)).left :=
  inferInstanceAs (IsAffine (Spec (.of k[X])))

/-- The `R`-points of the group scheme `𝔾ₐ(k)` are the additive group of `R`: a point corresponds
to the image of `y`. -/
noncomputable def homMulEquiv (R : Type u) [CommRing R] [Algebra k R] :
    ((Spec (.of R)).asOver (Spec (.of k)) ⟶ 𝔾ₐ(k)) ≃* Multiplicative R :=
  Spec.mapMulEquiv.symm.trans (algHomMulEquiv R)

variable {k}

/-- The point of `𝔾ₐ(k)` corresponding to an algebra homomorphism `ψ : k[y] → R` is `ψ(y)`. -/
@[simp]
theorem homMulEquiv_mapMulEquiv {R : Type u} [CommRing R] [Algebra k R]
    (ψ : WithConv (k[X] →ₐ[k] R)) :
    homMulEquiv k R (Spec.mapMulEquiv ψ) = Multiplicative.ofAdd (ψ.ofConv X) := by
  change algHomMulEquiv R (Spec.mapMulEquiv.symm (Spec.mapMulEquiv ψ)) = _
  rw [MulEquiv.symm_apply_apply, algHomMulEquiv_apply]

end AdditiveGroup

end CommRing

namespace AdditiveGroup

section FrobeniusKernel

variable (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]

/-- The Frobenius kernel `α_p = Spec k[y] ⧸ (y ^ p)` of the additive group over a field `k` of
characteristic `p`: the closed subgroup scheme of `𝔾ₐ(k)` cut out by the Hopf ideal `(y ^ p)`,
a group object in `Over (Spec k)` by the quotient Hopf algebra structure.
(blueprint: `def-sc-gm-ga`) -/
noncomputable def FrobeniusKernel : Over (Spec (.of k)) :=
  (Spec (.of (k[X] ⧸ frobeniusKernelIdeal k p))).asOver (Spec (.of k))

noncomputable instance : GrpObj (FrobeniusKernel k p) :=
  inferInstanceAs (GrpObj ((Spec (.of (k[X] ⧸ frobeniusKernelIdeal k p))).asOver (Spec (.of k))))

instance : IsAffine (FrobeniusKernel k p).left :=
  inferInstanceAs (IsAffine (Spec (.of (k[X] ⧸ frobeniusKernelIdeal k p))))

/-- The closed immersion `α_p ⟶ 𝔾ₐ`, the spectrum of the quotient map `k[y] → k[y] ⧸ (y ^ p)`.
It is a homomorphism of group schemes. (blueprint: `def-sc-gm-ga`) -/
noncomputable def frobeniusKernelι : FrobeniusKernel k p ⟶ 𝔾ₐ(k) :=
  (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mkₐ k (frobeniusKernelIdeal k p)).toRingHom)).asOver
    (Spec (.of k))

instance : IsMonHom (frobeniusKernelι k p) :=
  inferInstanceAs (IsMonHom ((bialgSpec (.of k)).map
    (CommBialgCat.ofHom
      (Bialgebra.Quotient.mkBialgHom (R := k) (frobeniusKernelIdeal k p))).op).hom)

instance : IsClosedImmersion (frobeniusKernelι k p).left :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

instance : Mono (frobeniusKernelι k p) :=
  Over.mono_of_mono_left _

end FrobeniusKernel

end AdditiveGroup

end AlgebraicGeometry
