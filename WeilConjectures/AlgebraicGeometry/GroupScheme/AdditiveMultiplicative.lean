/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.HopfAlgebra.GroupLike
public import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
public import WeilConjectures.Mathlib.AlgebraicGeometry.Group.Affine
public import WeilConjectures.Mathlib.RingTheory.Bialgebra.SymmetricAlgebra
public import WeilConjectures.Mathlib.RingTheory.HopfAlgebra.Quotient

/-!
# The multiplicative and additive groups and their finite subgroups

Let `k` be a field. This file defines the affine group schemes over `k`

* the *multiplicative group* `𝔾ₘ = Spec k[t, t⁻¹]`, with `m^*(t) = t ⊗ t`, `ε(t) = 1` and
  `i^*(t) = t⁻¹`;
* the *additive group* `𝔾ₐ = Spec k[y]`, with `m^*(y) = y ⊗ 1 + 1 ⊗ y`, `ε(y) = 0` and
  `i^*(y) = -y`;
* the group scheme `μ_n = Spec k[t]/(tⁿ - 1) ⊆ 𝔾ₘ` of `n`-th roots of unity;
* the Frobenius kernel `α_p = Spec k[y]/(yᵖ) ⊆ 𝔾ₐ` when `char k = p > 0`,

each as the spectrum of a commutative Hopf algebra, hence a group object in `Over (Spec k)`
(`instGrpObjSpecAsOverSpec`). The coordinate ring of `𝔾ₘ` is the Laurent polynomial ring, with
Mathlib's group-algebra Hopf structure; that of `𝔾ₐ` is the symmetric algebra `Sym_k(k) = k[y]`
on one primitive generator. The two finite subgroups are cut out by Hopf ideals, so their closed
immersions are homomorphisms.

## Main definitions

- `AlgebraicGeometry.MultiplicativeGroup`, `AlgebraicGeometry.AdditiveGroup`
- `AlgebraicGeometry.RootsOfUnity`, `AlgebraicGeometry.RootsOfUnity.ι`
- `AlgebraicGeometry.FrobeniusKernel`, `AlgebraicGeometry.FrobeniusKernel.ι`

## Blueprint

- `def-sc-gm-ga`: the multiplicative group, the additive group, and their finite subgroups.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry LaurentPolynomial TensorProduct
open scoped MonObj

namespace AlgebraicGeometry

variable (k : Type u) [Field k]

/-! ### The multiplicative group -/

/-- Blueprint `def-sc-gm-ga`: the *multiplicative group* `𝔾ₘ = Spec k[t, t⁻¹]` over `k`, the
spectrum of the Laurent polynomial ring with its group-algebra Hopf structure:
`m^*(t) = t ⊗ t`, `ε(t) = 1`, `i^*(t) = t⁻¹`. -/
noncomputable def MultiplicativeGroup : Over (Spec (.of k)) :=
  (Spec (.of k[T;T⁻¹])).asOver (Spec (.of k))

namespace MultiplicativeGroup

/-- `𝔾ₘ` is a group object in `Over (Spec k)`. -/
noncomputable instance : GrpObj (MultiplicativeGroup k) :=
  inferInstanceAs (GrpObj ((Spec (.of k[T;T⁻¹])).asOver (Spec (.of k))))

instance : IsAffine (MultiplicativeGroup k).left :=
  inferInstanceAs (IsAffine (Spec (.of k[T;T⁻¹])))

variable {k}

/-- The comultiplication of `k[t, t⁻¹]`: `m^*(tⁿ) = tⁿ ⊗ tⁿ`. -/
@[simp]
theorem comul_T (n : ℤ) : Coalgebra.comul (R := k) (T n : k[T;T⁻¹]) = T n ⊗ₜ T n := by
  rw [← single_eq_C_mul_T, map_one, one_mul]
  exact AddMonoidAlgebra.comul_single _ _

/-- The counit of `k[t, t⁻¹]`: `ε(tⁿ) = 1`. -/
@[simp]
theorem counit_T (n : ℤ) : Coalgebra.counit (R := k) (T n : k[T;T⁻¹]) = 1 := by
  rw [← single_eq_C_mul_T, map_one, one_mul]
  exact AddMonoidAlgebra.counit_single _ _

/-- The antipode of `k[t, t⁻¹]`: `i^*(tⁿ) = t⁻ⁿ`. -/
@[simp]
theorem antipode_T (n : ℤ) : HopfAlgebra.antipode k (T n : k[T;T⁻¹]) = T (-n) := by
  rw [← single_eq_C_mul_T, map_one, one_mul, ← single_eq_C_mul_T, map_one, one_mul]
  simpa using AddMonoidAlgebra.antipode_single (R := k) (A := k) n (1 : k)

theorem isGroupLikeElem_T (n : ℤ) : IsGroupLikeElem k (T n : k[T;T⁻¹]) where
  counit_eq_one := counit_T n
  comul_eq_tmul_self := comul_T n

end MultiplicativeGroup

/-! ### The additive group -/

/-- Blueprint `def-sc-gm-ga`: the *additive group* `𝔾ₐ = Spec k[y]` over `k`, the spectrum of the
polynomial ring in one primitive variable `y`, realised as the symmetric algebra `Sym_k(k)`:
`m^*(y) = y ⊗ 1 + 1 ⊗ y`, `ε(y) = 0`, `i^*(y) = -y`. -/
noncomputable def AdditiveGroup : Over (Spec (.of k)) :=
  (Spec (.of (SymmetricAlgebra k k))).asOver (Spec (.of k))

namespace AdditiveGroup

/-- `𝔾ₐ` is a group object in `Over (Spec k)`. -/
noncomputable instance : GrpObj (AdditiveGroup k) :=
  inferInstanceAs (GrpObj ((Spec (.of (SymmetricAlgebra k k))).asOver (Spec (.of k))))

instance : IsAffine (AdditiveGroup k).left :=
  inferInstanceAs (IsAffine (Spec (.of (SymmetricAlgebra k k))))

/-- The coordinate `y` of `𝔾ₐ`. -/
noncomputable abbrev coord : SymmetricAlgebra k k :=
  SymmetricAlgebra.ι k k 1

/-- The comultiplication of `k[y]`: `m^*(y) = y ⊗ 1 + 1 ⊗ y`. -/
theorem comul_coord : Coalgebra.comul (R := k) (coord k) = coord k ⊗ₜ 1 + 1 ⊗ₜ coord k :=
  SymmetricAlgebra.comul_ι k k 1

/-- The counit of `k[y]`: `ε(y) = 0`. -/
theorem counit_coord : Coalgebra.counit (R := k) (coord k) = 0 :=
  SymmetricAlgebra.counit_ι k k 1

/-- The antipode of `k[y]`: `i^*(y) = -y`. -/
theorem antipode_coord : HopfAlgebra.antipode k (coord k) = -coord k :=
  SymmetricAlgebra.antipode_ι k k 1

end AdditiveGroup

/-! ### The roots of unity -/

/-- The Hopf ideal `(tⁿ - 1)` of `k[t, t⁻¹]` cutting out `μ_n`. -/
noncomputable def rootsOfUnityIdeal (n : ℕ) : Ideal k[T;T⁻¹] :=
  Ideal.span {T n - 1}

instance (n : ℕ) : (rootsOfUnityIdeal k n).IsHopfIdeal k :=
  Ideal.IsHopfIdeal.span_singleton_sub_one (MultiplicativeGroup.isGroupLikeElem_T n)

/-- Blueprint `def-sc-gm-ga`: the group scheme `μ_n = Spec k[t]/(tⁿ - 1)` of `n`-th roots of
unity, the closed subgroup scheme of `𝔾ₘ` cut out by the Hopf ideal `(tⁿ - 1)` of
`k[t, t⁻¹]`. (As `t` is a unit modulo `tⁿ - 1` for `n ≥ 1`, the quotient is `k[t]/(tⁿ - 1)`.) -/
noncomputable def RootsOfUnity (n : ℕ) : Over (Spec (.of k)) :=
  (Spec (.of (k[T;T⁻¹] ⧸ rootsOfUnityIdeal k n))).asOver (Spec (.of k))

namespace RootsOfUnity

variable (n : ℕ)

/-- `μ_n` is a group object in `Over (Spec k)`. -/
noncomputable instance : GrpObj (RootsOfUnity k n) :=
  inferInstanceAs (GrpObj ((Spec (.of (k[T;T⁻¹] ⧸ rootsOfUnityIdeal k n))).asOver (Spec (.of k))))

/-- The closed immersion `μ_n ⟶ 𝔾ₘ`, induced by the surjection `k[t, t⁻¹] → k[t]/(tⁿ - 1)`. -/
noncomputable def ι : RootsOfUnity k n ⟶ MultiplicativeGroup k :=
  (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mkₐ k (rootsOfUnityIdeal k n)).toRingHom)).asOver
    (Spec (.of k))

/-- The closed immersion `μ_n ⟶ 𝔾ₘ` is a homomorphism of group schemes. -/
instance : IsMonHom (ι k n) :=
  inferInstanceAs (IsMonHom ((bialgSpec (.of k)).map
    (CommBialgCat.ofHom (Bialgebra.Quotient.mkBialgHom (R := k) (rootsOfUnityIdeal k n))).op).hom)

instance : IsClosedImmersion (ι k n).left :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

end RootsOfUnity

/-! ### The Frobenius kernel of the additive group -/

/-- The Hopf ideal `(yᵖ)` of `k[y]` cutting out `α_p`, for `k` of characteristic `p`. -/
noncomputable def frobeniusKernelIdeal (p : ℕ) : Ideal (SymmetricAlgebra k k) :=
  Ideal.span {AdditiveGroup.coord k ^ p}

/-- In characteristic `p`, the element `yᵖ` of `k[y]` is primitive, so `(yᵖ)` is a Hopf ideal. -/
instance (p : ℕ) [hp : Fact p.Prime] [CharP k p] : (frobeniusKernelIdeal k p).IsHopfIdeal k := by
  -- a bialgebra over a field has the same characteristic, its counit being a retraction
  have hchar (A : Type u) [CommRing A] [Bialgebra k A] : CharP A p :=
    have : Nontrivial A := (Bialgebra.counitAlgHom k A).toRingHom.domain_nontrivial
    charP_of_injective_algebraMap (algebraMap k A).injective p
  have := hchar (SymmetricAlgebra k k)
  have := hchar (SymmetricAlgebra k k ⊗[k] SymmetricAlgebra k k)
  refine Ideal.IsHopfIdeal.span_singleton_of_comul_eq ?_ ?_ ?_
  · rw [← Bialgebra.comulAlgHom_apply, map_pow, Bialgebra.comulAlgHom_apply,
      AdditiveGroup.comul_coord, add_pow_char, Algebra.TensorProduct.tmul_pow,
      Algebra.TensorProduct.tmul_pow, one_pow]
  · rw [← Bialgebra.counitAlgHom_apply, map_pow, Bialgebra.counitAlgHom_apply,
      AdditiveGroup.counit_coord, zero_pow hp.out.ne_zero]
  · rw [← HopfAlgebra.toLinearMap_antipodeAlgHom, AlgHom.toLinearMap_apply, map_pow,
      ← AlgHom.toLinearMap_apply, HopfAlgebra.toLinearMap_antipodeAlgHom,
      AdditiveGroup.antipode_coord, neg_pow, neg_one_pow_char, neg_one_mul]

/-- Blueprint `def-sc-gm-ga`: the *Frobenius kernel* `α_p = Spec k[y]/(yᵖ)` of `𝔾ₐ` over a field
`k` of characteristic `p > 0`, the closed subgroup scheme of `𝔾ₐ` cut out by the Hopf ideal
`(yᵖ)`. -/
noncomputable def FrobeniusKernel (p : ℕ) [Fact p.Prime] [CharP k p] : Over (Spec (.of k)) :=
  (Spec (.of (SymmetricAlgebra k k ⧸ frobeniusKernelIdeal k p))).asOver (Spec (.of k))

namespace FrobeniusKernel

variable (p : ℕ) [Fact p.Prime] [CharP k p]

/-- `α_p` is a group object in `Over (Spec k)`. -/
noncomputable instance : GrpObj (FrobeniusKernel k p) :=
  inferInstanceAs (GrpObj
    ((Spec (.of (SymmetricAlgebra k k ⧸ frobeniusKernelIdeal k p))).asOver (Spec (.of k))))

/-- The closed immersion `α_p ⟶ 𝔾ₐ`, induced by the surjection `k[y] → k[y]/(yᵖ)`. -/
noncomputable def ι : FrobeniusKernel k p ⟶ AdditiveGroup k :=
  (Spec.map (CommRingCat.ofHom
    (Ideal.Quotient.mkₐ k (frobeniusKernelIdeal k p)).toRingHom)).asOver (Spec (.of k))

/-- The closed immersion `α_p ⟶ 𝔾ₐ` is a homomorphism of group schemes. -/
instance : IsMonHom (ι k p) :=
  inferInstanceAs (IsMonHom ((bialgSpec (.of k)).map
    (CommBialgCat.ofHom
      (Bialgebra.Quotient.mkBialgHom (R := k) (frobeniusKernelIdeal k p))).op).hom)

instance : IsClosedImmersion (ι k p).left :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

end FrobeniusKernel

end AlgebraicGeometry
