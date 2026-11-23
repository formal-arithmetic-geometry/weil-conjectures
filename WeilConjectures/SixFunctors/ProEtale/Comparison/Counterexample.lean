/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.Topology.Compactification.StoneCech
public import WeilConjectures.Mathlib.Topology.ExtremallyDisconnected
public import WeilConjectures.Mathlib.Topology.LocallyConstant.Algebra
public import WeilConjectures.RingTheory.ProEtale.IndWeaklyEtale
public import WeilConjectures.RingTheory.ProEtale.PullbackProfinite
public import WeilConjectures.RingTheory.ProEtale.WeaklyEtaleIndEtale
public import WeilConjectures.SixFunctors.ProEtale.Comparison

/-!
# Pro-étale objects from locally constant functions on profinite sets

For a field `K` and a profinite set `T`, the affine scheme `Spec C_lc(T, K)` of locally constant
`K`-valued functions on `T` is an object of `(Spec K)_proét`: `C_lc(T, K)` is the filtered
colimit of the finite products `K^{T_i}` over the finite quotients `T_i` of `T`. For an infinite
discrete set `I`, the object `Spec C_lc(βI × βI, K)` is a cofiltered limit of zero-dimensional
finite-type `K`-schemes, but is itself not locally of finite type over `K`.

## Main definitions

- `AlgebraicGeometry.ProEtale.locallyConstantProEt`: `Spec C_lc(T, K)` as an object of
  `(Spec K)_proét`, for a profinite `T`.

## Main statements

- `AlgebraicGeometry.ProEtale.not_locallyOfFiniteType_locallyConstantProEt`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

namespace ProEtale

section LocallyConstant

variable (K : Type u) [Field K] (T : Type u) [TopologicalSpace T] [CompactSpace T] [T2Space T]
  [TotallyDisconnectedSpace T]

instance weaklyEtale_spec_map_algebraMap_locallyConstant :
    WeaklyEtale (Spec.map (CommRingCat.ofHom (algebraMap K (LocallyConstant T K)))) := by
  rw [HasRingHomProperty.Spec_iff (P := @WeaklyEtale)]
  exact RingHom.weaklyEtale_algebraMap_iff.2 inferInstance

/-- For a profinite space `T`, the affine scheme `Spec C_lc(T, K)` of locally constant `K`-valued
functions on `T`, as an object of the small pro-étale site of `Spec K`. -/
noncomputable def locallyConstantProEt : (Spec (.of K)).ProEt :=
  Scheme.ProEt.mk (Spec.map (CommRingCat.ofHom (algebraMap K (LocallyConstant T K))))

end LocallyConstant

variable (K : Type u) [Field K] (I : Type u) [TopologicalSpace I] [DiscreteTopology I]

/-- For an infinite discrete set `I`, the pro-étale object `Spec C_lc(βI × βI, K)` of
`(Spec K)_proét` is not locally of finite type over `K`. -/
theorem not_locallyOfFiniteType_locallyConstantProEt [Infinite I] :
    ¬ LocallyOfFiniteType (locallyConstantProEt K (StoneCech I × StoneCech I)).hom := by
  intro h
  have hft : (algebraMap K (LocallyConstant (StoneCech I × StoneCech I) K)).FiniteType :=
    HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType).1 h
  have : Algebra.FiniteType K (LocallyConstant (StoneCech I × StoneCech I) K) :=
    RingHom.finiteType_algebraMap.1 hft
  have := Algebra.FiniteType.isNoetherianRing K (LocallyConstant (StoneCech I × StoneCech I) K)
  refine not_finite_iff_infinite.2 ‹_› (LocallyConstant.finite_of_isNoetherianRing (R := K)
    (U := fun i ↦ stoneCechClopen i ×ˢ Set.univ)
    (fun i ↦ (isClopen_stoneCechClopen i).prod isClopen_univ)
    (fun i ↦ ⟨(stoneCechUnit i, stoneCechUnit i), stoneCechUnit_mem_stoneCechClopen i, trivial⟩)
    fun i j hij ↦ ?_)
  exact Set.disjoint_prod.2 (.inl (pairwise_disjoint_stoneCechClopen hij))

/-- The pro-étale object `Spec C_lc(βI × βI, K)` of `(Spec K)_proét`, for a discrete set
`I`. -/
noncomputable abbrev stoneCechProdProEt : (Spec (.of K)).ProEt :=
  locallyConstantProEt K (StoneCech I × StoneCech I)

end ProEtale

end AlgebraicGeometry
