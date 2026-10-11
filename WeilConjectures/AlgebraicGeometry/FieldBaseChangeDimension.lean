/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import WeilConjectures.Mathlib.RingTheory.NoetherNormalization
public import WeilConjectures.Mathlib.Topology.KrullDimension

/-!
# Base change to a field does not increase the dimension

For a finitely generated algebra `A` over a field `k` and a field extension `K` of `k`, the
Krull dimension of `A ⊗[k] K` is at most that of `A`: a Noether normalization
`k[T₁, …, Tₙ] → A` base changes to an integral map `K[T₁, …, Tₙ] → A ⊗[k] K`.
Globalising, the base change of a scheme locally of finite type over a field to a larger field
has no larger dimension, and hence for `f : X ⟶ Y` locally of finite type and a point
`Spec K ⟶ Y` with values in a field, `X ×_Y Spec K` has dimension at most `dim X`.

## Main statements

- `ringKrullDim_le_of_isIntegral`: an integral algebra has dimension at most that of its base.
- `ringKrullDim_tensorProduct_le_of_finiteType`: `dim (A ⊗[k] K) ≤ dim A`.
- `AlgebraicGeometry.topologicalKrullDim_pullback_le_of_field`: base change of a scheme locally
  of finite type over a field `k` to a field extension of `k` does not increase the dimension.
- `AlgebraicGeometry.topologicalKrullDim_pullback_le`: `dim (X ×_Y Spec K) ≤ dim X` for
  `X ⟶ Y` locally of finite type.
-/

@[expose] public section

universe u

open CategoryTheory Limits TensorProduct

/-- An integral algebra `S` over `R` has Krull dimension at most that of `R`: contracting a strict
chain of primes of `S` gives a strict chain of primes of `R` (incomparability). -/
theorem ringKrullDim_le_of_isIntegral (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsIntegral R S] : ringKrullDim S ≤ ringKrullDim R :=
  Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap R S))
    fun _ _ h ↦ Ideal.IsIntegral.comap_lt_comap (R := R) h

/-- Base change of a finitely generated algebra `A` over a field `k` to a field `K` over `k`
does not increase the Krull dimension: a Noether normalization `k[T₁, …, Tₙ] → A` base changes
to an integral map `K[T₁, …, Tₙ] → A ⊗[k] K`. -/
theorem ringKrullDim_tensorProduct_le_of_finiteType (k A K : Type*) [Field k] [CommRing A]
    [Algebra k A] [Algebra.FiniteType k A] [Field K] [Algebra k K] :
    ringKrullDim (A ⊗[k] K) ≤ ringKrullDim A := by
  cases subsingleton_or_nontrivial A with
  | inl hA =>
    have : Subsingleton (A ⊗[k] K) := by
      refine subsingleton_of_zero_eq_one ?_
      rw [Algebra.TensorProduct.one_def, Subsingleton.elim (1 : A) 0, zero_tmul]
    simp [ringKrullDim_eq_bot_of_subsingleton]
  | inr hA =>
    obtain ⟨n, g, hg, hfin⟩ := exists_finite_inj_algHom_of_fg k A
    rw [ringKrullDim_eq_of_finite_inj_algHom_mvPolynomial g hg hfin]
    let φ := Algebra.TensorProduct.map g (AlgHom.id k K)
    algebraize [g.toRingHom, φ.toRingHom]
    have : Module.Finite (MvPolynomial (Fin n) k) A := hfin
    have : Algebra.IsIntegral (MvPolynomial (Fin n) k ⊗[k] K) (A ⊗[k] K) := by
      refine ⟨fun z ↦ z.induction_on isIntegral_zero (fun a x ↦ ?_) fun _ _ ↦ .add⟩
      have ha : IsIntegral (MvPolynomial (Fin n) k ⊗[k] K) (a ⊗ₜ[k] (1 : K)) :=
        (Algebra.IsIntegral.isIntegral (R := MvPolynomial (Fin n) k) a).map_of_comp_eq
          Algebra.TensorProduct.includeLeftRingHom Algebra.TensorProduct.includeLeftRingHom
          (RingHom.ext fun p ↦ by simp [φ, RingHom.algebraMap_toAlgebra])
      have hx : a ⊗ₜ[k] x = a ⊗ₜ[k] 1 * algebraMap _ (A ⊗[k] K)
          (1 ⊗ₜ[k] x : MvPolynomial (Fin n) k ⊗[k] K) := by
        simp [φ, RingHom.algebraMap_toAlgebra]
      rw [hx]
      exact ha.mul isIntegral_algebraMap
    refine (ringKrullDim_le_of_isIntegral (MvPolynomial (Fin n) k ⊗[k] K) _).trans_eq ?_
    rw [ringKrullDim_eq_of_ringEquiv ((Algebra.TensorProduct.comm k _ K).toRingEquiv.trans
      (MvPolynomial.algebraTensorAlgEquiv k K).toRingEquiv),
      MvPolynomial.ringKrullDim_of_isNoetherianRing,
      ringKrullDim_eq_zero_of_isField (Field.toIsField K)]
    simp

namespace AlgebraicGeometry

/-- The affine case of `topologicalKrullDim_pullback_le_of_field`: for `Spec A` of finite type
over a field `k` and a field `K` over `k`, `Spec (A ⊗[k] K)` has dimension at most `dim A`. -/
theorem topologicalKrullDim_pullback_le_of_field_of_spec {k K : Type u} [Field k] [Field K]
    {A : CommRingCat.{u}} (p : Spec A ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    (q : Spec (.of K) ⟶ Spec (.of k)) :
    topologicalKrullDim (pullback p q : Scheme.{u}) ≤ topologicalKrullDim (Spec A) := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective p
  obtain ⟨ψ, rfl⟩ := Spec.map_surjective q
  have hφ : φ.hom.FiniteType := HasRingHomProperty.Spec_iff.mp ‹_›
  algebraize [φ.hom, ψ.hom]
  calc topologicalKrullDim (pullback (Spec.map φ) (Spec.map ψ) : Scheme.{u})
      _ = topologicalKrullDim (Spec (.of (A ⊗[k] K))) :=
        IsHomeomorph.topologicalKrullDim_eq _ (pullbackSpecIso k A K).hom.homeomorph.isHomeomorph
      _ = ringKrullDim (A ⊗[k] K) := PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _
      _ ≤ ringKrullDim A := ringKrullDim_tensorProduct_le_of_finiteType k A K
      _ = topologicalKrullDim (Spec A) := (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _).symm

/-- **Base change to a field extension does not increase dimension.** For a scheme `Z` locally of
finite type over a field `k` and a field `K` over `k`, `dim (Z ×_k K) ≤ dim Z`: on an affine
open `Spec A` of `Z` this is `dim (A ⊗[k] K) ≤ dim A`. -/
theorem topologicalKrullDim_pullback_le_of_field {Z : Scheme.{u}} {k K : Type u} [Field k]
    [Field K] (p : Z ⟶ Spec (.of k)) [LocallyOfFiniteType p] (q : Spec (.of K) ⟶ Spec (.of k)) :
    topologicalKrullDim (pullback p q : Scheme.{u}) ≤ topologicalKrullDim Z := by
  let 𝒰 := Z.affineCover
  let j i := pullback.snd (𝒰.f i) (pullback.fst p q)
  refine topologicalKrullDim_le_of_iSup_eq_top (fun i ↦ (j i).opensRange) ?_ _ fun i ↦ ?_
  · refine eq_top_iff.mpr fun z _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ?_
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (𝒰.iUnion_range.ge (Set.mem_univ (pullback.fst p q z)))
    refine ⟨i, ?_⟩
    rw [Scheme.Hom.mem_opensRange, ← Set.mem_range, Scheme.Pullback.range_snd]
    exact hi
  · calc topologicalKrullDim (j i).opensRange
        _ = topologicalKrullDim (pullback (𝒰.f i) (pullback.fst p q) : Scheme) :=
          (j i).isOpenEmbedding.isEmbedding.topologicalKrullDim_eq_range.symm
        _ = topologicalKrullDim (pullback (𝒰.f i ≫ p) q : Scheme) :=
          IsHomeomorph.topologicalKrullDim_eq _
          (pullbackRightPullbackFstIso p q (𝒰.f i)).hom.homeomorph.isHomeomorph
        _ ≤ topologicalKrullDim (𝒰.X i) := topologicalKrullDim_pullback_le_of_field_of_spec _ q
        _ ≤ topologicalKrullDim Z := (𝒰.f i).isOpenEmbedding.isInducing.topologicalKrullDim_le

/-- **Fibres over field-valued points have dimension at most that of the source.** For
`f : X ⟶ Y` locally of finite type and `s : Spec K ⟶ Y` with `K` a field,
`dim (X ×_Y Spec K) ≤ dim X`: `s` factors through `Spec κ(y)` for `y` its image point, so
`X ×_Y Spec K` is the base change of the fibre `f⁻¹(y)` along `κ(y) → K`.

Used for blueprint `sk-prop-sf-fullcd-etale-origin`: the geometric fibres of base changes of `X`
have dimension at most `dim X`. -/
theorem topologicalKrullDim_pullback_le {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] {K : Type u} [Field K] (s : Spec (.of K) ⟶ Y) :
    topologicalKrullDim (Limits.pullback f s : Scheme.{u}) ≤ topologicalKrullDim X := by
  obtain ⟨⟨y, t⟩, rfl⟩ := (Scheme.SpecToEquivOfField K Y).symm.surjective s
  calc topologicalKrullDim (pullback f (Spec.map t ≫ Y.fromSpecResidueField y) : Scheme.{u})
      _ = topologicalKrullDim (pullback (pullback.snd f (Y.fromSpecResidueField y)) (Spec.map t) :
          Scheme) :=
        (IsHomeomorph.topologicalKrullDim_eq _ (pullbackLeftPullbackSndIso f
          (Y.fromSpecResidueField y) (Spec.map t)).hom.homeomorph.isHomeomorph).symm
      _ ≤ topologicalKrullDim (f.fiber y) :=
        topologicalKrullDim_pullback_le_of_field (k := Y.residueField y) _ _
      _ = topologicalKrullDim (f ⁻¹' {y}) :=
        IsHomeomorph.topologicalKrullDim_eq _ (f.fiberHomeo y).isHomeomorph
      _ ≤ topologicalKrullDim X := topologicalKrullDim_subspace_le _ _

end AlgebraicGeometry
