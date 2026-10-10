/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.Mathlib.RingTheory.Nullstellensatz

/-!
# Rational points of schemes over an algebraically closed field

A nonempty scheme locally of finite type over an algebraically closed field `K` has a `K`-point
(`AlgebraicGeometry.exists_comp_eq_id_of_locallyOfFiniteType`): by the Nullstellensatz, the
closed points of a nonempty affine open have residue field `K`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A nonempty scheme `V` locally of finite type over an algebraically closed field `K` has a
`K`-point: a section of `f : V ⟶ Spec K`. A nonempty affine open of `V` is the spectrum of a
nonzero finitely generated `K`-algebra, whose maximal ideals are kernels of `K`-algebra maps to
`K` (`exists_algHom_ker_eq_of_isMaximal`). -/
theorem exists_comp_eq_id_of_locallyOfFiniteType {K : Type u} [Field K] [IsAlgClosed K]
    {V : Scheme.{u}} (f : V ⟶ Spec (.of K)) [LocallyOfFiniteType f] (v : V) :
    ∃ σ : Spec (.of K) ⟶ V, σ ≫ f = 𝟙 _ := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hv, -⟩ :=
    V.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ v) isOpen_univ
  let φ := Spec.preimage (hU.isoSpec.inv ≫ Scheme.Opens.ι U ≫ f)
  let := φ.hom.toAlgebra
  have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap K Γ(V, U)))) := by
    change LocallyOfFiniteType (Spec.map φ)
    rw [Spec.map_preimage]
    infer_instance
  have : Algebra.FiniteType K Γ(V, U) := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at this
    exact RingHom.finiteType_algebraMap.1 this
  have : Nontrivial Γ(V, U) := PrimeSpectrum.nontrivial (hU.isoSpec.hom.base ⟨v, hv⟩)
  obtain ⟨M, hM⟩ := Ideal.exists_maximal Γ(V, U)
  obtain ⟨ψ, -⟩ := exists_algHom_ker_eq_of_isMaximal K Γ(V, U) M
  refine ⟨Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ hU.isoSpec.inv ≫ Scheme.Opens.ι U, ?_⟩
  have hφ : hU.isoSpec.inv ≫ Scheme.Opens.ι U ≫ f = Spec.map φ := (Spec.map_preimage _).symm
  rw [Category.assoc, Category.assoc, hφ, ← Spec.map_comp, ← Spec.map_id]
  congr 1
  ext x
  exact ψ.commutes x

end AlgebraicGeometry
