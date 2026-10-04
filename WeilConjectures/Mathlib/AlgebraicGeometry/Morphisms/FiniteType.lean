/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.Mathlib.RingTheory.KrullDimension.Polynomial

/-!
# Complements on morphisms locally of finite type

We show that the sections over an affine open of a scheme locally of finite type over `Spec ℤ`
form a finitely generated `ℤ`-algebra
(`AlgebraicGeometry.IsAffineOpen.algebra_finiteType_of_locallyOfFiniteType`), and that for a
morphism of finite type between affine schemes the global sections of the source are generated
by the image of the global sections of the target together with finitely many elements
(`AlgebraicGeometry.exists_finset_closure_range_appTop_union_eq_top`). An integral scheme locally
of finite type over a field has the dimension of any of its nonempty open subschemes
(`AlgebraicGeometry.topologicalKrullDim_opens_eq`), which is finite
(`AlgebraicGeometry.topologicalKrullDim_ne_top`).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The sections over an affine open of a scheme of finite type over `Spec ℤ` form a
finitely generated `ℤ`-algebra. -/
theorem IsAffineOpen.algebra_finiteType_of_locallyOfFiniteType {X : Scheme.{u}}
    {f : X ⟶ Spec (CommRingCat.of (ULift.{u} ℤ))} [LocallyOfFiniteType f]
    {U : X.Opens} (hU : IsAffineOpen U) : Algebra.FiniteType ℤ Γ(X, U) := by
  have hft : RingHom.FiniteType (f.appLE ⊤ U (by simp)).hom :=
    HasRingHomProperty.appLE (P := @LocallyOfFiniteType) f ‹_›
      ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ (by simp)
  rw [← RingHom.finiteType_algebraMap,
    Subsingleton.elim (algebraMap ℤ Γ(X, U))
      (((f.appLE ⊤ U (by simp)).hom.comp
          (Scheme.ΓSpecIso (CommRingCat.of (ULift.{u} ℤ))).inv.hom).comp
        (ULift.ringEquiv (R := ℤ)).symm.toRingHom)]
  refine (hft.comp (RingHom.FiniteType.of_surjective _ ?_)).comp
    (RingHom.FiniteType.of_surjective _ (ULift.ringEquiv (R := ℤ)).symm.surjective)
  exact (Scheme.ΓSpecIso (CommRingCat.of (ULift.{u} ℤ))).symm.commRingCatIsoToRingEquiv.surjective

/-- If `f : X ⟶ Y` is a morphism of finite type between affine schemes, then `Γ(X, ⊤)` is
generated as a ring by the image of `Γ(Y, ⊤)` together with finitely many elements. -/
lemma exists_finset_closure_range_appTop_union_eq_top {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsAffine X] [IsAffine Y] [LocallyOfFiniteType f] :
    ∃ s : Finset Γ(X, ⊤),
      Subring.closure (Set.range ⇑f.appTop.hom ∪ (s : Set Γ(X, ⊤))) = ⊤ := by
  have hft : RingHom.FiniteType f.appTop.hom :=
    HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType).mp inferInstance
  let := f.appTop.hom.toAlgebra
  obtain ⟨s, hs⟩ := hft.out
  refine ⟨s, ?_⟩
  have h2 : (algebraMap Γ(Y, ⊤) Γ(X, ⊤)) = f.appTop.hom := RingHom.algebraMap_toAlgebra _
  have h3 := Algebra.adjoin_eq_ring_closure (R := Γ(Y, ⊤)) (A := Γ(X, ⊤)) (s : Set Γ(X, ⊤))
  rw [hs] at h3
  rw [← h2, ← h3]
  rfl

/-- An integral scheme `X` locally of finite type over a field `K` has the same dimension as each
of its nonempty open subschemes: both are the transcendence degree over `K` of the function
field of `X`. -/
theorem topologicalKrullDim_opens_eq {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] [IsIntegral X] (U : X.Opens) [Nonempty U] :
    topologicalKrullDim (U : Set X) = topologicalKrullDim X :=
  sorry

/-- An integral scheme locally of finite type over a field has finite dimension: the dimension of
any nonempty affine open subscheme, the spectrum of a finitely generated algebra. -/
theorem topologicalKrullDim_ne_top {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] [IsIntegral X] :
    topologicalKrullDim X ≠ ⊤ := by
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  rw [← topologicalKrullDim_opens_eq f U]
  have hft : RingHom.FiniteType (f.appLE ⊤ U (by simp)).hom :=
    HasRingHomProperty.appLE (P := @LocallyOfFiniteType) f ‹_›
      ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ (by simp)
  let φ : K →+* Γ(X, U) := (f.appLE ⊤ U (by simp)).hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom
  have hφ : φ.FiniteType := hft.comp (RingHom.FiniteType.of_surjective _
    (Scheme.ΓSpecIso (.of K)).symm.commRingCatIsoToRingEquiv.surjective)
  letI := φ.toAlgebra
  have : Algebra.FiniteType K Γ(X, U) := hφ
  have := IsHomeomorph.topologicalKrullDim_eq _ hU.isoSpec.hom.homeomorph.isHomeomorph
  change topologicalKrullDim (U : Set X) = topologicalKrullDim (PrimeSpectrum Γ(X, U)) at this
  rw [this]
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact ringKrullDim_ne_top_of_finiteType K _

end AlgebraicGeometry
