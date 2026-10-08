/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.Mathlib.RingTheory.KrullDimension.Polynomial
public import WeilConjectures.Mathlib.Topology.KrullDimension

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
(`AlgebraicGeometry.topologicalKrullDim_ne_top`). More generally, a quasi-compact scheme locally
of finite type over a field has finite dimension
(`AlgebraicGeometry.topologicalKrullDim_ne_top_of_compactSpace`).
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

/-- An affine open subscheme of a scheme locally of finite type over a field `K` has finite
dimension: it is the spectrum of a finitely generated `K`-algebra. -/
theorem IsAffineOpen.topologicalKrullDim_ne_top {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] {U : X.Opens} (hU : IsAffineOpen U) :
    topologicalKrullDim (U : Set X) ≠ ⊤ := by
  have hft : RingHom.FiniteType (f.appLE ⊤ U (by simp)).hom :=
    HasRingHomProperty.appLE (P := @LocallyOfFiniteType) f ‹_›
      ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ (by simp)
  let φ : K →+* Γ(X, U) := (f.appLE ⊤ U (by simp)).hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom
  have hφ : φ.FiniteType := hft.comp (RingHom.FiniteType.of_surjective _
    (Scheme.ΓSpecIso (.of K)).symm.commRingCatIsoToRingEquiv.surjective)
  let := φ.toAlgebra
  have : Algebra.FiniteType K Γ(X, U) := hφ
  have := IsHomeomorph.topologicalKrullDim_eq _ hU.isoSpec.hom.homeomorph.isHomeomorph
  change topologicalKrullDim (U : Set X) = topologicalKrullDim (PrimeSpectrum Γ(X, U)) at this
  rw [this, PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact ringKrullDim_ne_top_of_finiteType K _

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
  exact hU.topologicalKrullDim_ne_top f

/-- A quasi-compact scheme locally of finite type over a field has finite dimension: it is
covered by finitely many affine open subschemes, each of finite dimension. -/
theorem topologicalKrullDim_ne_top_of_compactSpace {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] [CompactSpace X] :
    topologicalKrullDim X ≠ ⊤ := by
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun U : X.affineOpens ↦ (U : Set X))
    (fun U ↦ U.1.isOpen) fun x _ ↦ by
      obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
      exact Set.mem_iUnion.mpr ⟨⟨U, hU⟩, hxU⟩
  refine (lt_of_le_of_lt (topologicalKrullDim_le_of_iSup_eq_top (fun U : t ↦ U.1.1) ?_
    (t.sup fun U ↦ topologicalKrullDim U.1) fun U ↦
      Finset.le_sup (f := fun V : X.affineOpens ↦ topologicalKrullDim V.1) U.2) ?_).ne
  · refine eq_top_iff.mpr fun x _ ↦ ?_
    obtain ⟨U, hU, hxU⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨U, hU⟩, hxU⟩
  · exact (Finset.sup_lt_iff bot_lt_top).mpr fun U _ ↦
      (U.2.topologicalKrullDim_ne_top f).lt_top

/-- A scheme which is quasi-compact and locally of finite type over a field has finite
dimension. -/
lemma exists_topologicalKrullDim_le {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ d : ℕ, topologicalKrullDim X ≤ (d : WithBot ℕ∞) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have h := topologicalKrullDim_ne_top_of_compactSpace f
  generalize topologicalKrullDim X = n at h
  induction n using WithBot.recBotCoe with
  | bot => exact ⟨0, bot_le⟩
  | coe n =>
    induction n using ENat.recTopCoe with
    | top => exact absurd rfl h
    | coe n => exact ⟨n, le_rfl⟩

end AlgebraicGeometry
