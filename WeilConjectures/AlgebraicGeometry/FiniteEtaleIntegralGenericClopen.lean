/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Limits
import WeilConjectures.AlgebraicGeometry.FiniteGenericFiberStratumInteriors

/-! Generic clopen decomposition over an integral affine base. -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

-- The prescribed interface retains an immersion hypothesis unused by this finite-map proof.
set_option linter.unusedVariables false in
/-- The generic part of the finite-etale adapted-stratification argument.
Source: Stacks Project Tag 095H and the blueprint generic-fibre interiors argument
(blueprint: lem-a1-finite-etale-integral-generic-clopen).

Proof: pull the source partition back to the integral affine scheme B. Finiteness makes
its source Noetherian and its fibres finite. Every point above the generic point lies in a
stratum interior. The complement of the union of these interiors is closed, with closed image
under the finite map, and its image misses the generic point. Let U be the complementary
nonempty open. On the restricted source each stratum is open, and its complement is the finite
union of the other open strata. Use these clopen open subschemes as C and their canonical
immersions as j. Their disjoint open cover yields the coproduct colimit, and open-restriction
range equations give the stated inverse-image equality. Empty source pieces are retained. -/
theorem finite_etale_integral_generic_clopen
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [Etale f]
    (S : FiniteLocallyClosedStratification X)
    (B : Scheme.{u}) [IsIntegral B] [IsNoetherian B] [IsAffine B]
    (t : B ⟶ Y) (ht : IsImmersion t) :
    ∃ U : B.Opens, Nonempty U ∧
      ∃ (C : Fin S.n → Scheme.{u})
        (j : ∀ i : Fin S.n, C i ⟶ pullback f (U.ι ≫ t)),
        (∀ i : Fin S.n, IsOpenImmersion (j i) ∧ IsClosedImmersion (j i)) ∧
        Nonempty (IsColimit (Cofan.mk (pullback f (U.ι ≫ t)) j)) ∧
        ∀ i : Fin S.n,
          Set.range (j i) = (pullback.fst f (U.ι ≫ t)) ⁻¹' S.stratum i := by
  classical
  let Z := pullback f t
  let p : Z ⟶ X := pullback.fst f t
  let g : Z ⟶ B := pullback.snd f t
  have : IsFinite g := inferInstanceAs (IsFinite (pullback.snd f t))
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian g
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace g
  have : IsNoetherian Z := ⟨⟩
  have himm (i : Fin S.n) : IsImmersion (S.immersion i) := S.isImmersion i
  let T : Stratification Z := Stratification.ofNoetherianSpace S.n
    (fun i ↦ p ⁻¹' S.stratum i)
    (fun i ↦ (S.isLocallyClosed_stratum i).preimage p.continuous)
    (by rw [← Set.preimage_iUnion, S.iUnion_stratum_eq_univ, Set.preimage_univ])
    (fun i j hij ↦ (S.pairwise_disjoint_stratum hij).preimage p)
    (fun i ↦ pullback (S.immersion i) p)
    (fun i ↦ pullback.snd (S.immersion i) p)
    (fun i ↦ inferInstance)
    (fun i ↦ by rw [Pullback.range_snd, S.range_immersion])
  let W := T.interiorUnion
  let U : B.Opens := ⟨(g '' (W : Set Z)ᶜ)ᶜ,
    (g.isClosedMap _ W.isOpen.isClosed_compl).isOpen_compl⟩
  have hη : genericPoint B ∈ U := by
    rintro ⟨x, hx, hxη⟩
    exact hx (generic_fiber_subset_stratum_interiors B g T x hxη)
  let R := pullback f (U.ι ≫ t)
  let q : R ⟶ Z := pullback.lift (pullback.fst f (U.ι ≫ t))
    (pullback.snd f (U.ι ≫ t) ≫ U.ι) (by simp [Category.assoc, pullback.condition])
  have hqp : q ≫ p = pullback.fst f (U.ι ≫ t) := pullback.lift_fst _ _ _
  have hqg : q ≫ g = pullback.snd f (U.ι ≫ t) ≫ U.ι := pullback.lift_snd _ _ _
  have hqW (x : R) : q x ∈ W := by
    by_contra hx
    have hxU : g (q x) ∈ U := by
      rw [← Scheme.Hom.comp_apply, hqg, Scheme.Hom.comp_apply]
      exact (pullback.snd f (U.ι ≫ t) x).property
    exact hxU ⟨q x, hx, rfl⟩
  let O : Fin S.n → R.Opens := fun i ↦ q ⁻¹ᵁ T.interiorOpens i
  have hcover (x : R) : ∃ i, x ∈ O i := by
    obtain ⟨i, hi⟩ :=
      (TopologicalSpace.Opens.mem_iSup (s := T.interiorOpens)).mp (hqW x)
    exact ⟨i, hi⟩
  have hmem (i : Fin S.n) (x : R) :
      x ∈ O i ↔ pullback.fst f (U.ι ≫ t) x ∈ S.stratum i := by
    have hi (j : Fin S.n) (hx : x ∈ O j) :
        p (q x) ∈ S.stratum j :=
      (interior_subset : interior (T.stratum j) ⊆ T.stratum j) hx
    have hp : p (q x) = pullback.fst f (U.ι ≫ t) x := by
      rw [← Scheme.Hom.comp_apply, hqp]
    constructor
    · intro hx
      exact hp ▸ hi i hx
    · intro hx
      obtain ⟨j, hj⟩ := hcover x
      have hji : j = i := by
        by_contra hne
        exact Set.disjoint_left.mp (S.pairwise_disjoint_stratum hne)
          (hi j hj) (hp.symm ▸ hx)
      exact hji ▸ hj
  have hdisj : Pairwise (fun i j ↦ Disjoint (O i) (O j)) := by
    intro i j hij
    apply TopologicalSpace.Opens.coe_disjoint.mp
    exact (S.pairwise_disjoint_stratum hij).preimage
      (pullback.fst f (U.ι ≫ t)) |>.mono
        (fun x hx ↦ (hmem i x).mp hx) (fun x hx ↦ (hmem j x).mp hx)
  have hclosed (i : Fin S.n) : IsClosed (O i : Set R) := by
    apply isOpen_compl_iff.mp
    have heq : (O i : Set R)ᶜ = ⋃ j, ⋃ (_ : j ≠ i), (O j : Set R) := by
      ext x
      simp only [Set.mem_compl_iff, Set.mem_iUnion]
      constructor
      · intro hx
        obtain ⟨j, hj⟩ := hcover x
        exact ⟨j, fun h ↦ hx (h ▸ hj), hj⟩
      · rintro ⟨j, hji, hj⟩ hi
        exact Set.disjoint_left.mp (TopologicalSpace.Opens.coe_disjoint.mpr
          (hdisj hji)) hj hi
    rw [heq]
    exact isOpen_iUnion fun j ↦ isOpen_iUnion fun _ ↦ (O j).isOpen
  refine ⟨U, ⟨⟨genericPoint B, hη⟩⟩, (fun i ↦ (O i).toScheme),
    (fun i ↦ (O i).ι), ?_, ?_, ?_⟩
  · intro i
    refine ⟨inferInstance, IsClosedImmersion.of_isPreimmersion _ ?_⟩
    simpa only [Scheme.Opens.range_ι] using hclosed i
  · apply nonempty_isColimit_cofanMk_of
    · simp only [Scheme.Opens.opensRange_ι]
      apply eq_top_iff.mpr
      intro x _
      exact TopologicalSpace.Opens.mem_iSup.mpr (hcover x)
    · simpa only [Scheme.Opens.opensRange_ι] using hdisj
  · intro i
    rw [Scheme.Opens.range_ι]
    ext x
    exact hmem i x

end AlgebraicGeometry.Scheme
