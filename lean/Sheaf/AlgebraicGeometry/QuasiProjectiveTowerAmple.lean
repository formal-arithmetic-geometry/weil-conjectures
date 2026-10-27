/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Sheaf.AlgebraicGeometry.GabberModificationData
public import WeilConjectures.AlgebraicGeometry.Ample
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.ProjectiveAmpleInvertible
import Sheaf.AlgebraicGeometry.AmpleFinitePrincipalAffine
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Segre
import WeilConjectures.AlgebraicGeometry.ProjectiveSpaceFiniteIndexIso
import WeilConjectures.AlgebraicGeometry.Modules.TensorPowerSectionNonvanishingPullback
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Immersion
import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor

/-! # Absolute ampleness in a quasi-projective tower

Source: Stacks Project, Properties Tags 01PS, 09NV; Morphisms Tag 0892.
(blueprint: lem-per-quasiprojective-tower-ample)
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A quasi-compact source allows the finite-section affine criterion to pull back
along an immersion. The affine loci are chosen inside its coborder range. -/
private theorem ample_pullback_immersion
    {X Y : Scheme.{u}} [CompactSpace Y] (i : Y ⟶ X) [IsImmersion i]
    (L : X.Modules) [L.IsInvertible] (hL : Scheme.Modules.IsAmple X L) :
    @Scheme.Modules.IsAmple Y ((Scheme.Modules.tensorPullback i).obj L)
      ((Scheme.Modules.invertible_pullback_tensor i).1 L).2 := by
  have : ((Scheme.Modules.tensorPullback i).obj L).IsInvertible :=
    ((Scheme.Modules.invertible_pullback_tensor i).1 L).2
  refine ⟨inferInstance, fun y ↦ ?_⟩
  obtain ⟨n, hn, s, U, hEU, hUO, hU, hUs⟩ :=
    Scheme.Modules.exists_affine_section_neighbourhood_of_finite X L hL {i y}
      (Set.finite_singleton _) i.coborderRange (by
        intro x hx
        rcases Set.mem_singleton_iff.mp hx with rfl
        exact subset_coborder ⟨y, rfl⟩)
  obtain ⟨t, ht⟩ :=
    Scheme.Modules.exists_tensorPow_section_nonvanishing_pullback i L n hn s
  refine ⟨n, hn, t, i ⁻¹ᵁ U, hEU (Set.mem_singleton _),
    i.isAffineOpen_preimage_of_le_coborderRange hU hUO, ?_⟩
  intro z
  change i z ∈ U ↔ z ∈ Scheme.Modules.nonvanishingLocus _ t
  rw [ht]
  exact hUs (i z)

/-- Compose the two finite projective-space immersions using the Segre embedding. -/
private theorem quasiProjective_comp
    {V B S : Scheme.{u}} (p : V ⟶ B) (b : B ⟶ S)
    (hp : GabberModification.QuasiProjective p)
    (hb : GabberModification.QuasiProjective b) :
    GabberModification.QuasiProjective (p ≫ b) := by
  classical
  obtain ⟨n, i, hi, hip⟩ := hp
  obtain ⟨m, j, hj, hjb⟩ := hb
  have : IsImmersion i := hi
  have : IsImmersion j := hj
  let α := ULift.{u} (Fin (n + 1))
  let β := ULift.{u} (Fin (m + 1))
  have : IsImmersion (ProjectiveSpace.map α j) :=
    MorphismProperty.of_isPullback (ProjectiveSpace.isPullback_map α j).flip hj
  let e := (ProjectiveSpace.isPullback_map α (ℙ(β; S) ↘ S)).isoPullback
  let k := i ≫ ProjectiveSpace.map α j ≫ e.hom ≫ ProjectiveSpace.segre α β S
  have : IsImmersion k := inferInstance
  have hk : k ≫ ℙ(α × β; S) ↘ S = p ≫ b := by
    dsimp only [k]
    rw [Category.assoc, Category.assoc, Category.assoc, ProjectiveSpace.segre_over,
      ← Category.assoc e.hom, IsPullback.isoPullback_hom_fst,
      ProjectiveSpace.map_over, ProjectiveSpace.map_over_assoc,
      ← Category.assoc, hip, hjb]
  obtain ⟨d, ε, hε, _⟩ := ProjectiveSpace.exists_finite_index_iso (α × β) S
  refine ⟨d, k ≫ ε.hom, inferInstance, ?_⟩
  rw [Category.assoc, hε, hk]

/-- An immersion into finite projective space over an affine base gives absolute ampleness. -/
private theorem exists_ample_of_quasiProjective_affine
    {X S : Scheme.{u}} [IsAffine S] [CompactSpace X]
    (f : X ⟶ S) (hf : GabberModification.QuasiProjective f) :
    ∃ (L : X.Modules) (hL : L.IsInvertible), @Scheme.Modules.IsAmple X L hL := by
  obtain ⟨n, i, hi, hif⟩ := hf
  have : IsImmersion i := hi
  let γ := ULift.{u} (Fin (n + 1))
  let g := ProjectiveSpace.map γ S.isoSpec.hom
  have : IsImmersion g :=
    MorphismProperty.of_isPullback
      (ProjectiveSpace.isPullback_map γ S.isoSpec.hom).flip inferInstance
  have : IsImmersion (i ≫ g) := inferInstance
  let P := ℙ(γ; Spec Γ(S, ⊤))
  obtain ⟨hN, hNamp, _⟩ := projective_closedImmersion_ample_invertible
    Γ(S, ⊤) n P (P ↘ Spec Γ(S, ⊤)) (𝟙 P) (by simp)
  have := hN
  exact ⟨_, _, ample_pullback_immersion (i ≫ g) _ hNamp⟩

/-- A finite-type quasi-projective tower over an affine Noetherian scheme has an
absolute ample invertible module on its top scheme. This assertion involves no group
or quotient.

Source: Stacks Project, Properties Tags 01PS, 09NV; Morphisms Tag 0892.
(blueprint: lem-per-quasiprojective-tower-ample).

Proof:
1. Compose the two finite-space immersions: map P^n_B to P^n_(P^m_S) by base
   change of B→P^m_S, identify it with P^n_S times_S P^m_S, and apply the
   closed Segre embedding. Its finite nonempty coordinate set is reindexed as
   ULift(Fin(d+1)). These maps are immersions and their composite lies over S.
2. Identify S with Spec Γ(S,⊤). Apply projective_closedImmersion_ample_invertible
   to the identity of the resulting finite projective space, obtaining an
   absolutely ample invertible module N on that projective space.
3. For each point of V choose a positive-power section of N whose affine
   nonvanishing open lies inside the coborder range of the immersion, using
   exists_affine_section_neighbourhood_of_finite. Its inverse image is affine
   because the immersion is closed in that coborder range. The pullback tensor
   power and fibre formulas give a section with exactly this inverse image as
   its nonvanishing locus. Thus the pullback module satisfies the ample criterion.
4. The source V is quasi-compact since p is quasi-compact and B is Noetherian.
The empty source and zero base ring require no exception: the ample criterion
has no points to check. The construction involves no group or quotient. -/
theorem exists_ample_of_quasiProjective_tower
    (S B V : Scheme.{u}) [IsAffine S] [IsNoetherian S] [IsNoetherian B]
    (b : B ⟶ S) (hb : GabberModification.QuasiProjective b)
    (p : V ⟶ B) [LocallyOfFiniteType p] [QuasiCompact p]
    (hp : GabberModification.QuasiProjective p) :
    ∃ (L : V.Modules) (hL : L.IsInvertible), @Scheme.Modules.IsAmple V L hL := by
  have : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace p
  exact exists_ample_of_quasiProjective_affine (p ≫ b) (quasiProjective_comp p b hp hb)

end AlgebraicGeometry
