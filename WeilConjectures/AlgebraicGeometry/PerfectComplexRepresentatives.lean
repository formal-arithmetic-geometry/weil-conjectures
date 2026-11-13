/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import Mathlib.Topology.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.PerfectAffineClassesSmall
import WeilConjectures.AlgebraicGeometry.PerfectComplexClassesSmallGluing
import WeilConjectures.AlgebraicGeometry.QuasiCompactOpenInduction

/-! # A set of representatives for perfect complexes

## References

* Stacks Project, Derived Categories of Schemes, Theorem (Bondal--Van den Bergh),
  set-of-representatives input.
-/

@[expose] public section

universe u w

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- On a quasi-compact quasi-separated scheme, the perfect objects of `D_QCoh(𝒪_X)`
have a set of representatives up to isomorphism. -/
theorem exists_perfectComplex_representatives (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))] :
    ∃ (I : Type u) (P : I → schemeDerivedQCohCategory X),
      (∀ i : I, IsPerfect X (P i).obj) ∧
      ∀ E : schemeDerivedQCohCategory X, IsPerfect X E.obj →
        ∃ i : I, Nonempty (E ≅ P i) := by
  classical
  have h_affine : ∀ U : X.Opens, IsAffineOpen U →
      PerfectComplexClassesSmallOnOpen.{u, w} X U := by
    intro U hU Y f hf hr _ _
    have : IsAffine U.toScheme := hU
    have he : Set.range f = Set.range U.ι := by
      change (f.opensRange : Set X) = Set.range U.ι
      rw [hr]
      exact U.range_ι.symm
    have : IsAffine Y := IsAffine.of_isIso (IsOpenImmersion.isoOfRangeEq f U.ι he).hom
    exact small_perfectComplex_classes_of_isAffine Y
  have htop := quasiCompactOpen_induction X
    (PerfectComplexClassesSmallOnOpen.{u, w} X) h_affine
    (fun U V hU hV pU pV pUV ↦
      perfectComplex_classesSmallOnOpen_union X U V hU hV pU pV pUV)
    ⊤ (by simpa using (isCompact_univ : IsCompact (Set.univ : Set X)))
  let Q : ObjectProperty (schemeDerivedQCohCategory X) := fun E ↦ IsPerfect X E.obj
  have : Small.{u} (Skeleton Q.FullSubcategory) :=
    htop X (𝟙 X) (Scheme.Hom.opensRange_of_isIso (𝟙 X))
  let e := equivShrink.{u} (Skeleton Q.FullSubcategory)
  let R : Shrink.{u} (Skeleton Q.FullSubcategory) → Q.FullSubcategory :=
    fun i ↦ (fromSkeleton Q.FullSubcategory).obj (e.symm i)
  refine ⟨Shrink.{u} (Skeleton Q.FullSubcategory), fun i ↦ (R i).obj,
    fun i ↦ (R i).property, ?_⟩
  intro E hE
  let A : Q.FullSubcategory := ⟨E, hE⟩
  refine ⟨e (toSkeleton A), ?_⟩
  have hR : R (e (toSkeleton A)) = (fromSkeleton Q.FullSubcategory).obj (toSkeleton A) := by
    dsimp [R]
    rw [e.symm_apply_apply]
  change Nonempty (E ≅ (R (e (toSkeleton A))).obj)
  rw [hR]
  exact ⟨Q.ι.mapIso (fromSkeletonToSkeletonIso A).symm⟩

end AlgebraicGeometry.Scheme
