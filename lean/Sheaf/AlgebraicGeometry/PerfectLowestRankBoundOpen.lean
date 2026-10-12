/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y2
-/
module

public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.DerivedFiberBetti
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.Modules.FreeComplex
import Sheaf.Topology.ConstructibleIsRetrocompact
import Sheaf.AlgebraicGeometry.DerivedPullbackComposition
import Sheaf.AlgebraicGeometry.PerfectJumpLoci
import Sheaf.AlgebraicGeometry.PerfectPseudoCoherentLocallyFiniteTor

/-! # The rank-bound open for lowest perfect cohomology

Source: Stacks Project, Tag 0BDL.
(blueprint: lem-sc-perfect-lowest-rank-bound-open).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

set_option autoImplicit false

namespace AlgebraicGeometry.Scheme

private theorem field_rank (R : CommRingCat.{u}) (hR : IsField R)
    (M : SheafOfModules.{u} (moduleRings (Spec R).toRingedSpace)) (r : ℕ)
    (hM : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M r) :
    Module.finrank R ((moduleSpecΓFunctor (R := R)).obj M) = r := by
  have : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M r := hM
  obtain ⟨ι, U, hU, e⟩ :=
    Modules.IsFiniteLocallyFreeOfRank.exists_restrict_iso_free M (r := r)
  let := hR.toField
  obtain ⟨x⟩ : Nonempty (Spec R) := inferInstance
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1
    (hU.ge (Set.mem_univ x) : x ∈ ⨆ i, U i)
  have : Subsingleton (Spec (.of R)) := inferInstance
  have hUi : U i = ⊤ := by
    refine eq_top_iff.2 fun y _ ↦ ?_
    rwa [Subsingleton.elim y x]
  have he := e i
  rw [hUi] at he
  have : IsIso (⊤ : (Spec R).Opens).ι := inferInstanceAs (IsIso (Spec R).topIso.hom)
  have := (Modules.finrank_moduleSpecΓFunctor_obj_free hR
    (Modules.isoFreeOfRestrictIso M _ he.some)).1
  simpa using this

private theorem betti_eq_of_universal
    [∀ T : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toRingedSpace))]
    (S T : Scheme.{u}) (E : schemeDerivedCategory S) (a : ℤ) (r : ℕ) (h : T ⟶ S)
    (hfree : ∀ (T' : Scheme.{u}) (g : T' ⟶ T),
      SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings T'.toRingedSpace)) a).obj
            ((derivedPullback (g ≫ h)).obj E)) r) (y : T) :
    derivedFiberBetti T ((derivedPullback h).obj E) a y = r := by
  have hM := hfree (Spec (T.residueField y)) (T.fromSpecResidueField y)
  have hr := field_rank (T.residueField y) (Field.toIsField (T.residueField y)) _ r hM
  obtain ⟨_, _, _, c, _⟩ := exists_derivedPullbackComposition.{u, w}
  let e := (DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings (Spec (T.residueField y)).toRingedSpace)) a).mapIso
      ((c (T.fromSpecResidueField y) h).app E)
  have he := ((moduleSpecΓFunctor (R := T.residueField y)).mapIso e).toLinearEquiv.finrank_eq
  change Module.finrank (T.residueField y)
    ((moduleSpecΓFunctor (R := T.residueField y)).obj _) = r
  exact he.trans hr

private theorem quasiCompact_open_of_locallyConstructible (S : Scheme.{u})
    (U : S.Opens) (hU : Topology.IsLocallyConstructible (U : Set S)) :
    QuasiCompact U.ι := by
  rw [quasiCompact_iff_forall_isAffineOpen]
  intro V hV
  have : IsAffine V.toScheme := hV
  have hc := (hU.preimage_of_isOpenEmbedding V.ι.isOpenEmbedding).isConstructible
  have hk := hc.isRetrocompact.isCompact
  have himg := hk.image V.ι.continuous
  rw [U.ι.isEmbedding.isCompact_iff]
  change IsCompact (U.ι '' (U.ι ⁻¹' (V : Set S)))
  rw [Set.image_preimage_eq_inter_range, Scheme.Opens.range_ι]
  simpa only [Set.image_preimage_eq_inter_range, Scheme.Opens.range_ι, Set.inter_comm]
    using himg

/-- The lowest fibre-rank sublevel is a quasi-compact open immersion, and every map
with universally rank-`r` lowest cohomology factors through this open.
Source: Stacks Project, Tag 0BDL, first proof paragraph, using Tag 0BDI.
(blueprint: lem-sc-perfect-lowest-rank-bound-open).

Proof:
1. A perfect complex is pseudo-coherent. Apply the jump-loci lemma in degree `a`.
   Upper semicontinuity makes `U = {x | β_a(x) < r + 1}` open. The same lemma makes
   each level set locally constructible; their finite union for `0 ≤ n ≤ r` is `U`.
2. Restrict the locally constructible set to each affine open. It is constructible
   there by quasi-compactness of the affine scheme, and hence retrocompact by
   Tag 09YH. In particular it is compact. Transport compactness along the two open
   embeddings to show that the inclusion of `U` is quasi-compact. No global
   quasi-separatedness hypothesis on `S` is needed.
3. Given the universal condition for `h`, test it on `T.fromSpecResidueField y`.
   Its lowest cohomology has dimension `r`. The base-change equality of Betti numbers
   gives `β_a(h y) = r`. Hence the range of `h` lies in `U` and the open-immersion
   lifting property gives the required factorization. -/
theorem exists_perfectLowestRankBoundOpen
    [∀ T : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toRingedSpace))]
    (S : Scheme.{u})
    [∀ U : S.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U))]
    (E : schemeDerivedCategory S) (hE : IsPerfect S E) (a : ℤ)
    (r : ℕ) :
    ∃ U : S.Opens, QuasiCompact U.ι ∧
      (∀ x : S, x ∈ U ↔ derivedFiberBetti S E a x ≤ r) ∧
      (∀ (T : Scheme.{u}) (h : T ⟶ S),
        (∀ (T' : Scheme.{u}) (u' : T' ⟶ T),
        SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
          ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings T'.toRingedSpace)) a).obj
              ((derivedPullback (u' ≫ h)).obj E)) r) →
          ∃ hU : T ⟶ U.toScheme, hU ≫ U.ι = h) := by
  classical
  have hpc := (perfect_isPseudoCoherent_and_hasLocallyFiniteTorDimension S E hE).1
  obtain ⟨hbase, hupper, hlevels⟩ := pseudoCoherent_jump_loci S E hpc a
  let U : S.Opens := ⟨{x | derivedFiberBetti S E a x < r + 1},
    hupper.isOpen_preimage (r + 1)⟩
  have hUeq : (U : Set S) = ⋃ n : Fin (r + 1),
      {x | derivedFiberBetti S E a x = n} := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    constructor
    · intro hx
      exact ⟨⟨derivedFiberBetti S E a x, hx⟩, rfl⟩
    · rintro ⟨n, hn⟩
      change derivedFiberBetti S E a x < r + 1
      rw [hn]
      exact n.isLt
  have hUlc : Topology.IsLocallyConstructible (U : Set S) := by
    rw [hUeq]
    exact Topology.IsLocallyConstructible.iUnion (fun n ↦ hlevels n)
  refine ⟨U, quasiCompact_open_of_locallyConstructible S U hUlc, ?_, ?_⟩
  · intro x
    exact Nat.lt_succ_iff
  · intro T h hfree
    have hrange : Set.range h ⊆ Set.range U.ι := by
      rw [Scheme.Opens.range_ι]
      rintro x ⟨y, rfl⟩
      change derivedFiberBetti S E a (h y) < r + 1
      rw [← hbase T h y, betti_eq_of_universal S T E a r h hfree y]
      exact Nat.lt_succ_self r
    exact ⟨IsOpenImmersion.lift U.ι h hrange, IsOpenImmersion.lift_fac _ _ _⟩

end AlgebraicGeometry.Scheme
