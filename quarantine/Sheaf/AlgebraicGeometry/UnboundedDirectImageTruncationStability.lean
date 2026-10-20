/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K8
-/
module

public import Sheaf.AlgebraicGeometry.UnboundedDirectImageComparisonMap
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure

import Sheaf.AlgebraicGeometry.ProEtaleClassicalBounds
import Sheaf.AlgebraicGeometry.ModuleCohomologyConventions
import Sheaf.CategoryTheory.RightDerivedFunctorUpperBound
import Sheaf.AlgebraicGeometry.UnboundedDirectImageBoundedBelow
import WeilConjectures.AlgebraicGeometry.ProEtale.Replete
import WeilConjectures.CategoryTheory.DerivedCategory.LeftComplete
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.TorsionSheaf
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Fixed-degree stabilization of the two direct-image comparison functors

Source: blueprint unbounded direct-image proof, Source and Target paragraphs.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace AlgebraicGeometry.ProEtale
private theorem module_higher_bound
    (k : Type u) [Field k] (hk : Finite k ∨ IsAlgClosed k)
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k))] [Y.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k))]
    (g : X ⟶ Y) [LocallyOfFiniteType g] [QuasiCompact g]
    (q : ℕ) (hq : 2 * ((topologicalKrullDim X).unbotD 0).toNat + 1 < q)
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    IsZero (((Etale.lowerStar (ModuleCat.{u + 1} A) g).rightDerived q).obj M) := by
  let U := Etale.moduleAbelianForget A Y
  let B := Etale.moduleAbelianForget A X
  have hM : (B.obj M).IsTorsion :=
    (Scheme.isTorsionModuleSheaf_iff_isTorsion M).mp inferInstance
  have hz := (classicalUniformBounds hk (X ↘ Spec (CommRingCat.of k))
    (Y ↘ Spec (CommRingCat.of k)) g (B.obj M) hM).1.2.2 (q : ℤ) (by omega)
  let FAb := Etale.lowerStar AddCommGrpCat.{u + 1} g
  let j := FAb.homologyRightDerivedFunctorPlusObjSingleFunctorIso (B.obj M) q
  have hz' := hz.of_iso j.symm
  let c := (Functor.rightDerivedBaseChange
    (Etale.moduleAbelianLowerStarIso A g).hom q).app M
  have hc : IsIso c := (Etale.module_cohomology_conventions A Y).2.2.1 X g M q
  have hzero : IsZero (U.obj
      (((Etale.lowerStar (ModuleCat.{u + 1} A) g).rightDerived q).obj M)) :=
    hz'.of_iso (asIso c)
  rw [IsZero.iff_id_eq_zero]
  apply U.map_injective
  rw [U.map_id, U.map_zero]
  exact (IsZero.iff_id_eq_zero _).mp hzero

private theorem target_upper_bound
    (k : Type u) [Field k] (hk : Finite k ∨ IsAlgClosed k)
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k))] [Y.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k))]
    (g : X ⟶ Y) [LocallyOfFiniteType g] [QuasiCompact g]
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (b : ℤ) [K.IsLE b] :
    ((lowerStar (ModuleCat.{u + 1} A) g).rightDerivedFunctor.obj
      ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj K)).IsLE
        (b + (2 * ((topologicalKrullDim X).unbotD 0).toNat + 1 : ℕ) + 1) := by
  let : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (CommRingCat.of k))
  let : QuasiSeparated g := inferInstance
  let d : ℕ := 2 * ((topologicalKrullDim X).unbotD 0).toNat + 1
  let G := comparisonUpperStar (ModuleCat.{u + 1} A) X
  let H := comparisonUpperStar (ModuleCat.{u + 1} A) Y
  let F := lowerStar (ModuleCat.{u + 1} A) g
  let E := Etale.lowerStar (ModuleCat.{u + 1} A) g
  have hE : ∀ M, ∀ q : ℕ, d < q → IsZero ((E.rightDerived q).obj M) :=
    fun M q hq ↦ module_higher_bound k hk A g q hq M
  have := CountableAB4Star.ofShape
    (C := Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) ℕ
  have := CountableAB4Star.ofShape
    (C := Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A)) ℕ
  have := (upperStarLowerStarAdjunction
    (ModuleCat.{u + 1} A) g).mapDerivedCategoryRightDerivedAdjunction.rightAdjoint_preservesLimits
  apply DerivedCategory.isLE_obj_of_forall_isLE_obj_truncGE
    F.rightDerivedFunctor (G.mapDerivedCategory.obj K) (b + d)
  intro n
  let L := (DerivedCategory.TStructure.t.truncGE (-(n : ℤ))).obj K
  have : L.IsGE (-(n : ℤ)) := inferInstance
  have : L.IsLE b := inferInstance
  have : (E.rightDerivedFunctor.obj L).IsLE (b + d) :=
    E.isLE_rightDerivedFunctor_obj_of_dimension d hE L b inferInstance
  have hsource : (H.mapDerivedCategory.obj (E.rightDerivedFunctor.obj L)).IsLE (b + d) :=
    H.isLE_mapDerivedCategory_obj _ _
  have : IsIso (unboundedDirectImageComparisonMap A g L) :=
    unboundedDirectImageComparison_boundedBelow A g L (-(n : ℤ))
  exact DerivedCategory.TStructure.t.isLE_of_iso
    (asIso (unboundedDirectImageComparisonMap A g L) ≪≫
      F.rightDerivedFunctor.mapIso ((G.mapDerivedCategoryTruncGEIso (-(n : ℤ))).app K))
    (b + d)

private theorem source_stable
    (k : Type u) [Field k] (hk : Finite k ∨ IsAlgClosed k)
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k))] [Y.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k))]
    (g : X ⟶ Y) [LocallyOfFiniteType g] [QuasiCompact g]
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (m N : ℤ)
    (hN : N + (2 * ((topologicalKrullDim X).unbotD 0).toNat + 1 : ℕ) ≤ m) :
    IsIso ((DerivedCategory.homologyFunctor
      (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A)) m).map
      ((comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.map
        ((Etale.lowerStar (ModuleCat.{u + 1} A) g).rightDerivedFunctor.map
          ((CategoryTheory.Triangulated.TStructure.truncGEπ
            DerivedCategory.TStructure.t N).app K)))) := by
  let d : ℕ := 2 * ((topologicalKrullDim X).unbotD 0).toNat + 1
  let F := Etale.lowerStar (ModuleCat.{u + 1} A) g
  let G := comparisonUpperStar (ModuleCat.{u + 1} A) Y
  let S := F.rightDerivedFunctor ⋙ G.mapDerivedCategory
  let T := (DerivedCategory.TStructure.t.triangleLTGE N).obj K
  let T' := S.mapTriangle.obj T
  have hT' : T' ∈ distTriang _ := S.map_distinguished T
    (DerivedCategory.TStructure.t.triangleLTGE_distinguished N K)
  have hF : ∀ M, ∀ q : ℕ, d < q → IsZero ((F.rightDerived q).obj M) := by
    intro M q hq
    exact module_higher_bound k hk A g q hq M
  have : T.obj₁.IsLE (N - 1) := inferInstance
  have : (F.rightDerivedFunctor.obj T.obj₁).IsLE (N - 1 + d) :=
    F.isLE_rightDerivedFunctor_obj_of_dimension d hF T.obj₁ (N - 1) inferInstance
  have : T'.obj₁.IsLE (N - 1 + d) := by
    exact G.isLE_mapDerivedCategory_obj _ _
  have hz₀ : IsZero ((DerivedCategory.homologyFunctor _ m).obj T'.obj₁) :=
    DerivedCategory.isZero_of_isLE _ (N - 1 + d) m (by dsimp [d] at *; omega)
  have hz₁ : IsZero ((DerivedCategory.homologyFunctor _ (m + 1)).obj T'.obj₁) :=
    DerivedCategory.isZero_of_isLE _ (N - 1 + d) (m + 1) (by dsimp [d] at *; omega)
  have : Mono ((DerivedCategory.homologyFunctor _ m).map T'.mor₂) :=
    (DerivedCategory.HomologySequence.mono_homologyMap_mor₂_iff T' hT' m).2
      (hz₀.eq_of_src _ _)
  have : Epi ((DerivedCategory.homologyFunctor _ m).map T'.mor₂) :=
    (DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff T' hT' m (m + 1)).2
      (hz₁.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi ((DerivedCategory.homologyFunctor _ m).map T'.mor₂)

/-- In each degree the two direct-image expressions stabilize on a common lower truncation.
Source: blueprint `sk-prop-pe-unbounded-classical-direct-image.proof.md`, Source and Target
paragraphs, and the sheafification argument of Steps 11--12
(blueprint: lem-sfb-unbounded-direct-image-truncation-stability).

Proof: Put d=2 dim(X)+1 and choose N=m-d-2. All fixed-ring module sheaves are torsion,
since the coefficient ring is finite. The abelian higher-direct-image bound, the canonical
module/abelian derived comparison, and faithful coefficient forgetting give R^q g_et,*=0
for q>d. Apply isLE_rightDerivedFunctor_obj_of_dimension directly to the
specified total derived functor. The source tail has upper bound N-1+d; exact inverse image
preserves it. For the target, exact comparison commutes with lower truncation. The bounded-below
canonical comparison and the etale bound put every target truncation in degrees at most
N-1+d. Pro-etale module sheaves have exact countable products; the derived direct image
is a right adjoint, so it preserves products. Left completeness and the Milnor triangle
put the unbounded target in degrees at most N+d. Both bounds are strictly less than m
and m+1. Apply each derived functor to the canonical
truncation triangle. Its long exact homology sequence makes the two truncation maps monic
and epic in degree m. The argument includes empty schemes, zero rings, all integer cutoffs,
and complexes unbounded in both directions. Only the bounded-below comparison is used.
-/
theorem unboundedDirectImage_truncation_stability
    (k : Type u) [Field k] (hbase : Finite k ∨ IsAlgClosed k)
    {ℓ : ℕ} [Fact ℓ.Prime]
    (_hℓ : IsUnit (algebraMap ℤ k (ℓ : ℤ)))
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (_hA : ∃ n : ℕ, (ℓ : A) ^ n = 0)
    {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k))] [Y.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k))]
    (g : X ⟶ Y)
    [LocallyOfFiniteType g] [QuasiCompact g]
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) (m : ℤ) :
    ∃ N : ℤ,
      IsIso ((DerivedCategory.homologyFunctor
        (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A)) m).map
        ((comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.map
          ((Etale.lowerStar (ModuleCat.{u + 1} A) g).rightDerivedFunctor.map
            ((CategoryTheory.Triangulated.TStructure.truncGEπ
              DerivedCategory.TStructure.t N).app K)))) ∧
      IsIso ((DerivedCategory.homologyFunctor
        (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A)) m).map
        ((ProEtale.lowerStar (ModuleCat.{u + 1} A) g).rightDerivedFunctor.map
          ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.map
            ((CategoryTheory.Triangulated.TStructure.truncGEπ
              DerivedCategory.TStructure.t N).app K)))) := by
  let d : ℕ := 2 * ((topologicalKrullDim X).unbotD 0).toNat + 1
  let N : ℤ := m - d - 2
  refine ⟨N, source_stable k hbase A g K m N (by dsimp [N]; omega), ?_⟩
  let G := comparisonUpperStar (ModuleCat.{u + 1} A) X
  let F := lowerStar (ModuleCat.{u + 1} A) g
  let S := G.mapDerivedCategory ⋙ F.rightDerivedFunctor
  let T := (DerivedCategory.TStructure.t.triangleLTGE N).obj K
  let T' := S.mapTriangle.obj T
  have hT' : T' ∈ distTriang _ := S.map_distinguished T
    (DerivedCategory.TStructure.t.triangleLTGE_distinguished N K)
  have : T.obj₁.IsLE (N - 1) := inferInstance
  have hle := target_upper_bound k hbase A g T.obj₁ (N - 1)
  have : T'.obj₁.IsLE (N - 1 + d + 1) := hle
  have hz₀ : IsZero ((DerivedCategory.homologyFunctor _ m).obj T'.obj₁) :=
    DerivedCategory.isZero_of_isLE _ (N - 1 + d + 1) m (by dsimp [N]; omega)
  have hz₁ : IsZero ((DerivedCategory.homologyFunctor _ (m + 1)).obj T'.obj₁) :=
    DerivedCategory.isZero_of_isLE _ (N - 1 + d + 1) (m + 1) (by dsimp [N]; omega)
  have : Mono ((DerivedCategory.homologyFunctor _ m).map T'.mor₂) :=
    (DerivedCategory.HomologySequence.mono_homologyMap_mor₂_iff T' hT' m).2
      (hz₀.eq_of_src _ _)
  have : Epi ((DerivedCategory.homologyFunctor _ m).map T'.mor₂) :=
    (DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff T' hT' m (m + 1)).2
      (hz₁.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi ((DerivedCategory.homologyFunctor _ m).map T'.mor₂)

end AlgebraicGeometry.ProEtale
