/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C5
-/
module

public import Sheaf.Paper.ModuleRingedToposDerivedComparison
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-! # Cohomology cocones for bounded flat coefficient tensors

Source: Hemo--Richarz--Scholbach Lemma 5.3(1), comparison (5.4), page 14
(blueprint: lem-sfb-filtered-flat-tensor-cohomology).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open ModuleRingedComparison
  (internalModules internalDerivedPullback internalDerivedPushforward)

variable (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj R] [IsCommMonObj R]

/-- Exact filtered coefficient colimits remain colimits after taking cohomology
of tensor with GK, or of G applied to tensor with the pulled coefficient.

Source: HRS Lemma 5.3(1), proof of comparison (5.4), page 14; Stacks 03DB, 03EP
(blueprint: lem-sfb-filtered-flat-tensor-cohomology).

Proof. Pass through the exact module/section equivalence, transporting the
specified coefficient cocone. Pullback preserves this colimit. Flatness is closed
under exact filtered colimits, both before and after pullback. Choose a bounded
below strict representative of K. Apply bounded_flat_tensor_continuity to it and
the transported cocone. For the first functor choose the supplied K-flat model of
GK: its strict tensor functor preserves the coefficient colimit, and its localized
tensor cocone is the specified derived one. Exact filtered colimits commute with
cohomology. For the second functor use the supplied functorial K-injective model:
the strict tensor diagram has the common lower bound of K, so qcqs continuity
makes the localized colimit comparison invertible. Apply cohomology to this
comparison and transport along the representative isomorphisms, including their
leg equations. Finally the exact equivalence reflects these colimits and carries
the tensor, pullback and direct-image legs back to the displayed internal maps.
Zero coefficients and empty schemes satisfy the same constructions. No filtered
colimit in the derived category is used. -/
theorem filtered_flat_tensor_cohomology_cocones
    (ℓ p : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [CharP k p]
    (hp : 0 < p) (hne : p ≠ ℓ)
    {X Y : Over (Scheme.Spec.obj (Opposite.op (CommRingCat.of k)))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) [QuasiCompact f.left] [QuasiSeparated f.left]
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (P : I ⥤ internalModules R Y.left) (c : Cocone P) (hc : IsColimit c)
    (hP : ∀ i : I, ObjectProperty.flat (P.obj i))
    (hfP : ∀ i : I, ObjectProperty.flat ((upperStar R f.left).obj (P.obj i)))
    (K : DerivedCategory (internalModules R X.left)) (hK : ∃ n : ℤ, K.IsGE n) :
    ∀ q : ℤ,
      Nonempty (IsColimit
        ((DerivedCategory.singleFunctor (internalModules R Y.left) 0 ⋙
          (derivedTensor R Y.left).obj ((internalDerivedPushforward R f.left).obj K) ⋙
          DerivedCategory.homologyFunctor (internalModules R Y.left) q).mapCocone c)) ∧
      Nonempty (IsColimit
        ((DerivedCategory.singleFunctor (internalModules R Y.left) 0 ⋙
          internalDerivedPullback R f.left ⋙ (derivedTensor R X.left).obj K ⋙
          internalDerivedPushforward R f.left ⋙
          DerivedCategory.homologyFunctor (internalModules R Y.left) q).mapCocone c)) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
