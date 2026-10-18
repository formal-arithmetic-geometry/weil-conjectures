/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q115
-/
module

public import Sheaf.AlgebraicGeometry.EtaleTorAmplitude
import Sheaf.AlgebraicGeometry.TorAmplitudeKFlatResolution
import Sheaf.CategoryTheory.TruncationsAndHomotopyColimits
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.SixFunctors.Etale.Derived.Tensor

/-!
# Connectivity of the derived tensor product

Source: `literature/blueprint/master/blueprint/sec-smooth-purity/
sk-prop-sf-kunneth-ordinary/lem-kun-derived-tensor-t-est.md`, node
`lem-kun-derived-tensor-t-est`; Stacks Project, Tag 0F1J, first reduction paragraph,
using Tag 0F1M and the lower truncation of Tag 0118.

The statement records the corrected lower-connectivity estimate: the first factor has
Tor amplitude in `[a, ∞)`, while the second factor has cohomology concentrated in
degrees at least `b`. The proof is postponed. Its source proof first applies the
bounded-below Tor-amplitude model lemma (Stacks Tag 0F1M) to obtain a K-flat complex
of flat sheaves representing `A`, with zero terms below `a`. It replaces a representative
of `B` by the canonical lower truncation from Tag 0118, which is quasi-isomorphic to
`B`, has zero terms below `b`, and requires no K-flatness. The defining K-flat model
formula for the derived tensor (Tag 06YU) then identifies the tensor with the direct-sum
total tensor complex. In every degree below `a + b`, each summand has either first
index below `a` or second index below `b`, so the total complex has zero terms and
therefore zero cohomology there (Tag 012Z).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- If `A` has Tor amplitude in `[a, ∞)` and `B` has no cohomology below `b`,
then the derived tensor `A ⊗ᴸ B` has no cohomology below `a + b`.

Source: `literature/blueprint/master/blueprint/sec-smooth-purity/
sk-prop-sf-kunneth-ordinary/lem-kun-derived-tensor-t-est.md`, node
`lem-kun-derived-tensor-t-est` (blueprint: lem-kun-derived-tensor-t-est); corrected source
proof via Stacks Project, Tags 0F1M, 0118, 06YU, and 012Z. The K-flat model has support
in degrees at least `a`; the truncated second model has support in degrees at least `b`;
the total tensor therefore has no nonzero term in degree below `a+b`, which gives the asserted
homology vanishing.
-/
theorem derivedTensor_isZero_homology_of_torAmplitudeGE
    (Λ : Type (u + 1)) [CommRing Λ] (T : Scheme.{u})
    (A B : DerivedCategoryModule Λ T) (a b : ℤ)
    (hA : DerivedCategory.hasTorAmplitudeGE Λ T a A)
    (hB : ∀ (j : ℤ), j < b →
      IsZero ((_root_.DerivedCategory.homologyFunctor
        (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) j).obj B))
    (i : ℤ) (hi : i < a + b) :
    IsZero ((_root_.DerivedCategory.homologyFunctor
      (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) i).obj
      (((derivedTensor (ModuleCat.{u + 1} Λ) T).obj A).obj B)) := by
  sorry

end AlgebraicGeometry.Etale
