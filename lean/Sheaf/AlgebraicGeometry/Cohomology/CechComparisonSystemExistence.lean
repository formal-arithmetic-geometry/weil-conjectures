/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B3
-/
module

public import Sheaf.AlgebraicGeometry.Cohomology.CechComparisonSystem
import Sheaf.AlgebraicGeometry.Cohomology.CechComparisonSystemComparison
import Sheaf.AlgebraicGeometry.Cohomology.CechComparisonSystemConnecting
import Sheaf.CategoryTheory.InjectiveCechAugmentationQuasiIso

/-! # Existence of normalized additive Cech comparisons

Source: Stacks Project, Tags 01EQ and 01FD. -/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] cohomologyHasSheafify cohomologyHasExt
/-- Every open cover admits a normalized additive Cech comparison system.

Source: Stacks Project, Tag 01EQ, Lemma 20.11.2; Tag 01FD, Lemma 20.15.1.
(blueprint: lem-pc-cech-comparison-system-existence)

Proof: For each abelian sheaf choose an injective resolution and form the ordered
Cech double complex. The section augmentation is a quasi-isomorphism: the augmented
Cech row of each injective is exact, and totalization has finite diagonals. Compose
the coefficient augmentation on homology with the inverse section augmentation and
the resolution-to-Ext identification. Comparison lifts between resolutions give
commuting augmentation squares. Homotopic lifts induce equal maps on homology, so
the resulting comparisons are independent of choices and natural in the sheaf.
In degree zero both augmentations are restriction of sections, so their quotient is
the gluing isomorphism followed by the sections-to-Ext identification. For a short
exact coefficient sequence surjective on all tuple sections, its Cech complexes
form a short exact sequence. Choose horseshoe resolutions and compare both
augmentations; naturality of homology boundaries gives precisely the connecting
law. Package these natural transformations, their zero law, and their connecting
law as the required system. Infinite covers cause no convergence issue because
total diagonals are finite. An empty cover forces X empty by hcover, and all
complexes and section groups are zero. -/
theorem exists_cechComparisonSystem
    {X : Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens) (hcover : iSup U = ⊤) :
    Nonempty (CechComparisonSystem U hcover) := by
  obtain ⟨comparison, hzero⟩ := exists_cechComparisonSystem_comparison U hcover
  let c : CechComparisonSystem U hcover :=
    { comparison := comparison
      zero := hzero
      connecting := fun T hT hg q =>
        cechComparisonSystem_comparison_connecting U hcover comparison q T hT hg }
  exact ⟨c⟩
end AlgebraicGeometry.Scheme.Modules
