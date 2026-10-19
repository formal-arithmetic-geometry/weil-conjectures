/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E3
-/
module

public import WeilConjectures.AlgebraicGeometry.StructureSheafCohomologyPullback
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.AlgebraicGeometry.PicardH1ProductSpanningBypass
import WeilConjectures.AlgebraicGeometry.ProperBasic

import Sheaf.AlgebraicGeometry.PicardExternalCupScalarComparison
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-!
# Projection pullbacks span the first cohomology of a product

Source: Stacks Project, Varieties, Tag 0BED, degree one
(blueprint: lem-sc-picard-h1-product-spanning).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct DirectSum

namespace AlgebraicGeometry.Scheme

attribute [local irreducible] Modules.scalarCohomology structureSheafAb

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 800000 in
-- Comparing derived-cohomology carriers with their unit-coefficient forms needs extra elaboration.
/-- Every first cohomology class on the product is a sum of projection pullbacks.
No rational points or uniqueness of the two summands are asserted here.
Source: Stacks Project, Varieties, Tag 0BED, degree one
(blueprint: lem-sc-picard-h1-product-spanning).

Proof: Properness over Spec k supplies compactness, and the unit modules are
quasi-coherent. Apply picard_kunneth_qcoh in degree one. The comparison and scalar
normalization of individual external cup products are isolated in
picard_external_cup_scalar_comparison. Compose its additive product comparison with
the Kunneth equivalence. For each direct-sum index, arithmetic shows the degree pair
is either (1,0) or (0,1); the comparison formulas put each pure tensor in one projection
image. TensorProduct.induction_on extends this to each tensor summand, and
DirectSum.induction_on extends it to the whole direct sum. The zero case uses zero
classes, and addition adds the two factor classes separately. Finally, surjectivity of
the two equivalences lifts an arbitrary product class to the direct sum. No slice,
rational point or uniqueness is used. -/
theorem picard_h1_product_spanning (k : Type u) [Field k] (X Y : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))] [Y.Over (Spec (CommRingCat.of k))]
    [IsProper (X ↘ Spec (CommRingCat.of k))] [IsProper (Y ↘ Spec (CommRingCat.of k))]
    (hX : Function.Bijective (globalSectionsRingHom k (X := X)))
    (hY : Function.Bijective (globalSectionsRingHom k (X := Y))) :
    ∀ c : Sheaf.H (structureSheafAb
      (pullback (X ↘ Spec (CommRingCat.of k)) (Y ↘ Spec (CommRingCat.of k)))) 1,
      ∃ a : Sheaf.H (structureSheafAb X) 1,
        ∃ b : Sheaf.H (structureSheafAb Y) 1,
          structureSheafCohomologyPullback
              (pullback.fst (X ↘ Spec (CommRingCat.of k)) (Y ↘ Spec (CommRingCat.of k))) 1 a +
            structureSheafCohomologyPullback
              (pullback.snd (X ↘ Spec (CommRingCat.of k)) (Y ↘ Spec (CommRingCat.of k))) 1 b =
              c := by
  exact picard_h1_product_spanning_bypass k X Y hX hY

end AlgebraicGeometry.Scheme
