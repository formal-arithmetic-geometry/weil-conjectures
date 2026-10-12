/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E3
-/
module

public import Sheaf.AlgebraicGeometry.StructureSheafCohomologyPullback
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.AlgebraicGeometry.PicardKunnethQcoh
import Sheaf.AlgebraicGeometry.ProperBasic

import Sheaf.Paper.ZariskiModuleAbelianCohomologyNatural
import Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations

/-!
# Projection pullbacks span the first cohomology of a product

Source: Stacks Project, Varieties, Tag 0BED, degree one
(blueprint: lem-sc-picard-h1-product-spanning).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Every first cohomology class on the product is a sum of projection pullbacks.
No rational points or uniqueness of the two summands are asserted here.
Source: Stacks Project, Varieties, Tag 0BED, degree one
(blueprint: lem-sc-picard-h1-product-spanning).

Proof: Apply proper_basic to each structure morphism over the affine scheme Spec k.
The sources are quasi-compact and separated; their relative diagonals are closed
immersions, hence affine. Apply picard_kunneth_qcoh to the unit module sheaves in degree
one. The only degree pairs are (1,0) and (0,1). Identify the external tensor product of
the two unit modules with the unit module on the product using tensor pullback of the
unit and the tensor unitors. Compare module cohomology with cohomology of the underlying
abelian sheaf, using injective module resolutions and the acyclicity of injective modules
for abelian-sheaf cohomology. These comparisons commute with the canonical pullback and
cup-product maps: their resolution maps lift the same maps of structure sheaves, so
comparison uniqueness identifies them. In degree zero the comparison evaluates at 1
and identifies cohomology with global sections. The bijective structure maps identify
these global sections with k. A tensor in H1(X) tensor k is therefore a finite sum of
terms a tensor c, each mapped to the projection pullback of c times a; the other degree
pair gives projection pullbacks from Y. Surjectivity of the Kunneth equivalence gives
such a finite sum for any product class. Add the finitely many X classes to obtain a,
and the finitely many Y classes to obtain b. Additivity of pullback gives the displayed
equality. This proves existence only and does not use a slice map or slice injectivity. -/
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
              c := by sorry

end AlgebraicGeometry.Scheme
