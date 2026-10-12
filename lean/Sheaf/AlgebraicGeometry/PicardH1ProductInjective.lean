/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.AlgebraicGeometry.StructureSheafCohomologyPullback
public import WeilConjectures.AlgebraicGeometry.DensePoints
import Sheaf.AlgebraicGeometry.AffineOpenModuleCohomologyVanishing
import Sheaf.AlgebraicGeometry.PicardKunnethQcoh
import Sheaf.AlgebraicGeometry.ProperBasic

/-!
# Injectivity of the two slice pullbacks in degree one

Source: Stacks Project, Varieties, Tag 0BED, applied in degree one to the structure sheaves
(blueprint: lem-sc-picard-h1-product-injective).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- For proper `k`-schemes with only scalar global functions, the two rational-point slices
jointly detect classes in the first cohomology of the structure sheaf of their product.
Source: Stacks Project, Varieties, Tag 0BED, degree one
(blueprint: lem-sc-picard-h1-product-injective).

Proof: properness implies quasi-compactness and separatedness, hence affine diagonals
(`pqf-lem-proper-basic`). Apply `lem-sc-picard-kunneth-qcoh` to the structure sheaves in
degree one. The only summands have bidegrees `(1,0)` and `(0,1)`; scalar global sections
identify them with `H¹(X, O)` and `H¹(Y, O)`. Functoriality of the cup-product map shows that
pullback along `(1,y)` acts as the identity on the first summand and zero on the second:
the cross term factors through `Spec k`, whose first cohomology vanishes by
`pqf-lem-affine-vanishing`. Pullback along `(x,1)` similarly acts as zero and identity.
Thus the pair of pullbacks is the identity under the Kunneth identification, so is injective. -/
theorem picard_h1_product_injective (k : Type u) [Field k] (X Y : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))] [Y.Over (Spec (CommRingCat.of k))]
    [IsProper (X ↘ Spec (CommRingCat.of k))] [IsProper (Y ↘ Spec (CommRingCat.of k))]
    (hX : Function.Bijective (globalSectionsRingHom k (X := X)))
    (hY : Function.Bijective (globalSectionsRingHom k (X := Y)))
    (x : (X ↘ Spec (CommRingCat.of k)).fieldPoints k)
    (y : (Y ↘ Spec (CommRingCat.of k)).fieldPoints k) :
    let f := X ↘ Spec (CommRingCat.of k)
    let g := Y ↘ Spec (CommRingCat.of k)
    let iX : X ⟶ pullback f g := pullback.lift (𝟙 X) (f ≫ y.1) (by
      dsimp only [f, g]
      rw [Category.id_comp, Category.assoc, y.2]
      simp)
    let iY : Y ⟶ pullback f g := pullback.lift (g ≫ x.1) (𝟙 Y) (by
      dsimp only [f, g]
      rw [Category.id_comp, Category.assoc, x.2]
      simp)
    Function.Injective
      ((structureSheafCohomologyPullback iX 1).prod (structureSheafCohomologyPullback iY 1)) := by
  sorry

end AlgebraicGeometry.Scheme
