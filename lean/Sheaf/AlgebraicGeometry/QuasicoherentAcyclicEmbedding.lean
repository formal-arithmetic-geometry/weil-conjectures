/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.AlgebraicGeometry.Coherent
public import Sheaf.Topology.RingedSpaceModuleCohomology
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Over
import Sheaf.AlgebraicGeometry.AffineMorphismCohomologyEdge
import Sheaf.AlgebraicGeometry.AffineOpenModuleCohomologyVanishing
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineMorphism

/-!
# Embedding a quasi-coherent module into an acyclic quasi-coherent module

Source: Stacks Project, Cohomology of Schemes, Tag 0BDY, Lemma 30.4.3 (1)
(blueprint: lem-sc-picard-qcoh-universal-delta-embedding).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- On a quasi-compact scheme over a field with affine diagonal, every quasi-coherent
module embeds into a quasi-coherent module with vanishing cohomology in positive degrees.
Source: Stacks Project, Cohomology of Schemes, Tag 0BDY, Lemma 30.4.3 (1)
(blueprint: lem-sc-picard-qcoh-universal-delta-embedding).

Proof:
1. Choose a finite affine open cover using quasi-compactness. Its finite disjoint union
   `U` is affine; let `j : U ⟶ X` be the covering morphism.
2. Affine diagonal makes intersections of affine opens affine
   (`lem-sc-picard-affine-diagonal-intersections`). The inverse image under `j` of any
   affine open is a finite disjoint union of these intersections and hence affine
   (`lem-weil-pbc-affine-morphism-permanence`), so `j` is affine.
3. The canonical map `F ⟶ j_* j^* F` is injective on stalks: choose a covering open
   containing a given point; evaluation at its copy in `U` gives a left inverse on
   that stalk. The tensor pullback `j^* F` is quasi-coherent.
4. Affine vanishing (`pqf-lem-affine-vanishing`) gives vanishing of positive cohomology
   on `U`. The affine pushforward cohomology comparison
   (`lem-weil-pbc-affine-morphism-cohomology-edge`) transfers it to `j_* j^* F` on `X`.
   Affine pushforward preserves quasi-coherence (`lem-pc-affine-morphism-hi`). Take
   `F' = j_* j^* F`. The field hypothesis is retained as required by the node. -/
theorem exists_quasicoherent_acyclic_embedding (k : Type u) [Field k] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))] [CompactSpace X]
    [IsAffineHom (pullback.diagonal (X ↘ Spec (CommRingCat.of k)))]
    (F : SheafOfModules.{u} (moduleRings X.toRingedSpace))
    [F.IsQuasicoherent] :
    ∃ F' : SheafOfModules.{u} (moduleRings X.toRingedSpace),
      F'.IsQuasicoherent ∧ ∃ i : F ⟶ F', Mono i ∧
        ∀ p : ℕ, 1 ≤ p → IsZero ((RingedSpace.moduleCohomology X.toRingedSpace p).obj F') := by
  sorry

end AlgebraicGeometry.Scheme
