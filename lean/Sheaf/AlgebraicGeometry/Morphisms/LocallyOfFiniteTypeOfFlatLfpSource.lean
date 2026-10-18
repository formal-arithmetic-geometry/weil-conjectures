/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q27
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Sheaf.RingTheory.FiniteTypeFppfSourceDescent

/-!
# Local finite type descends through a flat locally finitely presented source cover

Source: Stacks Project, Descent, Tag 02KL, `lemma-flat-finitely-presented-permanence`,
locally-of-finite-type alternative, with algebra input Tag 0367
(blueprint: lem-a1-lft-flat-lfp-source-descent).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Local finite type descends through a surjective flat locally finitely presented source map.
Source: Stacks Project, Descent, Tag 02KL, locally-of-finite-type alternative
(blueprint: lem-a1-lft-flat-lfp-source-descent).

Proof, following the seven steps of the node:
1. For each `y : Y`, choose affine neighbourhoods `V = Spec R` of `h(y)` and
   `W = Spec A` of `y` mapping into `V`, using `lem-weil-pbc-affine-opens-basis`.
   Cover the inverse image of `W` by affine opens `U_alpha = Spec B_alpha` of `X`.
   By `lem-weil-pbc-lft-pointwise-criterion`, it suffices to show `R → A` finite type.
   If `Y` is empty the pointwise criterion is vacuous.
2. By `lem-weil-pbc-flat-morphism-affine-criterion`, each `A → B_alpha` is flat;
   by `lem-weil-pbc-lfp-affine-opens-finite-presentation` it is finitely presented.
   By `lem-weil-pbc-lft-affine-pairs`, each composite `R → B_alpha` is finite type.
   The maps form the tower induced by `q ≫ h`.
3. By `lem-weil-pbc-flat-lfp-open`, `q` is open. Its surjectivity makes the images
   of these affine opens cover `W`. Quasi-compactness of the affine scheme `W`
   (`lem-weil-pbc-affine-scheme-qcqs`) selects finitely many such images.
4. Form the finite coproduct `Z` of the selected affine opens, using
   `lem-weil-pbc-scheme-coproduct-family`. By
   `lem-weil-pbc-finite-affine-coproduct-spectrum`, it is `Spec B`, where `B` is the
   product of the selected rings. The induced map `q_Z : Z → W` is surjective.
   Its stalk maps agree with those of `q` after open restrictions, so it is flat
   (`def-weil-flat-morphism`). Its affine component neighbourhoods show it is locally
   finitely presented (`def-sbc-locally-finite-presentation`). The component composites
   are finite type over `R`, so `p_Z : Z → V` is locally of finite type by the pointwise
   criterion. The coproduct universal property gives `p_Z = q_Z ≫ h|_W`.
5. Apply the affine-pair flatness, finite-presentation and finite-type criteria again:
   `A → B` is flat and finitely presented, and `R → B` is finite type. The tower
   `R → A → B` has the composite induced by `p_Z`.
6. Surjectivity of `q_Z` provides, over every maximal ideal of `A`, a prime of `B`.
   The extended maximal ideal lies in this proper prime. Together with flatness,
   `lem-weil-pbc-flat-faithfully-flat-maximal-ideals` makes `A → B` faithfully flat.
   For the zero ring `A`, the maximal-ideal condition is empty and the same criterion applies.
7. Apply `lem-a1-finite-type-fppf-source-algebra` (Tag 0367) to conclude `R → A` is
   finite type. The pointwise criterion at every `y` now gives local finite type of `h`.
Only affine neighbourhoods need be quasi-compact; there are no separation assumptions. -/
theorem locallyOfFiniteType_of_flat_lfp_source
    {X Y S : Scheme.{u}} (q : X ⟶ Y) (h : Y ⟶ S)
    [Flat q] [LocallyOfFinitePresentation q] [Surjective q]
    [LocallyOfFiniteType (q ≫ h)] : LocallyOfFiniteType h := by
  sorry

end AlgebraicGeometry
