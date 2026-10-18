/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q31
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.Topology.Defs.Filter
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Quasi-compact opens of base-changed finitely presented affine charts

Source: Stacks Project, Morphisms, Tags 01TP, 01TQ, 01TR, 01TS, 01TT and 01TU
(blueprint: lem-nagata-qc-open-basechanged-affine-chart-fp).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A quasi-compact open subscheme of a base-changed finitely presented affine chart is of finite
presentation over the new base. The open immersion `j` identifies `Spec A` with the affine open
`V` of `S`; `i` identifies `W` with the given open subscheme of the pullback. The conclusion spells
out finite presentation as local finite presentation, quasi-compactness and quasi-separatedness.

Source: Stacks Project, Morphisms, Tags 01TP, 01TQ, 01TR, 01TS, 01TT and 01TU
(blueprint: lem-nagata-qc-open-basechanged-affine-chart-fp).

Proof plan, following the five steps of the node:
1. Both open immersions `j` and `i` are locally of finite presentation. For an open immersion,
   use `lem-weil-pbc-affine-opens-basis` to take an affine neighbourhood inside the image.
   Its inverse image is the same affine neighbourhood, with identity ring map and its
   zero-generator, zero-relation presentation (`def-weil-pbc-finitely-presented-algebra` and
   `def-sbc-locally-finite-presentation`).
2. `Spec B` and `Spec A` are quasi-compact and quasi-separated by
   `lem-weil-pbc-affine-scheme-qcqs`. The spectrum map of `algebraMap A B` is locally of finite
   presentation by its affine ring map (`def-weil-affine-spectrum` and
   `def-sbc-locally-finite-presentation`). Apply clause (1) of
   `lem-weil-pbc-qcqs-morphism-permanence` to obtain finite presentation of that spectrum map.
3. Clause (1) of `lem-weil-pbc-qcqs-morphism-permanence` also makes `j` quasi-compact and
   quasi-separated. Compose by clause (d) of `lem-weil-pbc-proper-fp-permanence` and base change
   by clause (3) of the former node. The resulting projection to `T` is of finite presentation.
   Since `T` is quasi-separated, clause (2) makes its source pullback quasi-separated.
4. The open immersion `i` is separated by `lem-weil-pbc-separated-cancellation`, hence
   quasi-separated by `lem-pc-separated-quasi-separated`. Its source is quasi-compact and its
   target is now known to be quasi-separated, so clause (1) of
   `lem-weil-pbc-qcqs-morphism-permanence` makes it quasi-compact. Step 1 supplies its local
   finite presentation.
5. Compose `i` with the projection using clause (d) of `lem-weil-pbc-proper-fp-permanence`.
   The three resulting properties are exactly the three conjuncts below. -/
theorem finitePresentation_qcOpen_basechanged_affine_chart
    (S T : Scheme.{u}) [CompactSpace S] [QuasiSeparatedSpace S]
    [CompactSpace T] [QuasiSeparatedSpace T] (t : T ⟶ S)
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.FinitePresentation A B]
    (j : Spec (CommRingCat.of A) ⟶ S) [IsOpenImmersion j]
    (W : Scheme.{u})
    (i : W ⟶ pullback (Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ j) t)
    [IsOpenImmersion i] [CompactSpace W] :
    LocallyOfFinitePresentation
        (i ≫ pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ j) t) ∧
      QuasiCompact
        (i ≫ pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ j) t) ∧
      QuasiSeparated
        (i ≫ pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ j) t) := by
  sorry

end AlgebraicGeometry
