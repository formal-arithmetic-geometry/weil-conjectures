/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S2
-/
module

public import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.Limits
import Sheaf.AlgebraicGeometry.FpqcMorphismsDescend
import Mathlib.AlgebraicGeometry.RelativeGluing

/-! Auxiliary step of effective fpqc descent, following the Stacks Project. -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Effectivity over all affine bases implies effectivity over arbitrary bases
for a class stable under the chosen pullbacks.
Source: Stacks Project, Descent, Tag 02W3, final general-base part of the proof.
(blueprint: lem-galois-fpqc-effectivity-affine-base-gluing)

For each affine open A of S, base change f and D to A. Base-change stability of
fpqc covers and hbase preserve the hypotheses, and hlocal gives an effective
object W_A over A. For nested affine opens B ⊆ A, the two objects over B have
canonically isomorphic pullbacks to X_B. Full faithfulness of fpqc descent of
morphisms gives a unique comparison isomorphism. Uniqueness proves the identity
and composition laws. These comparisons exhibit pullback squares, so relative
gluing over the directed affine cover constructs W over S. The local
identifications of W ×_S X with V agree on overlaps by the same uniqueness and
glue to an isomorphism; transport compatibility is checked on that open cover.
Its projection to W witnesses effectivity. No finite-coproduct or affine-source
hypothesis is used here, and empty bases give empty gluing. -/
theorem fpqc_effectivity_of_affine_bases (P : MorphismProperty Scheme.{u})
    (hbase : ∀ {Y V V' : Scheme.{u}} (g : Y ⟶ V) (h : V' ⟶ V),
      P g → P (pullback.snd g h))
    (hlocal : ∀ {X S : Scheme.{u}} [IsAffine S] (f : X ⟶ S),
      Presieve.singleton f ∈ Scheme.fpqcPrecoverage S →
      ∀ {V : Over X} (D : Over.DescentDatum f V), P V.hom → D.IsEffective)
    {X S : Scheme.{u}} (f : X ⟶ S)
    (hf : Presieve.singleton f ∈ Scheme.fpqcPrecoverage S)
    {V : Over X} (D : Over.DescentDatum f V) (hV : P V.hom) : D.IsEffective := by
  sorry

end AlgebraicGeometry
