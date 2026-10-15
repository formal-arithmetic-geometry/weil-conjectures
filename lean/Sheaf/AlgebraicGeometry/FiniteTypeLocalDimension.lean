/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.Algebra.Field.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
# Finite local dimension for finite type schemes over a field

Source: Stacks Project, Algebra, Tag 00P1 (lemma-dimension-at-a-point-finite-type-field),
with the affine stalk calculation and the Noetherian local finiteness consequence of Tag 00KQ
(proposition-dimension) (blueprint: lem-kun-finite-type-local-dimension).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The local ring at any point of a finite type scheme over a field has finite Krull dimension.
Source: Stacks Project, Tags 00P1 and 00KQ
(blueprint: lem-kun-finite-type-local-dimension).

Proof plan:
1. A field is Noetherian: its only ideals are zero and the unit ideal, both finitely generated.
   Thus its one-point affine spectrum is Noetherian (`def-weil-field`,
   `def-weil-pbc-noetherian-ring`, `def-weil-affine-spectrum`, `pqf-def-locnoeth`).
2. Apply `lem-weil-pbc-finite-type-over-noetherian` (Tag 01T6) to the structure morphism.
   The scheme `X` is Noetherian, hence locally Noetherian.
3. Choose a Noetherian affine neighbourhood of `x`. By
   `lem-weil-pbc-affine-open-stalk-localization` (Tag 01HV), its germ map is localization
   at the complement of the corresponding prime. This complement is multiplicative by primality.
   Apply `lem-weil-pbc-localization-noetherian` (Tag 00FN) to obtain a Noetherian stalk.
   It is local because `X` is a scheme (`def-pc-scheme`, `pqf-def-locnoeth`).
4. The finiteness clause of `lem-weil-pbc-noetherian-local-system-of-parameters`
   (Tag 00KQ) now gives finite Krull dimension of the stalk, as required. -/
theorem ringKrullDim_stalk_lt_top_of_finiteType
    (K : Type u) [Field K] (X : Scheme.{u}) [X.Over (Spec (.of K))]
    [LocallyOfFiniteType (X ↘ Spec (.of K))] [QuasiCompact (X ↘ Spec (.of K))]
    (x : X) : ringKrullDim (X.presheaf.stalk x) < ⊤ := by
  sorry

end AlgebraicGeometry
