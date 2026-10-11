/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Sheaf.AlgebraicGeometry.TorsionAbelianBaseChange

/-!
# Cancellation of proper base change along a proper surjection

Source: Stacks Project, Tag 0A4C, Lemma 59.91.7
(blueprint: lemma-weil-pbc-cancellation).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- Proper base change cancels along a proper surjective morphism.
Source: Stacks Project, Tag 0A4C, Lemma 59.91.7
(blueprint: lemma-weil-pbc-cancellation).

Proof (the seven steps of the DAG node):
1. Proper composition and `lemma-weil-pbc-property-iff-acyclicity` reduce the assertion to
   injective acyclicity for each prime, each base change of `h`, and each injective sheaf `I`.
2. Embed the inverse image of `I` under `f` into an injective sheaf `J`, using
   `lem-weil-pbc-module-sheaves-enough-injectives`. Surjectivity and
   `lem-weil-pbc-retract-supplied` make `I` a retract of the direct image of `J`.
3. Base change both maps. By `lem-weil-pbc-cartesian-square-pasting`, the outer rectangle
   is the base change square of the composite.
4. `lemma-weil-pbc-proper-underived-exchange` identifies the inverse image of the direct
   image of `J` with the direct image of its inverse image under the base-changed `f`.
5. The two PBC hypotheses give vanishing of positive higher direct images under the
   base-changed `f` and under the base-changed composite, by injective acyclicity.
6. Apply `lem-weil-pbc-grothendieck-spectral-sequence` and
   `lem-weil-pbc-first-quadrant-row-collapse` to obtain the required vanishing for the
   base-changed direct image of `J` under `h`.
7. Inverse image preserves the retraction. By `lem-weil-pbc-vanishing-descends-retract`,
   vanishing descends to the inverse image of `I`. All primes and base changes were
   arbitrary, so the acyclicity equivalence gives PBC for `h`. -/
theorem hasTorsionAbelianBaseChange_of_comp_of_surjective
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (h : Y ⟶ Z)
    [IsProper f] [IsProper h] [Surjective f]
    (hf : HasTorsionAbelianBaseChange f)
    (hfh : HasTorsionAbelianBaseChange (f ≫ h)) :
    HasTorsionAbelianBaseChange h := by
  sorry

end AlgebraicGeometry.Etale
