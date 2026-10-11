/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.Limits

/-!
# Effective fpqc descent reduced to affine faithfully flat morphisms

Source: Stacks Project, Descent, Lemma 35.36.2 (Tag 02W3), specialized to a
one-member fpqc covering (blueprint: lem-galois-fpqc-descending-types-morphisms).
-/

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- If a property of scheme morphisms is stable under base change and finite coproducts,
and descent data with this property are effective over flat surjective maps of affines,
then they are effective over every singleton fpqc covering (Stacks, Tag 02W3;
(blueprint: lem-galois-fpqc-descending-types-morphisms)).

Over each affine open of the base, pull back the cover and datum. Refine the resulting
fpqc cover by finitely many affine opens, use the affine effectiveness hypothesis on
their coproduct, and descend the resulting isomorphism through the refinement by full
faithfulness. On nested affine opens, full faithfulness gives unique transition
isomorphisms; relative gluing assembles the local descents and their compatible
isomorphisms into an effective descent over the original base. -/
theorem fpqcDescentEffective_of_affine
    (P : MorphismProperty Scheme.{u})
    (hbase : ∀ {Y V V' : Scheme.{u}} (g : Y ⟶ V) (h : V' ⟶ V),
      P g → P (pullback.snd g h))
    (hcoprod : ∀ (m : ℕ) (Y V : Fin m → Scheme.{u})
      (g : ∀ i, Y i ⟶ V i), (∀ i, P (g i)) → P (Limits.Sigma.map g))
    (haffine : ∀ {X S : Scheme.{u}} [IsAffine X] [IsAffine S]
      (f : X ⟶ S), Flat f → Surjective f →
        ∀ {V : Over X} (D : Over.DescentDatum f V), P V.hom → D.IsEffective)
    {X S : Scheme.{u}} (f : X ⟶ S)
    (hfpqc : Presieve.singleton f ∈ Scheme.fpqcPrecoverage S)
    {V : Over X} (D : Over.DescentDatum f V) (hV : P V.hom) :
    D.IsEffective := by
  sorry

end AlgebraicGeometry
