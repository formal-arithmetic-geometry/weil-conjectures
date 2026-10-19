## Worker report

The module `lean/Sheaf/TraceFormula/GeometricallyReducedFibresLimitDescent.lean`
states `AlgebraicGeometry.exists_eventually_geometricallyReduced_fibres`, the affine
inverse-limit descent statement for geometrically reduced fibres.  It has no definitions
and its proof is `sorry`, as required at stage 2.

The index data is rendered by `I : Type u`, `[Preorder I]`,
`[IsDirected I (· ≤ ·)]`, and `[Nonempty I]`.  The inverse system is
`D : Iᵒᵖ ⥤ Scheme.{u}`.  The hypotheses that every stage is quasi-compact and
quasi-separated are the typeclass binders
`[∀ j : Iᵒᵖ, CompactSpace (D.obj j)]` and
`[∀ j : Iᵒᵖ, QuasiSeparatedSpace (D.obj j)]`; affine transition morphisms are
`[∀ {j k : Iᵒᵖ} (f : j ⟶ k), IsAffineHom (D.map f)]`.  The limit
`S = \varprojlim_i S_i` is represented by `(c : Cone D) (hc : IsLimit c)`.

The fixed index and finite-presentation family are rendered by
`(a : I)`, `{Y : Scheme.{u}}`, and
`(q : Y ⟶ D.obj (op a)) [LocallyOfFinitePresentation q] [QuasiCompact q]
[QuasiSeparated q]`.  These are respectively local finite presentation,
quasi-compactness, and quasi-separatedness, with no flatness class added.
For the limit family `Y = Y_a ×_{S_a} S`, its projection to the limit is
`pullback.snd q (c.π.app (op a))`.  The hypothesis that every geometric fibre
of this projection is reduced is
`hred : ∀ s : c.pt,
GeometricallyReduced ((pullback.snd q (c.π.app (op a))).fiberToSpecResidueField s)`.
This uses the project's established Mathlib convention for reduced geometric fibres
(the chosen algebraic-closure fibre is represented by `fiberToSpecResidueField`).

The conclusion is `∃ b : I, ∃ hab : a ≤ b`, followed by
`∀ (i : I) (hbi : b ≤ i) (s : D.obj (op i)), ...`.  For `i ≥ a`, the transition
map is exactly `D.map (homOfLE (hab.trans hbi)).op`; hence the base-changed family
`Y_i = Y_a ×_{S_a} S_i` has projection
`pullback.snd q (D.map (homOfLE (hab.trans hbi)).op)`.  The final clause states
that its geometric fibre at every `s` is geometrically reduced.  The formulation
introduces no source or fibre nonemptiness hypothesis and permits empty sources and
fibres.

The recorded declarations used by the statement/proof plan are:

- `Sheaf.AlgebraicGeometry.LimitAffineTransition`,
  `AlgebraicGeometry.exists_limit_affine_transition` (the inverse-limit cone
  interface);
- `Sheaf.AlgebraicGeometry.LimitContainedInConstructible`,
  `AlgebraicGeometry.exists_eventually_range_subset_of_isConstructible`
  (the Tag 05F4 constructible-image descent interface);
- Mathlib `AlgebraicGeometry.GeometricallyReduced`,
  `AlgebraicGeometry.Scheme.Hom.fiberToSpecResidueField`,
  `AlgebraicGeometry.LocallyOfFinitePresentation`,
  `AlgebraicGeometry.QuasiCompact`, `AlgebraicGeometry.QuasiSeparated`,
  `AlgebraicGeometry.IsAffineHom`, and `CategoryTheory.Limits.pullback`/
  `pullback.snd`.

The proof docstring follows the four DAG proof clauses: constructibility of the good
locus (Tag 0579), the base-change equality (Tag 0576), eventual image containment
(Tag 05F4), and the second base-change equality at every later stage.  The two
statement-only Tag 0579/0576 nodes have no Lean declarations, so they are not imported;
their notions are represented by Mathlib's geometric-fibre predicate in this statement.

Edge cases checked: `I` is required nonempty as in the inverse-limit theorem; `Y`, the
limit, stages, and geometric fibres have no nonemptiness assumptions; `b = a` is allowed;
`a ≤ b` and `b ≤ i` are explicit; empty sources and empty fibres satisfy the universal
fibre clause; no flatness or Noetherian hypothesis was introduced; and the index universe
is the scheme universe `Type u`, as required for the inverse-system limit.

Searches for an existing declaration or duplicate notion were made as follows:

- `msearch.py ... leanfinder "geometrically reduced fibres descend along affine inverse limits"`:
  returned only generic algebraic `IsGeometricallyReduced` and reducedness declarations,
  with no affine-limit descent theorem (no exact match).
- `msearch.py ... loogle "AlgebraicGeometry.GeometricallyReduced, AlgebraicGeometry.LocallyOfFinitePresentation"`:
  returned 0 hits.
- `msearch.py ... grep "[Gg]eometrically[Rr]educed.*(descend|limit)|descend.*[Rr]educed" AlgebraicGeometry`:
  returned 0 hits.
- `rg` over `WeilConjectures/` and `lean/Sheaf/` for geometrically reduced fibre descent:
  found only unrelated fibre hypotheses and generic geometric-reducedness results; no exact
  declaration of this node.

The module compiled cleanly with
`python3 /home/ubuntu/weil-launcher-nt/scompile.py N5 lem-trf-geometrically-reduced-fibres-limit-descent`
(the expected `sorry` warning is suppressed by the module option).

## Second reading by N5

I reread the node and the Lean file clause by clause.  The Lean has the same directed
index, qcqs stage, affine transition, limit-cone, fixed-stage, finite-presentation,
base-change, fibre-reducedness, and eventual-stage clauses.  The objects are the same:
`c.pt` is the stated limit, `pullback.snd q ...` is each projection `q`/`q_i`, and
`fiberToSpecResidueField` is the chosen geometric-fibre convention used elsewhere in the
project.  No hypothesis was added or dropped, and no conclusion was weakened or
strengthened.  The empty-source/empty-fibre and no-flatness cases remain available.  I
found no mismatch requiring a change.
