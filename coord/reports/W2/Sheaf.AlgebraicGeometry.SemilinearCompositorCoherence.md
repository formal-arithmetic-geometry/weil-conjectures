## What changed

Proved `AlgebraicGeometry.ProEtale.VaryingRing.semilinear_compositor_coherence`
(node `lem-sf-semilinear-compositor-coherence`) with its public statement and
existing docstring unchanged. The nine clauses follow from ordinary section
pasting, adjoint composition, exact derived localization, conjugation, and
transport along the supplied equalities.

Repair of the return for head `367d9aef1a6`: removed duplicate generic and
varying-ring helpers, and reused existing declarations through private
`import all` of `StrictTowerDirectImageCoherence`, `StrictTowerProperOpenCalculus`,
and `VaryingRingProperOpenPasting`. The current main file still contains the
original single hole, so this packet retains the complete proof rather than
merely rebasing the rejected delivery. Removed the additional duplicate
`restriction_eq` and reused `StrictTower.restriction_eq` as well.

The node's proof dependencies now record the three existing modules used for
these generic lemmas. The declaration-specific ordinary section and coherence
calculations remain private in the item module. No other Lean module changes.
The local elaboration commands are documented in
`coord/changes/W2-semilinear-coherence-proof-scope.md`.

Validation: the repaired file compiles through `lcompile.py` with exit code 0
and no warnings (38.2 seconds). The downstream scan lists only
`Sheaf.Paper.SystemCompatibleCompositorNormalization`; it has no textual use
of the removed private helper names. No public declaration is removed.

## Proved and sorry left

Closed the sole original hole in
`AlgebraicGeometry.ProEtale.VaryingRing.semilinear_compositor_coherence`
(node `lem-sf-semilinear-compositor-coherence`): 1 of 1 holes proved.
Holes added: 0. Holes left in delivered modules: 0. Statements split off: 0.

## No longer needed

Removed five redundant private imports from the original item:
`Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
`Mathlib.CategoryTheory.Adjunction.CompositionIso`,
`Mathlib.CategoryTheory.Adjunction.Mates`,
`Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`, and
`Mathlib.CategoryTheory.Localization.Predicate`.

Removed local copies of the generic helpers `pasting_transport`, `site_pasting`,
`restriction_pasting`, `mate_transport`, `descend_coherence`,
`site_congr_transport`, `site_left_unit`, `site_right_unit`, `restriction_eq`,
`descend_left_unit`, `descend_right_unit`, `conjugate_triangle_assoc`,
`conjugate_unit`, `leftAdjoint_unit_left`, `leftAdjoint_unit_right`,
`derived_unit_left`, `derived_unit_right`, and `leftAdjointIdIso_transpose`.
Their needed instances are supplied by the two existing StrictTower modules.
Removed duplicate varying-ring helpers `derived_transport`, `derivedJ_transport`,
`derived_id_fac`, `jAdj_unit_fac`, `derivedJId_transpose`, and `jId_eq`, and
local comparison definitions `moduleGId`, `moduleJCongr`, `jCongr`, `moduleJId`,
and `derivedJId`; the proof uses the existing VaryingRing declarations instead.
No DAG node or library module is withdrawn or bypassed, and no planned
mathematical dependency is pruned.

## Where the brief, the DAG or earlier work was wrong

The earlier delivery reproved generic helper statements already available in
the library. The return was correct: private visibility does not justify
proving a duplicate fact. This repair imports and applies those declarations;
it does not rename or repackage the rejected duplicates. The remaining
varying-ring section calculations use the actual semilinear sequence-site
functors, rather than the constant-coefficient StrictTower functors.

The public statement, definitions, and unit route are unchanged. No target
statement changes and no source-library file changes.

## Second reading by W2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
