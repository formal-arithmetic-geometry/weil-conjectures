## What changed

Completed `AlgebraicGeometry.directImage_qc_support_reduction` in
`Sheaf.AlgebraicGeometry.DirectImageQCSupportReduction`, with its original signature and
visibility unchanged. The proof follows the existing three-step plan: take the finite union
of closed proper cohomological supports, construct a compact open neighborhood, then compose
the supported-open adjunction unit with the canonical derived direct-image comparison.

Added proof-only imports `Sheaf.AlgebraicGeometry.DerivedOpenLocalization`,
`Sheaf.AlgebraicGeometry.DerivedOpenRestrictionMaps`,
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction`,
`Mathlib.Data.Int.Interval`, `Mathlib.Algebra.Category.Grp.Zero`, and
`Mathlib.Topology.Sheaves.Abelian`.
The existing node copy records the localization and derived-adjunction inputs explicitly.
All public imports and all existing declarations remain unchanged.

## Proved and sorry left

Closed the single original hole:
`AlgebraicGeometry.directImage_qc_support_reduction`
(node `lem-pc-direct-image-qc-support-reduction`). No holes added; no sorry remains in the
item and no new module or theorem is introduced. This is a proof from existing declarations,
not a decomposition. The second reader independently checked `#print axioms`: this theorem uses only
`propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx` in its proof closure.

## No longer needed

No original import, planned node, or planned module is pruned: each supplies a definition,
statement, or geometry instance used by the proof. The redundant candidate imports
`Mathlib.AlgebraicGeometry.Morphisms.FiniteType` from the sandbox exploration is omitted:
the needed declarations are already available through `Mathlib.AlgebraicGeometry.Noetherian`.
No target-reachable dependency is claimed to have disappeared.

## Where the brief, the DAG or earlier work was wrong

The previous attempt had a complete proof skeleton but failed to compile: rewriting the
closed-support equality required exposing set membership, and zero-stalk transport needed
`Mathlib.Topology.Sheaves.Abelian`. Zero-stalk transport now applies `map_isZero` separately to the shared module forgetful
functor, the underlying additive presheaf functor, and the stalk functor. This avoids
transporting the independent `Scheme.Modules` category instances. Proposition-valued local instances use `let` to satisfy the style linter.
The already-proved localization existence theorem supplies the open-site instances by
`Classical.choice`, avoiding expensive repeated existential elimination of the target type.

The original plan omitted explicit Lean infrastructure for deriving the canonical restriction
adjunction and choosing the localizations on open sites in the ambient Hom universe. Existing
proved APIs and existing nodes supply both; no new mathematical hypothesis is required.
A declaration-scoped unused-variable linter option documents that the unchanged
coherent-cohomology hypothesis is not needed independently: proper support
already includes closedness of each support. The bounded interval may be empty, in which case
all stalks vanish and the finite union is empty; the same proof works. No arbitrary object is
defined by choosing from an unfinished existence theorem. The localizations are chosen from
the existing size theorem, which specifies localization up to the equivalence used downstream.

The local literature files are absent on this machine. Read the official Stacks Project
Tag 08EV page (https://stacks.math.columbia.edu/tag/08EV), specifically its support-reduction
paragraph, and the recorded unit `sk-thm-picard-duality`; its realized statement/step lists
are empty. The original support-reduction route is retained.

Validation: the complete proof compiled with no warnings before the delivery dry check.
The proof preserves the empty support and empty degree-interval cases. All added imports
are proof-only; import-direction checks permit each of the three added project modules.


## Second reading by T4

1. **Interface unchanged — pass.** Diffed the only delivered Lean module against the
   repository and separately compared its complete theorem signature byte for byte.
   The scheme universes, locally finite-type and Noetherian instances, derived-category
   family, boundedness, coherence and proper-support hypotheses are unchanged. Every
   existential witness and clause remains: compact open, the three morphism properties,
   containment of all nonzero stalks, additive equivalence, adjunction, comparison with
   its unit equation, invertibility of the canonical composite, and inverse isomorphism.
   No definition, public import, declaration visibility or existing docstring changed.
   No change record or forced adaptation is needed.

2. **Proof and axioms — pass.** Compiled the delivered file without errors or warnings
   (51.9 seconds). Compiled a scratch copy with `#print axioms` for
   `AlgebraicGeometry.directImage_qc_support_reduction`,
   `AlgebraicGeometry.nonempty_derivedOpenLocalization`, and
   `AlgebraicGeometry.RingedSpace.exists_derivedModuleDirectImageComposition`
   (57.2 seconds). All three use exactly the allowed standard axioms, without `sorryAx`.
   The delivered file contains no sorry or forbidden axiom/implementation escape.
   The supports chosen from `hsupport` are uniquely specified by equality to the
   nonzero-stalk locus. The induced subscheme is the actual vanishing-ideal construction.
   The localizations come from the existing proved size theorem and its localization
   universal property. The comparison is specified by its right-derived-unit equation.
   Thus none of these choices introduces arbitrary data from an unproved existence result.

3. **Split statements — pass, none introduced.** There is no new theorem, module, node,
   or lower hole, so no split statement to validate or duplicate-search. Checked the
   argument when `a > b`, when E is zero, and when X or the support is empty: the empty
   finite supremum is covered by the union theorem's n = 0 case, and outside the interval
   three zero-preserving functors give subsingleton stalks. No nonemptiness is assumed.

4. **Route and imports — pass.** Read the existing finite-union, supported-open and
   composition declarations and the upstream derived-adjunction construction. Searched
   both Lean source roots for compact-support reduction, supported-open pushforward,
   compact closed-immersion neighborhoods and open localizations. The proof uses these
   existing APIs directly; the other open-localization adjunction theorem supplies an
   abstract right adjoint rather than the specific canonical functor needed here.
   All six added imports are proof-only and supply the finite interval, zero-group lemma,
   additive stalk transport, exact restriction, derived adjunction or open localizations.
   Original public imports still supply signature types; original proof imports are used.
   Every original proof dependency remains needed, so pruning is correctly reported as
   none. Opened `dag/units/sk-thm-picard-duality.json`: `realized.statement` and its step
   list are empty. The original three support-reduction steps remain intact, consistent
   with the support paragraph of [Stacks Tag 08EV](https://stacks.math.columbia.edu/tag/08EV).

5. **DAG matches — pass.** Diffed the existing node and checked that changes are confined
   to proof, proof_deps and proof_origin. Step 1 matches the interval supremum and stalk
   argument; step 2 matches the proper reduced closed support and immersion shrink;
   step 3 names exact restriction, deriving its adjunction, open-site localizations,
   the supported unit and unit-compatible composition. The proof-dependency list is
   exactly the union of the three steps' uses, and all named nodes already exist.
   The mathematical statement, statement dependencies and Lean statement record are
   unchanged. No new-node fields need validation.

Changes by the second reader: no Lean or DAG repair was necessary. Added this independent
review and strengthened the report's validation evidence to record that the completed
proof has no transitive sorry axioms. One original hole closed, zero holes added;
`AlgebraicGeometry.directImage_qc_support_reduction` is fully proved, not a decomposition.
