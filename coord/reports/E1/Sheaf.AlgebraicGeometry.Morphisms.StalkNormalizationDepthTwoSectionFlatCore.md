## What changed

Reviewed `AlgebraicGeometry.Scheme.stalk_normalization_depth_two_section_flat_core` in
`lean/Sheaf/AlgebraicGeometry/Morphisms/StalkNormalizationDepthTwoSectionFlatCore.lean`.
The existing proof correctly combines finite flat target-locus openness with faithfully
flat stalk descent. The only Lean difference against the current repository is removal
of the word `then` in a proof comment. No signature, definition, docstring, import,
visibility, or node changes are delivered. This is the listed upstream-review #1428
repair audit; the mathematical repair has already landed.

## Proved and sorry left

`AlgebraicGeometry.Scheme.stalk_normalization_depth_two_section_flat_core` is proved.
Against the current repository baseline, holes closed: none; holes added: none.
The module already has no `sorry`, and this delivery adds no declarations or holes.
The previous report's claim of a newly filled proof was stale: both repository and
sandbox already contain the same proof. This delivery records the independent reading,
not new ledger progress or a decomposition.

## No longer needed

None. Both recorded proof dependencies are used: `lem-sbc-finite-flat-target-locus`
and `lem-weil-pbc-flat-algebra-faithfully-flat-descent`. The three public Mathlib imports
support the public statement; the two proof-only imports are already plain `import`.

## Where the brief, the DAG or earlier work was wrong

The repair queue describes the former false normalization-only statement. That statement
was previously replaced under the landed change record
`coord/changes/stalk-normalization-depth-two-section-flat-core.md`. The current core
explicitly assumes a flat pullback along a flat test meeting the chosen point. It does
not derive this assumption from depth two; the normalization caller supplies it from
the formal splitting argument with rational generic-section data. No further interface
repair is necessary. The first worker's hole-count report did not reflect the current
repository baseline.

## New nodes

None.

## Second reading by E1

1. PASS: compared the sole delivered module against the repository with `diff`.
   All existing declaration signatures are byte-for-byte identical. Only one proof
   comment differs; there are no definition or interface changes.
2. PASS: the module compiled locally with lcompile.py without errors or warnings.
   No `sorry`, axiom, unsafe, opaque, implemented_by, or extern declaration occurs.
   A scratch copy with `#print axioms` reports only `propext`, `Classical.choice`,
   and `Quot.sound` for the theorem. No data is chosen from an unproved existence result.
3. PASS: no split-off statements or new declarations exist, so no duplicate search or
   new-node validation is needed. The current general descent statement is true:
   an empty fibre gives vacuous flatness; the supplied test point is necessary to lift
   every nonempty fibre point, and no global surjectivity of the test is assumed.
4. PASS: inspected both proof dependencies and searched the local scheme-flatness and
   algebra-descent sources for alternatives. The existing proof directly lifts each
   point, descends along its flat local stalk map, and restricts to the open finite
   flat target locus. Both dependency imports are used. No recorded dependency is
   bypassed. The unit `sk-prop-input-spreading` is unchanged; its formal computation
   and rational-section hypothesis stay in the upstream caller, and its current
   `realized` record is untouched.
5. PASS: the existing node's two proof steps, proof_deps, and proof_origin describe
   exactly the Lean argument and the already landed repair boundary. No node edits
   are needed.

Second reading changed the report to distinguish the already proved theorem from
newly closed holes; the Lean proof required no repair.
