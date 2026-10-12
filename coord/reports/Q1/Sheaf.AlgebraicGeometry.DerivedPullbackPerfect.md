## What changed

Proved `AlgebraicGeometry.derivedPullback_preserve_perfect` without changing its
signature or visibility. Its proof constructs the ordinary termwise pullback of
each local strictly perfect model. Private helpers prove that this functor
preserves the unit, finite free modules, the finite-free retract equations, and
the original bounds.

Added `Sheaf.AlgebraicGeometry.LocalizedPullbackPerfectModel`. Its
`Scheme.Modules.localizedPullback` is a real construction: the source open-site
equivalence, ordinary module pullback of the restricted scheme morphism, and the
inverse target open-site equivalence. The module proves
`AlgebraicGeometry.localizedPullback_perfectModel_iso`, which identifies its
termwise image with the restriction of derived pullback. The proof explicitly
establishes flatness of finite-free retracts, uses `flatComplexDerivedPullback`,
identifies tensor and ordinary module pullback by uniqueness of left adjoints,
and composes the restriction and localization comparisons. It uses standard
derived categories on open subschemes independently of the original universe.

Updated the existing node's proof, proof dependencies and proof origin and added
a node for the fully proved local computation. No existing definition, statement,
interface, or other holder's module was changed. The unit's `realized` lists are
empty; the proof follows the original local strictly perfect model route.

Sources read: Stacks [09UA](https://stacks.math.columbia.edu/tag/09UA), its
alternative argument through [09U7](https://stacks.math.columbia.edu/tag/09U7),
and the existing project's flat-complex and open-restriction modules and nodes.
The former implements 06YD/06YJ, the latter implements 08DW. Relevant Mathlib
and source-library definitions and exact-functor comparison signatures were
read directly. The literature TeX files are absent from this machine, so the
Stacks web text supplied the source reading.

## Proved and sorry left

Closed the one existing hole:
`AlgebraicGeometry.derivedPullback_preserve_perfect`
(node `lem-pc-derived-pullback-perfect`).

Also fully proved the new theorem
`AlgebraicGeometry.localizedPullback_perfectModel_iso`
(node `lem-pc-localized-pullback-perfect-model`), its additive instance, and all
private helpers. Zero holes added; zero holes left in either delivered module.
This is a proof from existing declarations, not a decomposition into new holes.
It still uses the project's existing proof dependencies; this does not assert
that all their transitive axioms are already closed.

Both delivered files compile cleanly with `lcompile.py --all`, in import order.
Checks include arbitrary localization universe `w`, unbounded ambient `E`, empty
opens and schemes, zero complexes, and rank-zero finite free modules. Bounds
and retracts are transported without assuming flatness of the scheme morphism.

## No longer needed

The direct proof import `Sheaf.AlgebraicGeometry.FlatComplexDerivedPullback` was
removed from the item and is now used in the proved local-model module. Its node
`lem-pc-flat-complex-derived-pullback` is still needed transitively and is not
pruned. No original node or module is no longer needed globally: pruned none.
Both original public imports remain necessary for the unchanged statement.
Redundant imports were removed from the new module after compilation.

## Where the brief, the DAG or earlier work was wrong

The old plan omitted the Lean interface glue between localized-site complexes
in `Scheme.IsPerfect` and module complexes on an open subscheme in
`flatComplexDerivedPullback`. It also did not record the derived open-restriction
comparison as a dependency. The new proved local computation supplies these
transports, with no additional universe hypothesis in the original statement.

The mathematical statement was sound. No statement was disputed or weakened.
The explicit instance for invertibility of the pullback-unit map is needed in
Lean's module visibility regime; finality is proved by terminal preservation
of the inverse-image functor on opens.

## New nodes

`lem-pc-localized-pullback-perfect-model`, in
`dag/nodes/sec-picard-framework/lem-pc-localized-pullback-perfect-model.json`,
records the fully proved local derived-object computation. It does not assert
preservation of perfectness or of strict perfectness: the latter is proved in
the item's module and combined with this computation. Its hypotheses supply an
actual local complex and its model isomorphism. Its construction includes no
choice from an unproved existence theorem. No change record was necessary.

## Second reading by Q1

1. Compared the delivered item module with the repository version. The existing
   theorem signature and visibility are byte-for-byte unchanged; only its proof,
   proof imports, and author line changed. The added module and node are new.
   Verdict: no accidental statement or definition change.
2. Compiled both delivered modules with `lcompile.py --all`. There are no
   `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by` tokens in
   the delivered Lean files. The proof uses only existing declarations and the
   explicitly recorded local computation node. Verdict: clean compilation and
   no new holes.
3. Read the new node and checked its edge cases conceptually (empty opens,
   zero complexes, and rank-zero finite free modules). The local computation
   theorem is strictly stronger than the final preservation step and its
   statement matches the Lean declaration exactly. Searches found no existing
   declaration with this statement. Verdict: the new statement is true and
   needed, with complete source and proof documentation.
4. Checked the proof route against the unit record and the imported dependency
   nodes. The localized pullback construction, finite-free retract argument,
   flat-complex computation, and open-restriction comparison are all retained.
   The direct flat-complex import was moved to the new computation module;
   no dependency is pruned from the transitive route. Verdict: route preserved
   and imports are minimal for the two modules.
5. Checked the DAG proof steps, `proof_deps`, `proof_origin`, and the new node's
   Lean record against the source. They agree with the declarations and use
   the recorded Stacks sources. Verdict: DAG and Lean are synchronized.

Changed during second reading: appended this review section only; no Lean,
statement, node, or import repairs were required.
