## What changed

Proved `AlgebraicGeometry.Scheme.exists_affineEtale_normalized_cartesian_comparisons`
in `Sheaf.AlgebraicGeometry.AffineEtaleNormalizedCartesianComparisons` without changing
its signature, visibility, or docstring. The original public import is unchanged.

Private proved helpers construct natural comparisons between two functors with cartesian
object squares, and prove diagonal normalization. The component isomorphisms are constructed
with `IsPullback.isoIsPullback`, lifted through the étale and affine full subcategories.
Naturality follows by pullback extensionality: naturality of the first projections proves
the first equation, and the fact that arrows are over the base proves the second.

The main proof pastes the supplied squares using `IsPullback.paste_horiz`, rewrites the
base arrows using diagram functoriality and cone naturality, and obtains gamma and delta.
The supplied diagonal identities identify the composite projections with the single
projections. Pullback uniqueness then identifies each diagonal comparison with `Iso.refl`.
The existential choices used here select isomorphisms from fully proved existence results;
there is no choice from an unproved existence theorem.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.exists_affineEtale_normalized_cartesian_comparisons`
(node `lem-weil-pbc-affine-etale-normalized-cartesian-comparisons`).

No `sorry` remains in the module, and no holes or modules were added. All private helpers
are fully proved. This is a proof, not a decomposition. Single-file compilation passes
without warnings. The delivery dry run supplies the axiom probe.

## No longer needed

None of the original imports, nodes, or modules is pruned. The existing DAG plan is followed:
cartesian square pasting and fibre-product uniqueness are used directly through Mathlib.
The unit's realized statements and proof steps are preserved.

Two imports tried during proof development were removed after compilation confirmed they
were unnecessary: `Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic` and
`Mathlib.CategoryTheory.Whiskering`. Both are already available through the original import;
these removals do not prune any original dependency.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface error was found. The previous sandbox attempt contained an
empty Lean file and two valid search records; its file was replaced with the repository
module before writing the proof. The DAG's three steps are realized without new nodes,
so no node fields need updating.

## Second reading by G1

1. **Statements and interfaces.** Diffed the delivered module against the repository
version. The public theorem signature, visibility, and docstring are byte-for-byte
unchanged; no definitions or target statements were altered. Verdict: pass.

2. **Proof and axioms.** Compiled the module with `lcompile.py`; it succeeds without
errors or warnings. Searched the delivered source for `sorry`, `axiom`, `unsafe`,
`opaque`, `implemented_by`, and `extern`; none occur. The proof uses only the supplied
pullback hypotheses and fully proved helper lemmas. Verdict: pass.

3. **Split-off statements.** No statements were split off and no new nodes were added.
The private helpers are proof-local reductions, each strictly below the target and
fully proved. Verdict: pass.

4. **Shortest route and pruning.** The construction uses `IsPullback.paste_horiz`,
`IsPullback.isoIsPullback`, and pullback uniqueness directly, while retaining every
dependency required by the DAG unit route. The two development-only imports listed
above were removed; no original proof dependency can be pruned. Verdict: pass.

5. **DAG agreement.** The existing node's statement and proof plan agree with the
delivered Lean proof, including all three normalization clauses and both projection
equations. The unit's `realized` route is preserved. Verdict: pass.

Changed only the delivered proof module and this second-reading report; no repairs,
new nodes, statement changes, or dependency changes were needed.
