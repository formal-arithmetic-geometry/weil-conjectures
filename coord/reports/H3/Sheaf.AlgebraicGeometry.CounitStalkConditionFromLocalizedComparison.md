## What changed

Replaced the sorry in `AlgebraicGeometry.SingleComplexBaseChange.counit_stalkCondition_of_localizedComparison`
by a compiling reduction, preserving its signature and public imports. Added proof-only imports of
`Sheaf.Algebra.Homology.KFlatResolution`,
`Sheaf.AlgebraicGeometry.LocalizedComparisonQuasiIsoSquare`, and
`Sheaf.AlgebraicGeometry.StalkComparisonCoordinateInvariance`.

The proof constructs coordinates from a K-flat resolution `s : P → G`: its source isomorphism is
`asIso (DerivedCategory.Q.map s)`, its target representative is the actual ordinary pullback of G,
and its chain map is ordinary pullback of s. The representing equation is proved by naturality of
the existing counit. A proved private helper `resolution_counit_isIso` transports the K-flat
counit from `exists_derivedPullback` to the selected universal counit; this repeats the inaccessible
private helper of SingleComplexBaseChangeStalkCondition without changing that module.

The quasi-isomorphism comparison square identifies the comparison in these coordinates with a
composition of three invertible factors. Coordinate invariance then covers every coordinate
system. The item's DAG proof and proof dependencies now describe this route.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.SingleComplexBaseChange.counit_stalkCondition_of_localizedComparison`
(node `lem-pc-counit-stalk-condition-from-localized-comparison`). Its module has no sorry left.
The private `resolution_counit_isIso` helper is proved completely.

Added two named holes, each in a separate new module:

- `AlgebraicGeometry.SingleComplexBaseChange.exists_localizedComparison_quasiIso_square`
  (node `lem-pc-localized-comparison-quasiiso-square`): an actual commuting-square identity
  for a quasi-isomorphism, including an isomorphism of source objects. It assumes no
  comparison map is invertible and imposes no K-flatness on P or G.
- `AlgebraicGeometry.SingleComplexBaseChange.isIso_stalkComparison_iff_coordinates`
  (node `lem-pc-stalk-comparison-coordinate-invariance`): pointwise independence of
  invertibility from two coordinate systems for any derived morphism, not just the counit.

This is a decomposition: one hole closed, two added, net minus one. The remaining work is
formalizing the universal-property, coefficient-linearity and stalk-cohomology transport
arguments, spelled out in the new theorem docstrings and node steps. Neither new theorem
repackages the hypothesis or conclusion of the original theorem.

All three files compile together without warnings with lcompile.py. The new statements were
checked against the zero and acyclic complexes, identity s, empty X', negative degrees,
unbounded complexes, and nonflat pullback. In particular, no assertion is made that ordinary
pullback of a quasi-isomorphism is a quasi-isomorphism: only the displayed composite is
identified, and its invertibility is deduced using the hypothesis on G.

## No longer needed

None. No import was removed and no previously needed module or node was pruned. The original
exact-stalk and model dependencies are still needed inside the intermediate transport arguments.
The large mixed-total-tensor interfaces in DerivedTensorActionNaturality and
DerivedTensorLocalizationCohomology were inspected, but do not state transport for these
cohomologyModel/Coordinates interfaces and were not imported.

## Where the brief, the DAG or earlier work was wrong

The original proof plan mentions source and target transport but supplies no declarations
stating their compatibility with the actual chosen cohomology models. The two new statements
make that missing glue explicit, separating resolution naturality from coordinate independence.
No existing statement or definition is changed.

The nearest-ancestor utility returns null for this item because created.item is a module name
rather than a DAG node id. The existing blueprint.from records lem-pc-rf-perfect-base-change
through lem-pc-rf-base-change-complex; the new nodes preserve that ancestor and explain their
place in its base-change comparison step. The unit's realized lists are empty, and its route
is unchanged.

The local literature checkout lacks perfect.tex. The cited source was read from the official
Stacks source (perfect.tex, equation-bc and lemma-base-change-tensor), saved only in the sandbox
scratchpad. LeanFinder found generic Tor/projective-resolution naturality lemmas, which do not
match these interfaces. The logged LeanSearch request failed with HTTP 500; this is recorded
as unavailable, not a negative result. Logged Mathlib grep found no localizedComparison or
stalkComparison declaration. Blueprint-wide searches for comparison coordinates and tensor
cohomology found no matching statement; the K-flat search found general resolution definitions
but no comparison transport statement.

## New nodes

`lem-pc-localized-comparison-quasiiso-square`, in
`lean/Sheaf/AlgebraicGeometry/LocalizedComparisonQuasiIsoSquare.lean`, isolates naturality of the
canonical localized comparison under a quasi-isomorphism, with the precise equality needed
for the actual pulled-back stalk maps. Its proof uses exact stalks, model universal counit
equations, coefficient actions, and the specified natural pullback-stalk identification.

`lem-pc-stalk-comparison-coordinate-invariance`, in
`lean/Sheaf/AlgebraicGeometry/StalkComparisonCoordinateInvariance.lean`, isolates independence
of the condition from two K-flat coordinate systems for the same arbitrary derived arrow.
Its proof uses exact stalks, K-flat stalks, and the representing equations to obtain a square
with invertible vertical arrows. No new data definition, change record, or forced adaptation
is introduced.

## Second reading by H3

1. **Visible changes and signatures.** Compared each delivered module with the repository
version. The existing target declaration has the same signature byte for byte; the two added
modules contain only the new split-off declarations described in this report. Verdict: pass.

2. **Compilation and proof hygiene.** Compiled all three modules together with `lcompile.py`.
There are no errors or warnings, no axioms or unsafe declarations, and no `sorry` in a
definition. The only remaining `sorry`s are the two named split-off theorems, each with a
docstring and corresponding DAG node. Verdict: pass.

3. **Truth and strength of split statements.** Checked the edge cases of identity and zero
complexes, acyclic complexes, empty schemes, negative degrees, and non-flat pullback. The
localized-comparison statement asserts only the required commuting square and does not claim
ordinary pullback preserves quasi-isomorphisms. Coordinate invariance quantifies over arbitrary
derived arrows and only compares invertibility, so neither statement adds an assumption or
weakens a conclusion. Verdict: pass.

4. **Shortest route and pruning.** The target proof uses the existing K-flat resolution,
the existing counit naturality, and the two strictly smaller transport statements. Imports
were checked and proof-only imports are non-public. No old proof dependency became unused;
the report's pruning section is complete. Verdict: pass.

5. **DAG and unit agreement.** Checked each node's Lean declaration, proof dependencies,
proof origin, chapter, and unit against the delivered source. The target node records the
resolution/comparison/coordinate route, and the unit's realized route is unchanged. Verdict:
pass.

I changed only this report section: it records the independent signature, hygiene, statement,
pruning, and DAG checks above. No Lean source, node statement, or definition was altered.
