## What changed

Proved `AlgebraicGeometry.Scheme.CompletionGluingData.exists_formalGlueingData_matching_chart`
from an affine-datum presentation. The original signature and docstring are unchanged.
The proof constructs the inverse map from matching sections to H0, proves its linearity,
proves injectivity using sheaf separatedness and both pullback projections, and proves
surjectivity using sheaf gluing on Y and separatedness on the overlap. It then inverts that
linear map and verifies the selected chart equation.

Added proof-only imports of `PuncturedCompletionAffineDatum` and
`PuncturedCompletionChartRestriction`. The latter theorem is proved directly: the inverse-image
chart equality, the restriction square, the Spec-Gamma adjunction, and the baseMap projection
identity give its equivalence and scalar law. Only the affine datum construction remains open.
No definitions, existing interfaces, or target signatures were changed. All three modules compile
individually in import order within the 60-second limit (last set: 3.7, 10.8, and 24.5 seconds).

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.CompletionGluingData.exists_formalGlueingData_matching_chart`
(node `lem-sbc-punctured-completion-formal-glueing-chart`). The item now has no direct sorry.

Also proved the new theorem
`AlgebraicGeometry.Scheme.CompletionGluingData.exists_matching_chart_restriction`
(node `lem-sbc-punctured-completion-chart-restriction`). Its proof uses no holed declarations.

Added one hole:
`AlgebraicGeometry.Scheme.CompletionGluingData.exists_formalGlueingData_affine_datum`
(node `lem-sbc-punctured-completion-affine-datum`), whose whole proof is `by sorry` in its own module.
It is only the affine coordinate construction and its local equations: it neither constructs
a global matching section nor asserts the H0/matchingRing equivalence. Its source and complete
construction proof are in the docstring and node. This delivery is a decomposition with one
hole closed and one added, not an unconditional proof of the original theorem.

The new statement was checked against an empty punctured spectrum/empty index set, nilpotent
and redundant generators, and empty chart section rings. The cover and compatibility equations
retain their meanings in all these cases. The restriction theorem assumes neither finiteness
nor a maximal-ideal generator condition and also covers empty charts.

## No longer needed

No imports were removed; both original public imports are needed by the unchanged signature.
No transitive node or module is pruned. The finite-morphism permanence node is used by the new
affine-datum construction instead of being a direct dependency of the original node.
The existing `PuncturedCompletionFormalGlueingPrime` and
`PuncturedCompletionFormalGlueingData` interfaces were read but are not imported: their
one-way compatibility and prime-coordinate map cannot supply the chart equivalences or the
converse needed here. They remain used elsewhere and are not proposed for global pruning.
The unit route is preserved; its realized nodes and stages are untouched.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found in the item. The old DAG described the sheaf equalizer argument
but its proof dependencies supplied only definitions and finite-morphism permanence; no
declaration exposed the affine coordinate equivalences and the converse local equations.
The earlier prime-coordinate lemma has arbitrary chart opens and maps out of H0, whereas
this proof needs canonical principal opens and equivalences on every ambient coordinate.
The affine-datum node states precisely that missing construction; the remaining global
assembly is now actual Lean rather than another existential bridge.

LeanSearch was unavailable (HTTP Internal Server Error); recorded as unavailable. LeanFinder,
Loogle, Mathlib-source grep, local library rg, and whole-blueprint searches were run. The
Stacks pages 0BLH, 05EL, and 05ER were read. No matching theorem or duplicate node was found.

## New nodes

`lem-sbc-punctured-completion-affine-datum`, module
`Sheaf.AlgebraicGeometry.Morphisms.PuncturedCompletionAffineDatum`: the actual affine
coordinate modules, their equivalences with chart sections, and the local iff defining H0.
Its one named theorem remains sorry and becomes the next construction item.

`lem-sbc-punctured-completion-chart-restriction`, module
`Sheaf.AlgebraicGeometry.Morphisms.PuncturedCompletionChartRestriction`: identification of
inverse-image chart sections and functorial restriction of the first matching-ring projection.
Its theorem is proved. Both nodes are strictly parts of the original three-step argument.
There are no change records because no existing interface changes.

## Second reading by J2

1. **Interfaces and statements.** Compared each delivered module with the repository versions. The existing target declaration is byte-for-byte unchanged; the two added declarations match their DAG statements, with no weakened hypotheses or altered conclusions. Verdict: pass.

2. **Proof and axioms.** Compiled all three modules with `lcompile.py --all`; the target proof has no direct `sorry`, and the only remaining hole is the named affine-datum theorem, whose proof is exactly `by sorry` in its own module. No axiom, unsafe, opaque, extern, or hollow definition was found. Verdict: pass subject to the documented split hole.

3. **Split statements and searches.** The affine-datum theorem isolates the coordinate construction and local equations; the chart-restriction theorem isolates the restriction equivalence and is proved. Both are strictly simpler than the target and have source/docstring explanations and DAG nodes. Existing library and Mathlib searches found no duplicate declarations. Verdict: pass.

4. **Pruning and route.** The two original public imports remain necessary for the target signature. The two added modules are proof dependencies, and the unit route and realized nodes are unchanged. No unused import or reachable proof dependency was removed. Verdict: pass.

5. **Verification and changes.** No definition or existing statement was changed, so no change record or forced adaptation is needed. The local compile and delivery preflight are the remaining checks. Verdict: pass.

Changed in this reading: appended this review section only; no Lean code, node statement, or proof was altered.
