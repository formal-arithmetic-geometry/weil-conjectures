## What changed

Proved `AlgebraicGeometry.Scheme.strictHenselizationStructuralMap_fiber_eq_closedPoint_of_eq`
in `Sheaf.AlgebraicGeometry.StrictHenselizationClosedFiberForward` without changing its signature.
Added a proof-only import of `Sheaf.AlgebraicGeometry.StrictHenselizationChartMaximalIdeal`.

The new module proves `AlgebraicGeometry.Scheme.strictHenselization_chart_maximalIdeal` from
`etale_local_ring_triples` and `strictHenselization_triples`. It transports the local-ring
structure and extended-maximal-ideal identity through the small-model and chart/triple colimit
comparisons. Choosing a representative of the pointed chart proves the precise structural-map
compatibility using coprojection equations and naturality of `isoSpec.inv`.

The original theorem then cancels the affine open immersion in the point equation, applies the
ideal-map adjunction, and identifies the prime with the maximal ideal. Specialization and T0
antisymmetry identify the closed points under the arbitrary affine isomorphism. The original
node now records this argument through the new, fully proved chart node. The unit route is kept.

Both modules compile with the local compiler. The chart proof uses a declaration-scoped heartbeat
increase for elaborating its nested category/diagram comparisons; it compiles in about eleven
seconds. No definitions, existing interfaces, target statements, or other modules were changed.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.strictHenselizationStructuralMap_fiber_eq_closedPoint_of_eq`
(node `lem-weil-pbc-strict-henselization-closed-fiber-forward`).

Also proved the new theorem `AlgebraicGeometry.Scheme.strictHenselization_chart_maximalIdeal`
(node `lem-weil-pbc-strict-henselization-chart-maximal-ideal`). No `sorry` remains in either
delivered module; no holes were added or split off. Both delivered theorems were independently checked with `#print axioms`: each uses only
`propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx` in its proof closure.

Edge cases: no domain, noetherian, or maximality assumption is added to the chart ring. The ideal
containment proof applies when the affine presentation ring is a field. The local colimit has a
field quotient by the triple theorem, excluding a zero-ring affine presentation isomorphic to
its spectrum. The proof uses the arbitrary supplied isomorphism, with no pointedness assumption.

## No longer needed

Removed the original module's direct proof imports of
`Sheaf.AlgebraicGeometry.EtaleLocalRingTriples`,
`Sheaf.AlgebraicGeometry.StrictHenselization`, and
`Sheaf.RingTheory.StrictHenselizationTriples`. The two triple modules are now imported
by the proved chart module; `StrictHenselization` is already publicly imported by
`StrictHenselizationStructuralMap`. No module is removed from the import closure, and
no original planned dependency is discarded from the transitive argument. The original dependencies
`lem-weil-pbc-etale-local-ring-triples` and `lem-weil-pbc-strict-henselization-triples`
remain necessary through the proved chart lemma. The two strict-henselization definition nodes
remain necessary for its colimit and structural-map equations. An exploratory direct import of
`Mathlib.FieldTheory.IsSepClosed` was removed from the new module after successful recompilation.
No import of `StrictHenselizationFunctoriality`, `StrictHenselizationLocalStructure`, or
`StrictHenselizationClosedFiberBackward` is needed for this argument; these were not dependencies
of the original node and no global pruning of them is claimed.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The original plan's colimit transport was implicit; the new proved
chart lemma supplies both compatibility equations needed by the ideal argument. LeanSearch
returned an internal server error, so that search is recorded as unavailable; LeanFinder,
Loogle, source grep, library searches and blueprint searches were used. The cited Stacks texts
were absent from this checkout and were read at the official pages for Tags 04HX, 04GW and 04GP.

## New nodes

`lem-weil-pbc-strict-henselization-chart-maximal-ideal` is a fully proved, reusable affine-chart
transport theorem in `Sheaf.AlgebraicGeometry.StrictHenselizationChartMaximalIdeal`. It states a
local coordinate-ring structure, the structural R-map equation, and the extended-maximal-ideal
identity, strictly preceding the prime-containment and closed-point transport argument. Its
proof follows the existing triple declarations and the actual canonical colimit comparisons.
There are no change records because no existing interface changed.

## Second reading by M1

1. PASS: compared every delivered module with the repository. The existing theorem's
   complete signature is byte-identical, including all hypotheses and its conclusion;
   its docstring and visibility are unchanged. The chart module is new. No definitions,
   targets, or other existing interfaces change, so no change record is needed.
2. PASS: compiled both modules in import order using `lcompile.py`, without errors or
   warnings (about 11 s and 3 s). Independent scratch copies with `#print axioms` show
   only `propext`, `Classical.choice`, and `Quot.sound` for both theorems. No `sorry`,
   forbidden declaration, or hollow definition occurs in the delivered files.
3. PASS: there are no split-off holes. The new, fully proved chart theorem is a genuine
   intermediate statement: it constructs the structural ring-map equation and the
   extended-maximal-ideal equation; the original theorem still proves prime containment
   and transports the closed point under an arbitrary isomorphism. Reviewed the chart
   colimit comparison and coprojection equations against both triple declarations.
   Fields and non-domain chart rings require no extra assumptions; a zero chart ring
   cannot admit the supplied geometric point. Locality excludes a zero colimit ring.
   Independent LeanFinder search for maximal ideals of local pointed etale colimits,
   Loogle search for maximal-ideal transport, and source searches in both library roots
   found generic tools but no existing theorem supplying this chart compatibility.
   `StrictHenselizationLocalStructure` supplies locality only, not either map equation.
4. PASS: the proof takes the direct chart/ideal-adjunction route through the existing
   triple theorems and Mathlib colimit/ideal/specialization APIs. All proof-only imports
   are private imports; the sole public import supplies signature constants. The three
   removed direct imports are listed above and remain available transitively. No old
   proof dependency is eliminated from the transitive argument and no module is globally
   pruned. Read `dag/units/sk-thm-p1.json`: the unit's statement and realized steps stay,
   and this internal strict-henselization calculation bypasses none of them.
5. PASS: the existing node changes only `proof`, `proof_deps`, and `proof_origin`.
   The new node includes the required source, statement dependencies, proof steps,
   searches, origin, creation, blueprint, chapter/unit and Lean records. For each node,
   the union of the steps' `uses` equals `proof_deps`; the statements and proof steps
   agree with the Lean. No arbitrary data is chosen from an unproved existence theorem.

Changed only this report: corrected the omitted direct-import removals and replaced
the unsupported claim of unresolved transitive dependencies with the clean independent
axiom results. The Lean proofs and DAG records needed no repair. Closed 1 original
hole out of 1; added 0 holes; 0 split off; no modules pruned.
