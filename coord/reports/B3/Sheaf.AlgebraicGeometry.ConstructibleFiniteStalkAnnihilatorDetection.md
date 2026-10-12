## What changed

Proved `AlgebraicGeometry.Scheme.exists_finite_stalk_annihilator_detection` with its
original signature and public imports unchanged. Added five proof-only imports for
inverse-image stalks, constant stalks, the localized etale-site equivalence, transport of
constant sheaves along that equivalence, and lifting field-valued points through strata.

The proof uses six fully proved private helpers. It transports a localized constant chart
to the chart's small etale site, identifies its stalk annihilator with that of the constant
module, extracts a finite set of possible ideals on each compact stratum, and shows that
the stalk-annihilator function on X has finite range. It selects one actual point per ideal
in that range. The selected intersection is below the intersection at all geometric
points. A separate scalar-endomorphism argument uses joint faithfulness of geometric
stalks to pass from stalk annihilation to annihilation of every section module.

Updated the existing node's proof and proof_origin to this implementation. Its proof_deps
remain the same. No existing statements, definitions, or other modules were adapted.
The finite-chart method adapts the already proved private constant-chart comparison and
compactness argument of `ConstructibleStalkCardinalityBound`, with module coefficients
and annihilator ideals in place of set cardinalities; that module is not imported.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.exists_finite_stalk_annihilator_detection`
(node `lem-weil-pbc-constructible-finite-stalk-annihilator-detection`).
All six private helpers are fully proved. No sorry remains in the delivered module.
No holes or modules with holes were added; nothing was split off. This is a proof,
not a decomposition into new intermediate statements with sorry.
The final module compiles without warnings in about seven seconds.
`#print axioms AlgebraicGeometry.Scheme.exists_finite_stalk_annihilator_detection`
returned exactly `propext`, `Classical.choice`, and `Quot.sound`: the result does not
transitively depend on sorry either.

The finite-range argument handles empty X without choosing a point in an empty chart:
its range is empty and the finite enumeration has length zero. On a zero sheaf every
annihilator is the unit ideal. Neither finite underlying stalk sets nor a finite
coefficient ring is used; finite generation from constructibility is not needed here.

## No longer needed

None of the original imports, nodes, or planned dependency modules is pruned.
The proof avoids explicit point choices on every selected chart and instead chooses
representatives only for ideals actually realized by stalks of X. No chart-point lifting
auxiliary node is added. A redundant trial import of
`Mathlib.CategoryTheory.Linear.FunctorCategory` was removed; it was not in the original
module. All five retained proof-only imports supply declarations used in the proof.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error found. The module initially contained only its four
public statement imports; unlike the standing brief's assumption, it did not yet import
the planned inverse-image stalk module. The proof imports that existing module privately.
The unit route is preserved: the argument still uses finite stratification, compact
constant charts, inverse-image stalk comparisons, and geometric-stalk conservativity.
The selection of one point per realized ideal is a simplification below the unit level.

Searches run with msearch: LeanFinder for finitely many isomorphism classes of geometric
stalks of a constructible sheaf (topological constructibility results only); Loogle for
`Module.annihilator` (including `LinearEquiv.annihilator_eq` and annihilator membership);
grep for `annihilator.*stalk|stalk.*annihilator` (no hits). Direct source searches found
the constant-chart/cardinality argument and the needed stalk-conservativity extensionality.

## Second reading by B3

1. Compared the delivered module with the repository version. The public theorem signature and all existing declaration interfaces are byte-for-byte unchanged; only the proof, proof-only imports, author line, and DAG proof metadata differ.

2. Compiled the module with `lcompile.py`; it succeeds without warnings. The module has no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`. The proof uses only the permitted existing imports and the private helpers are fully proved. The theorem's axioms are limited to `propext`, `Classical.choice`, and `Quot.sound`.

3. Reviewed the six private helper arguments and the finite-range representative construction. The theorem statement is unchanged, and no new public statement or split-off hole was added. The edge cases of empty schemes and zero sheaves are covered by the finite-range and conservativity arguments.

4. Checked the proof route against the unit: finite constructible stratification, compact locally constant charts, stalk comparison, and geometric-stalk conservativity are all retained. The proof uses the shortest available route below the unit; no old proof dependency is removed because the node's stated dependencies remain required by the route. The five added imports are proof-only and each supplies a declaration used by the proof.

5. Checked the DAG node and report against the Lean proof. The node's proof and proof origin describe the finite annihilator-range argument and scalar-endomorphism step, with unchanged statement and proof dependencies. Searches found no existing theorem duplicating the result.

Changed nothing during this second reading; the delivered proof and metadata pass all five checks.
