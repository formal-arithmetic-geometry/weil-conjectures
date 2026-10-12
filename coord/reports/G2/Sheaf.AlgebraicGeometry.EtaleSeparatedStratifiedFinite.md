## What changed

Added `Sheaf.AlgebraicGeometry.ConstructibleStratifiedFinite` with the intermediate
finite constructible stratification theorem, left as one documented `sorry`. The target
module now derives quasi-finiteness from étaleness and quasi-compactness, applies that
intermediate theorem, and adds étaleness of each pullback by base change. The target node's
proof route and dependencies were updated accordingly.

## Proved and sorry left

`AlgebraicGeometry.Scheme.exists_etale_separated_stratified_finite` is proved. The new
`AlgebraicGeometry.Scheme.exists_constructible_stratified_finite` remains a single `sorry`
with node `lem-weil-pbc-etale-separated-stratified-finite-intermediate`.

## No longer needed

The target proof no longer directly uses the bounded-fibre, spectral, closed-subscheme,
finite-locally-free, residue-field, or fibre-degree dependencies; those details are
encapsulated by the intermediate theorem. No imports were removed from the target module.

## Where the brief, the DAG or earlier work was wrong

The original six-step proof plan requires a substantial construction of a finite
stratification from the closed degree filtration. That construction is now explicitly
split into a separate intermediate theorem so the target proof is a genuine reduction.

## New nodes

`lem-weil-pbc-etale-separated-stratified-finite-intermediate` is the finite constructible
stratification result for flat locally finitely presented separated quasi-finite morphisms;
its proof follows Stacks Tag 07RZ and is currently split as documented above.

## Earlier second reading (a previous round; superseded)

Pending the second reader assigned by group G2; the delivered proof compiles and preserves the target statement unchanged.

## Second reading by G2

1. **Statements unchanged.** Compared the delivered target module with the repository version: the existing theorem signature is byte-for-byte unchanged. The new intermediate theorem is a genuinely smaller reduction (finite constructible stratification with finite pullbacks), rather than a restatement of the target.

2. **Proof checks.** Both modules compile with `lcompile.py --all`. The target theorem has no `sorry`; the only remaining `sorry` is the named intermediate theorem, with its documented source and matching DAG node. No forbidden declarations or hollow definitions were introduced.

3. **New statement.** The intermediate statement is true and exactly sufficient for the target: under qcqs target, flat locally finitely presented separated quasi-finite hypotheses, it supplies a finite constructible locally closed stratification with finite pullbacks. It is not duplicated in the library or Mathlib, according to the recorded searches.

4. **Pruning and route.** The target proof follows the planned route: étale gives locally quasi-finite, quasi-compactness gives quasi-finite, then the intermediate stratification theorem and étale base change. The old direct-construction imports for bounded fibres, flat quasi-finite stratification, and fibre degree are no longer needed and were removed; the unit route and its realized target node are preserved.

5. **DAG agreement.** The target node proof and `proof_deps` match the Lean proof, and the new intermediate node records its statement, source, proof origin, dependencies, and Lean declaration. The intermediate remains the sole split-off theorem.

Changed during second reading: removed the unused imports `Sheaf.AlgebraicGeometry.FlatQuasiFiniteStratification`, `Sheaf.AlgebraicGeometry.HasUniversallyBoundedFibersOfIsLocallyQuasiFinite`, and `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`, and added this review record.
