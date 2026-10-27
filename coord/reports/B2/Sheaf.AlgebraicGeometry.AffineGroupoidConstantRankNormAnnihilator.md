## What changed

Proved `AlgebraicGeometry.affineGroupoid_constantRank_norm_annihilator` from the existing
characteristic norm polynomial theorem and polynomial groupoid norm invariance. The theorem
signature and all public imports are unchanged. Its private helpers construct the groupoid
on test points and extract the canonical polynomial's monicity, degree and Cayley–Hamilton
property. The proof compares every coefficient, lifts to the equalizer subring, verifies all
three displayed finite-sum identities, and descends the root through the target identity
section.

Added `Sheaf.AlgebraicGeometry.AffineGroupoidCanonicalNormCharts`, proving the comparison
between the canonical determinant norm's tensor-localization characterization and the
actual affine-open section norms. Its private helpers identify the two localization scalar
actions on fractions, transport bases, and use `principalFreeNorm_spec` uniqueness.
The public theorem then applies `principalFreeNorm_affineOpen` and the norm matrix formula
on a free affine chart. A finite basis is reindexed by `Fin`; no nonzero section-ring
hypothesis is introduced. This includes zero rings, empty inverse images and empty bases.

Added private imports of the new chart module and `Mathlib.Algebra.Polynomial.Eval.Degree`
to the item. The new module privately imports the existing principal basis cover and
principal-free norm modules, and the finite-free basis API. Updated the item's DAG proof
and proof dependencies, and added the node of the proved chart comparison.

Both modules were compiled together with `lcompile.py --all`: the chart comparison in
9.6 seconds and the item in 17.8 seconds, with no errors. The two item lint warnings
were then repaired without changing its public signature; delivery performs the final
compile and axiom checks.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.affineGroupoid_constantRank_norm_annihilator`
(node `lem-a1-affine-groupoid-constant-rank-norm-annihilator`).

Also proved the new lower comparison theorem
`AlgebraicGeometry.affineGroupoid_canonicalNorm_chart_formula`
(node `lem-a1-affine-groupoid-canonical-norm-charts`).

Original holes: 1. Closed: 1. Remaining in the item: 0. Added: 0. Split off: 0.
Every new private helper has a complete proof or construction. The proof uses existing
named dependencies, including their currently unproved statements, as stage 3 requires;
it does not claim to close those dependencies.

## No longer needed

None. All original proof dependencies remain used, and no module, node or import is pruned.
No additional characteristic-polynomial expansion or Cayley–Hamilton lemma is needed:
the existing canonical norm theorem and `Polynomial.Monic.as_sum` suffice.

## Where the brief, the DAG or earlier work was wrong

The plan omitted two Lean interface conversions. The canonical norm is characterized using
principal tensor-localization bases, whereas polynomial norm invariance requires norms on
actual affine-open section algebras. The existing principal-free norm uniqueness and
affine-open comparison lemmas bridge them. The principal-basis module also bundles a
localization scalar structure that must be identified with the usual fraction action.
Finally, `Scheme.IsGroupoid` supplies explicit scheme laws, whereas polynomial invariance
requires an existential groupoid on each test scheme; the private `pointGroupoid`
construction supplies that structure directly. These are completed proof steps, with no
statement or definition repair.

## New nodes

`lem-a1-affine-groupoid-canonical-norm-charts` states and proves the general affine norm-chart
comparison needed for the polynomial extension. Its sources are Stacks Tags 02DU(1),
02DV(1),(3), and 03BJ. Searches of LeanSearch, LeanFinder, Loogle, Mathlib and the project
found the supporting matrix/localization results and principal norm APIs but no direct
comparison statement. It has its own new module and Lean attachment. No change record is
needed: no existing public signature, definition, attribute or public import changes.

## Second reading by B2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
