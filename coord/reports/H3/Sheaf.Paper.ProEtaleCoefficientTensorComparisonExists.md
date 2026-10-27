## What changed

Proved `AlgebraicGeometry.Scheme.CoefficientTensorTransport.tensorComparison_exists`
without changing its signature or either supplied tensor model. The proof uses
`SheafOfModules.ringIso_tensor_transport` for preservation of flat K-flat complexes
and the natural signed-total tensor comparison. A proved private helper obtains
full faithfulness of restriction to flat K-flat representatives from the existing
resolution and resolving-representative whiskering theorems. The existing
`tensorComparisonDescent` theorem then descends the comparison; its inverse has
exactly the direction required by the item.

The node's proof, proof dependencies and proof origin now record these actual
steps. All added imports are private proof imports. No shared definition,
statement, source-library module or public import was changed.

## Proved and sorry left

Closed 1 original hole:
`AlgebraicGeometry.Scheme.CoefficientTensorTransport.tensorComparison_exists`
(node `lem-pbc-coefficient-restriction-tensor-comparison-existence`).
Added 0 holes. There are no remaining `sorry` declarations in the delivered module.
No new intermediate obligations were split off. The complete proof compiled in
26.7 seconds; the final delivery check also validates the warning-free version.

## No longer needed

The item does not need `lem-weil-pbc-site-derived-tensor-descent`
(`Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`) as a
proof dependency: its two tensor models are already supplied, and the existing
representative comparison descent theorem suffices. It was not imported by the
original file, so no import is removed. Its declarations remain available to
other consumers. Both original public imports are retained.

No reconstruction of ordinary scalar restriction, of its exactness, of the
signed total tensor comparison, or of derived tensor models is needed. These
are supplied by existing declarations. The geometric input `aY` is unnecessary
for this existence-only clause, but its binder is preserved verbatim.

## Where the brief, the DAG or earlier work was wrong

The original plan was mathematically appropriate but omitted the existing
`lem-sfb-ring-isomorphism-tensor-transport` declaration, which already packages
its representative-level content. It can be applied directly on the original
site with object universe u+1 and morphism universe u. This is a generic tool
from the six-functor unit; the proper-base-change unit supplies no replacement
for ring-isomorphism tensor transport. The unit's realized statement and proof
steps are preserved.

The proof uses neither the separate compatibility theorem nor any assertion
that arbitrary comparisons are normalized. The sectionwise pure-tensor map and
signed total comparison come from the existing transport theorem. Exact
restriction's localization factorization is invertible on every complex, so the
descent theorem's two invertibility requirements impose no extra assumptions.
The constructions permit empty sites and zero coefficient rings, and impose no
boundedness or constructibility assumptions.

## Second reading by H3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
