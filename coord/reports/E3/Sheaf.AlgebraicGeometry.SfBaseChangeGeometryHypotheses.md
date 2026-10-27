## What changed

Proved `AlgebraicGeometry.sf_baseChange_geometry_hypotheses` in
`Sheaf.AlgebraicGeometry.SfBaseChangeGeometryHypotheses`, preserving its full signature,
all public imports, and its seven-step mathematical route. Added only a private proof import
of `Mathlib.Algebra.CharP.CharAndCard` and three proved private helpers:
`dimension_empty`, `field_extension_dimension_le`, and `corner_geometry`.

The corner helper derives characteristic p from the cardinality of the finite base field,
transports it to the closure, and maps the unit ell through global sections to each stalk.
The field-extension helper combines the existing matching affine covers, tensor symmetry,
affine dimension preservation, subspace monotonicity, and the open-cover dimension bound.
For an arbitrary field-valued point, the residue-field equivalence gives its factorization;
`pullbackLeftPullbackSndIso` then identifies its fibre with the scalar extension of an ordinary
fibre. Thus the natural bound chosen before the geometric point works uniformly. Empty
schemes and fibres are handled by the absence of irreducible closed subsets. Properness uses
the chosen square's second projection equation, and Nagata's compactification has a
quasi-compact open factor by `Compactification.quasiCompact_openImmersion`.

Updated only the node's proof text and proof origin to record these constructions precisely.
No definitions, public signatures, consumers, adopted source files, or unit routes changed.

Searches through the required `msearch.py` interface used LeanFinder for the uniform geometric
fibre bound, Loogle for proper and locally-finite-type morphisms, and grep for geometric fibre
dimension declarations. The results supplied standard finite-morphism and quasi-compactness
facts, not a replacement for this assembly. Reading the recorded dependencies supplied all
non-elementary ingredients; no new public lemma was needed.

Validation: the public theorem signature was compared verbatim with the shared source;
all Lean lines satisfy the 100-character limit. The module is checked through `lcompile.py`
and the delivery's compiler/axiom probes.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.sf_baseChange_geometry_hypotheses`
(blueprint: `lem-sf-bc-geometry-hypotheses`).

Original holes: 1. Closed: 1. Added: 0. Split off: 0. Remaining in the module: 0.
Every private helper is proved. No other module is delivered and no new hole is introduced.

## No longer needed

None. All existing mathematical proof dependencies are used. No imports, declarations,
nodes, or modules are withdrawn; there is no pruning claim.

## Where the brief, the DAG or earlier work was wrong

The DAG's final step described quasi-compactness of the open factor as included in
`Compactification`. The actual structure records open immersion and properness; its API
proves quasi-compactness of the open factor from `QuasiCompact h`. The proof now invokes
that theorem explicitly, as the item's existing docstring already anticipated.

The affine-cover dependency requires a nonempty ordinary fibre, so the empty case is proved
separately. The geometric-point quantifier permits any algebraically closed field-valued
point, not only a chosen algebraic closure of a residue field; the proof uses the actual
residue-field map and works for arbitrary field extensions. The node proof now records this.

## Second reading by E3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
