## What changed

Replaced the proof of `CochainComplex.PerfectDualScalar.perfect_dual_scalar_calculus`.
Its signature is unchanged. The proof constructs the cochain scalar-dual map,
proves its finite-projective inverse, signed evaluation square, naturality,
identity, tower and localization formulas. A separate proved theorem,
`CochainComplex.PerfectDualScalar.perfect_dual_derived_transport`, constructs the
canonical derived comparison from evaluation and proves its five compatibility
clauses. The private monoidal structure uses the recorded tensor and unit
isomorphisms directly, avoiding generic inverse selection during type checking.
No source-library declaration or existing definition was changed.

## Proved and sorry left

Closed one original hole:
`CochainComplex.PerfectDualScalar.perfect_dual_scalar_calculus`.
The new theorem `CochainComplex.PerfectDualScalar.perfect_dual_derived_transport`
is also fully proved. No holes are added or left in either delivery module.
Existing imported statements retain their own proof status; this delivery uses
the declared scalar tensor coherence and projective Hom evaluation model.

## No longer needed

The declared dependency `lem-sf-finite-projective-dual` is not used: Mathlib's
`dualTensorHomEquiv`, ordinary-dual finite/projective instances, and the
Hom-to-single equivalence supply the inverse and degreewise properties.
`lem-pc-ring-derived-map-representative` is also unnecessary: the derived map is
the curry of transported evaluation, whose naturality follows by uncurrying.
Thus the homotopy-lifting, representative-independence and cocycle route in the
old plan is omitted. No existing module is withdrawn; other consumers may still
need these nodes. The old proof-only entries
`def-weil-finitely-generated-module`, `def-weil-pbc-projective-module`, and
`def-pc-perfect-ring-complex` are omitted from the parent's proof dependency list:
their notions remain in its unchanged statement dependencies; the actual perfect
pairing argument is recorded in the new theorem's node.

Removed exploratory proof imports `Mathlib.LinearAlgebra.Dual.Lemmas`,
`Mathlib.Algebra.Homology.DerivedCategory.KProjective`, and
`Mathlib.Algebra.Module.LocalizedModule.Exact`. Contraction supplies the dual API,
and the localization functor exposes its exactness. The full perfect-subcategory
monoidal construction is private because the existing specialized helper fixes
the default derived-category instance, whereas this statement quantifies over
arbitrary `HasDerivedCategory` instances.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement discrepancy was found. The DAG's finite dual-family
inverse can be replaced by existing tensor-dual equivalences. Its representative
route is longer than the canonical evaluation construction. The DAG copies and
Lean proof docstrings now describe the actual argument. The blueprint unit route
is unchanged. The localization proof works for zero rings and subsets containing
zero; the scalar proof does not assume flatness or a free basis. Odd degrees are
handled by the given signed evaluation and Hom differential formulas.

## New nodes

`lem-pod-perfect-dual-derived-transport` records the separate canonical perfect
dual scalar comparison and its compatibility with bounded projective models.
It is proved in `Sheaf.Algebra.Homology.PerfectDualDerivedTransport`; it leaves no
new item with a hole. Its statement assumes only the chain evaluation data and the two term
properties used in transport, and omits all concrete chain-map constructions and localization
assertions. Its source is the coefficient-ring computation in point duality,
with the projective Hom calculation of Stacks Tag 0A66 and perfect duality of
Tag 0FNG. Recorded searches found component APIs, but no theorem with all fixed
model, evaluation, identity and tower equations. No change record is required
because no existing statement, definition or consumer interface changed.

## Second reading by Q6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
