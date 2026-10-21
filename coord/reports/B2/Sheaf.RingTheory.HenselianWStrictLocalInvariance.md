## What changed

Proved `isWStrictlyLocalRing_iff_quotient_of_henselianRing` with its signature unchanged.
Only the assigned Lean module and its proof-dependency record change. Added three proved
private helpers for stalk sections, clopen gluing of sections, and ascent of w-locality.
The forward direction uses quotient-localization and the existing strictly henselian
quotient theorem. The reverse direction follows the node's connectedness, section-gluing,
smooth-lifting and maximal-local recognition argument. The node now records the actual
ring tensor-product base-change route and disjoint-open coproduct gluing.

Read Bhatt--Scholze Lemmas 2.2.9, 2.2.13 and 2.2.15 in the supplied PDF. Searched with
LeanFinder, Loogle and Mathlib grep through msearch.py; no direct invariance theorem was
found. The adopted finite-algebra stability theorem could shorten the forward direction,
but the delivered proof instead uses the original quotient-localization dependencies.

Validation: lcompile.py compiled the retained proof cleanly in 5.8 seconds. On resumption,
preflight required a change record for file-level open commands. Scoped these commands to
the private helpers and used explicit TensorProduct notation in the public proof; the
interface checker now reports no changes, and lcompile.py compiled cleanly in 5.2 seconds.
The delivery runs compilation and the declaration/axiom probes again.
The zero ring, I=0, and empty closed-point space require no extra hypotheses; the finite
clopen refinement permits an empty index set. No source-library module was changed.

## Proved and sorry left

Closed 1 of 1 holes: `isWStrictlyLocalRing_iff_quotient_of_henselianRing`
(node `lem-zl-henselian-wstrict-local-invariance`). Added 0 holes; split off 0 statements.
There is no `sorry` in any delivered Lean file. The proof uses the existing named theorem
`Algebra.Smooth.exists_lift_of_henselianRing` from
`Sheaf.RingTheory.HenselianSmoothAlgebraLifting` (node
`lem-trf-henselian-smooth-algebra-lifting`), whose existing proof remains `sorry`.
This is a proof from existing dependencies, not a claim that the transitive closure is closed.

## No longer needed

Removed proof imports:

- `Mathlib.AlgebraicGeometry.Sites.MorphismProperty`
- `Mathlib.AlgebraicGeometry.Pullbacks`
- `WeilConjectures.RingTheory.HenselianFactorizationCriterion`
- `Mathlib.AlgebraicGeometry.Scheme`
- `Sheaf.Topology.WLocalComponents`
- `Mathlib.RingTheory.Smooth.Basic`

The removed Mathlib imports are supplied through imports the proof does use. The removed
non-Mathlib modules are not needed by this argument: `HenselianRing.jac` already supplies
Jacobson containment, and the source library directly supplies closed-point injectivity
into connected components and their total disconnectedness. Removed their corresponding
proof dependencies `lem-weil-pbc-henselian-factorization-criterion` and
`det-pe-wlocal-components`.

Also removed `lem-weil-pbc-etale-covering-base-change` and
`lem-weil-pbc-fibre-product-affine-spectra` from the node's proof dependencies. Algebraic
base-change instances handle the tensor products directly, so no scheme pullback or
quotient-tensor comparison is needed. Removed the three obsolete tool_uses entries for
the factorization criterion, component package, and scheme covering base change.
No module is withdrawn: these removals are local to this proof, and other consumers remain.

Newly used existing Mathlib leaves are `lem-weil-pbc-faithfully-flat-base-change`,
`lem-weil-pbc-etale-ring-base-change`,
`lem-weil-pbc-flat-surjective-spectrum-faithfully-flat`, and
`lem-weil-pbc-scheme-morphism-gluing`. The clopen gluing uses Mathlib's coproduct universal
property for disjoint opens, the disjoint-cover specialization of scheme morphism gluing.

## Where the brief, the DAG or earlier work was wrong

No statement defect. The plan requested the factorization criterion only for a field
already in `HenselianRing`. Its topological component package and scheme-level base-change
translation can be replaced with proved source/Mathlib APIs. No unit-level route changes.
No definitions, public signatures, target statements, or public imports changed.

## Second reading by B2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
