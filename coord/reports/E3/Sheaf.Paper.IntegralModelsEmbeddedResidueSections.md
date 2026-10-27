## What changed

Replaced the proof hole in `AlgebraicGeometry.ProEtale.integralModelsEmbeddedResidueSections`
by a proof from the existing `ConstantCompletion.flat_and_quotients` theorem and the new
`integralModelsEmbeddedCompletionDiagram`. The public statement and existing public import
are unchanged. The two proof imports are private imports. The principal ideal image argument is
proved locally, without exposing another module's private declarations.

To control elaboration, the proof uses a generic ring-sheaf transport lemma and an
existential wrapper, keeping the large coefficient-map terms out of the algebraic proof.
The completion definition is locally irreducible; section formulas are simplified
explicitly instead of unfolding the limit. The proof supplies the Noetherian instance
of the lifted integer ring explicitly. It
specializes both completion kernel formulas at exponent one, reduces the range
of all ideal elements to the single generator, transports the kernels and surjectivity
through evaluated ring isomorphisms, constructs the global section using the inverse source
isomorphism, and derives the residue square from the completion lift/projection equation.
The source and completed generators agree by the scalar comparison square.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.ProEtale.integralModelsEmbeddedResidueSections` (one of one original
holes). Its complete Lean proof uses the existing generic completion theorem, whose proof
is an existing project obligation.

Added one hole in
`AlgebraicGeometry.ProEtale.integralModelsEmbeddedCompletionDiagram`
(node `lem-sfb-embedded-integral-completion-diagram`). It concerns only coefficient-object
and map identification; it makes no assertion about kernels, surjectivity or generators.
Thus this delivery is a decomposition: one original hole closed, one lower hole added,
net zero holes. There is no hole left in the item module and none inside a definition.

The new comparison is strictly a step of the original argument: its conclusion does not
supply any of the section-kernel or local-surjectivity conclusions of the item. Those are
proved by the algebra and sheaf transport argument in the item, rather than included in
another name for the same obligation. The docstring and node describe its proof from the
already stated projection-normalized integral limit and monoidal constant comparisons.

## No longer needed

No existing import was removed, and no module is withdrawn. The item's old proof route no
longer uses `lem-integral-coefficient-ext-comparison`
(`Sheaf.Paper.IntegralCoefficientExtComparison`),
`det-prop-sfb-qlbar-colimit-x-integral-limit`
(`Sheaf.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit`), or
`det-prop-integral-criterion-constant-coefficients`
(`Sheaf.AlgebraicGeometry.IntegralConstantCompletion`). The embedded normalized completion
already supplies the appropriate coefficient tower, so comparison to spectral coefficients
and a second specialization of completion are unnecessary for this route. This is only a
proof-dependency pruning claim; these modules may still have other consumers.

The definition node `def-sfb-embedded-integral-model-coefficients` remains a statement
dependency and a dependency of the new diagram. `sk-prop-sfb-qlbar-colimit-x` remains needed
by the diagram. `lem-weil-pbc-constant-completion-equivalence` is used directly for the
kernel formulas. The integral-models unit route is retained.

## Where the brief, the DAG or earlier work was wrong

The old proof plan suggests passing through the spectral/embedded module-category
comparison. That theorem only gives a module equivalence preserving constructibility; it
has no normalization for the actual scalar and residue maps required here. Using it as
though it gave these squares would not prove the item. The normalized embedded integral
limit is the shorter route, with its remaining section-ring map comparison stated
explicitly. No existing statement or definition is changed.

Edge cases: the principal-kernel transport holds for the zero ring and for zero generators;
the proof uses no nonempty object or nonempty scheme hypothesis. The comparison argument
uses finite quotients, exact constant inverse image and an equivalence of sites, and does
not claim that arbitrary inverse image preserves infinite limits. Sectionwise surjectivity
is invoked only for the existing generic constant completion quotient theorem.

## New nodes

`lem-sfb-embedded-integral-completion-diagram`, in
`dag/nodes/sec-six-functors-basics/lem-sfb-embedded-integral-completion-diagram.json`,
records the scalar-compatible identification of the actual reconstructed small-site
coefficient diagram with the canonical constant completion diagram. Its four isomorphisms
are constrained by the three map squares. It isolates the coefficient-identification part
of paragraph (1); the upper proof supplies both principal kernels and surjectivity.
No change record is required because no existing public interface or definition changes.

## Second reading by E3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
