## What changed

Proved `WeilConjectures.rationalTensorScalarComparison_existsUnique` in
`Sheaf.Paper.DerivedPullbackTensorHom`, preserving its signature and its normalized
component formula. First construct the restricted integral natural isomorphism by
conjugating `scalarTensorOrdinary` with the three scalar-completion comparisons.
Localize its components, prove naturality on pairs of pure tensors using the
integral naturality equation, and extend to arbitrary arrows by tensor induction
in both variables. Component extensionality proves uniqueness.

Added proved private helpers `prod_hom_heq`, `rawBilinearIso_existsUnique`,
`bilinearAdd`, `bilinearPost`, `bilinearPre`, and `rationalTensor_spec`. The last helper exposes
the existing bilinear specification before the local irreducibility boundary;
it avoids repeatedly unfolding the chosen rational tensor and its dependent
module structures. Explicit additive-map equations avoid expensive unrestricted
simplification. The complete file compiled in 54.8 seconds with no warnings.
No public signature, definition, attribute, import, or file-level
option changes.

## Proved and sorry left

Closed one of the seven original holes:
`WeilConjectures.rationalTensorScalarComparison_existsUnique`.
Added zero holes; split off zero statements. The proof uses existing dependency
specifications, including the still-unproved rational tensor construction, as
permitted by stage 3. This does not assert that its transitive axiom closure is
already free of sorry.

The six remaining original holes, all attached to
`def-weil-derived-pullback-tensor-hom`, are:

- `WeilConjectures.rationalDerivedPullback_existsUnique`
- `WeilConjectures.rationalDerivedTensor_existsUnique`
- `WeilConjectures.rationalDerivedInternalHom_existsUnique`
- `WeilConjectures.commonStageDerivedPullback_existsUnique`
- `WeilConjectures.commonStageDerivedTensor_existsUnique`
- `WeilConjectures.commonStageDerivedInternalHom_existsUnique`

## No longer needed

None. All existing imports remain needed by the public constructions or the
existing proofs. No nodes or modules are withdrawn. No new proof dependencies
are introduced: the proof follows the existing declaration docstring using the
already imported integral scalar-comparison and rationalization specifications.

## Where the brief, the DAG or earlier work was wrong

The item node is a definition node with an empty proof-step list. Its declaration
docstring supplies the actual rational tensor-comparison argument, realized here.
The earlier J7 report recorded this comparison as an isolated successful proof
that exceeded the full-file compile limit. The retained sandbox contained a
partial attempt with a dependent-structure mismatch and an excessive unfolding
path. The private specification boundary and explicit additive equations repair
those issues without splitting the module or raising its compilation limit.

The current blueprint file is
`literature/blueprint/latest/blueprint/sec-proetale-coefficients/` followed by
`sk-prop-sf-open-closed-triangle/def-weil-derived-pullback-tensor-hom.md`.
It now defines ambient condensed-coefficient operations uniformly, whereas this
existing module formalizes the earlier finite/integral/rational/common-stage
constructible operations. The node already records this discrepancy in
`blueprint_update`. This proof preserves the existing declaration and does not
claim to complete that separate interface migration or authorize withdrawal of
any of its consumers.

## Second reading by G5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
