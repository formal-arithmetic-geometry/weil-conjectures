## What changed

Replaced the hole in `WeilConjectures.compactSupportProjectionFormula_fieldStages`
by an assembly from the integral-stage laws and two smaller transport statements.
The theorem's signature and its existing public import are unchanged.

Private proofs perform the actual mathematical work for invertibility and
naturality. The coefficient projection square transports invertibility by
functoriality and cancellation of its endpoint isomorphisms. Uncurrying the
specified mate proves two-input naturality. The residue Tor criterion makes
every integral model an admissible second input; raw rationalization retains
these objects literally. At the common stage the two inputs are moved to their
finite coefficient compositum, where invertibility is already proved, then
naturality at the two isoToStage isomorphisms returns it to the original pairs.
This works for the original coefficient field and every field in the closure.

Added `CompactSupportProjectionCoherence`, the four existing comparison equations
without the invertibility and naturality fields, and two theorems transporting
these equations through rational localization and common-stage inclusion.
Only the transport of these four equations remains unfinished. A proof-only
`import all Mathlib.Logic.Small.Defs` exposes `Shrink` for the definitional
identification of the cached finite-stage category with the raw rational category.
An explicit type conversion proves that identification by reflexivity. The
transparency options stay enabled, and no generated auxiliary names are used. Source-level checks
verified that the original theorem signature is identical, all four comparison
field signatures are copied verbatim, and every node proof-dependency list equals
the union of its proof-step dependencies.

Validation: all four modules were checked with lcompile; the complete item proof
compiled in 18.9 seconds. The delivery checks the final packet again.

## Proved and sorry left

Closed the item's original hole in
`WeilConjectures.compactSupportProjectionFormula_fieldStages`
(node `lem-sf-projection-field-stage-laws`). Its proof is complete relative to
the imported declarations. Proved the private helpers
`coefficient_projection_isIso`, `projection_natural`, `projection_isIso_of_iso`,
`coherence_of_laws`, `integral_finiteTor`, `rational_projection_isIso`,
`rational_projection_laws`, and `common_projection_isIso`.

Added exactly two holes, both whole proofs of named public theorems:

- `WeilConjectures.compactSupportProjectionCoherence_rational`, node
  `lem-sf-rational-projection-comparison-equations`, in
  `Sheaf.Paper.RationalProjectionComparisonEquations`.
- `WeilConjectures.compactSupportProjectionCoherence_common`, node
  `lem-sf-common-projection-comparison-equations`, in
  `Sheaf.Paper.CommonProjectionComparisonEquations`.

The item has zero remaining holes. This is a decomposition: one upper hole
closed, two lower holes added, hence net -1 before closure pruning. The new
statements assert only four map equations, not invertibility or naturality, and
have the corresponding lower-stage equations as hypotheses. The Lean assembly
proves the two other fields and supplies these hypotheses from the existing
integral laws. No definition contains a hole.

## No longer needed

The planned dependency `lem-sf-concrete-projection-field-descent`, module
`Sheaf.Paper.ConcreteProjectionFieldDescent`, is not needed by this proof and
was not imported. Invertibility uses `SixFunctorExchangeComparison.projection`
directly, and naturality uses the specified natural transformation. This avoids
the bundled descent theorem's additional tensor-cocycle hypothesis, which is
unnecessary for those two calculations. The four comparison-equation transports
are recorded separately by the two new statements.

The original module had one public import, which is retained. No existing
module is withdrawn. The other declared proof dependency, integral-stage laws,
is used. The updated DAG records the residue Tor criterion and the two exact
remaining transport steps.

## Where the brief, the DAG or earlier work was wrong

The planned field-descent theorem requires `TensorCoherence S.closure`, while
this item's operation datum does not supply that proposition as a field.
Its invertibility and naturality consequences do not require this hypothesis;
the proof uses the component square and the natural mate directly. Tower
independence is not needed to prove invertibility at any fixed common-stage
pair: one compositum and naturality along its presentation isomorphisms suffice.

The current rational category is raw scalar localization, with unchanged
objects. An induction through rational integral-model generators is therefore
unnecessary for the statement actually formalized here.

No statement was changed. The residue criterion used here is a coefficient Tor
statement; no Verdier duality or biduality theorem is used. The unit's route is
preserved: integral projection laws, rational localization, then common finite
coefficient fields.

A read-only traversal of statement and proof dependencies also found the
pre-existing reference cycle `lem-pc-ring-hom-extension-differential` ->
`lem-pc-ring-hom-extension-differential-adjacent` ->
`lem-pc-ring-hom-extension-differential`, already reachable from the original
field-stage node. No cycle returns to any delivered node. Those unrelated
records were not changed.

## New nodes

`def-sf-projection-comparison-equations` records precisely the compactification,
composition, pentagon and proper fields of `CompactSupportProjectionLaws`, with
their original second-input predicate. It is a concrete Prop structure, not an
existence witness or a weakened replacement for the original laws.

`lem-sf-rational-projection-comparison-equations` is the equality-transport step
from integral to rational coefficients for a higher-operation datum. Its source
is the Compatibility paragraph of the current field projection proof, together
with the coherence sentence of the interface proof. The docstring and node give
the canonical tensor, pullback and support comparison cancellations separately.

`lem-sf-common-projection-comparison-equations` is the equality-transport step
from all finite field stages to the common-stage category. Its source is the
same Compatibility paragraph and the common finite coefficient field paragraph.
Its proof records common-field representatives, canonical comparisons,
compositor and proper-counit compatibility, and return to the original pairs.

LeanSearch found general localized monoidal pentagons but no theorem for these
support compositors; LeanFinder returned unrelated scheme localizations;
Loogle and grep supplied no assembled projection comparison theorem. Existing
`ProjectionFormulaCoherence` assumes a stronger six-functor datum and imports
the parent projection formula, so it cannot be used here.

Edge cases checked: zero and torsion objects, empty schemes, repeated fields and
identity enlargements, arbitrary finite extensions, and nonseparated structure
morphisms. All morphism hypotheses and compactification transports are copied
verbatim from the existing four law fields. The common-field construction uses
a finite compositum and imposes no nonemptiness condition on the schemes.

## Second reading by S3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
