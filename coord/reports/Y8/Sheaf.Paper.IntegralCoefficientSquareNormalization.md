## What changed

Filled `AlgebraicGeometry.ProEtale.IntegralCoefficientSquare.integral_coefficient_square_normalization` in `Sheaf.Paper.IntegralCoefficientSquareNormalization` without changing any public statement or definition. Private proved helpers construct the normalized quotient pushouts, the scalar square and generator-normalized chain comparison, and transport flatness and K-flatness through the existing section-module equivalences. The completed identification and exact scalar extension come from the proved admissible-scalar theorem. Module inverse-image flatness and the generic flat-term K-flat functor theorem give the two pullback conclusions. Updated the node proof and dependencies to this implementation.

Proof imports were added for the extension-along-isomorphism generator formula, change-of-scalars square, section module encoding and tensor comparison, inverse-image flatness, and the generic flat-term K-flat theorem. Private existing quotient and isomorphism-transport helpers are accessed with proof-only `import all`. All original public imports remain verbatim.

## Proved and sorry left

Closed the one original hole: `AlgebraicGeometry.ProEtale.IntegralCoefficientSquare.integral_coefficient_square_normalization` (node `lem-sfb-integral-coefficient-square-normalization`). Holes added: zero. No `sorry` remains in the delivered module. No new theorem is split off. Every private helper has a complete Lean proof.

The quotient-pushout, scalar-comparison and scalar-restriction K-flat calculations compile separately. The complete file compiles cleanly in 34.4 seconds through `lcompile.py`; the final assembly is proved generically before specializing to the concrete coefficient ring. Delivery preflight checks the landed packet and axioms.

## No longer needed

Removed the direct proof imports `Sheaf.NumberTheory.Padics.IntegersProfiniteTower`, `Sheaf.NumberTheory.Padics.IntegersCosetBasis`, `Sheaf.Paper.CompactAdicContinuousIdentification`, and `Sheaf.CategoryTheory.ConstantLeftModuleInverseImage`, and their direct node dependencies `lem-sfb-integers-profinite-tower`, `lem-sfb-integers-coset-basis`, `lem-sfb-compact-adic-continuous-identification`, and `lem-pe-constant-left-module-inverse-image`. The first three supply topology already encapsulated in admissible scalar realization; the last is superseded here by the canonical Cartesian coefficient comparison and its existing exactness instances. The separate node `def-sfb-constant-sheaf-scheme-pullback-comparison` is also unnecessary for this proof, because constants were already defined by pullback from the point. These dependencies may remain needed transitively or by other consumers; no module is withdrawn.

The general ringed-topos K-flat module remains used for its proved invariance-under-isomorphism helpers. Its full pullback theorem is replaced here by the already proved internal inverse-image flatness theorem and the general flat-term K-flat functor theorem, using the same inverse-image route.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The plan did not need to repeat the topology and normalized completion identification that admissible scalar realization now proves. Its quotient conclusion was recorded for modules; the ring-sheaf pushout required spelling out the universal property from its proved projection-kernel argument. The section/internal universe parameters must be kept independent in the general K-flat comparison.

Proof-local elaboration settings and attributes are documented in `coord/changes/Y8-integral-coefficient-square-proof-context.md`. No public interface or consumer adaptation is required; `tools/downstream.py` reports zero downstream modules for this item.

## Second reading by Y8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
