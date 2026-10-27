## What changed

Filled the four existing theorem proofs in
`lean/Sheaf/SixFunctors/CoefDualizingConstruction.lean`, preserving each signature.
The construction applies the existing Verdier-preservation theorem to the regular
coefficient unit, identifies internal Hom from the unit with the identity by
uniqueness of right adjoints, and transports bounded constructibility and the Tor
interval. The interval is widened to `[min c d,d]` to ensure ordered endpoints,
including on the empty scheme.

The mate equation follows from the normalized mate definition, counit naturality,
and injectivity of the inverse adjunction Hom bijection. Representing-object
uniqueness is a proved private generic Yoneda calculation. Factorization uses the
composite-adjunction counit formula and the exact published unbounded scalar
composition theorem after checking Noetherianity and the scalar-extension D+ bound.

Used `import all` for the already proved helpers of
`ExceptionalCoefficientComparison`, `WeilVerdierPreservationStrata`, and
`EtaleCompactSupportCoefficientChange`. These remain proof imports and expose no
new public interface. Two private helpers added here have complete proofs.
Updated `lem-coef-dualizing-construction` to record the actual argument.

Validation: all four signatures compared verbatim against the shared source;
the file compiled successfully through lcompile.py before the final import cleanup.
Delivery runs the final compile and axiom checks. Empty schemes, equal quotient
levels, positive level one, nonflat quotient maps and potentially reversed
vacuous Tor intervals introduce no extra hypotheses.

## Proved and sorry left

Closed all four original holes (node `lem-coef-dualizing-construction`):

- `AlgebraicGeometry.Etale.coefDualizingConstruction`.
- `AlgebraicGeometry.Etale.coefDualizingConstruction_mate`.
- `AlgebraicGeometry.Etale.coefDualizingConstruction_representing`.
- `AlgebraicGeometry.Etale.coefDualizingConstruction_factorization`.

No sorry remains in the delivered module; no holes or new modules were added.
This closes 4 of 4 local holes, with 0 split off. Existing imported theorem holes
remain separate items; this is a proof from their stated declarations.

## No longer needed

Removed these redundant direct proof imports:

- `WeilConjectures.Compactification.NagataCompactification`.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`.
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`.
- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`.
- `Mathlib.Analysis.Normed.Unbundled.SpectralNorm`.
- `Mathlib.Analysis.Normed.Unbundled.RingSeminorm`.
- `Mathlib.Topology.Algebra.Valued.LocallyCompact`.
- `Mathlib.AlgebraicGeometry.Noetherian`.
- `Mathlib.RingTheory.Ideal.Quotient.Defs`.
- `Mathlib.RingTheory.Ideal.Operations`.
- `Mathlib.RingTheory.DiscreteValuationRing.Basic`.
- `Mathlib.RingTheory.LocalRing.Basic`.

The node no longer directly needs:

- `lem-weil-l-adic-extension-absolute-value`,
  `lem-weil-l-adic-extension-integers-dvr`, and
  `lem-weil-valued-dvr-finite-quotients`: the existing finite coefficient-ring
  theorem supplies finiteness, without repeating valuation theory here.
- `lem-pur-derived-change-of-rings`: scalar extension is already defined, and
  its needed boundedness is supplied by the recorded scalar/tensor calculation.
- `lem-amb-etale-compact-comparisons`: factorization uses the specified unbounded
  composition map directly. Removed this obsolete top-level tool approval.
- `lem-sf-compact-coefficient-composition`: the exact existing ordinary-etale
  unbounded scalar-composition theorem supplies the equation without introducing
  tensor presentation models.

These are removed from this node's proof dependencies, not withdrawn from the
library. Their public statement imports are retained because the assigned module
still uses their definitions and public interface. No entire module is claimed
pruned from the targets' import closure.

## Where the brief, the DAG or earlier work was wrong

The planned factorization appeal names a bounded-below coefficient theorem with
explicit CoefficientTensorModel arguments. The required equation is already
stated exactly by `etaleCompactScalarComposition` in
`Sheaf.Paper.EtaleCompactScalarCoherence` (node
`lem-pur-etale-compact-scalar-coherence`); the private proved scalar-extension
lower-bound helper provides its second D+ hypothesis. Using it avoids a further
comparison bridge. This off-route tool serves only the existing coefficient
composition step and does not bypass any blueprint unit statement or step.

Coefficient finiteness is also already supplied by
`Padic.finite_coefficientExtensionRing` (node
`def-weil-l-adic-coefficient-extension`), registered by the existing
`finiteCompositionCoefficient` instance. No statement or definition repair,
consumer adaptation, new node, axiom, or chosen data was needed.

## Second reading by Y2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
