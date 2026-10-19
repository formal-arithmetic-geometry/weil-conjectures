## What changed

Proved `WeilConjectures.completedCoefficientMap_existsUnique` in
`Sheaf.Paper.FiniteFreeCompletedScalarComparison` without changing its signature.
The quotient transition equality gives a natural transformation of ring-sheaf towers.
The inverse-limit lift supplies the map after forgetting commutativity; full
faithfulness lifts it back to commutative ring sheaves. Joint monicity of the limit
projections proves uniqueness. The proof compiles with independent scheme and
coefficient universes. On retry, the sandbox was checked against the current shared
source: its only Lean difference is this theorem body. A fresh single-file check
through `lcompile.py` finished with exit code 0 and no diagnostics.

## Proved and sorry left

Closed one of the original six holes:
`WeilConjectures.completedCoefficientMap_existsUnique`.
No holes added and no statements split off.

Five original holes remain, all attached to
`lem-weil-finite-free-completed-scalar-comparison`:

- `WeilConjectures.completedScalarChainComparison_existsUnique`
- `WeilConjectures.completedScalarComparison_existsUnique`
- `WeilConjectures.completedScalarIdentityMultiplication_existsUnique`
- `WeilConjectures.completedScalarIdentityUnit_existsUnique`
- `WeilConjectures.finiteFreeCompletedScalarComparison`

## No longer needed

None. All imports are retained for the original remaining obligations and their
recorded proof route. The completed coefficient-map proof uses the existing
`integralScalarQuotientMap_transition` declaration, constant sheafification,
full faithfulness of forgetting commutativity, and the inverse-limit API.

The original remaining proof obligations are retained rather than moved to new
statements. Investigation of the identity case found a sectionwise multiplication
construction in `RingedTopoiDerivedPullback`, but adapting its naturality and its
pure-tensor normalization to this module's independently sized coefficient and site
universes was not finished. No exploratory helpers are included in the delivery.

## Where the brief, the DAG or earlier work was wrong

The retained draft did not compile: its extensionality argument stopped at a site
object instead of a coefficient, and its full-functor preimage required explicit
source and target objects. Both are fixed. The similarly named
`integralCompletedScalarMap_existsUnique` only supports equal scheme and coefficient
universes, so it cannot replace the theorem proved here.

## Second reading by N2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
