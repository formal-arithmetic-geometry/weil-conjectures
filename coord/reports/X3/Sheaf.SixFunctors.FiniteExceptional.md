## What changed

Filled six proof bodies in `Sheaf.SixFunctors.FiniteExceptional`, preserving all public
statements, definitions and public imports. The quotient composition and identity proofs use
constant-sheaf functoriality and quotient induction. The pullback composition proof is the
existing constant-ring coefficient-composition identity.

Scalar reduction uses the proved general finite-ring scalar-extension lemmas
`scalarExtension_tor`, `scalarExtension_bounded_of_tor`, and
`scalarExtension_constructible`, accessed by a proof-only `import all` of
`Sheaf.SecSmoothPurity.ScalarExtensionFunctor`. These apply to every scheme and preserve
the original interval, even for a nonflat quotient. No coefficient witness is chosen.

Operation preservation uses `exists_sfFiniteExceptionalOperations` at this field and positive
level and a finite dimension bound for the compactification. Its literal functor equalities
supply preservation. Right-adjoint uniqueness and repleteness transport the right-hand
preservation to the existing `sfFiniteExceptional` definition.

Added proof imports for that package, finite-Tor repleteness and constant-ring pullback
composition. Updated the existing node's proof route and dependency union. No signatures,
non-theorem bodies, source-library modules or target statements changed.

## Proved and sorry left

Closed six of the original nine holes, all in node `lem-coef-finite-exceptional`:

- `WeilConjectures.FiniteExceptional.reduction_preserves`.
- `WeilConjectures.FiniteExceptional.operations_preserve`.
- `WeilConjectures.FiniteExceptional.quotient_comp`.
- `WeilConjectures.FiniteExceptional.quotient_id`.
- `WeilConjectures.FiniteExceptional.finitePull_comp`.
- `WeilConjectures.FiniteExceptional.qMap_isIso`.

Three original holes remain in the same node:

- `WeilConjectures.FiniteExceptional.adjunction_existsUnique`.
- `WeilConjectures.FiniteExceptional.dualFormula_existsUnique`.
- `WeilConjectures.FiniteExceptional.finite_exceptional`.

The quotient comparison proof specializes the existing coefficient system to the finite
quotient stages, cancels its normalized realization isomorphisms, conjugates by
`finiteImageIso`, and lifts the resulting natural isomorphism through the full inclusion.
The auxiliary closure is `AlgebraicClosure (ULift (Padic l))`; no data from the system
is used to define a public object. The system was already publicly imported.

Added holes: zero. Split off: zero. This is partial proof progress, not a proof of the
complete finite exceptional coefficient theorem.

## No longer needed

Removed these unused direct proof imports:

- `Sheaf.SixFunctors.FiniteCoefficientVerdier`.
- `Sheaf.Paper.ProEtaleFiniteCoefficientDirectImage`.
- `Sheaf.Paper.FiniteCoefficientDirectImage`.
- `Sheaf.Paper.EtaleCompactSupportCoefficientChange`.
- `Sheaf.Paper.BasicOperationsCoefficientReduction`.
- `Sheaf.Paper.FiniteTensorConstructibleCohomology`.
- `Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses`.
- `Sheaf.CategoryTheory.AbsoluteTraceExchange`.
- `Sheaf.SixFunctors.CompactCoefficientComposition`.
- `Sheaf.Paper.ComparisonTorAmplitude`.
- `Sheaf.Paper.FiniteCoefficientFlatModel`.
- `Sheaf.Paper.ProEtaleConstructibleOrigin`.
- `Sheaf.Paper.PullbackTorAmplitude`.
- `Sheaf.Paper.FiniteCoefficientReductionFlatModel`.
- `Sheaf.Paper.OpenExtensionFiniteTor`.
- `Sheaf.Paper.DualityPairing`.
- `Sheaf.SixFunctors.FiniteDualitySiteComparison`.
- `Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses`.
- `Sheaf.Paper.FiniteCoefficientHomChange`.
- `Sheaf.Paper.FiniteStageVerdierBiduality`.
- `WeilConjectures.Compactification.NagataCompactification`.
- `Sheaf.Paper.CanonicalOriginCompactSupportComposition`.
- `Sheaf.Paper.SfPreservationClass`.

The direct reduction-preservation proof no longer needs
`lem-sf-reduction-flat-model`; the already proved scalar-extension package supplies this
argument. Its node dependency was removed from the item's proof union. The other planned
results remain in the DAG where the three outstanding obligations still need them. Removal
of their currently unused direct imports is not a claim that those mathematical obligations
or globally shared modules can be withdrawn. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No false statement or definition repair was found. The existing plan expands preservation
into lower-level arguments already packaged by the finite-operations and scalar-extension
modules; the delivery reuses those results. The direct quotient identities need no separate
coefficient-tower lemma. The constant-ring pullback composition is also already proved.

## Second reading by X3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
