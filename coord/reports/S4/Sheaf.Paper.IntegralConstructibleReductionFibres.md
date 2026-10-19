## What changed

Proved `scalarData_map_id`, `scalarData_map_comp`, `scalarMap_naturality`,
`quotientTransition_condition`, `rawFiberComparison_eq`, and `regularCounit_isIso`
in `Sheaf.Paper.IntegralConstructibleReductionFibres`.

The first three proofs use the restricted presheaf laws. The quotient transition
condition follows from the cokernel equation and scalar bilinearity. The raw fibre
identity follows from the prescribed rationalization normalization. The regular
coefficient single complex is K-flat: tensoring it with any acyclic complex is
isomorphic to that complex by the monoidal unitor. The existing normalized K-flat
pullback counit therefore gives `regularCounit_isIso`.

Added the proof-only import
`WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle` for the single-complex
tensor comparison. Existing statements, definitions, and public imports are unchanged.

## Proved and sorry left

Closed six of the seven original holes, all in namespace
`AlgebraicGeometry.Scheme.A1Integral`:

- `scalarData_map_id`
- `scalarData_map_comp`
- `scalarMap_naturality`
- `quotientTransition_condition`
- `rawFiberComparison_eq`
- `regularCounit_isIso`

One original hole remains:
`AlgebraicGeometry.Scheme.A1Integral.integralConstructibleReductionFibres`, attached
to `lem-a1-integral-constructible-reduction-fibres`. Its existing source and complete
natural-language proof remain in its docstring. This is a partial proof delivery;
the principal quotient, stratification, inverse-limit and fibre comparison theorem
is not proved. Added holes: zero. Split-off statements: zero.

Validation: the resumed delivery dry run compiled the packet and passed preflight,
printing `OK (dry run)` with review class `AUTO` (commit `e54a016e56`). The saved log
is `scratchpad/dry-run-resume-oct20-current.log`. Earlier saved dry run
`scratchpad/dry-run-checked.log` also passed. No push was started before this resume.

## No longer needed

None. The remaining principal theorem retains its original declared dependencies
and route; no module or node is claimed pruned.

## Where the brief, the DAG or earlier work was wrong

The interrupted earlier attempt had a redundant tactic after functor extensionality
in `rawFiberComparison_eq`; removing it closes that proof. The regular coefficient
counit needs the single-complex tensor comparison with the project's independent
coefficient universe conventions, supplied by the added proof-only import.

Earlier compiler and preflight infrastructure failures are recorded in the saved
scratchpad logs. Current delivery validation succeeds. Exploratory ordinary quotient
helpers remain scratch work only and are not part of the delivery.

## Second reading by S4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
