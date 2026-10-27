## What changed

Filled four of the six theorem proofs in
`Sheaf.Paper.FdIntegralInverseScalarCocycle`, preserving every public signature,
definition, docstring and public import. Added a private `import all` of
`Sheaf.Paper.PbcScalarExtension` to reuse its proved finite-level constant-comparison
naturality lemma. The forward cocycle is the supplied associator
normalization; its inverse follows from naturality and inverse cancellation.
The unit equations follow from unit normalization, inverse naturality and the
completed associator unit laws. The ordinary unit laws are recovered by cancelling
the actual completion comparison from the forward normalization. The coefficient
map equality uses uniqueness of the limit map and naturality of the normalized
constant comparisons. Field-inclusion composition cancels the middle Shrink
algebra equivalence. The two added categorical helpers are private and completely proved.
The existing private constant-comparison lemma is reused without copying it.

## Proved and sorry left

Closed four existing holes:

- `WeilConjectures.fdIntegralInverseScalarCocycle`.
- `WeilConjectures.fdIntegralInverseScalarUnits`.
- `WeilConjectures.fdIntegralCoefficientMap_eq`.
- `WeilConjectures.fdIntegralCoefficientInclusion_comp`.

Two original holes remain, both owned by
`lem-fd-integral-inverse-scalar-cocycle`:

- `WeilConjectures.fdIntegralOrdinaryPresentation_existsUnique`.
- `WeilConjectures.fdIntegralOrdinaryBalancing`.

No holes added or split off. This is a partial proof delivery, not a decomposition.

## No longer needed

None. No imports, modules or node dependencies are removed. The remaining
presentation/balancing theorems still need the stated dependencies. The completed
unit normalization and associator unit fields already imply the ordinary unit
laws, so those clauses require no additional PBC unit theorem.

## Where the brief, the DAG or earlier work was wrong

No statement correction. The two presentation theorems need descent through the
good-complex localization and the tensor-generator comparison; they remain in
their original named form with their original source and complete proof sketches.
The latest blueprint places `def-fd-trace-function` under `sk-cor-plancherel`,
whereas the older node source records `sk-def-trace`; the current text has no
coefficient-category final sentence. This delivery uses the existing reviewed
auxiliary statement and does not change its source interpretation or unit route.

## Second reading by D3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
