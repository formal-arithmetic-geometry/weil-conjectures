## What changed

Replaced the sorry in `SheafOfModules.fieldScalarStrictLimit` by a direct canonical
Roos transport construction. The construction descends the actual cone isomorphism
through fully faithful localization, proves its ordinary-limit normalization, and
checks finite-basis coordinates and derived composition and identity coherence.
The normalization square reuses the proved `chain_augmentation` helper of
`Sheaf.Paper.NormalizedLimitSquareCoherence`.
The statement, all binders and universes are unchanged. The isolated generic
composition and identity proofs compile, and the scalar exactness/preservation
helpers compile. The final combined compile and delivery preflight provide the
packet-level validation.

Moved the five existing interface declarations verbatim to
`Sheaf.Paper.FieldScalarStrictLimitData`, publicly reexported from the item, so the
ordinary-coordinate obligation can import them without an import cycle. The change
record is `coord/changes/field-scalar-strict-limit-interface.md`.

The genuine remaining steps are isolated in `FieldScalarOrdinaryCoordinates` and
`SmallProEtaleExactProducts`. The former contains ordinary sheaf tensor algebra only;
the latter contains only geometric exactness of countable products on the specified
small model. Neither asserts a derived scalar/limit comparison or its coherence.
The comparisons and finite-basis isomorphisms are pinned by their coordinate formulas;
no arbitrary mathematical object is chosen from a mere existence assertion.

## Proved and sorry left

The original hole is `SheafOfModules.fieldScalarStrictLimit` (one original sorry).
Its proof is complete relative to two new obligations, so this delivery is a
**decomposition**, not a net proof gain: one hole closed and two holes added.
There are no sorries in the item or the extracted definition module.

The two sorries left are:

- `SheafOfModules.fieldScalarOrdinaryCoordinates`, node
  `lem-sp-field-scalar-ordinary-coordinates`: ordinary finite-basis coordinates,
  finite-free composition, balanced associator and identity unitor.
- `SheafOfModules.smallProEtaleExactProducts`, node
  `lem-sp-small-proetale-exact-products`: exact products on the specified small
  pro-etale model, including coefficient-universe transport.

No sorry occurs in a definition or private declaration. The finite-basis rank-zero,
identity, zero-ring and empty-site cases have been checked in the mathematical argument;
the generic comparison works for all unbounded complexes.

## No longer needed

Removed the direct proof imports of `Sheaf.CategoryTheory.StrictRoosComparison`,
`Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients`, and
`Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`. The proof uses
`StrictRoosDerivation` directly and the existing exact-derived functor API; it does not
construct a second model of derived scalar extension or use a monoidal complex tensor.
The direct exact-products import is represented by the small-model obligation.
`Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor` is retained as an interface import.

The original plan's `lem-weil-strict-roos-comparison` is not needed as a direct step:
its normalized derivation precursor suffices. The full finite-free transport theorem
is not applied, but its proved restriction-functor helper is used, so
`lem-weil-pbc-finite-free-strict-tower-transport` and its module remain needed.
No existing module is withdrawn or globally declared unreachable, and no source-library
declaration is removed. No unit statement or required unit step is bypassed. The earlier tool approvals are
retained when their modules remain in the import closure; no claim of global pruning
is made from zero current Lean importers.

## Where the brief, the DAG or earlier work was wrong

The finite-free transport theorem uses a different scalar model and basis interface;
applying it does not directly supply the displayed `RingedTensor.tensorFunctor` data.
The explicit ordinary finite-basis statement bridges that interface instead.
The existing full pro-etale exact-products statement has a coefficient universe
containing the displayed site's universe, while the item permits any small equivalent
site and imposes no universe equality. Its transport to that exact small-site signature
is therefore stated separately rather than silently adding a universe restriction.

The original stage-2 statement itself is unchanged. Its redundant coordinate clause
follows from naturality of the ordinary basis iso and the product projection equation.

## New nodes

`def-sp-field-scalar-strict-limit-data` owns the unchanged finite-free arrow and
comparison interface extracted to `FieldScalarStrictLimitData`. This is an interface
relocation, not a mathematical definition repair; the change record is
`coord/changes/field-scalar-strict-limit-interface.md`.

`lem-sp-field-scalar-ordinary-coordinates` states the ordinary finite-basis and balanced
scalar structure calculations in original steps 1, 3 and 5, with their explicit
pure-section formulas. It does not contain the derived comparison being proved.

`lem-sp-small-proetale-exact-products` states the exact countable-product input on the
precise small model allowed by the original theorem. It is independent of scalar
extension and derived-limit comparisons. Both new statements have complete proof
instructions in their docstrings and DAG nodes, with three kinds of Mathlib searches.

## Second reading by G3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
