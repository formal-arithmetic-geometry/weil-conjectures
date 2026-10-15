## What changed

The target module now imports three proof-only helper modules.  Its target theorem is
proved by applying the core valuation-ring theorem, the proved DVR association and
fraction-field factorization theorem, and the named uniqueness theorem, then packaging
existence and uniqueness into the required `∃!` conclusion.  The association and
existence helper is proved from Mathlib's DVR API.

## Proved and sorry left

`Padic.extension_integers_dvr` is closed.  `Padic.extension_integers_dvr_factorization`
is closed, including generator association and existence of unit-times-integer-power
expressions.  Two strictly smaller named statements remain as `sorry`: the
ring-theoretic core `Padic.extension_integers_dvr_core` (node
`lem-weil-l-adic-extension-integers-dvr-core`) and uniqueness of the factorization
`Padic.extension_integers_dvr_factorization_unique` (node
`lem-weil-l-adic-extension-integers-dvr-factorization-unique`).

## No longer needed

None.  The target's original public imports remain required by its unchanged signature;
the proof-only imports are exactly the helper modules used in the proof.

## Where the brief, the DAG or earlier work was wrong

The original proof plan bundled the proper valued-field construction and the DVR
factorization uniqueness into one very large theorem.  The implementation required those
as independent intermediate statements, so the delivery adds the two corresponding
nodes; no target statement or existing definition was changed.

## New nodes

`lem-weil-l-adic-extension-integers-dvr-core` records the finite-extension valuation-ring
core and is stated in `lean/Sheaf/NumberTheory/Padics/ExtensionIntegersDvrCore.lean`.

`lem-weil-l-adic-extension-integers-dvr-factorization` records the association and
existence portion and is stated and proved in
`lean/Sheaf/NumberTheory/Padics/ExtensionIntegersDvrFactorization.lean`.

`lem-weil-l-adic-extension-integers-dvr-factorization-unique` records the strict
uniqueness portion and is stated in
`lean/Sheaf/NumberTheory/Padics/ExtensionIntegersDvrFactorizationUnique.lean`.

## Earlier second reading (a previous round; superseded)

The target module and all three new nodes compile in the sandbox.  The proved
factorization module preserves the target signature; the two remaining nodes are strict
substatements with their own source and blueprint tags.  The unit route is retained.

## Second reading by E2

1. Compared the delivered target module with the repository version. The existing theorem
   signature is unchanged byte for byte; only its proof and proof-only imports changed.
2. Compiled all four delivered modules with `lcompile.py`; they compile without errors or
   warnings. The only remaining `sorry`s are the two named split-off theorems, each with a
   docstring and matching DAG node; no definitions contain `sorry`.
3. Checked the split-off statements against the target: the core theorem removes the
   association and factorization clauses, while the uniqueness theorem isolates only
   uniqueness. Both are true strict reductions, and no duplicate declaration was found in
   Mathlib or the repository.
4. Read the proof routes and imports. The factorization proof uses Mathlib's DVR API, the
   target uses the three helper declarations, and the uniqueness module now exposes only
   the Mathlib imports required by its statement. The unit's route through the original
   valuation-ring node is retained.
5. Checked the DAG records: statements, proof dependencies, proof origins, Lean records,
   and statuses agree with the delivered declarations. The two split-off nodes document
   their sources and intended reductions.

Changed the uniqueness helper to remove its unused public import of the factorization
helper, and recorded this second reading.
