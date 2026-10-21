## What changed

Proved `AlgebraicGeometry.finiteField_stratifiedGeneration` in
`Sheaf.Paper.FiniteFieldStratifiedGeneration`, preserving its statement verbatim.
Private, proved helpers implement finite used prefixes, their concatenation, shifts,
endpoint isomorphisms, and middle-term extensions. Concatenation explicitly inserts
the second list's initial zero as a shift by zero of an earlier zero, so every
step satisfies the exact three alternatives of the target.

For sheaves, apply constant-field flatness, the existing ordered stratification and
extension filtration, and the distinguished single triangles. The proved coefficient
encoding lemmas supply finite constant local models in the target's intrinsic
module-sheaf encoding. Apply the existing degreewise bounded-devissage theorem to
pass to complexes and restrict the resulting sequence to `Fin (n + 1)`.

Added proof imports for Mathlib's lifted-field instance, the proved bounded
devissage module, and the two coefficient-encoding modules. Their private proved
encoding lemmas are accessed with `import all`, as in FlatModelGeneration itself.
A private local instance specializes the existing locally-bijective criterion to the fixed
module universe; it introduces no mathematical assumption or exported instance.
The DAG proof and proof dependencies now describe this implementation.
The required instance record is
`coord/changes/finite-field-stratified-generation-local-instance.md`.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.finiteField_stratifiedGeneration`
(node `lem-sfb-finite-field-stratified-generation`): 1 of 1.
The item has zero remaining `sorry`; the delivery adds zero holes and splits off
zero statements. Every added private helper is proved. No other Lean module is
changed. The file is checked using the required remote single-file compiler;
the delivery command performs its independent compilation and axiom probes.

## No longer needed

Removed these direct proof imports:

- `Sheaf.CategoryTheory.TruncationsAndHomotopyColimits`;
- `Sheaf.CategoryTheory.GrothendieckSheafification`;
- `Mathlib.CategoryTheory.Sites.LocallyBijective`;
- `WeilConjectures.CategoryTheory.TruncationTriangle`.

The proof no longer directly needs nodes `def-kun-truncations`,
`lem-sfb-grothendieck-sheafification`,
`lem-weil-pbc-site-sheafification-iso-locally-bijective`, or
`lem-weil-pbc-truncation-triangle`: the site instances already exist and the
proved bounded-devissage theorem supplies the good-truncation induction.
Removed the latter three nodes' obsolete entries from `tool_uses`, preserving
the order of the retained approvals. No library module or declaration is
withdrawn; these modules can still be needed transitively by other consumers.
Clauses about thick generation, retracts and Tor amplitude are not used.

## Where the brief, the DAG or earlier work was wrong

The first preflight requested a change record for the newly named local
instance. Added that record and marked the specialization `private local`,
explicitly preserving both name visibility and local instance scope.
No mathematical statement or definition repair was needed. The already-proved
bounded-devissage theorem avoids rebuilding the truncation tower. The generic
tool `lem-sfb-degreewise-bounded-devissage` is used for exactly this tower, keeping
the unit's route. The coefficient-encoding results and the finite-model
local-constancy results are used as interface tools; they do not alter the
stratification or add an etale-origin hypothesis to this item.

Two elaboration details need explicit handling: a lifted coefficient field needs
`Mathlib.Algebra.Field.ULift`, and instance search cannot infer a coefficient
universe by inverting `max`. The local specialization fixes that universe using
the existing criterion. The proof includes the zero-length list and concatenation
with either prefix of length zero; no positive length or nonempty scheme is used.

## Second reading by U3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
