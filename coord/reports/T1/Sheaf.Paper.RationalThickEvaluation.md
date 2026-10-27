## What changed

Proved the three scalar-action theorems in `lean/Sheaf/Paper/RationalThickEvaluation.lean`.
The proof constructs the ring homomorphism from coefficient integers to compatible
constant sections, restricts it to the actual slice site, and uses the sectionwise
Hom module structure from `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomModule`.
This module is the only added proof import.

The resulting scalar chain action is uniquely determined on every degree and section.
Its descent agrees with Mathlib's localization of the center. The induced linear
structure is unique because the scalar formula determines every Hom module structure.
Mathlib's shift-linearity descent then applies to exactly the chosen linear instance.
All additional helpers and constructions are private; the module-linear instance is
local to a section and proofs. Existing public signatures, definitions, docstrings,
attributes and public imports are unchanged. No source-library file is edited.

Server compilation succeeded without warnings. Separate `#print axioms` checks for
each of the three proved theorems reported only `propext`, `Classical.choice` and
`Quot.sound`. The four original theorem signatures were also compared textually.
The additional import passes `import_direction.py may`.

## Proved and sorry left

Closed three of the four original holes, with no added holes:

- `WeilConjectures.IntegralOnSlice.scalarChain_existsUnique`;
- `WeilConjectures.IntegralOnSlice.linear_existsUnique`;
- `WeilConjectures.IntegralOnSlice.shift_linear`.

The one remaining hole is
`WeilConjectures.IntegralOnSlice.rationalThickEvaluation`, unchanged, with its original
complete proof plan and source in node `lem-sf-rational-thick-evaluation`.
This is a partial proof delivery of a module with multiple holes, not a decomposition:
zero statements are split off, and every new private theorem has a complete proof.

## No longer needed

None. No imports, nodes or modules are withdrawn. The remaining evaluation theorem
still requires its recorded completion, internal-Hom and localization dependencies;
the DAG route is retained. The three completed proofs implement its stated
componentwise scalar-action argument using Mathlib localization and shift linearity.

## Where the brief, the DAG or earlier work was wrong

No false statement or mathematical error was established. Searches found Mathlib's
derived linearity and localization-of-center APIs, but not a direct theorem for the
full completed-evaluation statement.

For subsequent work on the remaining hole: the concrete
`restrictionCompletion_bijective` and `restrictionHom_complete` statements in
`Sheaf.Paper.RationalSliceCompletedEvaluation` have suitable slice conclusions, but
that module imports this item, so it cannot be imported here. The generic
`ConstantCompletion.koszul_quotient_reflector`, `ringedInternalHom_exact`, and
`isLocallyDerivedRingedIdealComplete_derivedInternalHom` interfaces use a single
small-site/coefficient universe; applying them here requires the actual slice
transport with independent site-object, site-morphism and coefficient universes.
Once completed evaluation and its exact shift structure are available, the adopted
`WeilConjectures.Mathlib.CategoryTheory.Triangulated.Generators` module already gives
triangulated, isomorphism and retract closure of natural-transformation isomorphism
loci. These observations are not asserted as new unproved declarations.

## Second reading by T1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
