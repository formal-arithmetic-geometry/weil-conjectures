## What changed

Proved all six theorem holes in `Sheaf.Paper.RationalRealizationFiniteConeModels`.
Every existing signature, definition, instance and public import is unchanged.
No other Lean module is changed, and no new public declaration is added.

`image_closed` applies Mathlib's triangulated essential-image instance for a full
triangulated functor. `extension_cone` lifts the connecting arrow by fullness,
clears its denominator in the actual raw tensor Hom module, and constructs an
integral distinguished cone. TR3 compares its realized triangle with the twice
rotated input, using identity and the invertible uniformizer power. Its third
component is invertible, and shifting back gives the requested middle-object
model. Faithfulness proves uniqueness of the lifted arrow.

`filtration_model` uses finite-path induction from integral zero, applying the
proved extension theorem to each SES triangle. Private proved helpers concatenate
finite construction lists, append shifted cones, and retain all intermediate
witnesses. `sheaf_model` applies that proof to the supplied filtration.

`bounded_model` uses the standard derived t-structure, identifies each successive
quotient with its shifted cohomology sheaf via homology isomorphisms, and applies
the proved filtration and extension results. The same finite-path induction
retains exactly the requested truncation tower. `acyclic_model` uses the derived
t-structure zero criterion and the actual integral zero object.

Added private proof imports: `Mathlib.RingTheory.Localization.BaseChange`,
`Mathlib.Data.Fin.Tuple.Basic`, and
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure`.
All new helpers are private and proved, including the finite-list bookkeeping.
The final module compiled cleanly in 25.6 seconds with zero sorries and no
warnings. All Lean lines are at most 100 characters.

Edge cases are included in the proofs: zero connecting arrow and denominator
exponent zero; empty filtration; arbitrary negative shifts; empty cohomology
interval or crossed bounds (the tower has length zero); acyclic and empty-scheme
cases. The last truncation degree is a-1+(b-a+1).toNat, which is at least b even
when a>b. All cone indices in each construction list are strictly earlier.

## Proved and sorry left

Closed all 6 original holes in namespace
`AlgebraicGeometry.Scheme.RationalConeModels`:

- `image_closed`.
- `extension_cone`.
- `filtration_model`.
- `sheaf_model`.
- `bounded_model`.
- `acyclic_model`.

Sorries left in the module: 0. Added holes: 0. Split-off statements: 0.
No hollow definitions, axioms, statement weakening or new public data choices.
The supplied filtration choices are made inside theorem proofs. Underlying
library dependencies may still contain their own original holes; no such hole
is added or moved by this delivery.

## No longer needed

Removed unused private proof imports:

- `Sheaf.CategoryTheory.TruncationsAndHomotopyColimits`.
- `WeilConjectures.CategoryTheory.TruncationTriangle`.
- `Mathlib.CategoryTheory.Triangulated.Pretriangulated`.

The proof no longer needs node `lem-weil-pbc-truncation-triangle` or module
`WeilConjectures.CategoryTheory.TruncationTriangle`: it constructs the successive
triangle directly from the standard derived t-structure and the proved homology
comparison API. Removed this node from the item's proof dependencies, final
proof-step uses, and approved tool list. No source-library declaration or module
is deleted; other consumers may still require it.

No other node, module or declaration is withdrawn. The unit's own route remains
unchanged. The generic essential-image argument replaces denominator clearing
only for `image_closed`; all explicit integral witnesses in `extension_cone`
and both finite towers are constructed.

## Where the brief, the DAG or earlier work was wrong

No false statement or broken mathematical interface was found. The DAG's
explicit cone argument is unnecessary for the generic `image_closed` assertion,
because Mathlib already proves triangulated essential-image closure. It remains
the argument used for the stronger explicit `extension_cone` statement.

Direct specialization of tensor localization initially encountered distinct
module instances `ULift.module` and `OreLocalization.instModuleOfIsScalarTower`.
Proving denominator clearing and scalar-map identities for a generic coefficient
ring first, then specializing, resolves the mismatch without a definition repair.
The bounded proof avoids the cochain-level truncation theorem by using exactly
the standard t-structure truncations occurring in its statement.


The first server preflight requested a change record for section commands.
`coord/changes/S8-rational-finite-cone-proof-commands.md` records the added tensor
notation opening and `omit` prefixes for private helpers. The downstream check
reports zero consumer modules; no existing public signature or definition changes.

## Second reading by S8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
