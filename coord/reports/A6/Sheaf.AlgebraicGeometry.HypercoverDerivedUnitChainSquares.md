## What changed

Implemented the resolution-comparison and derived-unit normalization part of
`Sheaf.AlgebraicGeometry.HypercoverDerivedUnitChainSquares`.

`comparison` uses bounded-below injectivity and the existing K-injective
precomposition bijection. `unit_representative` constructs the transposed homotopy
and uses the defining unit equation of the actual published derived adjunction.
`sections_composition_representative` follows from universal uniqueness of the
source-library right-derived composition comparison, and applies to arbitrary I
and J as stated. `sections_representative` applies derived sections to the unit
identity and cancels the invertible resolution comparison. Evaluation additivity
is proved directly. The proved helper `CategoryTheory.derived_unit_cochain` in the new module
`Sheaf.CategoryTheory.DerivedAdjunctionCochainUnit` transports the canonical unit
equation from the homotopy category to cochain representatives. Two proved private
helpers handle the composition comparison.

Removed three unused imports, including the public general-resolution-construction
import. The change record is
`coord/changes/HypercoverDerivedUnitChainSquares-proof-imports.md`.
There are no current direct Lean importers to adapt. The existing definitions,
public declaration signatures and unit route are retained. Updated the item's DAG
proof steps 4-5 and their dependencies to describe the actual canonical API used.

Validation: both modules compile cleanly through `lcompile.py --all`: the helper
in 4.2 seconds and the item in 54.8 seconds (exit 0). An earlier delivery probe
of the unsplit file took 60.2 seconds and pushed nothing; profiling identified
proof type checking and linting as substantial costs. The generic cochain unit
calculation was extracted into its own proved module with its own API, without
changing shared definitions or their transparency. No profiler options remain.
Source-level existing public signatures are unchanged. The DAG proof dependency
set equals the union of the proof steps' uses; exactly 10 textual holes remain.
All Lean source lines have at most 100 characters.

## Proved and sorry left

Closed 5 of the original 15 holes; added 0 holes and split off 0 unproved statements. The new helper is proved without `sorry`.
All declaration names below are in `AlgebraicGeometry.Scheme.HypercoverUnit`.
All existing holes belong to `lem-sfb-hypercover-derived-unit-chain-squares`.

Proved:

- `sections_additive`
- `comparison`
- `unit_representative`
- `sections_composition_representative`
- `sections_representative`

The 10 existing, unchanged holes left are:

- `restriction_existsUnique`
- `augmentation_square`
- `coefficient_homotopy`
- `coefficient_naturality`
- `refinement_existsUnique`
- `refinement_naturality`
- `restriction_comp_section`
- `restriction_comp`
- `identity_directImage_existsUnique`
- `restriction_id`

This is a partial proof delivery, with the total-complex and ordinary comparison
clauses left at their original named statements, sources and proof docstrings.
No definition acquires a hole; the component-characterized unique-choice
constructions remain unchanged.

## No longer needed

Removed imports:

- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`
- `Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral`
- `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`

Removed proof dependencies:

- `def-sfb-right-derived-functor`: the proof uses the actual source-library
  `rightDerivedFunctor` and `rightDerivedFunctorUnitQ`, already part of the
  published pro-etale operations, rather than the generic alternative construction.
- `lem-pc-pre-derived-adjoint-functors-general`: the actual adjunction now exposes
  Mathlib's `derivedη_fac_app`, which gives its defining normalization directly.
- `lem-weil-pbc-ringed-topoi-derived-pushforward-composition`: the literal section
  functor equality and the published `rightDerivedFunctorCompIso'` suffice;
  the general ringed-topos existence theorem is unnecessary.

The latter two obsolete top-level tool-use approvals were removed. All other
recorded dependencies are retained for the proved comparison and remaining
signed-total clauses. The item and its DAG parents are retained; no module is
withdrawn, and no claim that these imports are globally unreachable is made.

## Where the brief, the DAG or earlier work was wrong

The old normalization plan was written against an existential pre-derived
adjunction interface. The current published pro-etale adjunction is the canonical
source-library `mapDerivedCategoryRightDerivedAdjunction`. Its defining unit
identity proves the required normalization without choosing any adjunction or
appealing to an existential compatibility statement. The same applies to the
canonical source-library composition isomorphism. No existing statement was
found false or weakened. The blueprint unit route is unchanged.

## New nodes

`lem-sfb-derived-adjunction-cochain-unit` realizes the canonical cochain unit
normalization used in step 4. Its one theorem is proved, with no new holes, in
`Sheaf.CategoryTheory.DerivedAdjunctionCochainUnit`. It is the general unit
transport calculation, not the item's resolution theorem or signed-total clauses.
The statement and proof specify the actual source-library derived adjunction.
The only change record is
`coord/changes/HypercoverDerivedUnitChainSquares-proof-imports.md`.

## Second reading by A6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
