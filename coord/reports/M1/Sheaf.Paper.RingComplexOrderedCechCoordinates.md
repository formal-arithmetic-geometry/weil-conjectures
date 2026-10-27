## What changed

Proved `AlgebraicGeometry.ringComplexOrderedCech_coordinates` with its statement unchanged.
The degree-zero cone first projection and positive-degree second projections give actual
isomorphisms, with inverses verified using `mappingCone.id_X`. Extension by zero proves
negative-degree vanishing. The shifted differential and `mappingCone.d_snd_v` give the
first and higher differential formulas after multiplying coordinates by successive powers
of the negation linear equivalence. The inverse-rotation formula gives augmentation
compatibility.

Added the proved theorem `AlgebraicGeometry.ringComplexOrderedCech_sections_coordinates`
in `Sheaf.Paper.RingComplexOrderedCechSectionCoordinates`, imported privately by the item.
Its coordinates are constructed from equality of the intersection's image with the principal
open of the product and `IsLocalization.algEquiv`. The face maps conjugate actual restriction
ring maps. Their A-algebra property follows from restriction of constants. Product linear
equivalences and extension term isomorphisms give the section-complex coordinates and
signed differential. All auxiliary definitions are private, explicit constructions.

Updated the item's proof plan and added a node for the proved section-coordinate theorem.
No existing definition, signature, public import, source-library module, or consumer changes.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ringComplexOrderedCech_coordinates`
(`lem-weil-pbc-ring-complex-ordered-cech-coordinates`).

Added zero holes. The new theorem
`AlgebraicGeometry.ringComplexOrderedCech_sections_coordinates`
(`lem-weil-pbc-ring-complex-ordered-cech-section-coordinates`) is proved in full.
There are zero `sorry` tokens in either delivered Lean module. This is a proof, not a
decomposition into unproved statements.

Validation: both modules are checked individually by lcompile; delivery runs the required
compile and axiom probes. The proofs do not require nonzero-ring, nonempty-list, nonzero-
generator, or distinct-generator assumptions. An intersection tuple always has q+1 entries;
when the family is empty there are no such tuples, so the pointwise proof is vacuous.
The proof uses no arbitrary object selected from an unproved existence theorem.

## No longer needed

No imports were removed and no library modules were withdrawn. The three planned geometric
proof dependencies are unnecessary for this proof:

- `lem-weil-pbc-principal-localization-open-immersion`: no scheme localization morphism is
  needed; the proof works directly with the existing open's structure-ring sections.
- `lem-weil-pbc-spec-module-tilde-sections`: no associated module sheaf is needed for the unit
  module's structure-ring sections.
- `lem-weil-pbc-spec-tilde-free-module`: no free-module comparison is used.

Their existing modules and declarations remain untouched. The construction and Cech-data
nodes remain dependencies. The unit's route is preserved.

## Where the brief, the DAG or earlier work was wrong

The planned conclusion is correct. The elementary cone-coordinate step required explicit
projection inverse identities, index transports, and shift signs. These are now proved.
The semantic search services returned some section APIs from an older Mathlib interface;
the implementation uses the localization and restriction declarations checked in the pinned
source instead. No assigned return or rework entry was present for this module.

## New nodes

`lem-weil-pbc-ring-complex-ordered-cech-section-coordinates` records the proved unaugmented
section calculation, a strict part of the original argument. Its source is Stacks Tag
099D(d), with the ordered Cech differential of Cohomology Tags 01EQ and 01FJ. LeanSearch,
LeanFinder and source grep found the principal-open localization APIs but no existing theorem
with the ordered-complex and scalar-restriction data. Blueprint and local node searches
found no duplicate. No change record is needed: no existing public interface was changed.

## Second reading by M1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
