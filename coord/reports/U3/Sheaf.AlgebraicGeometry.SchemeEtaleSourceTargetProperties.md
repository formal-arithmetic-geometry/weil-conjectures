## What changed

Proved `AlgebraicGeometry.scheme_etale_source_target_properties` with its signature and
public imports unchanged. All five properties use their Mathlib composition, base-change,
and Zariski source-locality instances. Singleton descent uses the existing declarations
for smoothness, etaleness, local finite presentation, local finite type, and the already
proved source-library `Flat.of_comp_of_flat_of_surjective`.

The private, proved helper `etale_source_family_iff` factors each etale source map through
its open image, descends there along the resulting surjective etale map, and glues by
Zariski source locality. This directly handles an arbitrary index universe and the empty
family. The private, proved helper `etale_target_cancel` uses the etale graph into a
pullback. The main proof combines these with composition, identity charts, and a family
of charts chosen over the source points. No separation or quasi-compactness is introduced.

Updated the item's proof, proof_deps, proof_origin, and obsolete tool_uses to follow this
argument. Added proof imports of Mathlib's UniversallyOpen module and the adopted Flat
complements. The newly used flat source-descent node is Lean-closed; the two other new
DAG dependencies (open images and factorization through an open) are Mathlib leaves.

Validation: the module compiled without warnings in 4.5 seconds through lcompile.py.
The new source-library import passes import_direction.py. The theorem statement,
including both universe parameters and all square and family clauses, is unchanged.
No shared definition, instance, public signature, or consumer file was changed.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.scheme_etale_source_target_properties`
(node `lem-sfb-scheme-etale-source-target-properties`).

Added 0 holes; split off 0 statements. There are 0 remaining sorries in the delivered
Lean file. Both private helpers are completely proved. The proof uses existing source
descent declarations, including the still-open lfp and lft statements; it adds no new
obligation duplicating them.

## No longer needed

Removed these proof imports:

- `Sheaf.AlgebraicGeometry.EtaleSmoothZeroDimensionalFibres`
- `Sheaf.AlgebraicGeometry.UnramifiedMorphism`
- `Mathlib.AlgebraicGeometry.OpenImmersion`
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`
- `Mathlib.RingTheory.RingHom.Flat`
- `Mathlib.CategoryTheory.Limits.MorphismProperty`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`
- `WeilConjectures.RingTheory.FlatPermanence`
- `Mathlib.AlgebraicGeometry.Limits`
- `Mathlib.AlgebraicGeometry.Morphisms.Basic`
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`

The last group of Mathlib imports is already supplied by the retained imports. The
following original proof dependencies are no longer used by this proof:

- `lem-weil-pbc-etale-smooth-zero-dimensional-fibres`: Mathlib directly gives smoothness
  of an etale map; the fibre dimension calculation is unnecessary here.
- `def-weil-unramified-morphism`: Mathlib directly supplies local finite type of an
  etale map, so the auxiliary unramified predicate is unnecessary.
- `lem-sfb-etale-stalk-invariants`: no dimension, regularity, normality, or separate
  stalk-invariant theorem is needed for flatness descent.
- `lem-weil-pbc-flat-permanence`: the already proved scheme-level flat source-descent
  theorem replaces the entire new stalk argument.
- `lem-weil-pbc-scheme-coproduct-family`: descent through open images avoids both the
  scheme coproduct and its small-universe reduction.

Accordingly removed the obsolete tool approvals for
`lem-weil-pbc-flat-permanence` and
`lem-weil-pbc-etale-smooth-zero-dimensional-fibres`, preserving all other approvals
in their original order. These are dependency removals for this proof, not withdrawals
of any source-library declaration or claims about their use by other modules.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The original plan was longer than necessary: it rebuilt
flat source descent despite an existing proved theorem, used a stronger etale-stalk
invariant theorem than needed, and introduced a coproduct with an avoidable universe
reduction. The open-image refinement replaces that part of the plan. Empty sources,
empty index types, arbitrary index universes, and nonseparated etale target maps are all
covered by the compiled argument. The unit realization record has no statement or step
attached to this node, and no unit-level route is bypassed.

## Second reading by U3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
