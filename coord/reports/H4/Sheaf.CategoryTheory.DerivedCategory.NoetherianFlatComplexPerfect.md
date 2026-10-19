## What changed

Proved `DerivedCategory.exists_bounded_finite_projective_model_of_flat_of_finite_homology`
in `Sheaf.CategoryTheory.DerivedCategory.NoetherianFlatComplexPerfect`, preserving its
signature, universes, visibility, and all existing public imports. Its only proof import is
now `WeilConjectures.CategoryTheory.DerivedCategory.Perfect.OfFlat`.

The source library already proves the same mathematical theorem via
`DerivedCategory.isPerfect_of_flat_of_finite_homology`. Convert explicit support to
strict support, transport finite homology, apply that theorem in its required universe,
and unpack `IsPerfect`. A localization lift and its factorization isomorphism transport
the resulting model isomorphism back to the arbitrary derived-category universe in the
item. This retains the full original statement; it does not assume the two universe
choices coincide. Updated the node proof and dependency list to this actual route.

The unit record has empty realized statement and step lists. Reusing the existing proof
of this node does not replace any unit-level route.

Validation: the module compiled cleanly through `lcompile.py` in 2.3 seconds. No new
statements, definitions, instances, or auxiliary modules were added. The original
signature handles zero complexes, empty support intervals, and arbitrary integers;
no inequality between the chosen bounds is needed or added.

## Proved and sorry left

Closed 1 of 1 holes:
`DerivedCategory.exists_bounded_finite_projective_model_of_flat_of_finite_homology`
(node `lem-pc-noetherian-flat-complex-perfect`).

Holes added: 0. Holes left in the delivered module: 0. Split off: 0.
This is a proof from an already proved library result, not a decomposition.

## No longer needed

Removed proof imports:
- `Sheaf.Algebra.Homology.BoundedAboveFlatRingedSpaceKFlat`;
- `WeilConjectures.Algebra.FlatTorIdealCriterion`;
- `Mathlib.CategoryTheory.Monoidal.Tor`;
- `Mathlib.RingTheory.Flat.EquationalCriterion`.

The replacement proof does not directly use the declared dependencies
`lem-pc-noetherian-finite-kernels-cokernels`, `lem-pc-bounded-above-flat-kflat`,
`def-weil-pbc-tor-modules`, `lem-weil-pbc-flat-tor-ideal-criterion`, or
`lem-weil-pbc-finitely-presented-flat-module-projective`: the source library theorem
already supplies the mathematical construction. Removed them from this node's
proof_deps and withdrew the obsolete tool_uses approval for
`lem-weil-pbc-flat-tor-ideal-criterion`. The abstract derived-category definition remains
needed for the localization comparison. These are direct dependency removals; no claim
is made that the removed modules have no other consumers or leave the global closure.
The pre-existing public imports are retained to preserve the module's exported interface.

## Where the brief, the DAG or earlier work was wrong

The node's own lean_audit already identifies the proved source theorem, but the stage-2
statement remained a sorry. Its universe-u theorem cannot be applied directly to the
item's arbitrary universe w, which is why the proof includes a localization lift rather
than specializing the item's signature.

Searches were actually run through msearch.py: LeanFinder for bounded flat complexes
with finite cohomology over a Noetherian ring returned K-projective and support lemmas;
Loogle for DerivedCategory.IsPerfect returned unknown identifier; the service grep for
isPerfect_of_flat_of_finite_homology returned no hits. Local rg found the exact source
result in Perfect/OfFlat.lean. Read every original proof dependency's node and available
Lean signature before choosing this shorter route. import_direction.py confirmed the
new proof import creates no cycle.

## Second reading by H4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
