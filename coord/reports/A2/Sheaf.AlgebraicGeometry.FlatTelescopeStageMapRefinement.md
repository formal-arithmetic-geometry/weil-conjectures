## What changed

Replaced the sorry in
`AlgebraicGeometry.exists_flat_telescope_stage_map_refinement` by a compiling reduction.
The public statement and visibility are unchanged. Three proved private helpers
absorb all integer shifts into telescope presentations, extract an unshifted
presentation of each supplied object, and construct the stage-map predicate from
a strict tower square with a transported target.

The proof lifts the conjugated homotopy arrow using fullness of the quotient, applies
`AlgebraicGeometry.exists_flat_telescope_arrow_diagram`, and verifies the source
augmentation with `CochainComplex.quasiIso_flat_truncation_telescope`. It then verifies
the representative, quasi-isomorphism, both stage-map witnesses, and the equality
in the original homotopy category. In particular, the lower construction supplies
truncation augmentations and cone restrictions, not an assumed quasi-isomorphism
of the common-source map or either stage-map predicate.

Added the proof-only import `Sheaf.AlgebraicGeometry.FlatTelescopeArrowDiagram`.
Its single public theorem records the construction portion of the existing plan:
three bounded-flat towers, strict sum squares, target presentation isomorphisms,
compatible quasi-isomorphic truncation augmentations, and the retained arrow
homotopies. It does not choose any data in a definition. The item's node now
records this route. Both delivered modules compiled individually through lcompile.py;
the existing dependency was initially absent from the shared build and became
available with its normal refresh.

## Proved and sorry left

Closed: `AlgebraicGeometry.exists_flat_telescope_stage_map_refinement`
(node `lem-sc-flat-telescope-stage-map-refinement`), the item's only original hole.
No sorry remains in the item's module. Its three new private helpers are proved.

Added and left: `AlgebraicGeometry.exists_flat_telescope_arrow_diagram`
(node `lem-sc-flat-telescope-arrow-diagram`), in the new module
`Sheaf.AlgebraicGeometry.FlatTelescopeArrowDiagram`.
This is a decomposition: one upper hole closed and one construction hole added,
net zero holes. The compatible diagram construction is still unproved; the
quasi-isomorphism and presentation/transport verification are complete Lean proofs
from its explicit data and the existing telescope comparison theorem.

## No longer needed

Removed the direct proof import
`Mathlib.CategoryTheory.Localization.CalculusOfFractions` and the direct dependency
`lem-pc-right-fraction-common-refinement`. The construction retains homotopies and
gives equality in the homotopy category directly, so the assembly uses no
localization equality or right-fraction refinement. This is pruning for this proof;
no claim is made that other targets cease to need this Mathlib module or node.

Removed direct imports `Sheaf.Algebra.Homology.BoundedFlatReplacement` and
`Sheaf.Algebra.Homology.FlatTruncationTower` from the item's module. Their nodes
`lem-pc-kflat-bounded-flat-replacement` and `lem-pc-flat-truncation-tower` remain
needed as construction dependencies in the new module; they are delegated, not
globally pruned. The telescope comparison and stage-map definitions remain needed.
No unit-level statement or proof step is bypassed or changed.

## Where the brief, the DAG or earlier work was wrong

The existing bounded replacement, truncation tower and telescope comparison
statements do not supply simultaneous maps to the two prescribed telescope
presentations. The new theorem states precisely that missing construction step.
A target tower cannot in general be kept at a fixed index while accommodating an
arbitrary arrow: the construction allows different target presentations and
homotopy isomorphisms, as the stage-map definition already permits.

The fraction criterion only turns a localized equality into a homotopy equality
after an additional refinement; it does not itself construct compatible flat
tower maps. This reduction requests the retained arrow homotopies directly and
therefore does not use that optional branch of the earlier plan.

The cited Stacks tags establish flat resolutions, compatible truncation towers,
and derived pullback, rather than literally asserting the simultaneous model-map
construction. Both the new docstring and node explicitly mark the construction
as an agent expansion of the existing plan. Zero and identity arrows and the
empty scheme require no additional hypothesis. Arbitrary translations are
handled by the proved shift helper, with the bound changed from b to b-k.

## New nodes

`lem-sc-flat-telescope-arrow-diagram`, in
`dag/nodes/sec-picard-framework/lem-sc-flat-telescope-arrow-diagram.json`, carries
`AlgebraicGeometry.exists_flat_telescope_arrow_diagram` in
`lean/Sheaf/AlgebraicGeometry/FlatTelescopeArrowDiagram.lean`. It isolates the
compatible diagram construction before its telescope quasi-isomorphism is
verified. It inherits the parent's chapter and unit, records the three search
kinds, and provides its source and construction proof in words. LeanSearch was
unavailable; LeanFinder and source searches found no matching theorem. There
are no interface changes to existing declarations and no change records.

## Second reading by A2

1. I compared the delivered stage-map module with the repository version. The target statement and all existing declaration signatures are unchanged; the new arrow-diagram module is recorded by its new node.

2. I compiled both delivered modules with `lcompile.py --all`. There are no forbidden `axiom`, `unsafe`, `opaque`, `extern`, or hollow definitions. The only remaining `sorry` is the named construction theorem `exists_flat_telescope_arrow_diagram`, and its node, docstring, and report entry agree. The stage-map theorem has no `sorry`.

3. The split statement is a genuine construction subproblem: it supplies explicit bounded-flat towers, strict squares, augmentations, and homotopy equalities, while leaving quasi-isomorphism and stage-map verification to the parent proof. It is strictly weaker than the parent target and is not a restatement. The theorem is not duplicated in the library or Mathlib.

4. I checked the proof from the target downward. It uses the arrow-diagram construction, the existing telescope comparison, and direct Mathlib shift and cone APIs. The removed fraction and direct tower imports are unused, and no unit statement or route is bypassed.

5. The item's node proof steps, dependencies, and origin match the Lean proof; the new node records its declaration, source, proof plan, and unit/chapter correctly.

I changed only the proof of the stage-map theorem, added the proof-only arrow-diagram module and node, pruned the unused imports and dependencies, and added this second-reading record.
