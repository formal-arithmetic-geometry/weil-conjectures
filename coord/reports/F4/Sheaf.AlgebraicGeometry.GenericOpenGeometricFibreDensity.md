## What changed

Replaced the proof of `AlgebraicGeometry.exists_open_geometric_fibre_dense_of_open`
with a complete Lean reduction to the ordinary-fibre density assertion of Stacks
Tag 054X. The existing signature and docstring are unchanged. The new module
`Sheaf.AlgebraicGeometry.GenericOpenFibreDensity` states that assertion as
`AlgebraicGeometry.exists_open_fibre_dense_of_generic_dense`.

The proof supplies two parts of the original argument outright. First, geometric
irreducibility makes the ordinary generic source fibre irreducible and the open
fibre nonempty; its open immersion therefore has dense range. Second, density
in ordinary fibres passes to arbitrary field extensions because the projection
is open. `Scheme.Pullback.range_map` identifies both required inverse images
with the canonical fibre inclusions' ranges. The conclusion uses exactly the
double pullback map in the original signature. Surjectivity of the projection
is not needed: `Dense.preimage` only requires an open map.

The original module's proof import of `GenericFlatFinitePresentation` is replaced
by `GenericOpenFibreDensity`. The latter retains generic flat finite presentation
as the planned input to the remaining Tag 054X argument. Updated the original
node's proof, proof dependencies and proof origin, and added the new node.
No definition, existing statement, visibility, or target was changed.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.exists_open_geometric_fibre_dense_of_open`
(node `lem-sbc-generic-open-geometric-fibre-density`). Its proof is complete,
and the original module contains no `sorry`.

Added exactly one hole:
`AlgebraicGeometry.exists_open_fibre_dense_of_generic_dense`
(node `lem-sbc-generic-open-fibre-density`), in the new module
`Sheaf.AlgebraicGeometry.GenericOpenFibreDensity`.
Its entire proof is `:= by sorry`, with the source and the full Tag 054X
argument in its docstring. It asserts only ordinary-fibre density from supplied
generic density. It neither assumes geometric irreducibility nor concludes
anything about field extensions, so it is strictly the middle part of the
original argument, not the original statement under another name.

This delivery is a decomposition: one hole closed, one hole added, net zero.
The generic-density deduction and all geometric-base-change glue are proved.
Both modules compile together, without warnings, through `lcompile.py --all`.

## No longer needed

Removed the direct proof import
`Sheaf.AlgebraicGeometry.GenericFlatFinitePresentation` from the original module.
The old direct proof dependency node
`lem-sbc-generic-flat-finite-presentation` is replaced by
`lem-sbc-generic-open-fibre-density`. It remains a dependency through the new
ordinary-fibre theorem, so no module or node is claimed to have become globally unnecessary. No other imports were
removed. The unit's statement and its proof route are unchanged.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The original plan did not give a Lean declaration
for its Tag 054X dimension-specialization argument (step 2); the existing generic
flat finite presentation theorem alone does not supply that conclusion. The new
node isolates the ordinary-fibre part rather than treating the missing dimension
theory as elementary. Generic density and field-extension glue do have complete
Mathlib proofs. The original plan additionally invokes surjectivity of the
field-extension projection; the Lean proof shows openness alone suffices.

Read Stacks Tags 054X and 0559 online and checked the links to Tags 03HV
(generalizations lift under flat maps) and 054U (fibre dimensions along the
specialization of a fibre component's generic point). The dimension lemma's tag
is 054U. Searches of the entire DAG and imported blueprint found no separate
ordinary-fibre density node; blueprint searches for `054X` and `fibre dense`
returned no match. LeanFinder returned dominance and rational-map lemmas, not
the shrinking assertion. LeanSearch returned an HTTP internal server error,
recorded as unavailable. The recorded grep search found topological irreducibility
and nowhere-density lemmas, not a scheme-fibre shrinking result.

Edge cases checked for the new statement: the empty source and empty fibres
satisfy density vacuously; W equal to the whole source works on the whole base;
W empty is allowed precisely when the generic fibre is empty (Tag 054X then
shrinks away the whole source). Nonreduced bases are included by the reduction
universal homeomorphism. No noetherianity, separatedness, quasi-compactness of W,
or nonemptiness of every fibre has been added. Generic irreducibility in the
original theorem supplies nonemptiness only where used in its generic-density
argument.

## New nodes

`lem-sbc-generic-open-fibre-density` is the ordinary-residue-field part of
Stacks Tag 054X, formulated for the inverse image of an open source subset under
the canonical fibre inclusion. It belongs to the original chapter and unit,
records the three actual search kinds and their results, and retains
`lem-sbc-generic-flat-finite-presentation` as its proof dependency. Its proof
includes reduction, simultaneous flattening, the fibre-dimension contradiction,
and return to dense open complements. There are no change records or forced
adaptations.

## Second reading by F4

1. **Interface preservation: pass.** Read both delivered modules and compared the
   original module with the repository using `diff -u`. Only its proof and its
   plain proof import changed. The full existing theorem signature, docstring,
   public imports and visibility are byte for byte unchanged. There are no
   definitions, forced adaptations, or statement changes in this delivery.
   The existing node differs only in `proof`, `proof_deps`, and `proof_origin`.

2. **Lean proof and axioms: pass as a decomposition.** Compiled both files in
   import order with `lcompile.py --all`: clean, without warnings. Read the
   actual proof from the two geometric-irreducibility instances to the final
   double-pullback map. The first supplies an irreducible ordinary generic
   fibre; the second supplies a nonempty open fibre. The open immersion is
   therefore dense. `Scheme.Pullback.range_map` identifies its range with the
   inverse image of W. After ordinary-fibre shrinking, `Dense.preimage` applies
   to the open base-change projection, and a second range identity proves the
   exact displayed conclusion for every field K and every z. A scratch copy
   with `#print axioms` for both declarations reported exactly `propext`,
   `Classical.choice`, `Quot.sound`, and `sorryAx`; the latter remains through
   the explicitly reported ordinary-fibre theorem. No forbidden declarations
   or data chosen from an unproved existence theorem occur. Removed the scratch
   copy after checking. This does not establish an axiom-free proof of the item.

3. **Split-off statement: pass.** Independently read
   [Stacks Tag 054X](https://stacks.math.columbia.edu/tag/054X),
   [Tag 054U](https://stacks.math.columbia.edu/tag/054U), and the use of density in
   [Tag 0559](https://stacks.math.columbia.edu/tag/0559).
   For the reduced induced closed complement Z, generic density of the open W
   is exactly nowhere density of Z in the generic fibre. Tag 054X applies to
   finite type f (the Lean pair `LocallyOfFiniteType` and `QuasiCompact`) and a
   base with generic point; its nonempty base open contains that generic point.
   No noetherianity, reducedness, separatedness, quasi-compactness of W, or
   geometric irreducibility is required. The docstring includes the reduction,
   simultaneous generic flatness, dimension equality from 054U, and the
   contradiction to nowhere density. Tested empty X, empty individual fibres,
   W equal to X, W empty with empty generic fibre, a one-point base, and
   nonreduced bases. These agree with the statement. This is the ordinary-fibre
   middle step, not a renaming of the original geometric statement: the
   generic-density deduction and arbitrary field-extension argument are proved
   separately in the original module. New node and Lean signature agree.
   Independent LeanFinder search for a closed subset with nowhere dense generic
   fibre returned topological nowhere-density lemmas, not the shrinking result;
   `msearch.py grep` with `nowhereDense|NowhereDense|dense.*restrict|Dense.*fiber|Dense.*fibre`
   and `rg` over both library roots found no usable replacement. The recorded
   earlier LeanSearch outage is retained honestly. Closing the remaining hole
   requires scheme reduction and relative fibre-dimension machinery beyond a
   short repair; no additional hole was introduced by this reading.

4. **Route and pruning: pass.** The shortest available generic-density and
   base-change steps use proved Mathlib results. Checked the definitions of
   `IsOpenMap.denseRange_of_isPreirreducibleSpace`, `Dense.preimage`,
   `Scheme.Pullback.range_map`, and the `UniversallyOpen` instance over an
   integral subsingleton target. Surjectivity is unnecessary for density under
   inverse image. Both public import lists supply types in their statements;
   Sheaf imports are plain proof imports. Generic flat finite presentation is
   retained in the unfinished ordinary-fibre theorem's documented proof plan.
   The only old proof dependency is accounted for under No longer needed.
   Read `dag/units/sk-prop-normal-form.json`: its statement and two proof steps
   are untouched, and its `realized` lists are empty. No realized unit node or
   chapter route was bypassed. No module is claimed globally pruned.

5. **DAG agreement: pass.** The original node now records exactly generic
   density, ordinary-fibre shrinking via `lem-sbc-generic-open-fibre-density`,
   and open-projection base change. Its `proof_deps` is the union of those
   steps' uses. The new node records the finite type and scheme-fibre statement
   dependencies, source places, complete proof plan, generic-flat dependency,
   search results, provenance, original chapter and unit, creation metadata,
   and its verbatim Lean declaration. Checked both node signatures against
   their Lean files and all Lean lines against the 100-character limit.

Second reading changes: clarified the old dependency node under No longer
needed and added this independent review and axiom qualification. The Lean and
node files required no repair. Holes closed: the original geometric-density
hole; holes added: the ordinary-fibre-density hole; net zero, a decomposition.
