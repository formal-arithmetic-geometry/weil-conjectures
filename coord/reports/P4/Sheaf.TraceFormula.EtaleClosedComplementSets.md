## What changed

Proved `AlgebraicGeometry.etaleClosedComplementSets` in
`lean/Sheaf/TraceFormula/EtaleClosedComplementSets.lean`, preserving its signature and the
bodies of `etaleSetDirectImage`, `etaleSetInverseImage`, and `etaleSetAdjunction`.

The proof reuses the existing arbitrary-coefficient full/faithful closed pushforward and
compares the open inverse image with restriction by uniqueness of left adjoints. For the
converse essential-image direction, terminal restriction gives terminal sections over the
open complement. Sheaf transitivity then gives descent for the topology induced by base
change to the closed subscheme, and the dense-subsite equivalence gives the desired sheaf
on the closed subscheme. Five proved private helpers implement this argument. No source-tree
file was edited.

Replaced the public composition-unit import with the smaller `UpperLowerStar.Defs`, and
replaced the old stalk proof imports with `OpenClosed.Supported` and
`Etale.LowerShriek.OpenImmersion.Complement`. Updated the DAG proof to the actual route.
The file compiles cleanly, and the three original direct consumers compile unchanged.
`#print axioms AlgebraicGeometry.etaleClosedComplementSets` reports exactly `propext`,
`Classical.choice`, and `Quot.sound`. Empty schemes and empty complements are covered by
empty-cover terminality and the same induced-topology proof.

## Proved and sorry left

Closed 1 of 1 original holes: `AlgebraicGeometry.etaleClosedComplementSets`
(node `lem-trf-etale-closed-complement-sets`). Zero holes remain in the item; zero holes are
added elsewhere. This is a complete proof, not a decomposition. The two new DAG records
attach already proved existing source declarations; neither creates a Lean module or a hole.
All private helpers are proved.

## No longer needed

Removed imports from this item:

- `WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits`
- `Sheaf.CategoryTheory.Sites.GeometricMorphism`
- `Sheaf.AlgebraicGeometry.PointedEtaleStalk`
- `WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageStalkGerm`
- `WeilConjectures.SixFunctors.OpenClosed.Stalk`

Removed proof dependencies, because the induced-topology proof needs no geometric stalks,
pointed-neighbourhood initiality, colimit calculation, explicit germ formula or unit formula:

- `def-weil-size-convention`
- `lem-weil-pbc-sets-etale-inverse-image-composition-units`
- `def-trf-geometric-morphism`
- `lemma-openclosed-stalk-lowerstar`
- `def-weil-pbc-geometric-stalks`
- `lem-weil-pbc-initial-functor-limit`
- `def-weil-pbc-category-colimit`
- `lem-weil-pbc-sets-etale-inverse-image-stalk-germ`
- `lem-weil-pbc-sets-etale-iso-on-geometric-stalks`

Removed the three obsolete top-level `tool_uses` approvals: `lemma-openclosed-stalk-lowerstar`,
`lem-weil-pbc-sets-etale-inverse-image-composition-units`, and
`lem-weil-pbc-sets-etale-inverse-image-stalk-germ`. Historical split/review records are preserved.
The unchanged statement dependencies still describe the geometric-morphism and adjunction
conventions; these are not used as proof lemmas. No module is withdrawn or source declaration
removed. These are item-local dependency removals; other consumers may still need the modules.
In particular `OrientedClosedBaseRestriction` explicitly imports the composition-unit module.

## Where the brief, the DAG or earlier work was wrong

The original geometric-stalk plan was unnecessarily long. The source library already proves
fullness and faithfulness for arbitrary coefficients; its abelian supported-sheaf theorem
cannot itself be instantiated at sets, but its underlying covering-sieve argument applies
with terminal section types in place of zero objects. The new proof writes that set argument.
No mathematical statement repair, target change, or bypass of a blueprint unit is involved.
The existing theorem docstring retains the original plan as documentation; the node's updated
six proof steps record the shorter argument actually implemented.

## New nodes

`lem-trf-etale-closed-base-change-density` records the already proved cover-density, local
fullness and local faithfulness of closed-immersion base change in
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.ClosedImmersion`. Locality is explicitly
measured using the topology on the closed subscheme, not the original topology on the ambient
scheme. The graph and agreement-locus arguments are recorded in full. Three Mathlib searches
are included; no new Lean declaration is introduced.

`lem-trf-etale-open-closed-sieve-cover` records the existing proved
`AlgebraicGeometry.Etale.sup_sieveOfRangeSubset_mem` in `OpenClosed.Supported`, together with
its sieve definition. A sieve covering after closed base change covers the ambient object
once the open-complement sieve is added. Its two pointwise cases, including the empty case,
are recorded. Three Mathlib searches are included; no new Lean declaration is introduced.

Change record: `coord/changes/p4-etale-closed-complement-imports.md`.

## Second reading by P4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
