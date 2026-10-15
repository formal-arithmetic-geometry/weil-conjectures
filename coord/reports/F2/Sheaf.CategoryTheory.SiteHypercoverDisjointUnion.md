## What changed

Proved `CategoryTheory.SimplicialObject.site_hypercover_disjoint_union` with its signature
and its public helper `IsProperFaceMatchingArrow` unchanged. The coproduct universal properties
construct the simplicial object and the natural isomorphism to its sheaf realization. A private,
proved transport lemma treats degrees zero, one, and all higher finite boundary diagrams,
showing that every requested matching arrow is the conjugate of an epimorphism.

Added two fully proved modules:

- `Sheaf.CategoryTheory.FormalCoproductSheafRealization` constructs `sheafRealization` as
  Mathlib's formal-coproduct extension of sheaf Yoneda into the slice, proves
  `isColimitSheafCofan`, and proves `sheafRealization_preservesFiniteLimits`. The proof
  identifies formal-family Yoneda with restricted ordinary Yoneda, constructs the equivalence
  between formal families over T and the slice over the singleton T, applies left exact
  sheafification, and identifies the resulting functor by coproduct universal properties.
- `Sheaf.CategoryTheory.FormalCoproductSheafCoverEpi` proves `sheafRealization_map_epi`:
  cancellation is tested on each target representable summand, then sheaf separatedness
  reduces equality to the component covering family.

All proof-only dependencies are ordinary imports. The item's existing public imports are
unchanged. Updated its DAG proof and dependencies and recorded the two new proved lemmas.
No target, existing statement, or existing definition changed; no forced adaptations or
change records are needed. The unit's realized statements and steps remain unchanged.

## Proved and sorry left

Closed one existing hole:
`CategoryTheory.SimplicialObject.site_hypercover_disjoint_union`
(node `lem-weil-pbc-site-hypercover-disjoint-union`).

Added zero holes. Both new public theorems
`CategoryTheory.Limits.FormalCoproduct.sheafRealization_preservesFiniteLimits` and
`CategoryTheory.Limits.FormalCoproduct.sheafRealization_map_epi` are proved. Every helper in
all three delivered Lean files is proved or concretely constructed; there is no `sorry` in
these files. This is a proof, not a decomposition with unfinished split-offs.

The proof uses the already stated `matching_object_one` and `matching_object_succ_succ`
from `Sheaf.CategoryTheory.SimplicialMatchingObject`; their existing holes remain in that
unchanged dependency. Thus this delivery closes the assigned module's hole without claiming
that all of its transitive dependencies are already free of `sorry`.

Validation: all three modules compiled together in import order without warnings through
`lcompile.py --all`. The new constructions use Mathlib's actual coproduct and sheafification
constructions, not data chosen from an unproved existence statement. The argument includes
empty index sets, empty covering families, and matching degrees zero and one.

## No longer needed

Removed these direct proof imports from the assigned module:

- `Mathlib.CategoryTheory.Sites.LocallySurjective`.
- `Mathlib.CategoryTheory.Sites.LeftExact`.
- `Mathlib.CategoryTheory.Sites.Sheafification`.
- `Sheaf.Paper.SiteSheafificationSectionsLocal`.
- `Sheaf.CategoryTheory.SiteCoveringAxioms`.

The route no longer needs nodes `lem-weil-pbc-site-sheafification-sections-local` or
`lem-weil-pbc-site-sheaf-sets-epi-locally-surjective`: separatedness proves the required
covering epimorphism directly. It also does not use the `IsSiteForCoverings` declaration of
`Sheaf.CategoryTheory.SiteCoveringAxioms`, since the theorem already has the precoverage
and its hypotheses. These are pruning of this item's proof route; other parents may still
need those modules.

Left exact sheafification remains used inside the proved realization lemma, through
`Mathlib.CategoryTheory.Sites.LeftExact` and node
`lem-weil-pbc-sheafification-sets-exact`. Its import was relocated, not pruned from the
transitive argument. Likewise `def-weil-pbc-sheafification` is recorded at that new lemma,
and the site's definition remains a statement dependency. No unit-realizing node was removed.

## Where the brief, the DAG or earlier work was wrong

The stated plan is mathematically usable. Its local-lifting/sheafification-section step is
unnecessary: separatedness plus the coproduct universal property proves the covering epi
with fewer hypotheses and avoids proving the local-sections lemma. The source's finite-limit
comparison needed substantial categorical glue, now fully implemented rather than left as
an assumption. No statement was disputed or weakened.

The local literature checkout was absent. The official Stacks pages were read instead:
[01G2](https://stacks.math.columbia.edu/tag/01G2),
[01G3](https://stacks.math.columbia.edu/tag/01G3),
[0DB1](https://stacks.math.columbia.edu/tag/0DB1), and
[0DB2](https://stacks.math.columbia.edu/tag/0DB2).
LeanSearch returned an internal-server error; this is recorded as unavailable in the
search records. LeanFinder, Loogle, Mathlib text searches, repository searches, and the
blueprint-reference search were used before adding the new lemmas. No exact existing
realization/covering-epi theorem was found. Existing finite-limit and matching-object nodes
were reused.

## New nodes

`lem-weil-pbc-formal-coproduct-sheaf-finite-limits` records the finite-limit preservation of
the coproduct-of-representable-sheaves functor in the slice over h_T. It is fully proved in
`Sheaf.CategoryTheory.FormalCoproductSheafRealization`; the record also attaches the concrete
realization and the slice colimit helper. It implements Stacks 01G2 and exact sheafification
in the comparison of 0DB1/0DB2. No unfinished work remains in this node.

`lem-weil-pbc-formal-coproduct-sheaf-cover-epi` records that componentwise precoverage covers
induce epimorphisms under that realization. It is fully proved in
`Sheaf.CategoryTheory.FormalCoproductSheafCoverEpi` from sheaf separatedness. It applies
without pullback or precoverage-stability hypotheses and includes empty covers. No
unfinished work remains in this node. There are no change-record paths.

## Second reading by F2

1. I compared the delivered item module with the repository copy. The declarations
`IsProperFaceMatchingArrow` and `site_hypercover_disjoint_union` have byte-for-byte
identical signatures; no target statement or definition was changed. The delivery adds only
private proof helpers and the two new helper modules recorded in the new DAG nodes.

2. I compiled all three delivered modules with `python3 /home/ubuntu/weil-launcher/lcompile.py
--all` after pruning unused imports. There are no `sorry`, `axiom`, `unsafe`, `opaque`,
`extern`, `implemented_by`, or `debug.skipKernelTC` declarations. Scratch `#print axioms`
checks give only `propext`, `Classical.choice`, and `Quot.sound` for both new public lemmas.
The assigned theorem additionally transitively depends on the already-open matching-object
statements, so its axiom print includes `sorryAx` only through those imported declarations.

3. I checked both new statements against their Lean types and their node records. The finite
limit statement is the exact preservation claim used by the matching-cone transport, and the
covering-epi statement is exactly the componentwise cancellation property required by the
hypothesis. Empty index and empty-cover cases are covered by the universal-property and
separatedness arguments. Repository and Mathlib searches found no duplicate declaration.

4. I checked the proof from the top down. The simplicial object is built by coproduct descent,
and matching arrows are transported through the realization functor and its natural
isomorphism. The route keeps the unit's matching-object and finite-limit steps. The item no
longer needs `Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal` or
`Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products`; the helper realization module also
no longer needs `Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products`,
`Mathlib.CategoryTheory.Limits.Preserves.Yoneda`, or
`Mathlib.CategoryTheory.Limits.FunctorCategory.Basic`. The remaining imports all compile and
are used. The removed nodes and modules listed above remain available to other parents.

5. I compared all three node records with the delivered declarations and verified that their
Lean statements, proof dependencies, proof origins, chapter, and unit agree with the code.
The `sk-thm-properbasechange` unit's realized statement and steps are unchanged; this proof
uses the recorded matching-object and finite-limit route rather than bypassing a realized
unit step.

Second reading changed the report, pruned the five unused proof imports named in point 4, and
left the statements, definitions, nodes, and unit route unchanged.
