## What changed

Replaced the sole `sorry` in
`CochainComplex.exists_differentials_on_graded_model_of_directed_colimit` by a complete
assembly proof without changing its signature or docstring. Added the modules
`Sheaf.Algebra.Homology.BoundedGradedFamilyMapColimitDescent` and
`Sheaf.Algebra.FiniteFamilyModuleMapEqualityColimit`.

The graded-family helper is proved by specializing the already landed
`CochainComplex.exists_bounded_graded_map_of_directed_colimit` to zero-differential
complexes with terms M(n) and M(n+1). This descends arbitrary adjacent maps and supplies
canonical coherent comparisons without assuming square-zero. The assembly then cancels
comparison isomorphisms to obtain zero composites over the colimit, imposes finitely many
adjacent composite equalities at a common later stage, handles all remaining triples by
shape or a zero source, and transports maps back to direct scalar extensions. Naturality
proves the final compatibility squares.

All existing public imports and declaration visibility are unchanged. The added imports
used only by proofs are plain imports. The graded-family module publicly imports
`Mathlib.Algebra.Homology.ComplexShape` for shape notation in its statement, and privately
imports the existing bounded graded component-map module. Updated node proofs and their
dependencies to match the final Lean route.

## Proved and sorry left

Closed the original hole:
`CochainComplex.exists_differentials_on_graded_model_of_directed_colimit`
(lem-pc-affine-differential-colimit-descent). No sorry remains in the item's module.

The second reading also closed the proposed new hole
`ModuleCat.exists_bounded_graded_maps_of_directed_colimit`
(lem-pc-bounded-graded-family-map-colimit-descent), using the existing bounded graded
component-map theorem; it is delivered as a proved helper, not a new hole.

Added one hole:
`ModuleCat.exists_stage_finite_family_map_eq`
(lem-pc-finite-family-module-map-equality-colimit). It remains a named theorem with source,
complete natural-language proof and node. It has no complex data and only equalizes maps
already defined at a stage. Its proof still needs finite simultaneous equality descent,
canonical comparison transport and the preorder-to-partial-order reduction.

This is a decomposition of one original hole into one new hole, not a sorry-free proof
or a claim of positive net hole progress. The existing holes in
`CochainComplex.exists_bounded_graded_map_of_directed_colimit` and
`ModuleCat.finitePresentation_descent_directedColimit` are unchanged.
Axiom probes for every delivered theorem show only propext, Classical.choice, Quot.sound
and sorryAx from the reported open statements.

## No longer needed

Removed the direct proof import `Sheaf.Algebra.FinitePresentationColimit` from the item's
module. Its old dependency `lem-pc-fp-module-map-descent-affine` is no longer direct, but
remains under equality descent and the existing component-map theorem. No old dependency
is wholly eliminated and no module is claimed globally pruned. All original public imports
remain. The graded-family helper now uses
`Sheaf.Algebra.Homology.BoundedGradedMapColimitDescent`, replacing its planned direct import
of `Sheaf.Algebra.FinitePresentationColimit`. Its broad homology import was narrowed to
`Mathlib.Algebra.Homology.ComplexShape` for the public statement.

## Where the brief, the DAG or earlier work was wrong

The earlier returned sandbox collided with N4's landed
`Sheaf.Algebra.Homology.BoundedGradedMapColimitDescent` module and node. The first worker
relocated its helper to BoundedGradedFamilyMapColimitDescent, preserving the landed file.
The second reading found that N4's theorem, although not an exact duplicate, can prove
this helper by representing both term families as zero-differential complexes. This
shorter route removes one proposed new hole. Deleted only the obsolete sandbox compiled
artifact for the old colliding module, which otherwise shadowed the actual landed theorem.
No repository source or compiled shared-library file was changed.

Read Stacks Tags [0BC7](https://stacks.math.columbia.edu/tag/0BC7), proof of (1), and
[05N7](https://stacks.math.columbia.edu/tag/05N7), clauses (2) and (3).
These give map descent and equality descent with fixed finitely presented term models.
The assertions here do not require flat transition maps or Noetherian hypotheses.
The literature source and blueprint section files are not materialized on this machine.
The unit record sk-thm-picard-semicon has empty realized entries; its given bounded affine
map-then-relation route is preserved without changing the unit record.

## New nodes

`lem-pc-bounded-graded-family-map-colimit-descent` carries the proved specialization from
arbitrary adjacent graded maps to the existing component-map descent theorem, with that
node as its sole proof dependency. It imposes no square-zero relation.

`lem-pc-finite-family-module-map-equality-colimit` carries common-stage equality for a finite
family of maps between fixed finitely presented modules. It has no differential or complex
input. Its sole proof dependency is lem-pc-fp-module-map-descent-affine. Its finite indexing
type has an independent universe parameter.

Both nodes inherit the item's chapter and unit, carry Lean statements verbatim, and cite
the appropriate affine approximation blueprint step. Their search records are present in
searches.jsonl. No change record is needed: no existing interface is changed or adapted.

## Second reading by X2

1. Compared the delivered item with the repository version. The sole existing theorem
signature is byte for byte identical, including every hypothesis, conclusion, universe
and binder. Its original docstring and public imports are retained. No existing definition
is changed. The existing node differs only in proof, proof_deps and proof_origin. The two
additional module paths and nodes are new and do not overwrite N4's landed module. Pass.

2. Compiled all three modules in import order through lcompile.py. No errors or warnings
remain. Scanned all delivered Lean: the only sorry is the named equality theorem; there
are no axioms, unsafe/opaque declarations, implemented_by or extern attributes, hollow
definitions or arbitrary data selected from unproved existence. The helper's two local
complexes are constructed with explicit zero differentials. Scratch axiom probes show
only the standard three axioms and sorryAx. The main proof uses hGfp to justify equality
descent after base change, hcomp to cancel comparison isomorphisms, the finite interval
for adjacent triples, and canonical conjugation/naturality for the final stage. Pass.

3. Matched both new statements with their Lean nodes and Stacks 05N7 (2)/(3). Empty T
allows i; empty or reversed bounds force every term to be zero; singleton support gives
zero adjacent maps; a one-stage diagram reduces to scalar comparison. Distinct mutually
comparable preorder indices need no antisymmetry in either final statement. Arbitrary
adjacent identity maps on three nonzero terms test that the map helper has no hidden
square-zero assumption. Both lemmas are true and strictly separate parts of the original
argument. The equality theorem requires finitely presented sources and targets exactly
as its cited dependency supplies. Its docstring explains finite upper bounds, transport
and the preorder reduction. Searched repository and upstream Lean with eventual-equality,
scalar-extension and bounded-graded words; additional msearch queries were LeanFinder
"eventual equality of scalar extended linear maps over a filtered ring diagram", Loogle
"Module.FinitePresentation, CategoryTheory.Functor.map", and grep
"extendScalars.*(eq|exists)|exists.*extendScalars". The Mathlib hits concern fixed-ring
filtered colimits or scalar equivalences, not the needed varying-ring equality theorem.
The existing N4 component theorem does suffice for the map helper, and was used. Pass
with that repair; the one remaining equality hole is genuinely narrower than the item.

4. Read downward from the target proof, including the current imported finite-presentation
and N4 component-map declarations. The shorter N4 specialization is now implemented.
All nonadjacent triples and out-of-support sources are handled explicitly in the assembly;
no new theorem merely renames the whole target. No old proof dependency is wholly pruned:
the finite-presentation node remains beneath the new route. The report distinguishes
replacement of direct imports from global pruning. Read the unit record's realized field
and step: zero-differential auxiliary complexes do not change its bounded affine
map-then-relation argument or bypass another unit. Pass.

5. Read all three node files. The item has the two actual helper dependencies; the map
helper now cites N4's existing component-map node; the equality helper cites the existing
finite-presentation descent node. Their proof steps describe the Lean assembly and the
remaining equality argument, respectively. Checked chapter, unit, source, created,
blueprint, search and Lean records of the new nodes. Pass.

Changed in this second reading: proved the map helper by the N4 specialization, replaced
its proof-only import and node route, updated its new declaration docstring, removed stale
sandbox artifacts of the earlier collision, and rewrote the report to count just one added
hole. The original assembly proof and every existing signature were left intact.
