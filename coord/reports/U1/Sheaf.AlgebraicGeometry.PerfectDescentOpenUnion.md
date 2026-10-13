## What changed

Completed a compiling reduction of AlgebraicGeometry.perfect_descent_open_union,
with its signature and original docstring unchanged. For each open-immersion
presentation, the proof obtains compatible local data at a finite stage, applies
both clauses of derived_open_gluing, proves the glued object perfect using
local_perfect_of_openRestriction_iso, and proves the adjoint comparison invertible
using schemeDerived_isIso_of_openRestriction. A proved private categorical helper
expands the adjunction counit formula and uses naturality of the restriction
comparison to identify the local adjoints exactly; no compatibility equation is
assumed inside the final proof.

Added PerfectOpenGluingData, an explicit Prop-valued definition of the cover,
local perfect objects, overlap isomorphism, adjoint maps, compatibility equation,
and invertible local comparisons. It asserts no global stage object. The separate
theorem perfect_descent_compatible_local_data isolates the common-stage descent,
overlap descent and construction of the compatible local adjoints. It is the
only new hole. All new definitions have actual bodies and make no choices from
unproved existence statements.

Read Stacks Tags 09RF, 08DG and 08CM, the assigned node and unit record, and the
reused declarations. Lean Finder, Loogle, Mathlib and repository searches found
no shorter descent theorem. LeanSearch returned a service error; that unavailable
search is recorded in each new node. Existing open-model transport and isomorphism-locality
theorems eliminated an initially considered extra locality hole. The unit's route
is unchanged: descent of local objects and the overlap, adjunction, open gluing,
and the local check all remain.

All three delivered modules compiled together without warnings via lcompile.py
--all. The expanded finite-stage statement was expensive to export because it
repeated dependent base-change geometry throughout its local-data type. Defining
the geometry-independent local-data predicate once fixes that expression; it is
not a split of a proof or an increase of the compilation time limit. Final single
file timings are below the 60-second limit.

## Proved and sorry left

Closed: AlgebraicGeometry.perfect_descent_open_union
(node lem-pc-perfect-descent-open-union), by a complete Lean proof from the named
intermediate statement and existing library declarations.

Added and left: AlgebraicGeometry.perfect_descent_compatible_local_data
(node lem-pc-perfect-descent-compatible-local-data), whose entire proof is
`:= by sorry` in its own new module. Its docstring gives the full source argument.
It concludes only two local stage objects and their compatible maps, never the
global descended object or global comparison isomorphism of the original theorem.

The original module has no remaining sorry. PerfectOpenGluingData and the private
isIso_restricted_adjoint helper have none. This is one hole closed and one hole
added, hence a decomposition with net zero holes closed; it is not a complete
sorry-free proof of the target's closure.

## No longer needed

Removed the original module's direct proof imports PerfectDescendMorphisms,
DerivedAdjoint and DerivedDirectImageOpenRestriction; their corresponding nodes
lem-pc-perfect-descend-morphisms, lem-pc-ringed-spaces-derived-adjoint and
lem-pc-restrict-derived-direct-image-open now belong to the local-data helper's
proof dependencies and remain imported there. They are not pruned from the
transitive proof route. Original direct definition dependencies
def-pc-perfect-complex and def-pc-derived-category remain available through the
unchanged statement imports and the new helper; they are not eliminated notions.

For completeness, the old direct proof_deps omitted from the new node are
`def-pc-perfect-complex`, `def-pc-derived-category`,
`lem-pc-perfect-descend-morphisms`, `lem-pc-ringed-spaces-derived-adjoint`, and
`lem-pc-restrict-derived-direct-image-open`. The first two remain definition
and transitive dependencies; the latter three move into the local-data argument.
The sixth old dependency, `lem-sc-derived-open-gluing`, is retained directly.
No module or mathematical dependency is proved unnecessary in the transitive
closure. The proposed extra PerfectOpenCoverLocality module was discarded before
delivery because existing OpenPerfectModelTransport suffices. No new locality
node or sorry is delivered.

## Where the brief, the DAG or earlier work was wrong

The previous missing PerfectDescentOnOpen compiled artifact has been published;
the unchanged module now compiles, so the earlier tool blocker is resolved.

The DAG's proposed morphism-descent and gluing declarations do not by themselves
package the geometric transports from the two descent predicates to compatible
local stage data. That remaining construction is now a precise independent
statement, while the subsequent gluing, perfectness, and adjoint-isomorphism
arguments are Lean proofs. No statement or definition of the existing library was
changed. The new statements were checked on empty/equal/disjoint opens and empty
schemes; no nonempty-overlap assumption is introduced. The stage index i supplies
nonemptiness of the directed system. Neither helper imposes boundedness or
quasi-coherence beyond the original perfectness hypotheses.

## New nodes

`def-pc-perfect-open-gluing-data`, in PerfectOpenGluingData.lean, defines explicit
local gluing data for any morphism g and any derived object E. Its two restriction
comparisons and its counit formulas tie each local map to the precise comparison
whose invertibility is used in the final proof.

`lem-pc-perfect-descent-compatible-local-data`, in
PerfectDescentCompatibleLocalData.lean, states the portion of Tag 09RF before
Tag 08DG: local perfect objects at one stage, their descended overlap
isomorphism, and compatible local adjoints. It is strictly a part of the original
argument: the global object, perfectness, and global isomorphism are constructed
and checked in PerfectDescentOpenUnion.lean. Its proof dependencies retain the
original descent-of-morphisms and adjunction route.

No change record is required: no existing statement, definition or public import
was changed, and there are no forced adaptations.

## Second reading by U1

1. Compared the delivered existing module against the repository with diff.
   Verdict: the complete signature and original docstring of
   `AlgebraicGeometry.perfect_descent_open_union` are byte-for-byte unchanged.
   Only private proof code, its proof body, and plain proof imports change.
   There are no existing definition changes, public-import changes, or adaptations.
2. Independently compiled all three modules in import order with lcompile.py:
   9.3 seconds for PerfectOpenGluingData, 4.0 seconds for
   PerfectDescentCompatibleLocalData, and 21.2 seconds for PerfectDescentOpenUnion;
   no errors or warnings. Appended #print axioms to a scratch copy and compiled it.
   PerfectOpenGluingData and isIso_restricted_adjoint use only propext,
   Classical.choice and Quot.sound. The remaining helper and the original theorem
   additionally use sorryAx. Exactly one textual sorry remains, the whole proof
   of perfect_descent_compatible_local_data. No forbidden declarations or hollow
   definitions occur. Existential data are eliminated within the theorem's Prop
   proof; no definition chooses an arbitrary witness from the open theorem.
3. Read the local-data definition, helper statement, docstring, and both new nodes.
   Verdict: a valid decomposition, not a renamed global-descent assertion. The
   remaining helper supplies local perfect objects, an overlap isomorphism and
   compatible maps. The existing gluing theorem supplies the global object and
   map; the delivered proof establishes perfectness and global invertibility.
   Checked empty schemes, empty/equal/disjoint opens, the zero object, and a
   singleton index system: no additional nonemptiness or overlap condition is
   needed. The initial i supplies a stage even for empty geometry.
   Read Stacks 09RF and 08FE online because the recorded local perfect.tex is
   absent here: https://stacks.math.columbia.edu/tag/09RF and
   https://stacks.math.columbia.edu/tag/08FE. The local-data construction follows
   the portion of 09RF preceding global gluing. The overlap isomorphism clause of
   perfect_descend_morphisms already incorporates stabilization of inverse laws.
   Independent Lean Finder search for derived-category descent, overlap maps and
   adjunction, Loogle search for Adjunction.homEquiv_symm_apply, Mathlib grep for
   restricted adjunction/perfect-colimit/gluing results, and repository searches
   found no duplicate or shorter usable descent theorem. PerfectComplexDescent
   and FilteredCartesianPerfectDescent are downstream and cannot replace this step.
   Closing the remaining geometry-and-coherence construction is not a short repair.
4. Read the proof from the original theorem downward. Verified the private
   adjunction calculation by naturality, inverse cancellation and the counit
   formula; both local restrictions of the global adjoint are invertible. The
   inverse-image cover and existing locality theorems complete the global checks.
   Verdict: plain imports provide the actual proof tools; public imports provide
   statements/definitions. The helper's proof imports retain its unfinished plan.
   Expanded No longer needed to enumerate every omitted old direct proof_dep:
   none is pruned transitively. The unit sk-thm-picard-semicon and its realized
   fields are unchanged, and the descent/adjunction/gluing/locality route remains.
5. Compared the changed node's proof steps and dependency union with the Lean
   proof, and checked both new nodes' signatures, source, search records, creation
   metadata, chapter, unit, blueprint provenance and lean records.
   Verdict: the DAG records the implemented reduction and the outstanding local
   construction; no existing mathematical statement changes.

Second-reading changes: clarified the exhaustive accounting of removed direct
proof dependencies and added this independent review. No Lean or node repair was
needed. The result remains one original hole closed and one helper hole added,
a decomposition with net zero holes closed and no transitive module pruning.
