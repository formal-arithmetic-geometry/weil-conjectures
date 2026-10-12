## What changed

`lean/Sheaf/CategoryTheory/ExactCouple.lean` now proves
`CategoryTheory.BigradedExactCouple.derivedMaps_exists` from two strictly smaller
statements, retaining every existing signature and definition. Uses Mathlib’s `kernelSubobject_factors_iff` and
`imageSubobject_factors_comp_self` directly to turn image/kernel equalities
into zero composites; no duplicate zero-composite helper is declared.
The proof supplies the incoming differential equality definitionally, combines map
construction with exactness, proves all three complex relations, and assembles the
original `DerivedMaps` structure.

The two new modules are `Sheaf.CategoryTheory.DerivedCoupleMapConstruction` and
`Sheaf.CategoryTheory.DerivedCoupleMapExactness`. Construction gives only the induced maps
and their defining equations; it does not assert exactness or zero composites, and
needs only exactness at the D terms. This construction is fully proved in Lean:
`alpha` is an explicit image-factorization composite, `forward` is a cycle
restriction into the alpha image followed by cokernel descent, and `backward`
is obtained by descent through the image epimorphism of alpha using
`ShortComplex.Exact.isColimitImage`. Integer transports are proved by transporting
the raw map families and cancelling the canonical image/kernel inclusions. Exactness assumes these prescribed maps and
proves only the three subobject equalities; it asserts no existence.

The construction module also proves `CategoryTheory.derivedCoupleMapData_unique`
by mono image cancellation, epi cycle-quotient cancellation, and epi image
cancellation. Alpha is independent of any choice; the two maps stored in
`DerivedCoupleMapData` are uniquely determined by their descent equations.
Its existence theorem is proved from the actual kernel/cokernel universal
properties, with no unproved existence theorem or arbitrary object witness.

The new theorem statements and the combination proof compile together with the
library options. The boundary cast in the generic statement is proved by
`congrArg₂` applied to the actual kernel/cokernel family, not by a new assumption.

## Proved and sorry left

Closed the original hole in
`CategoryTheory.BigradedExactCouple.derivedMaps_exists` (def-sp-exact-couple).
Its proof is complete Lean, but this is a decomposition, not a complete proof
from standard axioms: one original hole is closed and one strictly lower hole
is added. The original item module contains no `sorry`.

The only hole added and left in this delivery is
`CategoryTheory.derivedCoupleMapData_exact`, in
`Sheaf.CategoryTheory.DerivedCoupleMapExactness`, node
`lem-sp-derived-map-exactness`. It has a whole proof `:= by sorry`, a source,
and the three complete natural-language chases in its docstring and node.
It asserts only exactness of already-given induced maps and supplies no maps,
no existence statement, and no complex identities.

The construction module contains no `sorry` and is proved from Mathlib alone.
Its fully proved public declarations are
`CategoryTheory.derivedCoupleAlpha_comm`,
`CategoryTheory.derivedCoupleForward_exists`,
`CategoryTheory.derivedCoupleBackward_exists`,
`CategoryTheory.DerivedCoupleMapData.alpha_comm`,
`CategoryTheory.derivedCoupleMapData_unique`, and
`CategoryTheory.derivedCoupleMapData_exists`.
The definitions `CategoryTheory.derivedCoupleAlpha` and
`CategoryTheory.DerivedCoupleMapData.alpha` are real image-factorization
constructions. Complete private helpers prove image lifting and descent and indexed transport.
Both modules obtain zero composites directly from Mathlib’s factorization API.

Edge cases were checked mathematically before finalizing the statements:
`s = 0` gives the original page-two couple and successor shift `(1,-1)`;
all zero objects give unique zero induced maps and zero subobjects; zero incoming
boundaries make the cycle quotient a cokernel of zero. No division by s, positivity
assumption, boundedness, or nonzero-map assumption is used. General s only affects
index transports, all verified in Lean. Uniqueness is proved without any exactness
assumption, so it holds in these degenerate cases as well.

## No longer needed

The duplicate private helpers `CategoryTheory.zero_of_image_eq_kernel` and
`CategoryTheory.BigradedExactCouple.comp_zero_of_image_eq_kernel` were removed
in this repair; all five uses now apply existing Mathlib factorization lemmas.
No original imports, nodes or modules are pruned: the original public Mathlib
import is still required for the statements. The only new direct proof import is
`Sheaf.CategoryTheory.DerivedCoupleMapExactness`, whose public import already
supplies the map construction theorem and data. A redundant direct import of
`Sheaf.CategoryTheory.DerivedCoupleMapConstruction` was removed after compilation.

The kernel pullback and differential-image identities, iteration formulas, and
page-image theorem bundled in `Sheaf.CategoryTheory.DerivedCoupleExact` are not
needed for this reduction. That module is not imported, and no global pruning of
it is claimed because other target paths may still use it. No other new helper
module or import is needed. The existing unit record has no realized node steps
for this definition; the construction and exactness clauses of the original
blueprint are retained, and no unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The returned delivery correctly identified duplicate zero-composite helpers.
Both were new in this delivery, and importing the item into its construction
dependency would be cyclic. Removed both helpers and used the existing Mathlib
`kernelSubobject_factors_iff` and `imageSubobject_factors_comp_self` at each call.
All three repaired modules compile together through `lcompile.py --all`.
The earlier second-reading section below describes the pre-repair delivery;
its references to the removed private helper are superseded by this repair.

The item's node is a definition with empty proof and proof_deps, although its Lean
contains the substantial existence-and-exactness theorem `derivedMaps_exists`.
The node copy now records the actual reduction into construction, exactness, and
assembly. This is a bookkeeping omission, not a false mathematical statement.

`CategoryTheory.BigradedExactCouple.derived_couple_exact` in the existing
`DerivedCoupleExact` module already asserts existence of the desired maps, but
that module imports this item. `tools/import_direction.py may` confirms that
importing it here closes an import cycle. The two new raw-data statements avoid
any dependence on `BigradedExactCouple`, on `derived`, or on `pageCouple`, so their
imports are acyclic. Construction is now fully proved; only exactness of the
constructed maps is left. This is a strictly smaller assertion than the original
Nonempty DerivedMaps conclusion, and the combination proof constructs and
assembles the original structure.

LeanSearch was attempted and returned Internal Server Error; recorded as
unavailable. LeanFinder and Loogle were run, and Mathlib and the source library
were searched locally. No direct exact-couple theorem was found. The local
literature tree lacks homology.tex on this machine; the official Stacks pages
for Tags 011R and 0AMJ were read. Tag 011R omits its proof; the detailed proof
plans are marked as authored by M1 from those clauses and the existing DAG node.
No definition, target signature, public import, or module held by another group
was changed; no forced adaptations or change records are needed.

## New nodes

`lem-sp-derived-map-construction`, at
`dag/nodes/sec-abelian-varieties/lem-sp-derived-map-construction.json`, records
construction and uniqueness of three induced maps satisfying the restriction
and descent equations, with no derived exactness assertion. Its Lean record
also names the fully proved forward/backward constructions, explicit alpha
restriction, uniqueness theorem, and real map-data structure. The existence
statement in this node is completely proved; this node adds no hole.

`lem-sp-derived-map-exactness`, at
`dag/nodes/sec-abelian-varieties/lem-sp-derived-map-exactness.json`, records
exactness of already-given maps with those defining equations. Its three chases
use the existing Mathlib-leaf node `lem-sp-abelian-refinements`.

## Earlier second reading (a previous round; superseded)

1. **Unchanged interface: PASS.** Read the complete diff against the repository
   module and checked it with the project's declaration parser: no existing
   statement changed. Only the proof of `derivedMaps_exists`, a private proved
   helper, and one plain proof import were added. Every existing definition and
   public import is byte-for-byte unchanged. No change records are required.
2. **Proof and trust: PASS as a decomposition.** Compiled all three modules in
   import order through `lcompile.py`: construction 3.8 s, exactness 1.7 s,
   item 2.8 s, exit 0 without warnings. Scratch-copy `#print axioms` checks of
   both alpha definitions and all six public construction theorems show only
   `propext`, `Classical.choice`, `Quot.sound`. The exactness theorem and the
   original existence/derived/iteration declarations additionally show
   `sorryAx`, precisely from the single reported exactness hole. The delivery
   tool also probes all constants. No forbidden trust mechanisms or holed
   definitions occur. The new choice in the item uses a fully proved construction
   theorem, and the descended maps are uniquely determined by the proved
   uniqueness theorem, so no arbitrary data comes from an unproved existence.
3. **Split statement: PASS.** Read all three exactness chases in the docstring
   and DAG, including the epimorphic-refinement and cokernel-kernel tests.
   The first chase lifts a kernel element through f into cycles; the second
   lifts a quotient class through g; the third subtracts an incoming f-lift of
   a boundary before lifting through a. Their converses use the original zero
   composites and epi/mono cancellation. The only hole is exactness of
   already-constructed maps, strictly less than construction plus exactness of
   an exact couple; it is not an existence restatement. Checked s = 0 and all
   zero objects. Also checked a = 0: exactness forces f epi and g mono, so both
   derived terms vanish; and invertible a: f = g = 0 and E = 0, so the derived
   D map remains invertible. The arguments require no nondegeneracy assumption.
   Independent LeanFinder, Loogle and targeted local searches found no usable
   duplicate. Read the official Stacks pages [011R](https://stacks.math.columbia.edu/tag/011R)
   and [0AMJ](https://stacks.math.columbia.edu/tag/0AMJ): the construction and
   successor shifts agree, and 011R explicitly omits its proof. Fully formalizing
   the remaining three chases is not a few-minute repair.
4. **Route and pruning: PASS.** The construction already uses Mathlib's image
   kernel/cokernel universal properties; no shorter usable theorem was found.
   `DerivedCoupleExact` imports this item, so using it here would be cyclic.
   The original node has empty proof_deps, hence no omitted old dependency to
   list under No longer needed. Each delivered import is necessary; the new
   public construction import occurs in the exactness theorem's signature.
   The unit record `sk-prop-av-pqf-finite` has empty realized statement and step
   entries; it is unchanged, and the derived-couple construction/exactness
   clauses are both retained. No pruning or net hole reduction is claimed.
5. **DAG agreement: PASS after wording clarification.** Compared the new Lean
   signatures, raw data assumptions, explicit alpha definition and three
   equalities with the nodes. Proof steps and proof_deps have the same uses;
   proof_origin identifies the authored construction/chases. The new nodes
   have source, search, creation, blueprint, chapter/unit and Lean records.
   Clarified the exactness node to give the derived maps' bidegrees explicitly
   and identify alpha as the actual explicit restriction, matching Lean.

Second-reading changes: clarified only the two new nodes' statement wording
(removed duplicated equation introduction; made exactness-map bidegrees and
explicit alpha unambiguous), added independent search records to those nodes,
and appended this review. No Lean proof or signature needed repair. One original
hole is closed (`CategoryTheory.BigradedExactCouple.derivedMaps_exists`) and one
is added (`CategoryTheory.derivedCoupleMapData_exact`): decomposition, net zero.


## Second reading by M1

This is an independent reading of the repaired delivery, superseding the earlier
reading above.

1. **Interface: PASS.** Read the complete item diff against the repository and
   checked the declaration parser: every existing signature, definition and
   public import is unchanged. Only the body of `derivedMaps_exists` and its
   plain proof import changed. Both additional modules are new. No target or
   other claimed module is changed, so no change record is needed.
2. **Proof and trust: PASS as a decomposition.** Compiled all three delivered
   modules together through `lcompile.py --all`, in import order, without errors
   or warnings (6.7, 2.5 and 6.5 seconds). Read the complete construction,
   uniqueness and assembly proofs. Scratch-copy `#print axioms` checks cover
   both alpha definitions, all six public construction theorems, the exactness
   theorem, the original existence theorem and derived/iteration definitions.
   Construction and uniqueness use only `propext`, `Classical.choice`,
   `Quot.sound`; exactness and downstream declarations additionally use
   `sorryAx` from the one reported hole. No forbidden mechanism or sorry in a
   definition occurs. The new choice uses a fully proved construction, and
   proved uniqueness determines the maps by their equations.
3. **Split statements: PASS.** Compared both new Lean signatures with their
   node signatures: exact matches after whitespace normalization. Read all
   three exactness chases; the boundary correction uses precisely `hβeq`,
   and the refinements justify lifting through epimorphisms in an arbitrary
   abelian category. Checked s = 0, zero objects, a = 0 (f epi, g mono, both
   derived terms zero), and invertible a (E zero, derived alpha invertible).
   No positivity or nondegeneracy is needed. The remaining statement proves
   exactness of prescribed, already constructed maps, not their existence;
   it is strictly part of the original argument. Its named whole-theorem hole
   has a source, complete proof docstring and node. Independent LeanFinder
   and Loogle searches with different queries, plus local searches on Mathlib,
   WeilConjectures and Sheaf, found no usable duplicate. Read the official
   Stacks [011R](https://stacks.math.columbia.edu/tag/011R) and
   [0AMJ](https://stacks.math.columbia.edu/tag/0AMJ): the constructions and
   shifts agree. The remaining three indexed refinement chases require more
   than a few-minute repair; no additional hole was introduced by this reading.
4. **Route and pruning: PASS.** Construction uses Mathlib's image kernel and
   cokernel universal properties directly, including the existing factorization
   lemmas in place of the removed duplicate helpers. The only direct proof
   import is exactness; its public construction import is needed in its
   signature. The item's original public Mathlib import is needed for its
   definitions. `DerivedCoupleExact` imports the item and cannot be used here
   without a cycle. Original proof_deps were empty, so there are no omitted
   old dependencies to prune. The recorded unit has empty realized statement
   and step entries and is unchanged; no unit route is bypassed.
5. **DAG: PASS after repair.** Checked proof steps, dependencies and origins
   against the Lean. Both new nodes have all required source, search, creation,
   blueprint, chapter/unit and Lean fields. Corrected the item's final assembly
   step, which still said it applied a private zero-composite helper despite
   that helper having been removed. It now records the actual direct Mathlib
   factorization proof. Added the current independent search records to the
   two new nodes.

Second-reading changes: corrected stale private-helper wording in the item's
DAG proof, added independent search records, and appended this review. No Lean
proof, definition or signature required a change. Holes closed: one,
`CategoryTheory.BigradedExactCouple.derivedMaps_exists`. Holes added: one,
`CategoryTheory.derivedCoupleMapData_exact`. This remains a decomposition with
net zero holes reduced; no modules are pruned.
