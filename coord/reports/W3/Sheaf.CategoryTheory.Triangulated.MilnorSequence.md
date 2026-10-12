## What changed

Completed the Lean proof of `CategoryTheory.milnor_shortExact` without changing its signature.
This is a decomposition with one remaining boundary-factorization obligation, not an
axiom-free proof of the Milnor theorem.

The right-hand map is explicitly constructed from a cone of cohomology projections.
Successor compatibility follows by projecting `p ≫ (1-s) = 0`; `NatTrans.ofOpSequence`
extends it to all tower arrows. `limit.lift` gives the map, simultaneously for every
specified triple, using zero on nondistinguished triples. The projection equations and
right-hand naturality square are proved in the item's module.

Added `Sheaf.CategoryTheory.Triangulated.MilnorProjectionFactorization`, proving
`CategoryTheory.milnor_projection_epi` from the existing derived-product theorem and
Mathlib's long exact cohomology sequence. It pulls a limit element back through the
cohomology-product comparison, proves that it is killed by the transition map, and
uses exactness to find its antecedent. This lemma only asserts surjectivity of an
already given projection-compatible map; it does not assert the Milnor sequence.

Added `Sheaf.CategoryTheory.Triangulated.MilnorBoundaryFactorization`, stating the
remaining connecting-map descent, its monomorphism, middle exactness before the product
of cohomology, and its naturality. It asserts no right-hand map or surjectivity.

The main proof constructs the monomorphism from the inverse limit to the product of
cohomology. It cancels this map to establish the zero composite and transfers exactness
using `ShortComplex.exact_iff_of_epi_of_isIso_of_mono`. It then supplies the mono and epi
fields of `ShortExact`. Thus the combination of the parts is a Lean proof, not an
application of a renamed Milnor theorem.

The original two-step product/long-exact-sequence route remains. The unit's `realized`
record does not assign this supporting node to a unit statement or step; no unit route
was changed. All files compile through `lcompile.py`; the required delivery dry run is
run after this report is written.

Sources inspected on the official Stacks site because the local checkout contains only
literature lists: [07KC](https://stacks.math.columbia.edu/tag/07KC),
[07KY](https://stacks.math.columbia.edu/tag/07KY), and
[07KW](https://stacks.math.columbia.edu/tag/07KW). The stored source references retain
the project's literature paths. Search attempts are recorded in `searches.jsonl`;
LeanSearch returned Internal Server Error, while LeanFinder and Mathlib source search
returned generic exactness/product tools rather than this theorem.

## Proved and sorry left

Closed the one original hole: `CategoryTheory.milnor_shortExact`
(node `lem-pc-derived-limit-milnor-sequence`). Its proof depends on the following new hole.

Added one hole, in its own new module: `CategoryTheory.milnor_boundary_factorization`
(node `lem-pc-milnor-boundary-factorization`). Its entire proof is `by sorry`, with a
source and complete natural-language construction in its docstring and node.

Also proved the new `CategoryTheory.milnor_projection_epi`
(node `lem-pc-milnor-projection-factorization`) from existing declarations. It has no sorry.
The private definition `milnorProjectionCone` contains no sorry, including its compatibility
proof. No other sorry is left in any delivered file.

Accounting: one upper hole closed, one lower hole added; this is a decomposition, net zero
holes, with the right projection, its surjectivity, its naturality, and the exactness
assembly now implemented. Existing imported sorries, notably the derived-product theorem
and the Roos computation needed by the boundary obligation, remain unchanged.

Edge cases checked: zero objects, all-zero towers, arbitrary negative degrees, and
nondistinguished triples. The conditional zero map is used only outside the distinguished
hypothesis. No bound, Mittag-Leffler condition, or surjective transition assumption was added.

## No longer needed

Removed the direct proof import of
`Sheaf.CategoryTheory.Triangulated.DerivedLimitExistence` from the item's module. It is
used in the proof of `milnor_projection_epi` and remains in that new module's imports;
therefore it is not globally pruned. Added two non-public proof imports of the new modules
and the non-public import `Mathlib.CategoryTheory.Functor.OfSequence`.

No existing module or node has become unnecessary in the transitive proof route. The
original product, exact-products, long-exact-sequence, and Roos nodes remain dependencies
through the new nodes. Pruned: none. New modules import only what their statements or
proofs use; neither makes extra proof imports public.

## Where the brief, the DAG or earlier work was wrong

No mathematical error or statement dispute was found. The stated Roos theorem supplies
natural isomorphisms but does not pin its kernel isomorphism to the limit projections.
The proof therefore constructs the right map from its cone directly, and proves
surjectivity by exactness, without assuming extra compatibility of that isomorphism.

The local literature files named in the DAG are absent on this machine, so the official
pages above were read. The source-library search found no already proved Milnor statement.
No source or target statement was changed.

## New nodes

`lem-pc-milnor-boundary-factorization` records the natural left injection and exactness
before the product of cohomology. It is the sole new unfinished obligation, strictly one
side of the Milnor argument. Module:
`Sheaf.CategoryTheory.Triangulated.MilnorBoundaryFactorization`.

`lem-pc-milnor-projection-factorization` records that any map satisfying the cohomology
projection equations is epi. Its proof is complete, using the original product and
long-exact-sequence dependencies. Module:
`Sheaf.CategoryTheory.Triangulated.MilnorProjectionFactorization`.

Updated the parent node's `proof`, `proof_deps`, and `proof_origin` to the implemented
construction and assembly. No change records are needed because no existing statement
or definition changed.

## Second reading by W3

1. Diff check: the existing `milnor_shortExact` signature is byte-for-byte unchanged; the two added modules and three node records are new, and the parent node records only proof metadata changes. Verdict: pass.
2. Compilation and proof audit: all three modules compile with `lcompile.py --all`; the only remaining `sorry` is the named `milnor_boundary_factorization`, documented in its theorem and node. No definitions contain `sorry`, and no forbidden declarations were found. Verdict: pass.
3. Statement review: the split boundary theorem is a strictly smaller factorization/exactness obligation, while the projection theorem is a supporting epi lemma; neither restates the Milnor target or weakens it. Edge cases and nondistinguished triples are handled by the zero branch. Verdict: pass.
4. Route and pruning: the proof uses the constructed cone, projection epi lemma, boundary factorization, and exactness transfer. The removed `DerivedLimitExistence` import is no longer directly needed by the main module; no other imports or nodes can be pruned. Verdict: pass.
5. DAG agreement: parent and new nodes name the declarations, proof dependencies, sources, and split status matching the Lean files; the unit route and `realized` record are unchanged. Verdict: pass.

Changed only the report during this second reading; no Lean proof or statement repair was necessary.
