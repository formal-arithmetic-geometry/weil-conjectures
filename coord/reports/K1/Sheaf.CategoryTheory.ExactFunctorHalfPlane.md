## What changed

Repaired the upstream-sync compile failure in
`lean/Sheaf/CategoryTheory/ExactFunctorHalfPlane.lean`. Recovered the previous
K1 proof from returned delivery head `5e4b38de41` (landed as `58f66706d6`);
the retained sandbox initially held only launcher metadata.

The returned proof fails on the current build with unknown identifiers
`tower_stationary`, `stabilized_quotient_comparison`,
`cocone_iso_nonpositive`, and `prescribed_inclusion_images`. The upstream sync
retired the two Sheaf helper modules into re-export wrappers. Changed the two
proof-only `import all` lines to import their current upstream modules directly:
`WeilConjectures.CategoryTheory.FinitePageGradedQuotient` and
`WeilConjectures.CategoryTheory.NormalizedGradedFiniteKernel`.
This exposes the existing private helpers through their actual modules and
makes the complete proof compile cleanly (2.5 seconds through lcompile.py).
This is a concrete import repair, beyond rebasing the previous delivery.
An explicit lcompile.py axiom probe for all three helpers and
`exactFunctor_halfPlane` reports only `propext`, `Classical.choice`, and
`Quot.sound` (3.6 seconds). A static declaration comparison reports no changed
signature and zero remaining holes; all lines are at most 100 characters.
Both new proof import edges pass import_direction.py.

Retained all three complete helper proofs: `stable_limits` identifies stationary
cycles and boundaries with the specified GLB/LUB; `stable_iso` uses the existing
stabilized quotient comparison; `largePage_witness` constructs lambda, t and psi
from the normalized cocone, prescribed D images, and cokernel universal property.
No signature, definition, visibility, public import, or public theorem body changes.
The node copy updates only proof/proof_origin to name the current helper source.
There are no consumer adaptations or statement/definition change records.

Read all seven recorded proof dependencies, their current Lean signatures, and
the proper-base-change unit's realized route. The route is unchanged. The
construction applies to negative p and zero objects; at r=0 the stated bound
forces p <= -1 and q <= a, and the same argument applies.

Repeated shortest-route searches with msearch.py: LeanFinder returned general
homology exactness results rather than this comparison, Loogle did not recognize
`Subobject.map`, and the grep service returned no hits. Direct source searches
located all reused helpers in their current upstream modules; no new mathematical
obligation or duplicate declaration is needed.

## Proved and sorry left

Closed 3 of the current baseline's 3 holes, all on
`lem-sp-exact-functor-half-plane`:

- `CategoryTheory.BigradedExactCouple.stable_limits` (private).
- `CategoryTheory.BigradedExactCouple.stable_iso` (private).
- `CategoryTheory.BigradedExactCouple.largePage_witness` (private).

Zero sorry remains in the item, zero holes added, zero split off.
`CategoryTheory.BigradedExactCouple.exactFunctor_halfPlane` retains its original
statement and now has all local proof dependencies completed. This is a proof,
not a decomposition. Relative to the returned delivery, the repair changes only
the two proof-only imports; the three completed proofs are retained.

## No longer needed

Removed proof-only imports of the retired wrapper modules
`Sheaf.CategoryTheory.FinitePageGradedQuotient` and
`Sheaf.CategoryTheory.NormalizedGradedFiniteKernel`, replacing each by its
upstream source module. The underlying mathematical dependencies remain needed.
No node or module is pruned from the proof route. The public import of
`Sheaf.CategoryTheory.ExactCoupleConvergence` is unchanged.

## Where the brief, the DAG or earlier work was wrong

The previous proof imported private helpers through Sheaf modules that the
upstream sync subsequently replaced with wrappers. Those imports no longer
provided the helpers; direct upstream import-all restores them. The returned
compile error is reproduced and repaired without changing mathematical statements.
The node's earlier proof_origin said the proof was complete while the current
baseline still has three private helper holes; this delivery restores those proofs.


## Second reading by K1

1. **Unchanged interfaces — pass.** Read the complete 600-line module and its
   repository diff. An exact text comparison, replacing only the three completed
   proof bodies and restoring the two original import lines, reproduces the
   repository file byte for byte. Every existing signature, definition, docstring,
   visibility, and other proof body is unchanged. No statement/definition change
   record or consumer adaptation is needed.
2. **Proof and axioms — pass.** Independently compiled the delivered file through
   lcompile.py (2.7 seconds, no errors or warnings). Compiled a scratch copy with
   `#print axioms` for all 13 local declarations, including the two definitions,
   all private helpers, transport_square, and exactFunctor_halfPlane (3.6 seconds).
   Every axiom list is contained in propext, Classical.choice, and Quot.sound;
   there is no sorryAx. Static inspection finds no sorry, axiom, unsafe, opaque,
   implemented_by, extern, or skipped kernel check. finiteG and finiteGCycles are
   explicit factorizations; no data is selected from an unproved existence claim.
3. **Split statements and small cases — pass.** No statement or hole is added,
   and none is split off. Checked the strict stable-page bound: for every t >= r,
   the outgoing second index is below a and the incoming first index is negative.
   At r = 0 this bound forces p <= 1 and q <= a, exactly killing the adjacent
   initial differentials. Checked the large-page bound separately: it implies
   u = p-r <= -1 and q-r-1 < a. In particular r = 0 forces p <= -1 and q <= a,
   so the normalized cocone and zero following D term still apply. Negative p
   and zero objects require no extra hypothesis. Independent LeanFinder search
   found coimage/epi cokernel ingredients already underlying the reused quotient
   helper; Loogle and grep searches for antitone GLBs/stationary sequences found
   no shorter comparison replacing this argument. No duplicate theorem is added.
4. **Route and pruning — pass.** Read the seven recorded dependency statements,
   the actual upstream helper proofs, and sk-thm-properbasechange.realized.
   The proof follows finite-g naturality, stationary limits, weak-convergence
   comparison, normalized cocones, prescribed D images, and quotient comparison.
   Both private imports are used: FinitePageGradedQuotient exposes the stationary,
   quotient, D-image and derived-kernel helpers, while NormalizedGradedFiniteKernel
   exposes the normalized cocone and incoming-alpha cocone helpers. Both remain
   proof-only imports. The existing public ExactCoupleConvergence import supplies
   the signature's notions. Every old proof dependency remains used through its
   definitions or proved helpers, so there is no omitted prunable node or module
   and no bypass of a realized unit step.
5. **DAG agreement — pass after a wording repair.** The node's statement and Lean
   record still match the unchanged public theorem. Its five proof steps and all
   seven proof_deps describe the actual proof, using the upstream helpers rather
   than the retired wrappers. Corrected step 2 to name
   stabilized_quotient_comparison, the helper actually called by stable_iso,
   rather than quotient_comparison (which is called by largePage_witness).

Second reading changed only that helper name in the node's proof text and added
this review record. No Lean repair was necessary. Independently confirmed the
reported count: three baseline holes closed, zero holes added, zero remaining,
zero split off; this is a complete proof, not a decomposition.
