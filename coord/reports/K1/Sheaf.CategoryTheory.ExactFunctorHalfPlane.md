## What changed

Completed the three existing private helper proofs in
`lean/Sheaf/CategoryTheory/ExactFunctorHalfPlane.lean`.

* `stable_limits`: use the existing `page_zero` and `tower_stationary` helpers
  to prove stationarity after the specified bound. Identify the stationary
  cycles and boundaries with the given GLB and LUB.
* `stable_iso`: use the existing `stabilized_quotient_comparison` and cancel
  its isomorphism to obtain the required projection equation.
* `largePage_witness`: invert the normalized cocone map at `u = p-r` using
  `cocone_iso_nonpositive`. The equations `incomingAlphaIter_cocone` and
  `prescribed_inclusion_images` identify the images of both successive D
  inclusions after this cocone map with filtration steps p and p+1. Construct
  the step isomorphism using `Subobject.isoOfMkEqMk`. Use
  `derivedDInclusion_kernel`, `pageD_zero`, and exactness to identify the kernel
  of the epimorphic g map. Its cokernel comparison constructs psi with the
  required equation.

The existing public signatures, definitions, imports, top theorem body, and
unit route are unchanged. There are no new declarations or nodes and no
consumer adaptations. This implements the existing node proof, especially its
stationarity and explicit large-page construction steps.

Validation: the entire module compiles without warnings through lcompile.py.
All lines have at most 100 characters. The required dry run audits all module
declarations for nonstandard axioms. The argument is uniform for negative p,
r=0 when its bound holds, zero objects, and arbitrary normalized alpha colimits.

Shortest-route searches: LeanFinder returned exact-functor exactness/Ext
lemmas, not the requested half-plane comparison. Loogle returned no declaration
for the queried subobject equality helper. The msearch grep query returned no
hits; direct source reading found the already proved private helpers named
above, and these were reused instead of introducing intermediate obligations.

## Proved and sorry left

Closed 3 of 3 existing holes:

* `CategoryTheory.BigradedExactCouple.stable_limits` (private).
* `CategoryTheory.BigradedExactCouple.stable_iso` (private).
* `CategoryTheory.BigradedExactCouple.largePage_witness` (private).

All belong to `lem-sp-exact-functor-half-plane`. The public
`CategoryTheory.BigradedExactCouple.exactFunctor_halfPlane` now has its complete
local proof dependency chain filled. Zero sorry remains in the item. Zero holes
added, zero split off; this is a proof, not a decomposition.

## No longer needed

None. The two existing proof-only imports supply the tower, cokernel, image,
and normalized cocone helpers actually used. No node or module on the existing
route is pruned. A temporarily added direct import of FinitePageImageLift was
removed after compilation confirmed the existing import-all path suffices.

## Where the brief, the DAG or earlier work was wrong

No mathematical error was found. The node's proof_origin text already described
a complete Lean proof, but the delivered baseline actually retained three
private helper sorries. This delivery fills those precise gaps using the route
already recorded there. No statement or definition repair is needed.

## Second reading by K1

1. **Interfaces: pass.** Read the complete module and its diff against the shared
   repository. Replacing precisely the bodies of `stable_limits`, `stable_iso`,
   and `largePage_witness` by their original `sorry` reproduces the repository
   file byte for byte. All private and public signatures, definitions, visibility,
   imports, and the public theorem proof are unchanged. No change record or
   consumer adaptation is needed.

2. **Proofs: pass.** Independently compiled the delivered file with lcompile.py,
   without errors or warnings. A scratch copy with `#print axioms` for all three
   completed helpers and `exactFunctor_halfPlane` reports exactly `propext`,
   `Classical.choice`, and `Quot.sound` for each. No sorry, forbidden declaration
   form, or new data definition occurs. The existing finiteG definitions use
   proved factorization proofs. The public theorem's chosen weak-convergence
   comparisons are fixed by their projection equations, and those comparisons
   also pass the transitive axiom audit.

3. **Split statements and edge cases: pass.** No statement or hole was split off.
   Read the reused proofs in the repository's upstream modules
   HalfPlaneWeakConvergence, FinitePageImageLift, FinitePageGradedQuotient, and
   NormalizedGradedFiniteKernel. Stationarity uses both differential endpoint
   bounds at every t >= r, then handles t < r by monotonicity before applying
   the GLB/LUB laws. The large-page bound implies u=p-r <= -1 and
   q-1-r < a; these are precisely the cocone invertibility and derived-D
   vanishing requirements. For r=0 it forces p<=-1 and q<=a, so the same
   construction works. No nonnegative-p or nonzero-object assumption is used.
   The chosen lambda is explicitly the inverse of the cocone map, t is the
   canonical isomorphism of equal subobjects, and psi is fixed by its cokernel
   projection equation; no arbitrary existential witness supplies data.

4. **Shortest route and pruning: pass.** Independently searched with LeanFinder
   for eventual constancy of decreasing subobjects (results require Artinian
   hypotheses absent here), Loogle for `Subobject.map, imageSubobject` (unknown
   identifier), and msearch grep for stationarity and cocone helpers (no relevant
   Mathlib result). Direct rg/source reading found the existing page-zero,
   tower-stationarity, stabilized-quotient, cocone, prescribed-image, and derived-D
   kernel helpers that the proof already reuses. The existing public
   finitePage_graded_quotient specializes to nonnegative p and one selected page;
   it does not replace the arbitrary-page, arbitrary-integer witness required
   here. Both proof-only import-all modules supply private helpers used in the
   three proofs. ExactCoupleConvergence supplies public signature definitions.
   No import or old proof dependency became unused: `No longer needed` is
   complete. Read sk-thm-properbasechange's `realized` statement and step lists;
   no unit node or unit route is bypassed or changed.

5. **DAG agreement: pass.** Read lem-sp-exact-functor-half-plane and the Lean
   records of all seven proof dependencies. Its five steps match finite-g
   induction, stationary cycles/boundaries with the stable quotient comparison,
   weak-convergence naturality, explicit large-page witnesses, and mono/epi
   cancellation for naturality. The new bodies implement the already recorded
   second and fourth steps using precisely those helpers. The recorded
   proof_deps and proof_origin remain accurate; no node edit is necessary.

Second reading changed only this report by adding the independent checks above.
No Lean repair was needed. Closed 3 existing holes, added 0, split off 0;
no module or node was pruned.
