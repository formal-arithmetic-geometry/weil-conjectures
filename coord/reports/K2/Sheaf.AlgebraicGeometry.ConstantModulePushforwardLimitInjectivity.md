## What changed

Replaced the sole sorry in `Sheaf.AlgebraicGeometry.ConstantModulePushforwardLimitInjectivity`
with a complete Lean proof from a new finite-approximation lemma,
`AlgebraicGeometry.Etale.exists_constantModulePushforward_germ_eq_zero` in
`Sheaf.AlgebraicGeometry.ConstantModulePushforwardGermVanishing`.
The original declaration and all its hypotheses and universes are unchanged.

The proof takes a representative of a kernel element of the comparison on a geometric
stalk, transports it using hι and eK, applies eventual vanishing, transports the resulting
zero using hK, and uses colimit.w to conclude that the original element is zero.
Conservativity of the geometric-point family then gives monicity. This is a reduction,
not a renamed statement: the new lemma has no K, cocone, colimit, eK, e, or monomorphism
conclusion, and supplies a concrete transition arrow killing one stage element.

Updated the original node's proof, proof_deps and proof_origin to this route.
Both modules compile with the prescribed launcher; the remaining sorry is intentional.

## Proved and sorry left

Proved (relative to the named remaining geometric lemma):
`AlgebraicGeometry.Etale.mono_constantModulePushforwardComparison`
(lem-weil-pbc-constant-module-pushforward-limit-injectivity).
There is no sorry in the item's module. This closes one upper hole and adds one
lower hole: a decomposition, with net zero holes closed, not an unconditional proof.

One new sorry remains:
`AlgebraicGeometry.Etale.exists_constantModulePushforward_germ_eq_zero`
(lem-weil-pbc-constant-module-pushforward-germ-vanishing).
Its proof plan is finite approximation on affine etale neighborhoods, using the
existing section-continuity theorem and compatibility of canonical constant-sheaf maps.
The new lemma's statement was checked against zero modules, empty limit schemes,
singleton index categories, non-directed cofiltered categories, and non-quasi-separated
bases X. In the last case the argument works over an affine etale neighborhood U,
not over X: the base of the section-continuity theorem is quasi-separated.

## No longer needed

Removed proof imports:
- `Sheaf.AlgebraicGeometry.HigherDirectImageLimitSystem`
- `Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful`

The direct-image continuity route through derived degree zero and the general
ring-sheaf-module forgetful comparison is unnecessary. Its corresponding nodes
`sbc-lem-higher-direct-image-limit` and
`lem-weil-pbc-module-sheaves-colimits-forgetful` are not used by this reduction,
including the new lemma's plan. The replacement uses ordinary section continuity.
No surjectivity or descent of sections is needed.

The following old proof dependencies are no longer immediate dependencies of this item:
`def-weil-pbc-direct-image`, `lem-weil-pbc-colimit-constant-connected-diagram`,
`lem-weil-pbc-constant-module-pushforward-functoriality`,
`lem-weil-pbc-filtered-category-exists-directed-final`,
`lemma-constructible-pullback-constant`, plus the two nodes just listed.
Direct image, canonical constant maps, constant pullback, and final directed reindexing
remain notions or tools of the new germ lemma; they are not claimed globally pruned.
The constant connected-colimit calculation is handled within existing section continuity.
The unit sk-thm-p1 statement and realized steps are untouched; none is bypassed.
These are local dependency removals, not claims that other target branches no longer
reach these modules.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was changed or disputed. The old proof plan's coefficient
forgetting theorem concerns SheafOfModules over a sheaf of rings, whereas this item's
actual category is Sheaf with ModuleCat coefficients. The combining proof can work
with ModuleCat-valued stalks directly, avoiding that category-interface conversion.

LeanFinder, Loogle and Mathlib/source grep found no direct canonical germ-vanishing
result. LeanSearch was attempted and returned Internal Server Error; no absence
verdict is inferred from that outage. The source Tags 09Z1, 09YQ and 09Z6 were read
online. The repository has only literature metadata on this machine.

## New nodes

`lem-weil-pbc-constant-module-pushforward-germ-vanishing`, in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-constant-module-pushforward-germ-vanishing.json`,
states the concrete eventual-zero witness for a canonical stage germ. Its module is
`Sheaf.AlgebraicGeometry.ConstantModulePushforwardGermVanishing`.
Its complete proof in words reduces to affine-neighborhood section continuity.
Blueprint-wide search for constant-module continuity found no imported node stating
this germ lemma; the existing higher-direct-image vanishing lemma has a different,
derived abelian signature. The parent chain consists of stage-3-created nodes;
blueprint_refs.py ancestor reports no imported blueprint ancestor.
No change record is needed: no existing statement, definition, or public import changed.

## Second reading by K2

1. Compared the delivered item with the repository using diff. The existing theorem
   signature, universes, hypotheses, docstring, definitions and public import are
   byte-for-byte unchanged. Only its proof and two private proof imports change.
   Verdict: no accidental interface change; no change record is required.
2. Compiled both modules locally in import order with lcompile.py, without errors
   or warnings. Scratch copies with #print axioms show only propext, Classical.choice,
   Quot.sound and sorryAx for both the combining theorem and the new germ theorem. There are no forbidden declarations or hollow definitions. The
   sole delivered sorry is the named germ theorem listed above. Verdict: valid
   conditional proof; one-for-one decomposition, net zero holes closed.
3. Read the germ theorem, its complete docstring argument and node, and Stacks
   https://stacks.math.columbia.edu/tag/09YQ and
   https://stacks.math.columbia.edu/tag/09Z1. The affine-neighborhood restriction
   makes every base-changed stage qcqs; it avoids requiring X quasi-separated.
   Zero modules are immediate, cofilteredness rules out empty indices, empty limits
   give eventual vanishing by qcqs continuity, and the terminal singleton system
   reduces to restriction along the limit isomorphism. Non-posetal indices are
   covered by cofiltered refinement. The statement concerns one stage germ and
   supplies a transition witness; it does not restate monicity of a colimit map.
   Independent LeanFinder search for sections vanishing at inverse limits found
   structure-sheaf results only; Loogle for sheafFiber and Mono found no replacement.
   Source search found exists_unitComparison_app_eq_zero_of_isLimit, read in full:
   it concerns abelian push-pull sections, so its use still requires the constant
   coefficient and stalk-to-section bridges described in this node. No duplicate
   canonical germ result was found. Verdict: true, needed geometric subproblem;
   closing it would require substantial additional interface proofs.
4. Followed the combining proof from conservative geometric stalks through filtered
   colimit representatives, hι, germ vanishing, hK and colimit.w. The two removed
   proof imports are unnecessary. The report lists all seven old proof_deps as no
   longer immediate dependencies, distinguishing those retained by the new lemma
   from global pruning. Read sk-thm-p1.json and its realized fields: no unit step
   is removed or bypassed. Verdict: genuine reduction respecting the unit route.
5. Compared both nodes with Lean. Their recorded Lean signatures match verbatim;
   each proof_deps is exactly the union of its proof-step uses. The updated item's
   proof and proof_origin describe the actual Lean reduction. The new node has its
   source, searches, creation record, chapter, unit, blueprint provenance and Lean
   record. Verdict: DAG agrees with the delivered proof and remaining proof plan.

Second reading changed only this report: made the one-for-one decomposition and
net-zero hole count explicit and recorded the independent checks. The Lean proof
and statements needed no repair.
