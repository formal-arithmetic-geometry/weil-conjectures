## What changed

Replaced the sole sorry in `Sheaf.AlgebraicGeometry.TorsionControlledAlgebraizationDescentGluing`
by a compiling reduction. Its existing public signature and visibility are unchanged.
Added the proof-only imports `Sheaf.Topology.GlueSheavesOfModules` and
`Sheaf.AlgebraicGeometry.TorsionControlledAlgebraizationLocalDescent`, and
`WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel`.

The remaining algebraic source descent now has an explicit, smaller interface:
a global coherent source and arrow, compatible *local* formal comparisons,
and local source isomorphisms intertwining the arrow with locally bounded arrows.
It does not assert a global formal isomorphism or bounds for the actual global kernel/cokernel.

The item's proved private helpers glue levelwise morphisms, prove transition naturality
by locality, derive inverse overlap compatibility from equality of isomorphism homs,
glue inverse maps, and check both inverse identities locally. The main theorem lifts
the resulting isomorphism to the full subcategory and proves its factorization equation
levelwise by locality. Separate proved helpers transport ideal-product annihilation
through module isomorphisms, then through restriction/kernel/cokernel comparisons.
They preserve each supplied positive exponent; no finite subcover or uniform exponent is used.

## Proved and sorry left

Closed: `AlgebraicGeometry.torsionControlled_algebraization_descent_gluing`
(node `new-stage3-torsion-controlled-algebraization-descent-gluing`), by reduction.

Added: `AlgebraicGeometry.torsionControlled_algebraization_local_descent`
(node `new-stage3-torsion-controlled-algebraization-local-descent`), the only sorry
in the delivery. This is a decomposition, not a sorry-free proof or a net hole reduction:
one upper hole closed, one strictly smaller algebraic-descent hole added.

No sorry remains in the item's module. The four private helpers are proved.
Both delivered modules compile together through lcompile.py; the original theorem's
signature is unchanged. No new definitions or axioms are added and no downstream
module requires adaptation.

## No longer needed

No baseline import was removed: the original module imported only
`Sheaf.AlgebraicGeometry.CoherentFormalModule` publicly, and that import is necessary.
The explicit import of `WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel`
is necessary: removing it made synthesis of kernel preservation for restriction fail.
No global module pruning is claimed.

At the parent node the direct uses of FormalSystemsPullback,
TorsionControlledCompletionHomLiftExists, CoherentMapTorsionCompletionExt,
CoherentModuleLocalOnOpenCover, and Modules.IdealTimesQuasiCoherentAffineSections
are transferred to the smaller local-descent node. They remain needed there, so are
not claimed as pruned. The top-level formal gluing and bound transport do not need to
re-run torsion-controlled hom lifting or prove an ideal-product/restriction theorem:
the latter compare isomorphic modules *after* restriction, with the local ideal fixed.

## Where the brief, the DAG or earlier work was wrong

No false statement or signature correction was found. The original proof plan did
not expose the local arrow isomorphisms needed to transfer annihilation to the
restrictions of the actual global kernel and cokernel. The new interface exposes them.
The formal-gluing part is now fully proved rather than hidden in that plan.

The direct blueprint ancestor command returned None for the item because its
created.item is a module and its blueprint.from points to another created node.
The new node follows the parent descent node's recorded blueprint ancestor
`thm-weil-pbc-finite-etale-lifting` and its recorded chain. Searches for
"torsion-controlled" and "0889" found no existing blueprint node duplicating
this intermediate statement. No unit statement or realized step is bypassed.

The local literature/stacks-project directory is absent in this read-only clone.
The sources were read from the official Stacks pages for Tags 0889, 00AL, and 00AM;
the new interface expands the uniqueness/locality argument already used by the item.
LeanSearch returned HTTP 500, recorded as unavailable; LeanFinder, Loogle, logged
grep, and local rg searches were run and found no exact replacement theorem.

Edge cases checked mathematically: an empty cover forces the empty scheme;
J=0 makes completion the original system; for the unit ideal bounded arrows are
isomorphisms and comparison is through H, without assuming completion is faithful.
No nonempty cover, proper ideal, or uniform exponent is assumed.

## New nodes

`new-stage3-torsion-controlled-algebraization-local-descent` in
`dag/nodes/sec-proper-base-change/` states only algebraic source descent with
compatible local formal comparisons and local arrow isomorphisms. It is stated in
`lean/Sheaf/AlgebraicGeometry/TorsionControlledAlgebraizationLocalDescent.lean`.
Its proof plan retains the original overlap lifting, uniqueness, cocycle, module
sheaf descent, and coherence-locality steps. Its docstring gives the full proof
in words and the original sources. The parent node's proof and proof_deps now
follow the actual Lean reduction. There are no change records or forced adaptations.


## Second reading by S2

1. **Interfaces: pass.** Diffed the delivered existing module against the read-only
   repository. The existing theorem signature is byte-for-byte identical, including
   all hypotheses, quantifiers and conclusion; its visibility is unchanged. There
   are no definitions, interface corrections, or downstream adaptations. Restored
   its original docstring, which the first worker had unnecessarily rewritten.
2. **Proof and trust: pass as a decomposition.** Both modules compile locally through
   lcompile.py. Scratch-copy `#print axioms` checks show only `propext`,
   `Classical.choice`, and `Quot.sound` for all four private helpers. The main theorem
   and the new local-descent theorem additionally show `sorryAx`, as expected.
   The only textual hole is the whole proof of the public named theorem
   `AlgebraicGeometry.torsionControlled_algebraization_local_descent`. No definition,
   arbitrary witness-valued construction, forbidden axiom, unsafe declaration or
   implementation override was introduced. All existential elimination takes place
   inside theorem proofs.
3. **Split statement: pass.** Read the local-descent statement clause by clause and
   checked its full proof in words against the stated hom-lifting, completion
   extensionality, pullback and sheaf-descent interfaces. On overlaps, lift the
   completed comparisons and their inverses compatibly with H; extensionality gives
   inverse equations and the cocycle. Source descent and coherence locality then
   give F and a, and the completed gluing identifications give exactly the local
   comparisons retained in the statement. Empty covers force X empty; redundant or
   empty opens impose no extra condition. At J=0 comparison is ordinary module
   comparison, while at J=1 the annihilation hypotheses force each local arrow to
   be an isomorphism, and H supplies the comparison even though completion is zero.
   No uniform exponent or properness of J is assumed. The residual statement is
   algebraic descent with local comparisons; formal gluing, global factorization
   and transport to the actual global kernel/cokernel have separately proved Lean
   arguments. It is a genuine decomposition, not an alias of the original hole.
   Independent LeanFinder search for compatible completion comparisons and Loogle
   search for isomorphisms and zero objects, plus rg searches for ideal-product
   isomorphisms and torsion descent in both source roots, found no replacement.
   The remaining hole requires substantial descent formalization, not a short
   missed application. Source checked directly at
   [0889](https://stacks.math.columbia.edu/tag/0889),
   [00AL](https://stacks.math.columbia.edu/tag/00AL), and
   [00AM](https://stacks.math.columbia.edu/tag/00AM).
4. **Route and pruning: pass after import cleanup.** The main proof uses the existing
   morphism-gluing/locality theorem and standard kernel/cokernel comparison isos;
   no shorter applicable complete proof was found. Removed the redundant public
   import `Sheaf.Paper.DerivedHomMayerVietoris` from the new module: it is already
   publicly available through CoherentFormalModule -> Coherent. A scratch copy
   compiled without it. The original public import stays; all added imports in the
   existing module are proof-only. The original direct dependencies no longer
   used directly are `lem-weil-pbc-formal-systems-pullback`,
   `lem-weil-pbc-torsion-controlled-completion-hom-lift-exists`,
   `lem-weil-pbc-coherent-map-torsion-completion-ext`,
   `lem-weil-pbc-coherent-module-local-on-open-cover`, and
   `lem-weil-pbc-ideal-times-quasi-coherent-affine-sections`; each remains in the
   local-descent proof plan, so no module is claimed globally pruned. Read
   dag/units/sk-thm-p1.json and its realized statement/steps: neither edited node
   replaces a realized unit step; the below-unit source-descent route is retained.
5. **DAG: pass.** The existing node changes only proof, proof_deps and proof_origin.
   Its revised plan follows the local-descent call, levelwise formal gluing,
   locality and exact restriction/bound transport in Lean. The ideal-product node
   provides the actual definitions used, rather than its stalk theorem being
   needed. The new node includes the exact Lean signature, full source and proof
   plan, dependency union, searches, creation and blueprint ancestry records,
   and the inherited chapter/unit. No statement or realized unit record changed.

Second reading changes: restored the existing theorem docstring; removed one
redundant public import from the new module; documented the independent checks.
Holes closed: one upper hole by reduction. Holes added: one smaller descent hole.
Net hole reduction: zero. No global module pruning claimed.
