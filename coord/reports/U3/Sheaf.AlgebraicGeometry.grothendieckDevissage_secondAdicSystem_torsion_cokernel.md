## What changed

Replaced the only sorry in
`Sheaf.AlgebraicGeometry.grothendieckDevissage_secondAdicSystem_torsion_cokernel`
with a compiling reduction. The statement, universe, visibility, and all hypotheses stay
identical. At each e,n, the already proved `coherentMap_reduction_torsion_coker` applied
to α_n supplies the reduced K^(2t) cokernel bound. The evaluated σ and θ isomorphisms
and hsquare give `cokernel.mapIso`; multiplication naturality gives an isomorphism
of arrows using `Arrow.isoMk`, and Mathlib `Limits.im.mapIso` and `IsZero.of_iso`
transfer ideal annihilation across the resulting image isomorphism. The coherent adic conditions supply
K^(e+1) annihilation of the terms of δ_e. A new fixed-thickening reflection theorem
then supplies K^(2*(2t)), and the final arithmetic rewrite gives K^(4t).

New proof imports: `Sheaf.AlgebraicGeometry.CoherentMapReductionTorsionCoker`,
`Sheaf.AlgebraicGeometry.CompletionThickeningCokernelReflection`. Existing public imports are
unchanged. Updated the assigned node's proof, proof_deps, and proof_origin to match.

Both modules compile locally with lcompile.py, with no compiler warnings. The new
reflection lemma is a strictly smaller part of the argument: it concerns one coherent
map on one fixed thickening, assumes its I-reduced cokernel bounds, and has no second
adic system, comparison isomorphisms, or α hypotheses. The quotient reduction and
comparison-square transport are fully implemented in Lean, not passed to that lemma.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.grothendieckDevissage_secondAdicSystem_torsion_cokernel`
(node `lem-weil-pbc-devissage-second-adic-system-torsion-cokernel`). No sorry remains
in the assigned module. The duplicate private `product_zero_of_epi` is removed;
no replacement declaration or hole is added by this repair.

Added one hole:
`AlgebraicGeometry.completion_thickening_cokernel_reflection`
(node `lem-weil-pbc-completion-thickening-cokernel-reflection`), in its own new module.
Its proof is exactly `by sorry`; its docstring and node give the whole argument.

This is a decomposition: one hole closed, one strictly smaller hole added, net zero
holes. It is not a claim that the target's import closure is sorry-free.

## No longer needed

Repair additionally removes
`WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed`: transport across
an isomorphism uses tensor functoriality and the image functor, without an adjoint
or preservation of arbitrary epimorphisms. The duplicate private helper is deleted.

Removed these direct proof imports from the assigned module:
- `Sheaf.AlgebraicGeometry.ClosedImmersionCoherentEquivalence`: used only by the new
  reflection obligation, whose module imports it; it is not globally pruned. The old
  direct node `lem-weil-pbc-closed-immersion-coherent-equivalence` is retained only
  in the reflection node's proof dependencies.
- `Sheaf.AlgebraicGeometry.CoherentFormalModuleAnnihilated`: the four-way equivalence
  and simultaneous affine-limit kernel/cokernel bounds are unnecessary for this
  cokernel-only route. The corresponding direct proof dependency
  `lem-weil-pbc-formal-systems-annihilated-by-power` is removed.
- `Sheaf.RingTheory.KernelCokernelAnnihilatedModIdeal`: no scalar reverse map or
  simultaneous kernel/cokernel quotient bound is used. The corresponding direct
  dependency `lem-weil-pbc-kernel-cokernel-annihilated-mod-ideal` is removed.

No additional imports were introduced and then retained unused in the assigned module.
Pruning is relative to this proof; these modules can remain needed by other targets or
by the separately held kernel-half item. No unit statement or realized unit step is
bypassed. The new reflection node replaces the original geometric reflection portion
of the plan, retaining the closed-immersion route there.

## Where the brief, the DAG or earlier work was wrong

Return point 1 repaired: the previous private `product_zero_of_epi` duplicated the
private theorem in `CoherentMapReductionTorsionCoker`. That module is already imported,
but its helper is private and cannot be called by an importer. Rather than change
another module's visibility, this repair uses existing public Mathlib declarations
`Arrow.isoMk`, `Limits.im.mapIso` and `IsZero.of_iso` directly for the narrower
isomorphism transport needed here. No duplicate theorem remains. The assigned node's
transport step now describes this proof. The second-reading section below records the
previous delivery and needs a new independent reading after this repair.

The original plan bundled both halves of the scalar reverse-map argument. For the
cokernel half, quotienting induces an epimorphism from the original cokernel, so the
already proved coherent-map cokernel reduction lemma is sufficient. No incorrect
statement or unusable existing signature was found, and no existing interface changed.

The local literature checkout contains the citation lists, not coherent.tex. Read the
primary source at https://stacks.math.columbia.edu/tag/088A and
https://stacks.math.columbia.edu/tag/0888. The generic reflection proof expands the
second reflection step, using the ordinary termwise cokernel and exact completion;
it does not assume that affine completion is faithful. Zero is reflected by the global
completion equivalence on the thickening.

Edge cases of the new statement checked mathematically: the empty scheme has only
zero modules; K=0 gives a zero positive ideal power; K=1 forces F and G to be zero
from hF and hG; I=0 reduces to the original cokernel. For I=1, the completion
hypothesis is exceptionally strong (the thickening's coherent category must be zero),
so it does not supply a counterexample. General q,s are positive and independent;
there is no illicit assumption that the nilpotence exponent bounds the torsion exponent.

Searches were actually run with msearch.py: LeanFinder returned generic sheaf quotient
and subscheme facts, Loogle returned cokernel.mapIso, and Mathlib grep found no exact
completion-annihilation reflection theorem. LeanSearch was unavailable (HTTP 500),
recorded as unavailable. Local searches across both library roots and the whole DAG,
and blueprint_refs.py search, found no existing fixed-thickening cokernel reflection
statement. The existing coherentMap_reduction_torsion_coker was reused unchanged.

## New nodes

`lem-weil-pbc-completion-thickening-cokernel-reflection` states reflection for one
coherent map supported on V(K^q), assuming completion on that fixed thickening is an
equivalence and K^s kills the cokernels of all I-reductions. It concludes K^(2s) kills
the ordinary cokernel. It is recorded in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-completion-thickening-cokernel-reflection.json`
and stated in `lean/Sheaf/AlgebraicGeometry/CompletionThickeningCokernelReflection.lean`.
The natural-language argument actually proves the stronger exponent s first and then
factors the exponent-2s ideal inclusion. This follows the cokernel-only content of
Stacks 088A's reflection step. No change record or forced adaptation is needed.

## Earlier second reading (a previous round; superseded)

1. Compared the target module with the repository using diff and checked its complete
   theorem signature byte for byte. Verdict: unchanged, including universe, visibility,
   hypotheses and conclusion. There are no definition changes, adaptations or change
   records. Restored the existing target docstring; the updated argument remains in
   this report and the node's proof description.
2. Compiled both delivered modules in import order with lcompile.py: both pass without
   warnings. The target has no sorry; the only added sorry is the named public
   completion_thickening_cokernel_reflection. Scratch-copy #print axioms for both
   public declarations reports only propext, Classical.choice, Quot.sound and sorryAx.
   No forbidden declarations, hollow definitions or existence-chosen data occur.
   Verdict: the implemented reduction is valid, with the reported reflection hole.
3. Read the reflection statement, its complete docstring argument and node against
   Stacks Tags 088A, 0888 and 087T. Checked q=1, s=1, K=0, K=1, I=0, I=1 and the
   empty scheme: no counterexample. In particular I=1 forces the thickening's coherent
   category to be zero under the equivalence hypothesis. Exact affine completion is
   used to identify the completed ideal-action image; zero is reflected by the GLOBAL
   equivalence, not by assuming a faithfully flat affine completion. This is strictly
   smaller than the target: no second system or comparison square remains. Independent
   msearch searches used “zero adic completion”/“faithful completion” (LeanFinder),
   Functor.IsEquivalence and IsZero (Loogle; the short identifier was unknown), and
   reflectsZero/reflect-IsZero/isZero-map (grep). They found generic facts, no exact
   geometric theorem. Local library searches also found no public replacement; the
   analogous multiplication-image helpers in the reduction and formal-cokernel modules
   are private. Verdict: a true, sourced, nonduplicate remaining obligation, not a
   restatement of the item. Formalizing its descent and completion-image comparisons
   is not a short remaining proof.
4. Read the quotient reduction declaration and its implemented proof, and checked the
   directions of the evaluated square, cokernel.mapIso and its inverse. Each import
   supplies signature material, the reduction, the reflection obligation or the tensor
   adjunction used by the private helper. All three OLD direct proof dependencies are
   accounted for under No longer needed, including
   lem-weil-pbc-closed-immersion-coherent-equivalence (moved into the reflection node).
   No claim of global pruning is made. Read dag/units/sk-thm-p1.json realized: none of
   its statement or step nodes is bypassed or changed. Verdict: top-down reduction and
   pruning respect the unit route.
5. Compared the existing node's JSON fields: only proof, proof_deps and proof_origin
   change; its lean record stays identical. The proof steps and dependency union match
   the actual reduction. Checked the new node's statement against its Lean signature,
   source, complete proof plan, dependency union, searches, creation metadata,
   blueprint ancestry, chapter, unit and lean record. Verdict: consistent.

Second-reading changes: restored the original target docstring and added this review.
No proof or statement repair was needed. One original hole is closed and one strictly
smaller hole is added: decomposition, net zero holes; the target still uses sorryAx.


## Second reading by U3

1. Compared the delivered target with the repository using diff, and compared the
   existing theorem signature byte for byte using a script. Verdict: identical.
   Only proof imports, a declaration-scoped elaboration option and the proof change;
   no existing statement, visibility, definition or target changes. The new module
   has no definitions or witness selections. No change record or adaptation is needed.
2. Compiled both modules in import order with lcompile.py: clean, 2.4 s and 8.5 s.
   Compiled scratch copies with #print axioms for both public declarations: exactly
   propext, Classical.choice, Quot.sound and sorryAx. The target has no direct sorry;
   the only added hole is completion_thickening_cokernel_reflection. Read the entire
   multiplication naturality proof and the directions of cokernel.mapIso, Arrow.isoMk
   and im.mapIso: IsZero transfers from the reduced alpha cokernel to the reduced
   delta cokernel as required. No forbidden declarations or hollow definitions.
   Verdict: valid reduction, still dependent on the explicitly reported hole.
3. Read the new statement, docstring and node against Stacks Tags 088A, 0888 and
   087T. For a fixed thickening, right exact reduction identifies the reduced
   cokernels with reductions of the coherent cokernel. Exact affine completion
   identifies its ideal-action image with the completed image; its vanishing is
   reflected by the GLOBAL completion equivalence on the thickening. No faithful
   affine completion is assumed. Checked q=s=1, zero and unit K, zero and unit I,
   and the empty scheme. For I=1 the equivalence forces the coherent category on Z
   to be zero. No counterexample or missing hypothesis found. The lemma drops the
   second adic system and comparison square, so it is strictly a part of the item.
   Independent searches: LeanFinder for faithful-functor scalar-action detection
   after adic completion found AdicCompletion.map_exact/map_injective and related
   generic facts; Loogle for Functor.map_injective found generic faithfulness;
   grep for cokernel/completion found no exact Mathlib statement. Searched both
   local Lean roots for reflection, torsion and completion/IsZero. The existing
   kernel reflection lemma concludes only kernel annihilation and cannot replace
   this cokernel obligation. Verdict: true, sourced, nonduplicate split. Descent
   and ideal-image comparison still need substantial formalization, not a short fix.
4. The top-down proof reuses the already proved coherentMap_reduction_torsion_coker
   and implements the comparison-square transport before the reflection split.
   Checked all three old proof_deps against No longer needed: scalar quotient
   bounds and simultaneous formal kernel/cokernel bounds are removed; closed
   immersion equivalence moves into the reflection node. Existing public imports
   supply signature material; new imports are plain proof imports. The reflection
   module retains the closed-immersion route for its open proof. Read the complete
   realized field of dag/units/sk-thm-p1.json: no realized statement or step is
   bypassed. Verdict: pruning and the smaller reflection obligation keep the route.
5. Compared existing node JSON: only proof, proof_deps and proof_origin differ.
   Checked the steps against the Lean reduction and their dependency union. Checked
   the new node's exact Lean statement, source, natural-language proof, dependency
   union, searches, creation metadata, blueprint ancestry, chapter, unit and Lean
   record. Verdict: consistent; the new node describes the remaining proof plan.

Second-reading changes: made the old closed-immersion dependency's relocation explicit
under No longer needed and appended this independent review. No further proof repair
was needed. The prior repair's duplicated private helper is absent. One original hole
closed, one smaller hole added: decomposition, net zero holes, with sorryAx remaining.
