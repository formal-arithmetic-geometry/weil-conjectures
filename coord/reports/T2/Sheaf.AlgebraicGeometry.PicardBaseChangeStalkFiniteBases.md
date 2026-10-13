## What changed

Proved `AlgebraicGeometry.Scheme.picardRankMatch_baseChange_stalk_finite_bases`
in `Sheaf.AlgebraicGeometry.PicardBaseChangeStalkFiniteBases`, with its existing
signature and public imports unchanged. Added proof imports of the proved source
module `WeilConjectures.AlgebraicGeometry.Modules.FiniteDescent`. Mathlib's
pullback-pasting API is already available through the retained imports. No other existing module is adapted. The helpers have explicit binders and
qualified names, so the original file-level open/variable commands are unchanged.
The static interface comparison reports no interface changes.

Repair of the returned delivery: removed the private
`AlgebraicGeometry.Scheme.tensorPullback_finiteLocallyFree` theorem, whose
statement duplicated the private helper in
`Sheaf.AlgebraicGeometry.PicardPullbackBaseChangePrimal`. That existing helper
is private and cannot be reused by an importing module. The sole call site now
applies the existing public `SheafOfModules.IsFiniteLocallyFree.of_iso` theorem
directly to `tensorComparison h`, with the proved abstract-pullback instance.
No duplicate theorem is declared, no extra import is needed, and the proof
uses the library theorem rather than reproving preservation.

The universal local rank witnesses imply finite local freeness of either ordinary
direct image by open-cover locality. Uniqueness of left adjoints identifies tensor
pullback with ordinary pullback, which preserves finite local freeness. This proves
finite local freeness of the source. The fibre-product associativity isomorphism,
composition comparisons, and invertible adjunction unit along a scheme isomorphism
identify the iterated target with the single direct image after composite base change.

Both finite stalk bases are then constructed explicitly from local coordinate
projections and inclusions. This private coordinate-germ construction is adapted
from the already proved private helpers in
`Sheaf.AlgebraicGeometry.FiniteLocallyFreeStalkFinrank` (group S3). Its exported
finrank equality does not imply existence of a basis, and its useful linear
equivalence is private, so that module is not imported. The proof constructs the
linear equivalence and maps/reindexes the standard function basis itself.

The copied node's proof, proof dependencies, and proof origin now describe this
route. The unit `sk-prop-av-cube` has no realized nodes for this argument; its
statement and its general-cube-theorem step remain unchanged. Read the source
pages https://stacks.math.columbia.edu/tag/01C6,
https://stacks.math.columbia.edu/tag/0097, and
https://stacks.math.columbia.edu/tag/0BDP. Search calls through msearch for
leanfinder, loogle, and grep returned generic ingredients, not this theorem.

## Proved and sorry left

Closed the sole hole:
`AlgebraicGeometry.Scheme.picardRankMatch_baseChange_stalk_finite_bases`
(node `lem-sc-picard-base-change-stalk-finite-bases`).

No `sorry` remains in the item, and none is added elsewhere. The axiom probe
prints exactly `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`. All private helper
theorems are proved, and all private constructions contain real data and proved
laws. Zero holes split off. Local compilation and the axiom probe pass; the delivery dry run is the
final gate. Rank-zero frames are handled by the empty finite function basis;
the argument for an empty scheme is vacuous. No equality of ranks is assumed.

## No longer needed

Removed proof dependency `lem-weil-pbc-module-stalk-pullback`:
`Sheaf.AlgebraicGeometry.Modules.TensorPullbackStalk` is not needed by this proof.
The proof uses preservation of finite local freeness instead of computing the
stalk of tensor pullback by extension of scalars. This module was a planned
proof dependency, not an existing direct import, so no original import was removed.
Its independent consumers may still need it.

The proof also does not need the stalk-finrank theorem
`lem-sc-finite-locally-free-stalk-finrank` or its module
`Sheaf.AlgebraicGeometry.FiniteLocallyFreeStalkFinrank`, mentioned as an ingredient
in the node's earlier search notes. Its coordinate argument is proved privately
here, and no rank-comparison or proper-image lemma is needed. Retained every
original public import: they provide the statement's notions and stalk module
structure. Removed a trial redundant direct proof import of
`WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Free`, available through
FiniteDescent; no unused trial import remains. The second reader also removed the
redundant proof import `Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting`;
a scratch copy without it compiles cleanly.

## Where the brief, the DAG or earlier work was wrong

The earlier delivery unnecessarily restated the private tensor-pullback
finite-local-freeness helper from `PicardPullbackBaseChangePrimal`; the landing
checker correctly refused it. This repair removes that declaration and uses
the existing public isomorphism-transport theorem at its only call site.
No statement or definition error was found. The planned tensor-pullback stalk
calculation is stronger than necessary: finite local freeness itself survives
pullback, and finite local frames directly construct finite stalk bases. The
previously exported stalk-finrank equality alone cannot justify a basis.
The node's plan has been updated to the actual proof. No target signature,
visibility, definition, or other module interface changed.


## Earlier second reading (a previous round; superseded)

1. **Interface unchanged — pass.** Compared the delivered module with the repository
   by `diff` and checked the complete existing theorem signature byte for byte.
   Its binders, hypotheses, conclusion, visibility, file-level opens and variables,
   and all four original public imports are unchanged. No existing definition is
   changed, no other module is delivered, and no change record is needed.
2. **Kernel proof — pass.** Read every helper and the final proof, compiled the
   module locally with `lcompile.py`, and compiled a scratch copy of the actual
   delivery with `#print axioms` appended. The theorem uses exactly `propext`,
   `Classical.choice`, and `Quot.sound`. No `sorry` or forbidden declaration occurs.
   Coordinate maps are constructed by the stalk colimit, and their linearity,
   delta identities, and spanning identities are proved. The isomorphisms chosen
   from adjunction/composition theorems use already proved theorems, not an
   arbitrary witness supplied by an unproved existence statement.
3. **Split statements and edge cases — pass.** No statements are split off and
   no new holes or nodes are added. Checked finite empty frames: the sum and
   function basis constructions include rank zero. The cover argument also works
   for an empty scheme; the final assertion has no point in that case. Either
   branch of `hF` selects the corresponding rank witness; no equality of the two
   basis cardinalities is used. Independently searched with msearch leanfinder
   (`locally trivial sheaf module germs form finite basis`), loogle
   (`Module.Basis, _ ≃ₗ[_] _`), and grep, and searched library and installed Mathlib
   sources by alternate stalk/free/basis keywords. Results supplied generic
   germ and basis transport ingredients, not a public theorem replacing this
   coordinate construction. The existing finrank result has private coordinate
   helpers and exports no stalk basis. Read Stacks Tags 01C6, 0097, and 0BDP.
4. **Route and pruning — pass after import repair.** The proof uses the universal
   rank witnesses, proved open-cover locality and pullback preservation, then
   fibre-product associativity and explicit local coordinates. Its two new proof
   ingredients come from proved source/Mathlib declarations. Compiled a scratch
   copy without the direct pullback-pasting import; it succeeds, so removed that
   redundant import. `## No longer needed` lists the sole omitted old proof
   dependency, `lem-weil-pbc-module-stalk-pullback`, and distinguishes planned
   dependencies from existing imports. The unit `sk-prop-av-cube` has empty
   realized statement/step lists; this argument changes neither its statement
   nor its general-cube-theorem step and bypasses no realized unit node.
5. **DAG agreement — pass.** Compared the node JSON with the repository: only
   `proof`, `proof_deps`, and `proof_origin` change. The statement, statement
   dependencies, Lean signature, source, chapter and unit remain unchanged.
   Checked that `proof_deps` is exactly the union of the steps' `uses`; the three
   steps describe the local-freeness, associativity and coordinate arguments in
   the Lean. There are no new nodes to validate.

Second-reading changes: removed the redundant private proof import of
`Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting`, restored the existing
public theorem docstring verbatim, and updated this report. The proof itself
needed no repair. One existing hole is closed, zero holes are added, and zero
statements are split off.


## Second reading by T2

1. **Interface — pass.** Independently diffed the sole delivered module against
   the repository and compared the existing theorem signature byte for byte.
   Its hypotheses, conclusion, visibility, original docstring, and four public
   imports are unchanged. No existing definition or other module changes.
2. **Proof — pass.** Read the coordinate cocone, linearity, delta and spanning
   identities, basis transport, open-cover argument, and iterated direct-image
   isomorphism. Local compilation succeeds without warnings. A newly generated
   scratch copy of this delivery prints only `propext`, `Classical.choice`, and
   `Quot.sound` for the main theorem. No `sorry` or prohibited declaration occurs.
   All new data are actual constructions; the adjunction/composition choices use
   proved results and their universal properties, not unproved mere existence.
3. **Split statements and edge cases — pass.** No split statements, new nodes,
   or new holes. The coordinate construction works for an empty finite index
   set, and an empty base has no point to check. Both alternatives of `hF` use
   the appropriate clause of `hR`; neither requires rank equality. Independently
   searched leanfinder for locally free sheaf coordinate bases on germs, loogle
   for `Pi.basisFun`, and grep for stalk/basis/IsFree keywords, plus library and
   installed Mathlib sources. Found generic ingredients, not a public replacement
   for the stalk-basis construction. The similar S3 coordinate helpers are
   private and its public finrank result does not construct this basis.
4. **Route and pruning — pass.** Read the universal rank definition and the
   proved source-library locality/pullback preservation results. The retained
   proof import supplies these; the original public imports support the statement.
   Read Stacks Tags 01C6, 0097, and 0BDP. The shortest available route here is
   finite local freeness plus local coordinates, without the general tensor
   stalk formula. `## No longer needed` lists the sole removed old dependency,
   `lem-weil-pbc-module-stalk-pullback`; no original direct import was removed.
   Checked `sk-prop-av-cube.realized`: its statement and step lists are empty,
   and no prescribed unit route is bypassed.
5. **Nodes — pass.** Node diff changes exactly `proof`, `proof_deps`, and
   `proof_origin`. Its existing statement, signature record, source and unit
   are unchanged. Checked mechanically that dependencies are exactly the union
   of step uses; the steps match the locality, associativity, and coordinate
   arguments in Lean. No new-node records are needed.

Current second-reading changes: appended this independent review and recorded
new searches and an axiom probe. No further proof, import, or node repair was
needed: the earlier duplicate-helper repair is sound. Closed one existing hole
(`AlgebraicGeometry.Scheme.picardRankMatch_baseChange_stalk_finite_bases`),
added zero holes, and split off zero statements.
