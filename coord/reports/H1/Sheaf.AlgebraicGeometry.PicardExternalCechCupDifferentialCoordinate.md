## What changed

Replaced the proposed canonical-degree helper and expanded-coordinate module with a real
reduction of `picardExternalCechCupDegreeMaps_comm_ι`. After substituting the total degree,
its proof recovers the initial bidegree map, expands the two tensor-total differential
summands with Mathlib's inclusion formulas, recovers their two coproduct components, and
uses tensor-product extensionality. Only then does it invoke the pure-tensor signed
Leibniz statement for three adjacent bidegrees in the new proof-only import
`Sheaf.AlgebraicGeometry.PicardExternalCechCupLeibniz`.

All existing declaration signatures, definition bodies and public imports are unchanged.
No statement or definition change record is needed. The original node's proof and
proof dependencies now record the implemented reduction.

## Proved and sorry left

Hole closed: `AlgebraicGeometry.Scheme.Modules.picardExternalCechCupDegreeMaps_comm_ι`
(node `lem-sc-picard-external-cech-cup-differential-coordinate`). Its assembly proof contains
no `sorry`. The existing `picardExternalCechCupDegreeMaps_ι` remains proved.

Hole added: `AlgebraicGeometry.Scheme.Modules.picardExternalCechCupBidegree_leibniz`
(node `lem-sc-picard-external-cech-cup-leibniz`, new module
`Sheaf.AlgebraicGeometry.PicardExternalCechCupLeibniz`). Its proof is exactly `by sorry`;
its docstring states the source and complete alternating-face argument. It assumes only
three maps and their coordinates, and states an equality on pure tensors without any
family in other bidegrees, coproduct maps or total summand inclusions.

This is a decomposition: one old hole closed and one smaller hole added, net zero holes.
It is not a completed proof of the signed face calculation. Neither the proposed
`picardExternalCechCupDegreeMaps_comm_ι_rfl` nor
`picardExternalCechCupDegreeMaps_comm_ι_expanded` is delivered.

## No longer needed

The proposed expanded module and node are removed from the sandbox delivery, together
with the canonical-degree helper. They never belonged to the repository baseline.

Every old direct proof dependency of the item's node is replaced by the pure-tensor node:
`def-sc-cech-cup-product`, `def-sc-picard-external-right-cech-models`,
`lem-pc-module-pullback-adjunction`, and
`lem-sc-picard-external-cech-cup-bidegree`. All four remain needed by the lower face
calculation and are recorded there. No existing import or module is pruned: the bidegree
public import remains needed by the unchanged signatures, and the new Leibniz import is
private to the proof. The unit record is unchanged.

## Where the brief, the DAG or earlier work was wrong

The first proposal relocated the entire canonical identity after one differential
rewrite and definition unfolding. That is an equivalent restatement, not a strictly
smaller substep. Its new node cited the canonical statement as its proof dependency,
although the Lean canonical proof applied the new statement; the proposed canonical
helper had no delivered node. The report also incorrectly said that the canonical
helper still had `sorry`, while its body actually applied the expanded theorem, and the
expanded theorem lacked a complete docstring proof.

These faults are removed. The replacement separates the actual finite-face identity
from the tensor-total assembly, and records the remaining hole honestly.

## New nodes

`lem-sc-picard-external-cech-cup-leibniz` states the signed Leibniz identity on a pure tensor
for three maps with the existing external front/back coordinates. Its module is
`lean/Sheaf/AlgebraicGeometry/PicardExternalCechCupLeibniz.lean`. Source: Stacks Section
20.25, the computation following equation the project server (Tag 07MB), and Tag 0BED for the
external product coordinates. The node has the item's chapter and unit, and traces its
blueprint provenance to `thm-sc-theorem-of-cube` through the coordinate node.

Real searches were made using the launcher: LeanSearch (service returned Internal
Server Error, recorded as unavailable), LeanFinder (alternating differential and group
cohomology results, no exact match), Loogle (`"Alexander"`, no hits; `d₁_eq`, the generic
assembly formula), and Mathlib grep. Repository and upstream source searches found
`cechCupCochain_leibniz`, which is already proved, but it acts on one scheme and one
family with ordinary module cochains. Applying it to this two-scheme scalar construction
would still require identification of the pulled and refined cochains and their
restriction/differential compatibility; it is not the statement split here. Blueprint
searches for `Alexander` and `external Cech cup` found no imported duplicate.

## Second reading by H1

1. Compared the whole proposed module against the repository baseline with `diff`.
   Initially it added the canonical helper and changed indentation in the old signature.
   The final module has precisely one proof-only import and the original theorem's new
   body. Checked the original theorem signature byte for byte and the entire preceding
   file byte for byte after accounting for that import. Verdict: every existing signature,
   definition body, visibility and public import is preserved; no target changed.

2. Read the proof from its conclusion backwards. Substitution handles `hpq`;
   `picardExternalCechCupDegreeMaps_ι` identifies the source cup map;
   `mapBifunctor.d_eq`, `ι_D₁_assoc`, `ι_D₂_assoc`, `d₁_eq`, `d₂_eq` and
   `ι_mapBifunctorDesc` give the two correctly transported adjacent cup maps.
   `ModuleCat.MonoidalCategory.tensor_ext` reduces to pure tensors, and the natural-index
   shape signs supply `1` and `(-1)^p`. Compiled both modules locally in import order and
   checked every delivered declaration with `#print axioms` in scratch copies. The final
   result allows only the standard axioms and `sorryAx` from the explicitly open lower
   statement and pre-existing dependencies. No forbidden declaration or hollow definition.
   Verdict: sound assembly reduction with one named, documented lower hole.

3. Read the new statement against the existing bidegree predicate and the Stacks
   signed-face calculation. It fixes only `p,q`, three maps and their three coordinate
   hypotheses; the transports are `(p+1)+q=(p+q)+1` and `p+(q+1)=(p+q)+1`.
   Checked `p=q=0`: the two copies of the shared restriction have signs `-1` and `+1`;
   at `p=0` or `q=0` the same cancellation and nonempty face blocks remain valid.
   Characteristic two changes opposite signs to equal signs whose sum is zero. Empty
   index families give no tuples of these positive lengths, and zero coefficients give
   zero maps. No finiteness or covering assumption was introduced. Searches above found
   no exact existing external scalar statement. Verdict: true, strictly smaller than
   the assembly claim, with complete docstring and matching node; formal face proof open.

4. The original shortcut was refused as an equivalent restatement. The replacement
   actually proves the coproduct/inclusion/differential transport portion and leaves only
   the three-bidegree pure-tensor calculation. The public bidegree import is needed in
   the signatures, and the new private import is needed by the proof; no extra imports.
   Listed all four displaced old proof dependencies above. Read
   `dag/units/sk-prop-av-cube.json`: this coordinate node is below the unit, none of its
   realized entries is replaced, and the unit's cube-theorem route is unchanged.
   Verdict: legitimate decomposition, no claimed net hole reduction or module pruning.

5. Read both final nodes and the Lean modules together. The item's proof dependency is
   the pure-tensor node actually applied after the completed assembly rewrites. The new
   node lists the four existing ingredients of the remaining signed-coordinate argument,
   with their union as proof_deps, source, searches, provenance, chapter/unit and verbatim
   Lean signature. It has no dependency on the item and creates no circular route.
   Verdict: metadata agrees with the implemented reduction and documented remaining proof.

Changes by this second reading: removed the equivalent expanded statement/module/node
and the untracked canonical helper; restored the unchanged existing signature; wrote the
Mathlib tensor-total assembly proof; added the strictly smaller three-bidegree pure-tensor
Leibniz statement and node; corrected the report's hole accounting, provenance, searches
and dependency pruning.
