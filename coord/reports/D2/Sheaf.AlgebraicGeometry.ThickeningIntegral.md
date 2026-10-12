## What changed

Filled `AlgebraicGeometry.isIntegralHom_iff_of_thickenings` without changing its
signature, visibility, docstring, definitions or imports. The forward implication
proves universal closedness by composition and surjective cancellation, constructs
affineness from affine preimages and `isAffine_of_isThickening`, and applies
`IsIntegralHom.iff_universallyClosed_and_isAffineHom`. The reverse implication uses
composition and `IsIntegralHom.of_comp`. Updated the existing node's affine-open
step and proof dependencies to follow this proof.

## Proved and sorry left

Closed: `AlgebraicGeometry.isIntegralHom_iff_of_thickenings`
(node `lem-weil-pbc-thickening-integral`), one of one original holes.
Added holes: none. No sorry remains in the delivered module; no statements are
split off. This is a proof from an existing open dependency, not an axiom-free
completion: `AlgebraicGeometry.isAffine_of_isThickening` in the unchanged module
`Sheaf.AlgebraicGeometry.ThickeningAffineScheme` remains sorry. The scratch axiom
probe reports exactly `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`.
The delivery's local hole delta is one closed, zero added; the authoritative
closure ledger remains the maintainer's measurement.

Removed the first draft's undelivered sorry theorem
`AlgebraicGeometry.isIntegralHom_of_thickening_restriction` and its new node
`lem-weil-pbc-thickening-integral-hard-direction`.

## No longer needed

No imports removed and no modules pruned: all three imports are necessary.
The two public imports supply statement vocabulary; the private import supplies
the affineness theorem used only in the proof.

Removed `lem-weil-pbc-affine-morphism-permanence` from the original node's
`proof_deps`: its `isAffine_of_isAffineHom` source-affineness lemma is bypassed by
`IsAffineOpen.preimage` twice. All other original dependencies remain used in
setup, composition, cancellation, affine-preimage construction, or thickening
affineness. The discarded new hard-direction node is not delivered.

## Where the brief, the DAG or earlier work was wrong

The first draft compiled with four haveI/letI style warnings, moved the original
docstring onto the new theorem, left the original theorem undocumented, copied
stale review metadata into the new node, and did not update the item's existing
node. Its hard implication was unnecessary as a split: the already imported
thickening-affineness theorem suffices for the full affine-open argument.
No mathematical statement or blueprint unit route needed changing.

## Second reading by D2

1. Compared the final delivered module with the repository using `diff -u`.
   The only change is the original theorem's proof body: its signature is byte
   for byte unchanged, as are every import, definition, visibility and docstring.
   No other module or change record is delivered. Verdict: pass.
2. Compiled locally through `lcompile.py` without errors or warnings. Scanned for
   sorry, axioms, unsafe, opaque, implemented_by and extern: none in the final
   module. Compiled a scratch copy with `#print axioms` for the theorem; only
   the three standard axioms and `sorryAx` occur, the latter from the existing
   imported affineness theorem. No data is chosen from an unproved existence
   theorem. Verdict: pass, with the explicitly recorded open dependency.
3. No new statement or split-off hole survives this reading. Checked the argument
   for identity thickenings, empty schemes and the empty affine open: surjectivity
   and the restricted lifting proof cover these cases without extra assumptions.
   Rechecked the Stacks source (09ZV and 06AD) from the available local checkout.
   Searched with leanfinder, loogle and grep via `msearch.py`, and `rg` over the
   library and Mathlib using affineness descent, closed immersion, affine preimage,
   composite preimage and cancellation queries. These confirm the existing
   affineness theorem and Mathlib tools used; no duplicate theorem is added.
   Verdict: pass.
4. Proved the original hole directly from the existing planned declarations;
   the new hard-direction hole is removed. All imports are used and have the
   correct visibility. The old dependency pruned is listed above. Read
   `dag/units/sk-thm-p1.json`: this node does not realize its statement or any
   unit step, and the unit's realized declarations and route are preserved.
   Verdict: pass.
5. Updated the existing node's affine-open step, proof_deps and proof_origin.
   The steps now describe the actual restriction, its pointwise surjectivity,
   Stacks 06AD, Mathlib universal-closed cancellation and integral cancellation.
   The new draft node is removed, so no new-node schema obligation remains.
   Verdict: pass.

Changed during second reading: replaced the draft reduction by a complete proof
from the existing affineness dependency; removed its new theorem and node;
restored the original docstring; eliminated local-instance style warnings;
updated the existing DAG node; corrected this report's proof and pruning counts.
