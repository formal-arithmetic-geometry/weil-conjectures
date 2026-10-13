## What changed

Replaced the sole hole in
`AlgebraicGeometry.Scheme.exists_finite_etale_depth_two_model` without changing its
signature or public imports. The proof first obtains boundary depth from regular
parameters, then applies the existing global depth-two finite extension theorem.
It proves this extension flat by punctured local purity and a minimal nonflat
fibre argument, and applies the existing formal-unramifiedness criterion.

Added three modules, each with one public theorem and a matching DAG node:
`RegularLocalPuncturedEtalePurity`, `PuncturedLocalPurityFiniteFlatFiber`, and
`LocalPurityDepthTwoFiniteFlatStalk`, all under
`Sheaf.AlgebraicGeometry.Morphisms`. The latter two have complete Lean proofs.
The only new hole is the classical regular-local purity input, Stacks Tag 0BMA.
No definition or existing statement changed. No other group's module was adapted.

The local fibre proof verifies that the stalk base change is etale off the closed
point, extends that cover using the purity hypothesis, compares the extensions by
depth-two uniqueness, and descends flatness near the point. The global flatness
proof uses openness of the finite flat target locus and a generic point of an
irreducible component of its closed complement. It requires neither global
quasi-compactness nor quasi-separatedness of the target.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.exists_finite_etale_depth_two_model` (one of one original
holes). Its proof is complete relative to the imported declarations.

Also proved, without local holes:

- `AlgebraicGeometry.Scheme.flat_fibre_of_punctured_local_purity`, node
  `lem-sbc-punctured-local-purity-finite-flat-fibre`;
- `AlgebraicGeometry.Scheme.flat_of_local_purity_depth_two_finite_extension`, node
  `lem-sbc-local-purity-depth-two-finite-flat-stalk`.

The delivery adds exactly one hole:
`AlgebraicGeometry.Scheme.exists_finite_etale_extension_of_regular_local_punctured_spectrum`,
node `lem-sbc-regular-local-punctured-etale-purity`, in
`RegularLocalPuncturedEtalePurity.lean`. Its proof is exactly `:= by sorry`, and its
docstring gives the source and the dimension-induction argument. It is strictly
local: it concerns only the punctured spectrum of one regular local ring, with
no arbitrary boundary or global scheme extension construction.

This is a decomposition, closing one upper hole and adding one local hole; it is
not a claim that regular purity or the target is now axiom-free. Every private
helper is proved. There is no sorry in any definition and no arbitrary object
selected from an unproved existence theorem inside a definition.

All four delivered modules compiled together through `lcompile.py --all`.

## No longer needed

Removed the direct proof import `Sheaf.RingTheory.FlatLocalDepthFormula` from the
item's module. The formula remains genuinely needed, and is imported directly by
`PuncturedLocalPurityFiniteFlatFiber`; it is not a globally pruned module.

The original affine-model gluing route is replaced by the already constructed
global depth-two extension followed by local flatness. A separate construction
of affine finite etale models, a global finite-etale spreading theorem, and an
overlap cocycle/gluing theorem are not needed for this item. They were not
separately named dependencies of the original node, so no particular existing
module is claimed globally unreachable on this basis.

The original direct dependency
`lem-sbc-depth-two-finite-extension-uniqueness` is no longer direct for the item,
but remains necessary in the local fibre proof. Likewise the depth formula is an
indirect dependency. No existing node or module is claimed pruned globally.

## Where the brief, the DAG or earlier work was wrong

The original node's one-step plan compressed the substantive regular-local
purity theorem into its citation to Tag 0BMA without a separately usable Lean
statement of that input. The new local purity node isolates precisely this
remaining source argument. The rest of the extension argument is now verified
in Lean using existing statements and the two proved new theorems.

The seemingly reusable `RegularCodimensionTwoEtaleExtension` module cannot be
imported: it reaches this item through `RegularCodimensionTwoFiniteFlatStalk`,
creating an import cycle. The delivery instead uses lower existing depth-two
extension, uniqueness, flat-locus and purity declarations, with no cycle.

The route retains the regular-boundary purity input of blueprint unit
`sk-prop-input-spreading`; only its subsidiary scheme extension mechanism changes.
No statement is disputed or weakened. Edge cases checked: dimensions zero and
one are excluded by the local purity premise; empty covers have the empty
extension; an empty source gives an everywhere-flat target locus; V equal to L
has no boundary; disconnected targets are handled componentwise by the
closed-complement generic-point argument without an irreducibility assumption.
The new local fibre statement is vacuous when its fibre is empty.

Mathlib searches used leanfinder, loogle and grep; the leansearch service returned
Internal Server Error. None yielded regular-local purity. The searches and
results are recorded in the new nodes. Stacks Tags 0BMA, 0BM9, 0BLM, 0BJH, 0EY7
and 0EY6 were checked against their source statements.

## New nodes

`lem-sbc-regular-local-punctured-etale-purity`, in
`dag/nodes/sec-smooth-base-change/`, states the remaining regular-local
punctured-spectrum extension theorem, Stacks Tag 0BMA. Its proof plan records
normal-algebra reduction, the dimension-two miracle-flatness argument, and
parameter quotient induction with the lifting criterion. This node carries the
one newly added sorry.

`lem-sbc-punctured-local-purity-finite-flat-fibre`, in the same directory, records
the proved local comparison argument. Its hypotheses separate punctured local
purity from proper-generalization flatness; the conclusion is only flatness over
one specified point. Its actual proof dependencies include the existing flat
quasi-finite depth purity, depth formula, depth-two uniqueness, canonical stalk
flatness and flat descent core.

`lem-sbc-local-purity-depth-two-finite-flat-stalk`, in the same directory, records
the proved global flatness consequence. Openness of the finite flat target locus
and the local fibre lemma rule out a minimal nonflat target point. It proves
flatness of a supplied finite extension, not existence of an etale model.

Updated only `proof`, `proof_deps` and `proof_origin` of the existing item node to
match the actual Lean argument. There are no change records because no existing
interface changed.

## Second reading by U1

1. **Unchanged interfaces: pass.** Compared the item module with the repository
   using `diff`, and checked the existing theorem signature byte for byte.
   No existing declaration, definition, visibility or public import changed.
   Only the item's proof, docstring and private helper, proof imports, three new
   modules and their nodes are delivered. The existing node changes only
   `proof`, `proof_deps` and `proof_origin`; no change record is required.
2. **Proof and trust: pass.** Compiled all four modules together with
   `lcompile.py --all`. Inspected every proof and private helper; there is exactly
   one direct sorry, the named regular-local purity theorem reported above.
   No definition, arbitrary witness chosen in a definition, forbidden axiom or
   unchecked implementation is added. A separate scratch module printed axioms
   of all four public theorems: only `propext`, `Classical.choice`, `Quot.sound`
   and `sorryAx` from remaining imported statements. The delivery probe also
   checks all private declarations. Reported compile elapsed times include
   waiting for a compile slot; the enforced Lean limit itself passed.
3. **New statements: pass.** Read the local comparison proof, the generic-point
   proof of global flatness, and the regular-local purity statement. The only
   new hole is precisely [Stacks Tag 0BMA](https://stacks.math.columbia.edu/tag/0BMA),
   assertion (1). Its dimension induction agrees with Tags 0BM9 and 0BLM.
   Checked empty covers/fibres, V equal to L, dimension two as the base case,
   excluded dimensions zero and one, and disconnected/non-quasi-compact targets.
   The purity input is strictly local and does not duplicate the global item.
   Independent leanfinder search for Zariski--Nagata purity, loogle search for
   `IsRegularLocalRing`, grep search for branch-locus purity, and `rg` searches
   in the repository found no reusable exact theorem. The existing global
   regular-boundary extension theorem depends on this item, so using it would
   be circular. The remaining classical purity proof cannot be closed by a
   short existing-library argument.
4. **Route and pruning: pass.** The proof first uses the existing global depth-two
   extension, then supplies regular-local purity and proves flatness by local
   comparison and a generic point of the closed nonflat locus. All proof-only
   imports are plain imports. Every public import supports the signatures.
   Both old dependencies removed from the item's direct `proof_deps` are
   accounted for in `## No longer needed`: the flat local depth formula and
   depth-two finite-extension uniqueness remain used by the local fibre lemma.
   No module is claimed globally pruned. The unit `sk-prop-input-spreading`
   has empty `realized` assignments; its stated regular-boundary purity route
   is retained, with no unit statement or step changed.
5. **DAG agreement: pass.** Checked the four node statements against their Lean
   signatures and checked each `proof_deps` equals the union of the step uses.
   Read the actual dependencies, including the canonical-stalk flat instance
   and the flat-test descent core. The new nodes have source, proof, searches,
   creation, blueprint, chapter, unit and Lean records. The proved reductions
   are strictly parts of the argument, not fresh holed restatements.

Second-reading changes: clarified the regular-local purity docstring and its
node's induction step to state explicitly that regular parameters give depth
at least three, and that the parameter is a nonzerodivisor, as required by
Tag 0BLM. Added this independent review. No Lean statement or proof changed;
no further hole was closed or added. This remains a one-for-one decomposition.
