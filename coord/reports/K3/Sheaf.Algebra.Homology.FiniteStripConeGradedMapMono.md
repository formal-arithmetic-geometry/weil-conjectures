## What changed

Proved `HomologicalComplex₂.finiteStripGradedMap_mono` by the diagonal projection
and evaluated cokernel argument from its original docstring. The projection is
constructed explicitly using `totalDesc` and the cone biproduct isomorphisms.
Private, fully proved helpers check its value on total inclusions, its retraction
identity, and descent through the next-tail quotient. The public signature,
docstring, definitions used in that signature, and original public import are unchanged.
The cancellation proof of the first worker is retained, with its redundant `rfl`
step removed. The existing node's proof and proof_origin now describe the actual proof.

## Proved and sorry left

Closed the original hole in `HomologicalComplex₂.finiteStripGradedMap_mono`
(node `lem-sc-finite-strip-cone-graded-map-mono`): 1 of 1 original holes proved.
Also closed the first worker's proposed hole in
`HomologicalComplex₂.finiteStripGradedMap_hasLeftInverse`; it is now a private,
fully proved helper in the original module. Added holes: none. Sorry left: none.
Split-off statements delivered: none. This is a proof, not a decomposition.

The module compiles locally without warnings. A scratch copy with
`#print axioms HomologicalComplex₂.finiteStripGradedMap_mono` reports exactly
`propext`, `Classical.choice`, and `Quot.sound`.

## No longer needed

No original proof dependency or library module is pruned: the old proof_deps was
only `def-sc-finite-strip-cone-graded-map`, and it is still used and imported.
Removed the first worker's proposed proof import
`Sheaf.Algebra.Homology.FiniteStripConeGradedMapLeftInverse`, its new module,
and proposed node `lem-sc-finite-strip-cone-graded-map-left-inverse` from the
delivery. They had not landed. Their argument is now proved privately in the item.

## Where the brief, the DAG or earlier work was wrong

The first worker's split-off theorem postponed the entire original projection
and descent argument with all the same hypotheses. Its docstring did not include
the required complete proof in words, and the parent node had not been updated
to use it. The previous second-reading verdict did not address those faults.
No separately stated left-inverse theorem is needed: Mathlib's `totalDesc`,
image/kernel subobject lemmas, and cokernel preservation by evaluation suffice.
The repair follows the original DAG route and makes no statement change.

Independent searches used `msearch.py` with leanfinder (coproduct component
projection/inclusion identity) and loogle (cokernel descent). Leanfinder returned
`Sigma.ι_π_eq_id` and binary coproduct identities; the direct totalComplex API
`ι_totalDesc` fits the actual objects. The loogle query returned no identifier
match. Local `rg` searches of Mathlib and both library roots found the usable
`imageSubobject_arrow_comp_eq_zero`, `le_kernelSubobject`,
`isColimitOfHasCokernelOfPreservesColimit`, and `CokernelCofork.IsColimit.desc'`,
and no existing finite-strip projection or retraction theorem.

## Second reading by K3

1. Compared the delivered module with the repository by diff and checked the
   existing public theorem's signature byte for byte. Verdict: unchanged;
   all additions are private proof helpers; no public definitions or interface
   changes, no change record required.
2. Compiled the reviewed original pair, then the repaired single module through
   lcompile.py. Verdict: the final file compiles without errors or warnings,
   contains no sorry or forbidden declaration, and its axiom print contains
   only propext, Classical.choice, Quot.sound. Projection data are explicit;
   the quotient arrow comes from the cokernel universal property of an actual
   construction, not an arbitrary witness of an unproved existence theorem.
3. Read the proposed left-inverse statement and its node. Verdict: mathematically
   true but an insufficient whole-argument split. Closed its proof and removed
   the proposed public module/node. No split-off statements remain. Checked the
   edge cases in the proof: r=0 gives an empty target join; away from n+1=p the
   source of single(A.X p,0) is zero; outside the strip the existing support
   factorization supplies the zero target. The kernel computation treats every
   next-tail generator, including the source boundary p+1<=n+1.
4. Searched for alternate library routes and inspected the imports and the
   unit record dag/units/sk-thm-picard-duality.json. Verdict: the direct original
   diagonal projection/cokernel route is fully proved. There are no unused
   original imports or proof_deps; no unit realization or chapter route is
   bypassed. The unit's realized entries contain no assignment to this node.
5. Compared the original node, delivered node, and Lean proof. Verdict: its
   statement, lean record, and proof_deps stay unchanged; its proof and
   proof_origin now record the explicit projection, next-tail annihilation,
   cokernel descent, and cancellation. No new nodes are delivered.

Changes made by this second reading: closed the left-inverse construction,
made all projection/retraction machinery private in the item, removed the
proposed holed helper module and node, removed one redundant cancellation
step, updated the parent node's proof route, and corrected this report.
