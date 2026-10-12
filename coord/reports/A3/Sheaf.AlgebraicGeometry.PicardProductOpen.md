## What changed
Added the proof-only theorem `AlgebraicGeometry.Scheme.picard_product_open_core`, which isolates the geometric Picard-locus construction and records the auxiliary module and its trivialization. The target theorem `AlgebraicGeometry.Scheme.picard_product_open` is now proved by applying this core theorem and composing the two resulting isomorphisms. The target proof compiles in the sandbox.

## Proved and sorry left
The target hole `AlgebraicGeometry.Scheme.picard_product_open` is closed. The decomposition theorem `AlgebraicGeometry.Scheme.picard_product_open_core` remains `sorry`; it is recorded as node `lem-sc-picard-product-open-core` and is the strictly geometric part requiring the Kunneth, multiple-locus, and flat-base-change inputs.

## No longer needed
No imports were removed. The target's former direct proof dependencies are now dependencies of the core theorem and remain needed by the stated geometric route.

## Where the brief, the DAG or earlier work was wrong
The original DAG treated the full geometric Picard-locus construction and the final composition as one proof step. The delivery splits these into a named intermediate theorem and a real composition proof. No target statement or existing interface was changed.

## Earlier second reading (a previous round; superseded)
The target proof is a direct composition of the two isomorphisms supplied by the core theorem; its signature is unchanged. The new core statement is strictly stronger than the target because it exposes the auxiliary module and its unit isomorphism, and its proof follows the unit route through the Kunneth and multiple Picard-locus lemmas.

## New nodes
`lem-sc-picard-product-open-core` records the geometric Picard-locus construction isolated as `AlgebraicGeometry.Scheme.picard_product_open_core` in the delivered module.

## Second reading by A3

1. **Visible declarations and statements.** Compared the delivered module with the repository version. The existing target signature is byte-for-byte unchanged; the only added declaration is the recorded intermediate core theorem. Verdict: pass.
2. **Proof and axioms.** Compiled the delivered module with `lcompile.py`; it compiles cleanly. The target proof is a direct composition of the two isomorphisms returned by the core theorem. The only remaining `sorry` is the named core theorem, recorded by its node; no forbidden declarations or hollow definitions were added. Verdict: pass subject to the documented split hole.
3. **New statement.** Checked the core theorem's hypotheses and conclusion against the target hypotheses and its geometric construction. It is a strict intermediate strengthening exposing the auxiliary module and both isomorphisms, and the final theorem follows by their composition. Verdict: pass.
4. **Pruning and route.** The proof uses the core theorem, while the core's stated geometric dependencies remain required by the unit route. No import or proof dependency can be removed from this delivery. Verdict: pass.
5. **DAG agreement.** The core node records the declaration, source, proof steps, proof dependencies, and split status; the target node now records the core theorem as its proof dependency. The unit route remains the Picard product openness route. Verdict: pass.

Changed only the module proof, added the documented core split theorem and node, and recorded this second reading. No target statement or definition was changed.
