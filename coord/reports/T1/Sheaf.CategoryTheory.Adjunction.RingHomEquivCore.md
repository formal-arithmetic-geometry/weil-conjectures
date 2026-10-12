## What changed

Proved `CategoryTheory.Adjunction.ringHomEquivCore` without changing its statement. The proof constructs both maps of the ring hom-set equivalence, proves both inverse laws, proves its two naturality fields using the specified underlying-functor equalities, and derives the forward, unit and counit formulas by cancellation. Two proof-only imports separate the forward and inverse operation-preservation steps into new modules.

The operation-preservation lemmas are strictly parts of the argument: they supply only `IsRingHom` proofs for explicitly given underlying adjuncts. Neither states an equivalence, naturality, or any unit/counit formula. The main module constructs and proves all of those.

## Proved and sorry left

Proved `CategoryTheory.Adjunction.ringHomEquivCore` (the one original sorry).

Two named sorry obligations remain:

- `CategoryTheory.Adjunction.ringAdjunctPreservesOperations`, node `lem-weil-pbc-ring-adjunct-preserves-operations`, in `Sheaf.CategoryTheory.Adjunction.RingAdjunctPreservesOperations`.
- `CategoryTheory.Adjunction.ringCoadjunctPreservesOperations`, node `lem-weil-pbc-ring-coadjunct-preserves-operations`, in `Sheaf.CategoryTheory.Adjunction.RingCoadjunctPreservesOperations`.

Both have the original transported-operation hypotheses and complete natural-language proofs in their docstrings. Their identity-adjunction case reduces to the given ring morphism; the terminal-category case is automatic; the proofs do not require a canonical braiding or nontrivial ring objects. IsRingHom asks for addition, zero, multiplication and one, so no independent negation obligation is needed.

## No longer needed

No existing imports or modules were removed, and no node became unreachable. `def-weil-category-product` was removed from the main node's direct `proof_deps`: its role is now carried by the two operation-preservation nodes, which still depend on it. The original product definition is therefore still used transitively; the adjunct/counit identity node remains represented by Mathlib's homEquiv inverse laws and formulas. No unit statement or unit step was bypassed (`sk-def-exchange.realized` is unchanged).

## Where the brief, the DAG or earlier work was wrong

No mathematical defect found. The original node's single proof step conflated operation preservation with equivalence construction, naturality and identity formulas. This delivery separates the two operation-preservation obligations and fully proves the rest.

The local checkout does not contain `literature/stacks-project/sites.tex`; the cited Proposition 00YV was read at https://stacks.math.columbia.edu/tag/00YV. Its proof explicitly extends the operation-based abelian-group argument to rings and leaves the restriction details to the reader; the detailed categorical proofs in the two nodes are supplied by T1.

## New nodes

`lem-weil-pbc-ring-adjunct-preserves-operations`: the explicit conjugated forward adjunct is an internal ring homomorphism. Its module supplies only a proof field for the forward ring morphism; no equivalence data is assumed.

`lem-weil-pbc-ring-coadjunct-preserves-operations`: the explicit conjugated inverse adjunct is an internal ring homomorphism. Its module supplies only a proof field for the inverse ring morphism. No statement or definition was changed and no change record is required.


## Second reading by T1

1. Compared all delivered Lean with the repository. The only existing module is
   RingHomEquivCore; its diff changes only two proof-only imports and the proof body.
   Its theorem signature is byte-for-byte unchanged. The two other modules are new,
   contain only theorem declarations, and change no shared definition or target.
   Verdict: pass; no change record is needed.
2. Compiled all three files locally in import order, without errors or warnings.
   There are exactly two `sorry` tokens, in the named operation-preservation theorems
   listed above, and none in the main theorem. Scratch copies with `#print axioms`
   for each declaration show only propext, Classical.choice, Quot.sound and sorryAx.
   The main theorem still depends on the two open proofs; it is not axiom-free yet.
   No forbidden declaration, kernel-check bypass or hollow definition occurs.
   Verdict: pass for a partial stage-3 reduction.
3. Read both new signatures, docstring arguments and matching nodes. Each proves
   only one direction's operation preservation, not the equivalence or its formulas.
   Checked the binary-operation comparison identities by their two projections,
   and the constant identities by terminal uniqueness. These arguments apply also
   to arbitrary supplied braidings. As edge cases, the identity adjunction with
   identity lifts reduces both conclusions to the given morphism's IsRingHom
   instance; in a terminal category every required equation is automatic. Checked
   the cited [Stacks Proposition 00YV](https://stacks.math.columbia.edu/tag/00YV),
   which explicitly extends the operation-based restriction argument to rings.
   Repeated LeanFinder, Loogle and Mathlib grep with different search terms, and
   searched Sheaf and the upstream library. Cartesian natural transformations are
   monoidal and Mathlib can lift monoid transformations, but neither supplies the
   stated conjugated ring adjunct theorem. Closing either open lemma requires the
   operation-comparison argument, not a short existing-lemma application.
   Verdict: genuine, true partial obligations; both remain open.
4. Read the main proof from its conclusion downward. The inverse laws and naturality
   use the underlying adjunction and naturality of eqToIso; unit and counit formulas
   follow by cancellation. Both Mathlib public imports are needed by signatures;
   both new imports are used only by the proof and are correctly plain imports.
   The report now explicitly lists the removed direct product-definition dependency,
   which remains reachable through both new nodes. No module is pruned. Checked
   sk-def-exchange.realized: its statement realizers and empty step list are retained.
   Verdict: pass; no unit route is bypassed.
5. Compared every Lean signature with its node's verbatim lean.statement, and checked
   the existing node's changed fields against the repository. Only proof,
   proof_deps and proof_origin changed. Its new proof dependencies match the two
   preservation steps and the Mathlib adjunct/counit identity tool. Both new nodes
   have source, full proof, search records, creation, blueprint, chapter, unit and
   Lean records required by the brief. Verdict: pass.

Second reading changed only the report's direct-versus-transitive dependency wording
and recorded this review plus independent searches; the Lean proofs and statements
needed no repair.
