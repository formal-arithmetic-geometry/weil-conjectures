## What changed

Proved `AlgebraicGeometry.Scheme.Modules.exists_affine_perfect_sections_projective_model`
with its signature unchanged, using the existing affine bounded-projective characterization,
affine derived equivalence, and scheme-isomorphism derived/perfect transport. Added the fully
proved module `Sheaf.AlgebraicGeometry.AffineSectionsComplexCounit` for the actual chain-level
comparison. All new proof imports of the item are non-public. No existing definition,
statement, or public import changed. Updated the item's proof route in its node.

The comparison constructs the affine section natural isomorphism explicitly and maps the
quasi-coherent counit to complexes. It chooses no model from an unproved existence theorem.
The item uses standard localizations on Spec A and all its open sites; the user's given
localizations on Y and modules over A retain their original independent universes.

Sources read: [Stacks 01IB](https://stacks.math.columbia.edu/tag/01IB),
[Stacks 06Z0](https://stacks.math.columbia.edu/tag/06Z0), and
[Stacks 08EB](https://stacks.math.columbia.edu/tag/08EB). The local Stacks source files
are absent on this machine, so these source pages were read directly. LeanSearch returned
an internal-server error; LeanFinder, Loogle and source grep were also tried.

## Proved and sorry left

Closed 1 original hole:
`AlgebraicGeometry.Scheme.Modules.exists_affine_perfect_sections_projective_model`
(node `lem-pc-affine-perfect-sections-projective-model`).

Added 0 holes. The new theorem
`AlgebraicGeometry.Scheme.Modules.affine_sections_complex_counit`
(node `lem-pc-affine-sections-complex-counit`) and the private natural section comparison
are fully proved. No `sorry` remains in either delivered module. This is a proof from
existing stated dependencies, not a decomposition into new holes. Existing imported
affine equivalence/perfectness results may still transitively rest on project sorries.

Both modules compile in import order without warnings with `lcompile.py --all`.
The new comparison covers unbounded and zero complexes and the empty affine scheme.
The main proof imposes no extra hypotheses; its original bounded-above assumption is
not needed by this route but its binder is retained unchanged.

## No longer needed

The proof does not import or use `Sheaf.AlgebraicGeometry.SchemeIsoDerivedQCoh`
(node `lem-pc-scheme-iso-derived-qcoh`): the affine equivalence supplies the
quasi-coherent derived object directly. Removed that planned proof edge.

No pre-existing imports were removed from the item; all three were public statement
imports and remain. The direct planned edge to
`lem-weil-pbc-affine-tilde-gamma-adjunction` moves into the proved complex-counit helper;
it is still needed there and is not globally pruned. Every added proof import is used.
No other original proof-dependency node or module is pruned by this delivery.

## Where the brief, the DAG or earlier work was wrong

The first dry run detected an import cycle through the source affine pushforward theorem;
that import was removed and replaced by Mathlib restriction quasi-coherence plus
uniqueness of left adjoints. No false statement or unusable signature was found. The DAG's quasi-coherent-homology
transport step is unnecessary: use the affine derived equivalence comparison to provide
membership in D_QCoh. The unit statement and route are preserved; only this node's
chain-level glue and redundant intermediate edge change. The unit's `realized` record
has no nodes assigned to its statement or sole step; this delivery does not alter it.

## New nodes

`lem-pc-affine-sections-complex-counit`, in
`dag/nodes/sec-picard-framework/lem-pc-affine-sections-complex-counit.json`, records the
fully proved comparison module `Sheaf.AlgebraicGeometry.AffineSectionsComplexCounit`.
It has no perfectness or boundedness assumptions and no projective-model conclusion.
Its proof identifies chart pushforward with inverse-chart restriction by uniqueness
of left adjoints. Mathlib's restriction quasi-coherence and affine counit then give
the actual complex and pushforward comparison isomorphisms.
Blueprint searches for `complex counit` and `01IB` returned no matching imported node.
No change records or forced adaptations are needed.

## Second reading by B2

1. **Interfaces: pass.** Compared the item against the repository with `diff` and
   checked the theorem signature byte for byte. The existing signature and all
   existing public imports are unchanged. Only proof imports, the proof body, and
   its local elaboration option were added. The helper is new; no existing
   definition or target interface changes and no change record is required.
2. **Proof and compilation: pass.** Compiled both modules in import order with
   `lcompile.py --all`, without errors or warnings. Searched both sources for all
   forbidden constructs and sorries: none. Scratch-copy `#print axioms` shows
   exactly `propext`, `Classical.choice`, and `Quot.sound` for
   `affine_sections_complex_counit`; the item additionally uses `sorryAx` from
   existing imported open statements. No delivered definition obtains an
   arbitrary witness from an unproved existence theorem. The private comparison
   constructs its actual linear maps explicitly; the model is eliminated only
   inside the existential theorem proof.
3. **New statements: pass.** No new open statement is split off. The fully proved
   helper is strictly the chain-level reconstruction step, with no perfectness,
   boundedness, or projective-model conclusion. Checked zero, unbounded, and
   empty-affine cases: componentwise counit invertibility and inverse-chart
   pushforward remain valid. Checked scalar compatibility using the composition
   of `isoSpec.hom.appTop` with `GammaSpecIso.inv`, and differential compatibility
   using the natural counit. Independent LeanFinder and Loogle searches and
   source grep (`tilde.*counit|sections.*complex|fromTildeΓNatTrans`) found the
   Mathlib component APIs but no existing theorem giving this complex comparison.
   Read Stacks [01IB](https://stacks.math.columbia.edu/tag/01IB),
   [06Z0](https://stacks.math.columbia.edu/tag/06Z0), and
   [08EB](https://stacks.math.columbia.edu/tag/08EB) against the route.
4. **Route and pruning: pass.** The proof uses the existing affine equivalence
   and bounded-projective characterization, transports perfectness across the
   canonical chart, and lifts the comparison by full faithfulness. No shorter
   available theorem was found. The new helper's public imports provide types
   and functors in its signature; the item's five added imports are proof-only.
   All are used. The old direct adjunction edge moves into the helper, and the
   unused scheme-isomorphism quasi-coherent-homology edge is listed under
   `No longer needed`. The coherence unit's statement and sole step are kept;
   its already-empty `realized` assignments are unchanged. This delivery prunes
   a planned proof edge, not a proven globally unreachable module.
5. **Nodes: pass.** The existing node changes only `proof`, `proof_deps`, and
   `proof_origin`. For both nodes `proof_deps` is exactly the union of step uses.
   Read the new node whole: source, self-contained statement, searches, creation,
   blueprint ancestry, chapter/unit, and verbatim Lean statement are present and
   agree with the implemented reconstruction.

**Second-reader changes:** corrected the new helper's docstring scalar identity:
its proof uses `isoSpec.hom.appTop` composed with `GammaSpecIso.inv` equal to the
identity, rather than the previously stated identity for `isoSpec.inv.appTop`.
No proof, signature, definition, import, or node changes were necessary. Added
this independent review and its compilation/axiom evidence. Closed 1 original
hole and added 0 holes; the new helper is fully proved.
