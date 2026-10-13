## What changed

Replaced the sorry in `AlgebraicGeometry.Scheme.exists_finite_etale_extension_of_depth_three_of_quotient_extension` by a complete Lean proof from a compatible finite flat model and a proved differential criterion. The target signature and its public imports are unchanged. Two new proof-only imports are added:

- `Sheaf.AlgebraicGeometry.Morphisms.DepthThreePuncturedFiniteFlatModel` constructs a finite flat model with the required punctured isomorphism and etale principal quotient.
- `Sheaf.AlgebraicGeometry.Morphisms.FiniteUnramifiedPrincipalQuotient` proves that a finite morphism over a local ring is formally unramified when its principal quotient is etale. Its private algebra helper is fully proved using differential base change, the quotient-tensor isomorphism, and Nakayama.

The original completion/henselian lifting/gluing route remains in the model-construction lemma. The final step uses Mathlib's `Etale.of_formallyUnramified_of_flat`. The DAG records the actual reduction and both new nodes.

## Proved and sorry left

Closed the original direct hole in `AlgebraicGeometry.Scheme.exists_finite_etale_extension_of_depth_three_of_quotient_extension` (node `lem-sbc-depth-three-punctured-etale-lifting`). Its proof still depends on the one new construction hole below, so this is a decomposition, not a sorry-free proof of the original mathematical result.

Fully proved `AlgebraicGeometry.Scheme.formallyUnramified_of_finite_of_principal_quotient_etale` (node `lem-sbc-finite-unramified-principal-quotient`) and its private algebra helper. This theorem has no dependency on the model-construction hole and needs neither depth nor flatness.

Added exactly one hole: `AlgebraicGeometry.Scheme.exists_finite_flat_model_of_depth_three_of_quotient_extension` (node `lem-sbc-depth-three-punctured-finite-flat-model`). Its entire proof is `by sorry`, with a source and complete construction argument in its docstring. No sorry remains in the item's module. Direct holes closed: 1; holes added: 1; net: 0.

Edge cases checked: f = 0 makes the differential quotient condition immediate; the zero finite algebra has zero differentials and the empty cover is handled by the zero model. The generic criterion also correctly allows finite closed immersions (which are formally unramified); flatness is used separately when asserting etaleness. There is no regularity or nonzerodivisor hypothesis and no arbitrary data definition selected from an unproved existence statement.

## No longer needed

No modules or imports are pruned. No original imports were removed. Both new proof imports are used.

The original node no longer directly uses these old proof dependencies:
`def-weil-pbc-depth`, `def-weil-pbc-scheme-conventions`,
`def-weil-pbc-adic-completion`, `def-weil-pbc-henselian-terminology`, and
`def-weil-flat-morphism`. They have moved to the finite-flat-model node's construction
argument, rather than becoming obsolete in the transitive route. The remaining old
`def-weil-etale-morphism` dependency is used in the final criterion. This accounts for
every old dependency absent from the original node's new `proof_deps`.

## Where the brief, the DAG or earlier work was wrong

The DAG's proof dependencies record the relevant definitions, but do not provide the completion/henselian/gluing theorem as a usable Lean declaration. The remaining construction has therefore been stated as a separate finite-flat-model construction conclusion; its etaleness is verified separately by the proved generic criterion.

An initial sandbox experiment asserted compatibility of an arbitrary finite etale cover with q. That assertion is false (r could be the empty cover while q is nonempty). Both experimental modules and nodes were deleted and are absent from this delivery. The final model theorem retains its own compatible punctured isomorphism; the generic criterion asserts only unramifiedness of a supplied finite morphism with its own etale quotient. No second-reader statement is supplied by this worker.

## New nodes

`lem-sbc-depth-three-punctured-finite-flat-model`: the completion/henselian lifting and finite-algebra gluing construction, with flatness and quotient etaleness descended from the completed model. Module `Sheaf.AlgebraicGeometry.Morphisms.DepthThreePuncturedFiniteFlatModel`. This is the only new sorry and preserves the original unit route.

`lem-sbc-finite-unramified-principal-quotient`: the fully proved generic differential/Nakayama criterion. Module `Sheaf.AlgebraicGeometry.Morphisms.FiniteUnramifiedPrincipalQuotient`. Unlike the original theorem it does not construct an extension or an isomorphism, and has no depth or punctured-cover assumption. No existing interface was changed, so no change record or forced adaptation is required.

## Second reading by C1

1. **Visible interface: PASS.** Compared the item's complete module by `diff` with
   the repository. Only two plain proof imports and its proof body differ; the
   existing theorem signature is byte for byte unchanged. The sibling modules and
   nodes are new. No definitions, instances, public imports of existing modules,
   target statements, change records, or forced adaptations are introduced.
2. **Kernel proof: PASS with the reported construction hole.** Compiled all three
   modules in dependency order using `lcompile.py --all`; no errors or warnings.
   Independently checked `#print axioms` for the original theorem, model theorem,
   generic criterion and private algebra helper. The generic criterion and helper
   use only `propext`, `Classical.choice`, and `Quot.sound`; the model and original
   theorem additionally use `sorryAx`. There is exactly one textual hole, the
   whole proof of the public named model theorem. No forbidden declarations or
   data choices from an unproved existence theorem occur.
3. **Split statements: PASS.** Read the tensor base-change, quotient-tensor and
   Nakayama argument. Finiteness of differentials makes the quotient criterion
   valid even for a finite closed immersion; flatness is required only later.
   Checked f = 0, empty covers, and the identity finite cover. Checked the model
   construction against [0BLS](https://stacks.math.columbia.edu/tag/0BLS),
   [0BM6](https://stacks.math.columbia.edu/tag/0BM6),
   [0BLH](https://stacks.math.columbia.edu/tag/0BLH),
   [0BLL](https://stacks.math.columbia.edu/tag/0BLL),
   [09ZL](https://stacks.math.columbia.edu/tag/09ZL), and
   [0AVY](https://stacks.math.columbia.edu/tag/0AVY).
   Completion is faithfully flat and its punctured inverse image is the punctured
   completion; full faithfulness lifts the compatible quotient isomorphism and
   its inverse. Gluing gives a finite model whose flatness and quotient etaleness
   descend. The docstring gives this argument and the matching node records it.
   This leaves construction open while fully proving the separate differential
   step: an honest decomposition, not a sorry-free proof. Independent searches
   used different phrases about algebraization over completion and vanishing of
   differentials after quotient, with Lean Finder, Loogle and grep. No existing
   exact theorem was found; `Ideal.Quotient` was not a valid Loogle identifier,
   so a second query used `Ideal.span`. Read the existing unramified quotient and
   base-change lemmas: they have the opposite implication and do not close this
   goal. The construction cannot be closed in a few minutes with these results.
4. **Route and pruning: PASS after report repair.** The original completion,
   henselian lifting, full-faithfulness and gluing route is retained in the model
   node. The final formally-unramified-plus-flat criterion is a real proved step.
   All supplied imports serve signatures or proofs. The unit is
   `sk-prop-input-spreading`; its `realized` statement and seven step arrays are
   currently empty, and this delivery neither changes them nor bypasses its
   trait-purity route. Corrected `No longer needed` to enumerate the five old
   direct proof dependencies that moved into the model construction; no module
   is pruned.
5. **DAG agreement: PASS.** Checked the original node's new proof steps and
   dependency union, both new nodes' complete records, matching Lean signatures,
   sources, searches, chapter and unit, and construction proof. The generic node
   accurately records affine reduction followed by differentials and Nakayama.
   The original node now records model construction followed by that criterion
   and Mathlib's etale criterion. Existing statement and statement dependencies
   remain unchanged.

Changes by the second reader: corrected the dependency accounting in
`No longer needed` and added this independent review. No Lean proof or statement
needed repair. Original holes closed: one; new holes added: one; net zero.
