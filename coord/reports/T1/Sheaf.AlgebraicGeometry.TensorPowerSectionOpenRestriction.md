## What changed

The existing statement and docstring of `AlgebraicGeometry.Scheme.Modules.exists_tensorPowSection_open_restriction` are unchanged. Its proof now constructs the additive numerator equivalences from actual isomorphisms of module sheaves. Naturality, inverse cancellation and injectivity prove the complete coefficient-equation clause directly; the transition clause is reduced to a sheaf-morphism coherence theorem.

`TensorPowerSectionOpenRestrictionN` contains the canonical tensor comparison, its recursive tensor-power comparison, and the numerator comparison. The tensor comparison is selected from the existing `exists_restriction_tensor_comparison`, whose inverse is uniquely determined on all pure tensor sections by the sheaf tensor universal property. This is uniquely characterized data, not an arbitrary existence witness. The recursive definitions contain no postponed proofs or hollow data. The section-power theorem `openRestrictionTensorPowIso_inv_section` is proved by induction, including the degree-zero structure-ring isomorphism and the successor pure-tensor formula.

`TensorPowerSectionOpenRestrictionT` contains the one remaining transition-coherence theorem `openRestrictionNumeratorIso_mul`. Both new imports in the item are plain proof imports. The new modules' public imports are needed by their signatures or public definitions. A declaration-scoped `linter.unusedVariables` option suppresses the original unused quantified name `hW`; its spelling and the entire original theorem signature are preserved. No statement, definition or import visible from the existing item changes, and no other existing module is adapted.

## Proved and sorry left

Baseline hole closed: `AlgebraicGeometry.Scheme.Modules.exists_tensorPowSection_open_restriction` (node `lem-sc-tensor-power-section-open-restriction`). The item's module now has zero textual sorries.

New theorem proved: `AlgebraicGeometry.Scheme.Modules.openRestrictionTensorPowIso_inv_section` (node `lem-sc-tensor-power-section-open-restriction-N`).

One hole added and left: `AlgebraicGeometry.Scheme.Modules.openRestrictionNumeratorIso_mul` (node `lem-sc-tensor-power-section-open-restriction-T`). It has precisely a named theorem proof `:= by sorry`, with its source and full intended proof in the docstring. There are no other new or remaining textual holes in the delivered modules, and none in definitions.

This is a decomposition, not a completed proof: one baseline hole closed minus one added is net zero. The transition theorem is only the morphism-coherence part of the argument. The numerator isomorphisms, section-power compatibility and the whole coefficient-equation argument are actually constructed/proved. Existing dependencies are unchanged. Axiom inspection shows the three canonical definitions and the section-power theorem use only `propext`, `Classical.choice`, `Quot.sound`; the target and the remaining coherence theorem additionally use `sorryAx` from the new transition-coherence hole.

The worker's unlanded `exists_tensorPowSection_open_restriction_N` and `tensorPowSection_open_restriction_T` are removed, not counted as baseline holes closed. Their two draft holes are replaced by one true, strictly smaller coherence hole.

## No longer needed

No original import was removed. The existing public `ClearDenominators` import is necessary for the original signature; the new comparison and coherence imports are proof-only. No whole module is pruned.

The old parent's direct proof-dependency edges to `def-sc-invertible-module`, `def-sc-open-section-fraction-presentation`, and `lem-pc-sites-sheaf-tensor-bilinear-universal` are no longer used directly and are removed. Tensor-power definitions and the tensor universal property remain available through the canonical-comparison nodes and the existing restriction tensor comparison, so this is edge pruning only. The existing edges to `lem-weil-pbc-module-restriction-tensor-comparison` and `lem-weil-pbc-module-restriction-open-immersion-colimits` are retained: the proof uses the former's pure-tensor characterization and the latter's restriction machinery. New direct dependencies are the canonical construction, section-power comparison, and transition-coherence nodes. The union of each node's proof-step uses is its `proof_deps`.

## Where the brief, the DAG or earlier work was wrong

The first worker's coefficient theorem for an arbitrary compatible additive family N is false. Take X to be the disjoint union of two copies of Spec Q, U the whole space, L=F=O_X and s=0. Identify the degree-one numerator group with Q×Q, and choose N_1 to swap the components; choose identity comparisons in every other degree. All b>0 transitions are zero and b=0 transitions are identities, so the worker's hypothesis hN holds. Let V be the first component, n=1, t=(0,1), and z=0. The ambient equation is true because t restricts to zero on V; the restricted equation is false because N_1(t) restricts to 1. Every additive T sends zero to zero, so no choice of T repairs the assertion. Compatibility with multiplication does not imply compatibility with restriction. The repaired proof uses components of sheaf isomorphisms and their naturality instead.

The worker's new nodes also cited the parent itself as a proof dependency, had no Mathlib searches, used non-self-contained statement summaries as Lean signatures, and did not update the parent proof plan. All of those faults are repaired. The original item's statement is mathematically sound and unchanged.

The local literature directory lacks the cited source texts. Read the official Stacks pages [01CD](https://stacks.math.columbia.edu/tag/01CD), [01PW](https://stacks.math.columbia.edu/tag/01PW), and [09MR](https://stacks.math.columbia.edu/tag/09MR). Tag 01CD supplies functorial tensor pullback; its proof is omitted, so the detailed pure-tensor coherence argument is explicitly attributed to T1. The restriction paragraphs of 01PW and 09MR motivate the comparison, but none of their localization hypotheses is imported into these restriction statements.

## New nodes

`def-sc-tensor-power-open-restriction-comparisons` records the actual canonical tensor comparison, recursive tensor-power comparison and numerator comparison. Its primary Lean signature is verbatim and its other two declarations are listed. The characterization determines the inverse uniquely as a sheaf map and therefore determines the entire isomorphism; powers are constructed recursively, starting with `restrictUnitIso`.

`lem-sc-tensor-power-section-open-restriction-N` now records the proved section-power compatibility theorem, with its complete induction proof and verbatim Lean signature. It has no dependency on the parent theorem.

`lem-sc-tensor-power-section-open-restriction-T` now records only the transition morphism-coherence theorem. Its proof plan uses tensor universal-property uniqueness for naturality and unit/associator coherence, induction for power addition, and the proved section-power compatibility. It has no dependency on the parent theorem.

Searches were actually run via `msearch.py`: LeanSearch was unavailable with HTTP Internal Server Error; Loogle returned algebraic TensorPower map lemmas; Lean Finder returned tensor presheaf definitions; grep found `restrictUnitIso` and its uses. Local searches of `lean/Sheaf`, `lean/WeilConjectures` and Mathlib found the existing restriction tensor comparison and section formulas, but no theorem about these recursive comparisons. Each node records these searches. No change record is needed: all existing signatures and definitions are unchanged.

## Second reading by T1

1. Compared the complete delivered item with the repository version and separately compared the original theorem signature byte for byte: identical, including hypotheses, let expressions, quantifiers, conclusion and visibility. The original docstring is unchanged. New definitions and statements are confined to new modules; no existing definition is altered. Verdict: pass after replacing the worker's reduction.

2. Compiled all three delivered modules in import order with the prescribed `lcompile.py`; no errors or warnings. Inspected all definitions and proofs: no axiom, unsafe, opaque, implemented_by, extern, hidden or definition-level sorry. Scratch-copy `#print axioms` checks on the original theorem, all three new public definitions, the section-power theorem and the remaining coherence theorem show exactly propext, Classical.choice and Quot.sound for the constructions and section-power theorem, with sorryAx additionally present only for the remaining coherence theorem and the target that uses it. Verdict: pass with exactly the named coherence hole still open.

3. Read the old split statements and found the arbitrary-N coefficient assertion false by the two-component, zero-section counterexample above. Replaced it with a canonical sheaf-map coherence assertion and proved the section-power assertion. Checked the remaining coherence assertion at n=0, b=0, s=0, zero modules and the empty open: the recursive unit/tensor construction and structural identities apply in each case. Its statement is strictly part of the proof, with no section-equation or existential additive-equivalence conclusion. The recorded searches and local alternative-name searches reveal no duplicate theorem. The natural-language proof is detailed enough to take over. Verdict: pass after repair; no restatement of the item remains.

4. Used the existing restriction tensor comparison rather than recreating its tensor universal-property construction. The target now proves the section-equation clause directly by naturality/injectivity. The new module imports are necessary and correctly public only when their signatures/definitions require them; the item's imports remain proof-only. The removed old proof-dependency edges are fully listed above. Read `dag/units/sk-thm-curveestimate.json`: its realized statement is `thm-sc-proper-cohomology`, with no realized steps. This item is a lower technical lemma, and neither that realization nor the chapter/unit route is bypassed or changed. Verdict: pass.

5. Replaced both defective draft nodes, added the real construction node, and updated the parent's proof, proof_deps and proof_origin. Each new node has a self-contained statement, source, appropriate proof steps, exact Lean signature, all required search kinds, creation data, chapter/unit and blueprint origin. Every proof_deps is the union of proof-step uses. No new proof or statement edge returns to the parent, so the circular draft dependencies are gone. The parent statement and other protected fields are unchanged. Verdict: pass.

Second-reading changes: replaced the false arbitrary-N split and circular metadata; constructed canonical comparisons; proved section-power compatibility; supplied the direct target naturality/injectivity proof; reduced the two draft holes to one transition-coherence hole; completed source/search records, dependency pruning and honest decomposition accounting.
