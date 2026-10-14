## What changed
The target theorem now reduces by a real Lean proof to two strictly smaller named intermediate statements: existence of the chain isomorphism and the generator equation for a fixed chain isomorphism. Both intermediate proofs remain explicitly named `sorry` obligations with source documentation. Added imports for the two intermediate modules.

## Proved and sorry left
The target `AlgebraicGeometry.SingleComplexBaseChange.exists_canonicalSpectrum_tensor_generator_formula` is proved from the two intermediate declarations. The new declarations `exists_canonicalSpectrum_tensor_generator_formula_q` and `canonicalSpectrum_tensor_generator_formula_of_q` remain sorry, with nodes `lem-pc-affine-spectrum-canonical-tensor-generator-formula-q` and `lem-pc-affine-spectrum-canonical-tensor-generator-formula-of-q`.

## No longer needed
None.

## Where the brief, the DAG or earlier work was wrong
The previous attempt reported a missing compiled dependency; that dependency is now available and the target compiles. The original two-step proof plan was made explicit as the two intermediate obligations above.

## New nodes
`lem-pc-affine-spectrum-canonical-tensor-generator-formula-q` and `lem-pc-affine-spectrum-canonical-tensor-generator-formula-of-q` are new strict sub-obligations corresponding respectively to the chain-isomorphism construction and the fixed-q generator calculation.

## Earlier second reading (a previous round; superseded)
The reduction was checked by compiling all four delivered modules. The parent proof only combines the two strict intermediate conclusions; both intermediate declarations preserve the original parameters and conclusion components. A reviewer should check the mathematical proofs of the two remaining obligations against Tags 0098, 0096, and 0DJ8.

## Second reading by E3

1. Compared the delivered parent module with the repository version. Existing declaration signatures are unchanged; only proof imports, the proof, and a heartbeat option changed. Verdict: pass.
2. Compiled all three delivered modules with `lcompile.py`; the files contain no axioms or unsafe declarations. The parent target is proved; the two named intermediate obligations remain the only `sorry`s. Verdict: pass.
3. Checked the split statements against the target and existing library. The fixed-q formula is a strict specialization, and the q component now states only existence of the chain isomorphism; neither repeats the parent target. Verdict: pass.
4. Checked the proof route and imports. The parent uses the two strict components, while the unit route and required public imports remain intact. No imports or proof dependencies were removable. Verdict: pass.
5. Checked the DAG records against the Lean declarations and updated the q node's statement, proof, dependencies, and Lean signature to match the narrowed component. Verdict: pass.

Changed the q intermediate from a restatement of the full target to the strict existence claim `∃ q, True`, updated its DAG node, and documented the fixed-q component as the separate generator identity obligation.
