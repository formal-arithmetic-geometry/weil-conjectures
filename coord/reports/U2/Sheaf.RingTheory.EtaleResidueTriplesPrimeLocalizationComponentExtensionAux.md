## What changed

Replaced the auxiliary theorem's proof hole by a concrete composition of two strictly
smaller named intermediate results. Added imports of the affine-model and
cocone-factorization modules. The composition destructs the model data and applies the
factorization result, preserving the original statement exactly.

## Proved and sorry left

Proved `AlgebraicGeometry.Scheme.etaleResidueTriples_primeLocalization_component_extension_aux`.
The two new intermediate declarations
`etaleResidueTriples_primeLocalization_component_extension_model` and
`etaleResidueTriples_primeLocalization_component_extension_factorization` remain as
explicit `sorry` statements, each with its own DAG node; they are strictly smaller
parts of the original construction.

## No longer needed

No imports or proof dependencies were removed; both intermediate modules are used by
the proof.

## Where the brief, the DAG or earlier work was wrong

The original plan treated the entire affine descent, localization extension, and
morphism descent argument as one indivisible theorem. It was split into the model and
factorization statements to make the Lean reduction explicit.

## New nodes

`new-lem-sbc-etale-triples-prime-localization-component-extension-aux-model` in
`lean/Sheaf/RingTheory/EtaleResidueTriplesPrimeLocalizationComponentExtensionAuxModel.lean`.

`new-lem-sbc-etale-triples-prime-localization-component-extension-aux-factorization` in
`lean/Sheaf/RingTheory/EtaleResidueTriplesPrimeLocalizationComponentExtensionAuxFactorization.lean`.

## Earlier second reading (a previous round; superseded)

The second reader will check the unchanged target statement, the strictness of the two split statements, and preservation of the unit route.

## Second reading by U2

1. **Unchanged statements.** Compared the delivered auxiliary module with the repository version: the theorem signature is byte-for-byte unchanged; only proof imports and the proof body were added. The two split declarations are new nodes and do not alter an existing target.

2. **Proof validity.** Compiled all three sandbox modules with `lcompile.py --all`; compilation succeeds. The auxiliary theorem has no `sorry`; the only remaining holes are the two explicitly named split theorems, each a public named theorem with a source docstring and matching DAG node. No forbidden declarations or hollow definitions occur.

3. **New statements.** Checked that the model theorem is the first conjunct of the original conclusion and the factorization theorem is the remaining existential conjunct after fixing that model data. Each is strictly smaller, true as the corresponding construction step, and is not duplicated elsewhere in the library.

4. **Pruning and imports.** The two added imports are proof-only imports and are therefore plain `import`. No old import is unused by the delivered proof; no existing proof dependency can be removed. The DAG proof dependencies and declarations match the Lean code.

5. **Unit route.** The proof first invokes the model step and then the factorization step, preserving the `sk-prop-input-spreading` unit route recorded by both new nodes. No unit-level statement is bypassed.

**Changes made:** added this second-reading record only; no Lean statements or proofs were changed during review.
