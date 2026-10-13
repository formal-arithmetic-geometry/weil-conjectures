## What changed

Replaced the target theorem's proof with a concrete combination of two strictly smaller
interfaces: finite-presentation descent supplies the triple and structure equation, and
a separate compatibility statement supplies the pointing equation.

## Proved and sorry left

The target declaration `etaleResidueTriples_primeLocalization_component_extension_model`
is proved. The new declarations
`etaleResidueTriples_primeLocalization_component_extension_model_structure` and
`etaleResidueTriples_primeLocalization_component_extension_model_pointing` remain sorry,
as their proofs are the two independent descent steps.

## No longer needed

No imports or existing DAG nodes were pruned; the target's original public imports remain.

## Where the brief, the DAG or earlier work was wrong

The original node presented the full affine descent argument as one elementary step.
The proof requires two independent interfaces, so the step was split into structure
 descent and pointing compatibility.

## New nodes

- `new-lem-sbc-etale-triples-prime-localization-component-extension-aux-model-structure`
- `new-lem-sbc-etale-triples-prime-localization-component-extension-aux-model-pointing`

## Earlier second reading (a previous round; superseded)

The target compiles from the two strict substatements in the sandbox; signatures are unchanged.

## Second reading by G3

1. The target theorem's signature is byte for byte unchanged from the repository; the proof combines the two imported interfaces and compiles.

2. The target proof is valid Lean with no new axioms or forbidden declarations. The two split declarations are explicit named theorems with documented sources and nodes; their proofs remain the only listed sorry holes.

3. The split statements are true interfaces strictly simpler than the target: the structure theorem supplies only the existential and α equation, while the pointing theorem supplies only the final equality under those data. No duplicate full-target statement remains in their node descriptions.

4. The proof follows the shortest available route through the two stated descent interfaces. No imports or proof dependencies were pruned.

5. The DAG proof and proof_deps now match the actual theorem applications, and the unit `sk-prop-input-spreading` route remains represented by the target and its two substeps.

Changed: corrected the three DAG records to match the Lean declarations and target proof, and added this second-reading record.
