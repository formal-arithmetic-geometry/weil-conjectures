## What changed

Proved `AlgebraicGeometry.Scheme.singletonTensorDegreeComparisonHom_pure_image`
in `Sheaf.AlgebraicGeometry.EtaleSingletonTensorPureImage`, preserving its signature
and imports. The proof explicitly transports the finite scheme product's HasLimit
witness with `Subsingleton.elim`, `congrArg`, and `Eq.mp`, then uses the normalization
hypothesis. This follows the existing witness-transport implementation in
`EtaleSingletonTensorNormalizationEvaluation` without importing that module.
The auxiliary-declaration linter is locally disabled because the normalization
module's generated product-instance witnesses are used explicitly.

## Proved and sorry left

Closed the sole hole:
`AlgebraicGeometry.Scheme.singletonTensorDegreeComparisonHom_pure_image`
(node `new-etale-singleton-tensor-pure-image`). No holes remain in the item,
and no holes were added or split off. The proof only uses the given normalization
hypothesis and proof irrelevance; it introduces no existence-based data construction.
The calculation applies unchanged at n=0, to zero coefficients/functions, and to
empty schemes.

## No longer needed

None. The only import supplies the statement's definitions and its normalization
predicate. The original single proof dependency is still needed; the DAG route is
unchanged. No extra import of `EtaleSingletonTensorNormalizationEvaluation` is needed.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The DAG correctly identifies proof irrelevance as the
required transport. Plain definitional simplification is insufficient across module
boundaries because the selected limit cone is not exposed; explicit transport of
its HasLimit witness resolves this. The unit record has no realized nodes bypassed
by this proof.

## Second reading by Q3

1. Compared the delivered module with the repository using diff and a byte comparison
   of the complete theorem signature. Verdict: identical signature, visibility,
   docstrings and imports; only its proof and a theorem-local linter option changed.
   There are no delivered definitions, new modules or change records.
2. Compiled the file through lcompile.py without errors or warnings. A separate
   scratch copy with `#print axioms` reports exactly `propext`, `Classical.choice`
   and `Quot.sound`. Verdict: a kernel-checked proof, with no sorry or forbidden
   declaration. The metaprogram constructs congrArg and Eq.mp over an equality
   supplied by Subsingleton.elim; it does not bypass kernel checking or choose data.
3. No statements were split off and no holes were added. Verdict: no lower statement
   or associated new node needs review. Checked the normalization predicate against
   the conclusion: n=0 still has one factor, and zero inputs and empty schemes
   require no exceptional assumption.
4. Read the imported normalization definitions and the existing normalization
   evaluation proof; searched the singleton tensor modules for the same formula.
   The existing evaluation theorem only gives an unspecified existential map.
   Verdict: the direct use of hf after witness transport is appropriate; importing
   that theorem would not identify the prescribed q. The sole public import supplies
   the signature and must stay. No old proof dependency is pruned. Read sk-prop-h2:
   its realized statement and step lists are empty; this local calculation changes
   none of its route or uses.
5. Read new-etale-singleton-tensor-pure-image and its normalization dependency node.
   Verdict: proof, proof_deps and proof_origin describe the delivered proof exactly;
   no node edits are necessary. The scheme product witness is explicitly transported,
   the outer product witness is supplied locally, and hf gives the final equation.

Second reading changed only this report. The Lean proof is correct as submitted.
