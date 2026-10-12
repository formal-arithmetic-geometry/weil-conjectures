## What changed

Added two intermediate public theorems, each in its own module, for the split-biproduct filtration construction and the successor finite-sum comparison. The target theorem now combines these with finite pushforward coherence; all three modules compile in sandbox import order.

## Proved and sorry left

The target theorem `AlgebraicGeometry.Scheme.Modules.coherentIntegralFiltration_ideal_sum_succ` is reduced to two strictly simpler named intermediate theorems. The intermediate declarations `hasCoherentIntegralFiltration_of_biproduct` and `pushforward_fin_sum_succ_iso` remain as named `sorry` holes, with corresponding DAG nodes.

## No longer needed

No imports were removed beyond the original proof dependencies; the target uses finite pushforward coherence and both new helper modules. No existing proof dependency node is pruned.

## Where the brief, the DAG or earlier work was wrong

The original DAG plan omitted the categorical split-biproduct construction and the finite-sum comparison as explicit Lean interfaces. These are now stated as strictly smaller intermediate results.

## New nodes

`new-coherent-integral-filtration-biproduct-succ` and `new-pushforward-fin-sum-succ-iso` are added under `dag/nodes/sec-proper-base-change/`, with modules in the sandbox's `lean/Sheaf/AlgebraicGeometry/` directory.

## Earlier second reading (a previous round; superseded)

The target proof uses only the two new helper statements and finite pushforward coherence. Both helpers are strictly simpler than the target and match the construction in Tag 01YF; their remaining holes are explicit and named.

## Second reading by P4

1. I compared the delivered target module with the repository version. The existing target
signature is byte-for-byte unchanged; only its proof and proof-only imports were extended to
use the two explicitly stated intermediate results. The two added modules are new files, and
their declarations match their DAG `lean.statement` records.

2. I compiled all three delivered modules with `lcompile.py --all`; compilation succeeds with
no errors or warnings. The target theorem has no `sorry`. The only remaining holes are the two
named intermediate theorems, each recorded by a corresponding split node. No forbidden
`axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by` declaration was introduced.

3. I checked the split statements against the definitions they use. The biproduct extension
statement is strictly more general in its input filtration and isolates the categorical
extension step. The finite-sum statement isolates only the successor comparison. Both are true
for `r = 0` as well as positive `r`, and neither merely renames the target theorem.

4. I checked the proof route and imports. The target applies finite pushforward coherence,
obtains the required integral-ideal witness directly from `(Z, i, I)`, uses the successor
finite-sum comparison, and then applies the split-biproduct extension. This preserves the
unit's split-sum successor route; no prior proof dependency was removed or bypassed.

5. I checked all three DAG records against the Lean declarations, including module names,
statements, proof dependencies, source locations, chapter, and unit. The target node records
the two helper uses and finite pushforward coherence; each helper node records its own
strictly smaller interface and remaining proof hole.

No code changes were needed after this reading; I added this review record and retained the
explicitly named helper holes and their nodes.
