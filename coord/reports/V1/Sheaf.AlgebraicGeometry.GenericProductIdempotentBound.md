## What changed

Proved `exists_generic_product_idempotent_bound` in
`Sheaf.AlgebraicGeometry.GenericProductIdempotentBound`, without changing its signature,
visibility, or existing docstring. Added a fully proved private helper
`clear_span_denominator`. Updated the item's node proof to match the actual argument.
The second reader removed the redundant added proof import
`Mathlib.LinearAlgebra.Span.Basic`; the existing imports already provide the span API.

The generic pure tensors span the product over K'. Span induction clears denominators
into the R0-span. The product of the finitely many resulting denominators works for all
localizations and all compatible maps. Compatibility places that R0-span in the map's
range, and multiplying by the inverse of the denominator unit lifts each coordinate.

Validation: the full module compiles cleanly through lcompile.py; there is no sorry
in the delivered Lean source. The existing theorem signature was compared verbatim
with the repository's signature. The empty-coordinate case uses the empty product 1;
zero vectors use denominator 1. No finiteness of B or Noetherianity is used.

Searches: Loogle found `IsLocalization.Away.isUnit_of_dvd`; LeanFinder returned
localization base-change lemmas but no exact theorem; msearch grep found constituent
localized-module span lemmas. Searches of Sheaf and WeilConjectures found no shorter
existing theorem usable without a cycle. The proof uses Mathlib only.

## Proved and sorry left

Closed: `exists_generic_product_idempotent_bound`
(node `lem-weil-pbc-generic-product-idempotent-bound`), the sole original hole.
Added holes: none. Remaining holes in delivered modules: none.
The private helper `clear_span_denominator` is fully proved.
This is a complete proof, not a decomposition into new holed statements.

## No longer needed

Original imports removed: none. Removed the first worker's redundant added proof import
`Mathlib.LinearAlgebra.Span.Basic`. Existing public imports are needed by the unchanged
tensor-product, quotient, localization, fraction-ring and nilradical interface.
The node originally had no proof-dependency nodes or Sheaf proof imports to prune.
The proof does not need to construct a canonical localized reduced tensor-product map,
prove that reduction commutes with localization, or prove uniqueness of compatible f.
It instead uses the range of each specified f directly. In particular, it adds no
imports of GenericProductMapDenominators or GenericProductKernelBound. These modules
are not claimed globally redundant: other items still use them.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The DAG's plan is correct, but its localization and
nilradical comparison is unnecessary for this assertion. The direct spanning
argument closes it without any new nodes or unproved dependencies. The unit record
`sk-prop-sf-cbc` has no realized steps to bypass. The literature files cited by the
node are absent from this machine; the argument follows the existing complete
proof text in the node and declaration, preserving its source attribution.


## Second reading by V1

1. PASS: diffed the only delivered Lean module against the repository version.
   The existing theorem signature is byte-for-byte identical (also checked by a
   direct string comparison), and its visibility and docstring are unchanged.
   No existing definitions changed; no change records or adapted modules are needed.
2. PASS: compiled the module locally with lcompile.py without errors or warnings.
   A scratch copy with explicit `#print axioms` for both the public theorem and
   private `clear_span_denominator` reports exactly `propext`, `Classical.choice`,
   and `Quot.sound`. No sorry or forbidden declarations occur in the delivery.
   All selected data come from proved span membership, quotient surjectivity,
   fraction representations or unit membership, never an unproved existence theorem.
3. PASS: no statements were split off and no holes were added. Read the fully proved
   private helper: generators and zero use 1, sums use the product of denominators,
   and scalar multiplication uses a genuine fraction representation. Empty S and
   z=0 work with 1; arbitrary additive modules require no finite generation.
   The coordinate argument covers r=0 with product 1 and r=1 without extra hypotheses.
4. PASS: followed the proof from the target through tensor induction, denominator
   clearing, and inclusion of the R0-span in each compatible map's range. No
   localization/reduction comparison or canonical-map uniqueness is needed.
   Independent Loogle search `Submodule.span, IsFractionRing` and rg searches for
   denominator/span and scalar/span membership found no shorter applicable theorem
   in Mathlib or the two library roots. There were no old proof_deps to prune.
   The unit sk-prop-sf-cbc has empty realized statement/steps; its route is preserved.
   Removed the redundant added Span.Basic import after the entire proof compiled
   without it; every remaining public import supports the existing signature.
5. PASS: compared the delivered node JSON with its original. Only proof and
   proof_origin changed; proof_deps remains empty and agrees with the Mathlib-only
   proof. Each of the four proof steps matches the corresponding Lean argument.
   The statement, lean statement record, source, unit and chapter are unchanged.
   No new nodes require review.

Changes by the second reader: removed the redundant added proof import
`Mathlib.LinearAlgebra.Span.Basic`, corrected the import descriptions above, and
recorded this independent reading. No proof repair was necessary. Closed one original
hole (`exists_generic_product_idempotent_bound`), added none, left none.
