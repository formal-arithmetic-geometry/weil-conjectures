## What changed

Replaced the whole proof hole of `exists_generic_product_localization` with a reduction
combining the generic map, uniform torsion-kernel bound, and uniform coordinate-idempotent
bound. The existing signature, visibility, docstring, definitions, and public imports are
unchanged. The three new helper modules are plain proof imports. The localization element
is the product of the two bounds; compatible factor algebras are constructed by composition
through K'. No data definition chooses an arbitrary witness from an unproved theorem.

## Proved and sorry left

This is a decomposition, not an unconditional proof. One upper hole is closed:
`exists_generic_product_localization` (lem-weil-pbc-generic-product-localization).
Three lower holes are added and remain, each as the whole proof of a public named theorem:

- `exists_generic_product_map_denominators`
  (lem-weil-pbc-generic-product-map-denominators): construct the compatible reduced map
  and clear a denominator for each coordinate element; no injectivity or uniform bound.
- `exists_generic_product_kernel_bound`
  (lem-weil-pbc-generic-product-kernel-bound): uniform injectivity for a given compatible
  map; neither existence of the map nor lifting of coordinate idempotents.
- `exists_generic_product_idempotent_bound`
  (lem-weil-pbc-generic-product-idempotent-bound): uniform coordinate-vector lifting for
  a given compatible map; neither map existence nor injectivity.

Thus 0 of 1 original declarations is proved without sorryAx; 1 upper hole is replaced
by 3 strictly smaller holes. The delivery's syntactic hole balance is -2, not proof
progress. The maintainer's pinned sorry ledger determines closure and pruning figures.

## No longer needed

The original node's proof_deps was empty: no old proof-dependency node is omitted.
No original module import is removed, and no library module becomes unreachable.
Removed unused imports from the new helper modules:

- GenericProductMapDenominators: Mathlib.RingTheory.Finiteness.Defs,
  Mathlib.RingTheory.Noetherian.Defs, Mathlib.RingTheory.Localization.Away.Basic.
- GenericProductIdempotentBound: Mathlib.RingTheory.Finiteness.Defs,
  Mathlib.RingTheory.Noetherian.Defs.

These are trims in new modules, not pruning of existing library modules.

## Where the brief, the DAG or earlier work was wrong

The old item node had no declared intermediate proof dependencies. The first worker's
helper nodes had placeholder mathematical statements and nonspecific proof text, and
recorded searches not supported by searches.jsonl. These records are replaced with
self-contained statements, the actual proof sketches, verbatim Lean signatures, and
real search results. Blueprint ancestry now follows the original item's recorded
ancestor through SpreadGenericProductEmbedding and GenericProductLocalization.
The report previously called the target theorem proved without explaining the three
new holes; this is corrected to decomposition. Unowned fields of the original node
are restored to the repository's values.

## New nodes

`lem-weil-pbc-generic-product-map-denominators` is stated in
GenericProductMapDenominators.lean. Its canonical map is induced by tensor base change,
reduction and e; representing the inverse image of a supported coordinate vector as a
finite tensor sum supplies the nonzero denominator.

`lem-weil-pbc-generic-product-kernel-bound` is stated in GenericProductKernelBound.lean.
The finite reduced R0-algebra has finitely generated generic torsion kernel; multiplying
annihilators of generators kills it uniformly on all further principal localizations.

`lem-weil-pbc-generic-product-idempotent-bound` is stated in
GenericProductIdempotentBound.lean. Multiply denominators for the finite coordinate
vectors; these denominators are units whenever the product divides s. Compatibility
on b tensor 1 and R-linearity uniquely determine the map used in the argument.

No existing statement or definition changes, and no change record is needed.

## Second reading by A3

1. Compared the delivered item with its repository version using diff. The only changes
   are three plain proof imports and the proof body: the existing theorem signature is
   byte for byte identical. No other existing Lean module is delivered. Verdict: pass.
2. Compiled all four files in import order with lcompile.py, without errors or warnings.
   Inspected all declarations and searched for forbidden constructs: exactly the three
   listed helper theorems have whole-proof sorry; there are no definitions or extra
   axioms. A scratch copy printed axioms of all four declarations: propext,
   Classical.choice, Quot.sound and sorryAx only. The upper theorem therefore remains
   conditional on its three open components. Verdict: pass as a decomposition.
3. Read each helper signature and full docstring proof. The map lemma omits finiteness
   and Noetherianity but only constructs a map and individual denominators; the kernel
   lemma retains both hypotheses and gives only injectivity; the idempotent lemma
   needs only finitely many coordinates. Tested the empty product r=0, zero coordinate
   z=0, zero algebra B, and the case B=A with one split field. Empty coordinate claims
   are vacuous; when the generic product vanishes, finiteness and Noetherianity kill
   all of C by one nonzero annihilator. Empty denominator products are 1. The domain
   and fraction-ring hypotheses prevent a zero denominator. None of the components
   restates the full item. Searched Mathlib by alternative wording with LeanFinder,
   Loogle and grep, and attempted LeanSearch (HTTP Internal Server Error, recorded as
   unavailable). IsLocalizedModule.surj and tensorProduct_isLocalizedModule provide
   constituent fraction facts, not the complete reduced tensor-algebra assertions.
   Searched lean/Sheaf and the upstream sources; the generic embedding and domain
   lemmas depend on this item, while upstream torsion'_eq_ker and generic freeness
   provide components rather than an exact replacement. No helper can be closed by
   a short direct application of those declarations. Verdict: mathematical pass;
   three formal proof obligations remain open.
4. Followed the upper proof from the fixed splitting to the two bounds, their product,
   the constructed factor algebras, the compatible map, and its three conclusions.
   No prior proof dependency is bypassed. Read dag/units/sk-prop-sf-cbc.json: realized
   is currently {statement: [], steps: []}; the delivery does not change it or replace
   the compact-support base-change unit route. All three proof imports are used.
   Trimmed unused imports in the two new modules and recompiled. Verdict: pass.
5. Compared node proof_deps with the actual three theorem applications: they agree.
   The new nodes now contain their individual hypotheses and conclusions, complete
   proof sketches, real search records, status split, created metadata, chapter/unit,
   blueprint ancestry and exact multiline Lean statements. The existing node changes
   only stage-3-owned fields. Verdict: pass after metadata repairs.

Second reading changed the report's accounting, new-node statements/proofs/searches/
ancestry/signature records, restored unowned original-node fields, and removed five
unused helper imports. The correct upper Lean proof was retained.
