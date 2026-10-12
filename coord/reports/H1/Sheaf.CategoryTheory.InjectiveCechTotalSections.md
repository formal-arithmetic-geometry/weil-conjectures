## What changed
Proved `injective_cech_total_sections` from a strictly simpler intermediate row-total comparison and Mathlib's extension homology isomorphism. Added the proof-only import for `ExtendMap`.

## Proved and sorry left
`injective_cech_total_sections` is proved. `injective_cech_total_sections_nat` remains `sorry` as a strictly simpler row augmentation theorem, with node `lem-sc-injective-cech-total-sections-nat`.

## No longer needed
None of the originally listed dependencies was removed; all remain needed by the intermediate row comparison.

## Where the brief, the DAG or earlier work was wrong
The final integer-extension step is already supplied by `mapExtendIso` and `extendHomologyIso`; the DAG plan did not expose this short formal route.

## New nodes
`lem-sc-injective-cech-total-sections-nat`, in `dag/nodes/sec-picard-framework/lem-sc-injective-cech-total-sections-nat.json`.


## Earlier second reading (a previous round; superseded)
The proved target combines the isolated row comparison with standard extension homology isomorphisms; signatures are unchanged.

## Second reading by H1

1. Compared the delivered module with the repository version. Existing theorem signatures are byte-for-byte unchanged; the only added declaration is the explicitly split intermediate theorem.
2. Compiled the delivered module with `lcompile.py`; it succeeds. The target proof has no `sorry`; the remaining `sorry` is only `injective_cech_total_sections_nat`, with a named DAG node and docstring. No forbidden declarations or hollow definitions were added.
3. Checked the split statement against the row-augmentation portion of the blueprint. It is a strictly smaller, true intermediate claim and is required by the target proof; no duplicate library theorem was found.
4. The target proof uses `mapExtendIso` and `extendHomologyIso` for the extension step. The unit route is preserved through the row comparison, and no original dependency import was removed.
5. The DAG node statement and proof dependencies match the Lean declaration and proof route. The unit `sk-thm-picard-cech` remains the realized route.

Changed: added this second-reading record only; no Lean or DAG repairs were needed.
