## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-product-regular-sequence.json`: existing item split into four proof steps; status `split`.
- `dag/nodes/sec-smooth-purity/lem-pur-field-vector-space-tensor-nontrivial.json`: new statement-only Mathlib leaf, status `mathlib`, matching `Module.FaithfullyFlat.lTensor_nontrivial` in `Mathlib/RingTheory/Flat/FaithfullyFlat/Basic.lean:114` after the field vector-space specialization.
- `citations.json`: verbatim statement excerpts for every step/node citation.

## Attachments

None. I searched the project declarations in `WeilConjectures/` and found no sorry-free declaration tagged `(blueprint: lem-pur-product-regular-sequence)` or stating this tensor-product result.

## WANTED

None. The blueprint proof route and the existing algebra nodes suffice; the only newly isolated fact is supplied by Mathlib.

## Issues

The imported item was unsplit and its proof dependency list was empty, although Step 5b of `sk-thm-regular` uses the concatenation, quotient, and localization assertions. I kept the statement unchanged and made the missing argument explicit. The statement-only leaf is not a clause of the item: it is the independent nonzeroness theorem for arbitrary nonzero vector spaces over a field. I searched the whole DAG and blueprint for tensor-nonzeroness and found no node with that statement; the nearest existing field-extension tensor node is narrower.

## Not duplicates

- `lem-pur-field-vector-space-tensor-nontrivial` vs `lem-weil-common-extension-fields-tensor-nontrivial`: the new leaf covers arbitrary nonzero vector spaces over a field, while the existing node concerns tensor products of nonzero finite field extensions and does not state the general module result.

## What remains

None for this one-level stage-1 split. No Lean file was written and no compiler, Lake, or build command was run.

## Review by Q91

I read the item, the `sk-thm-regular` chapter/unit records, and the current blueprint proof at `literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-thm-regular/sk-thm-regular.proof.md`, especially Step 5b. I also checked the imported Stacks reference Tag 065K and the Mathlib source for `Module.FaithfullyFlat.lTensor_nontrivial`. The item has no matching declaration in either `WeilConjectures/` source checkout, so it requires a split.

Step 1 uses the regular-sequence definition for injectivity of multiplication by each next `f_i`, the tensor quotient/base-change statement for the prefix quotient, flatness of `S` as a `k`-vector space, and flat-tensor exactness. I opened each cited node and copied the exact sentence used into `citations.json`; these statements together identify the tensored injection with multiplication by `f_i⊗1`. Step 2 repeats the same check after quotienting by all `f`, with `R/(f)` flat over `k`, and uses tensor symmetry plus the same quotient/base-change statement to identify multiplication by `1⊗g_j`. The hypotheses are the given regularity of `f` and `g`, so the short exact sequences used in both blocks have the required injective middle maps.

Step 3 uses the quotient/base-change node twice to obtain the displayed map `a⊗b↦ā⊗b̄`. It uses the final nonzero-quotient clause of the regular-sequence definition for both factors and the new Mathlib leaf for nonzeroness of their tensor product; the first two steps then supply all injectivity clauses. I checked `r=0`, `s=0`, and both empty cases: the relevant injection list is vacuous and the quotient is still a tensor product of the nonzero surviving factors. Step 4 applies the existing localization-prime node with `A=T`, the chosen prime, and the full concatenated tuple. Its hypotheses match exactly: every entry lies in the prime and the prefix multiplication maps are injective from Steps 1–2, so it yields regularity of the localized tuple of length `r+s`.

All proof steps are short routine arguments (the longest is under 700 characters), and `proof_deps` is exactly the union of `uses`. I declared the quotient/base-change, vector-space flatness, flat-tensor exactness, and prime-localization results as generic off-unit tools in `split_report.tool_uses`; the new Mathlib leaf is in this unit. The server `check_dag` check passed after adding the required chapter/unit fields to the new node. The Mathlib queries and their raw outcomes remain in `searches.jsonl`; the four required search kinds for the new leaf were run with `msearch.py` and recorded in its node.
