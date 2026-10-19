# Stage-1 report: lem-zl-geometric-irreducibility-separable

## Files written

- `dag/nodes/sec-deligne-laumon-general/lem-zl-geometric-irreducibility-separable.json`: split statement, six proof steps, and Tag 0G33 provenance.
- `dag/nodes/sec-deligne-laumon-general/lem-zl-field-extension-algebraically-closed-geometric.json`: statement-only unsplit node; no Mathlib match.
- `dag/nodes/sec-deligne-laumon-general/lem-zl-geometric-irreducibility-transitive.json`: statement-only unsplit node; no Mathlib match.
- `citations.json`: verbatim statement quotes for all cited nodes and steps.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and `/home/ubuntu/weil-newtargets-master/WeilConjectures` for the item id, its blueprint tag, and the geometric-irreducibility/separable terminology; no sorry-free project declaration states this item.

## WANTED

None. The Stacks sources needed for the split are present locally.

## Not duplicates

- `lem-zl-field-extension-algebraically-closed-geometric` vs `lem-zl-geometric-irreducibility-subextension`: the existing node passes geometric irreducibility from a field extension to an intermediate subfield, whereas the new node assumes the base is algebraically closed in the top field and concludes geometric irreducibility.
- `lem-zl-field-extension-algebraically-closed-geometric` vs `lem-weil-pbc-separable-first-purely-inseparable`: the existing node decomposes an algebraic extension into its separable part followed by a purely inseparable part, whereas the new node proves geometric irreducibility from algebraic closure in the top field.
- `lem-zl-geometric-irreducibility-transitive` vs `lem-zl-geometric-irreducibility-transcendental`: the existing node concerns adjoining algebraically independent variables, whereas the new node is transitivity for an arbitrary field tower.
- `lem-zl-field-extension-algebraically-closed-geometric` vs `lem-pur-power-generated-spectrum-homeomorphism`: the existing node gives universal homeomorphisms for p-power-generated ring maps, whereas the new node is the field-extension criterion from Tag 037P.

## What was wrong or changed

The imported item had an empty proof and no proof dependencies. I retained its Tag 0G33 statement and definitions, then supplied the complete two-direction proof. In the converse direction I corrected the field-theoretic wording: the subfield `k'` of elements algebraic over `k` is algebraically closed in `K` by transitivity of algebraicity, which is the hypothesis needed for the 037P criterion; it is not `k` that is algebraically closed in `k'`. The two new lemmas are strictly smaller inputs used by the argument, rather than restatements of the item. The separable-first decomposition and the universal-homeomorphism specialization are reused from existing nodes; no duplicate nodes were created. The finite-separable tensor decomposition is reused from the existing Picard node.

## What I could not finish

No Lean code or compiler was used, as required for stage 1. The four new nodes remain unsplit statement-only queue entries.

## Review by N5

I read the item and the parent route in `dag/nodes/sec-deligne-laumon-general/lem-zl-bertini-field-extension.json`, the chapter and unit records, and the complete Stacks proof of Tag 0G33 in `literature/stacks-project/algebra.tex`. I also read the exact statements of every cited existing node: `lem-zl-geometric-irreducibility-subalgebra-colimit` supplies geometric irreducibility for the injective subalgebra `k(α)`, and `lem-pc-separable-tensor-algebraic-closure` supplies the product decomposition of a finite separable tensor product over an algebraic closure. The new node statements were checked against Tags 037P and 0G30; the reused nodes were checked against Tags 030K and 0BRA.

Step 1 verifies that `k(α)` is a finite separable intermediate field and uses only the subalgebra clause of the cited node. Step 2 uses the cited product decomposition with the correct finite separable hypothesis; an irreducible spectrum cannot be a product with two nonempty factors, so the degree is one and `α∈k`. In the converse, Step 3 defines `k'` as all elements algebraic over `k` and checks that an element algebraic over `k'` is algebraic over `k`, hence lies in `k'`; this verifies the exact hypothesis of the 037P node for `K/k'`. Step 4 checks the hypothesis of the new purely-inseparable characterization for `k'/k`, using the item assumption. Step 5 applies the purely-inseparable geometric-irreducibility node, and Step 6 applies the transitivity node to `k⊂k'⊂K`. I checked the edge cases `K=k`, purely inseparable nontrivial extensions, and finite separable extensions: the criterion gives the expected answers. All proof-step citations have verbatim quotes in `citations.json`; Mathlib searches were run with `msearch.py` for the item and each new node using LeanFinder, Loogle, grep, and LeanSearch, with unavailable/no-match results recorded where appropriate.
