# Delivery report

Files written:

- `dag/nodes/sec-trace-formula/lem-trf-total-site-free-module-resolution.json` — item, statement split into five proof steps.
- `dag/nodes/sec-trace-formula/lem-trf-total-site-simplex-free-resolution.json` — statement-only child, Mathlib searches found no exact match.
- `citations.json` — verbatim citations for every non-elementary use.

Attachments: none.

WANTED: none.

The read-only source tree has no declaration tagged `(blueprint: lem-trf-total-site-free-module-resolution)` and no matching declaration in the searched WeilConjectures modules. The imported item statement agrees with the source route: Stacks `spaces-simplicial.tex`, Tags 0D72 and 0D7C. I read Tag 0D72's ringed-topos component restriction and direct-sum left-adjoint formula, Tag 0D7C's componentwise free simplex resolution and vertex-zero contraction, and Tag 0D7D's use of the resolution before applying Hom. The chapter is `sec-trace-formula`; the recorded blueprint ancestor is `lem-trf-local-term-locality`, and the item proof realizes its paragraph (2) free-simplex-resolution branch.

## Review by NE

Step 1 checks the coherent transition maps against the identity and composition cocycle laws and uses `lem-pe-constant-left-module-inverse-image` for the constant coefficient comparisons; I opened that node and verified that it states the canonical ring comparison, exact module inverse image, and composition compatibility. Step 2 restricts to a fixed component and identifies the resulting complex with the simplex-indexed direct-sum complex. I created `lem-trf-total-site-simplex-free-resolution` for exactly this smaller component statement, after searching the DAG and blueprint for Tags 0D7C and the relevant keywords. Its statement is self-contained and was tested at `m=0`, `M=0`, and `M` over the zero ring; the contraction gives the expected identity augmentation in each case. The same step uses the exactness clause of the constant inverse-image node, which I checked directly.

Step 3 is an elementary direct-sum universal-property argument from the displayed definition of `P_p(G)`: a compatible map is determined by its identity summand and the cocycle formula gives the inverse. I deliberately kept this inline rather than creating a child that would merely restate one clause of the item. Step 4 is the standard simplicial face identity cancellation and fold augmentation check, again directly from the definitions and the cited Stacks face formula. Step 5 records naturality from the same fixed comparison maps and direct-sum inclusions. I checked that every non-elementary step has a cited node whose statement supplies the used fact, that `proof_deps` is the union of `uses`, and that no new node duplicates an existing DAG statement. Mathlib searches were run with `msearch.py` for the child using LeanFinder, Loogle, and grep; only generic alternating-face and extra-degeneracy APIs appeared, so the child remains unsplit.

No source or statement error was found. No Lean files were written and no compiler or Lake command was run.

## Not duplicates

`lem-trf-total-site-simplex-free-resolution` vs `lem-weil-pbc-cech-nerve-free-homology`: the existing node concerns sheafified Cech nerves of a locally surjective presheaf map, while the new node is the componentwise simplex complex indexed by all maps `[p] → [m]` for a fixed simplex and makes no sheafification or local-surjectivity assertion.
lem-trf-total-site-simplex-free-resolution vs lem-trf-total-site-free-module-resolution: the new node is only the fixed-component simplex-indexed chain complex used inside the item's total-module proof; the existing node asserts the coherent total-module complex and Hom bijection.
lem-trf-total-site-simplex-free-resolution vs def-trf-total-simplicial-etale-site: the new node proves exactness of a module chain complex for each fixed simplex, while the existing node defines the total simplicial etale site and asserts no exactness.
lem-trf-total-site-simplex-free-resolution vs lem-trf-total-site-injective-cech-resolution: the new node is the componentwise free resolution for arbitrary $M$ and does not mention injectives, direct images, or Hom exactness; the existing node is the injective augmented Cech theorem and uses the component resolution as an input.
