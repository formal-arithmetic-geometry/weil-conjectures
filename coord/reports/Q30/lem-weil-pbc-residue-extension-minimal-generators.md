## Worker report

Files written:

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-residue-extension-minimal-generators.json`: existing statement, now split in five steps. The statement is retained, with its finite-dimensionality and dimension definitions added to `stmt_deps`.
- `citations.json`: one verbatim statement quotation for each step/node citation.
- `report.md`: this report. `searches.jsonl` is the actual search-command log; `write_split.py` is sandbox-only drafting material.

New nodes: none. New Mathlib leaves: none. Existing Mathlib leaves reused: local Nakayama generators, quotient tensors, the tensor universal property, finite-dimensionality, and dimension.

Attachments: none. Searching `lean/WeilConjectures/` for the exact blueprint tag and residue-basis/minimal-generator notions found specialized results (regular local ideals and differential bases), not a declaration proving the entire present statement. In particular regular-local-ring minimal generators are not the arbitrary finite-module statement.

WANTED: none.

The original item had a complete statement but no proof or proof dependencies. Its original Mathlib searches correctly identified constituent facts rather than a single theorem giving every clause. I retained those searches and ran further LeanFinder (two phrasings for the whole statement and one finite-spanning question), LeanSearch, Loogle, and source grep through msearch.py. Actual hits and verdicts are appended. I read LocalRing/Module.lean:65–106, SpanRankOperations.lean:58–70 and Dimension/Constructions.lean:379: Nakayama lifting, span-rank comparison, and base-change dimension are components, not an exact attachment or one-line specialization for the whole item.

Whole-DAG searches for Nakayama/lemma-NAK/00DV, scalar-extension bases and dimensions, quotient tensors and basis/finite-spanning notions located the existing nodes. Whole-blueprint searches for `residue field generators`, `Nakayama`, `basis`, `finite spanning`, `generators`, `minimal generators`, and `residue extension` found no blueprint duplicate of this item. `blueprint_refs.py ancestor` returned thm-weil-pbc-finite-etale-lifting. I read its current latest blueprint statement and proof, the chapter and sk-thm-p1 unit. The existing ancestry passes through the essential-surjectivity branch of split step 7 to lci-field-change; the split realizes exactly that branch's residue-dimension/Nakayama subargument. It changes no unit or chapter route.

What was wrong: missing proof and missing definition dependencies for finite-dimensionality and dimension. No statement dispute, dropped case or altered hypothesis was needed. Nothing remains unfinished in this split.

## Not duplicates

No new nodes were created. I reused lem-weil-pbc-nakayama-local-generators and lem-weil-pbc-tensor-over-quotient-ring rather than introducing nodes with their Stacks tags. The existing lem-pc-finrank-field-base-change supplies only the numerical dimension equality; I instead wrote the basis-coordinate calculation required by the stronger explicit-basis clause directly in the item's proof. This is a clause of the item and was not moved to a new node.

## Review by Q30

I read Stacks algebra.tex, Tag 00SI (`lemma-lci-field-change-local`), especially its displayed fibre tensor calculation and concluding equality of residue dimensions followed by Nakayama. I also read Tag 00SJ (`lemma-lci-field-change`), its alternate proof's locally free conormal and generator count, and Tag 00DV (`lemma-NAK`), parts (4), (6), and (8). Tags were checked in tags/tags. This item is the abstract finite-module linear-algebra argument used there. Its assumptions are only a commutative local ring, a finite module, and an arbitrary field homomorphism from the residue field. The proof does not require that A be Noetherian, that M be free, that L/F be finite, or any flatness hypothesis on M.

Step 1 uses exactly the statements of def-weil-finite-dimensional-subspace (a finite spanning family) and def-weil-vector-space-dimension (basis cardinality and independence of basis). I opened both nodes. Reduction of coefficients gives the finite spanning family. Rather than invoking an unquoted exchange theorem, the step explicitly removes one dependent vector using a nonzero coefficient and terminates because the finite list shortens. The same argument gives the bound for every spanning list. These are routine elementary operations, not a hidden independent lemma. Empty lists are treated explicitly.

Step 2 uses the statement of lem-weil-pbc-nakayama-local-generators: a family generates M iff its residue images span. I opened it and checked that it says this for arbitrary local A and finite M; it is not merely the definition of Nakayama or a statement about ideals. The residue quotient is surjective, so every prescribed basis can be lifted. Nakayama's hypotheses are precisely those of the item; all choices of lifts work, including the empty family.

Step 3 uses the dimension definition and the preceding proved steps. Images of any generating family span, so the bound from step 1 gives minimality. The converse is made explicit by padding the lifted d-element family with zeros to get exactly r indices. No assumption that generators are distinct is introduced. This also proves the sharp lower bound and the d=r=0 case.

Step 4 uses the actual tensor-product definition node, including the universal property and generation by pure tensors, together with the two dimension definitions already read. For a prescribed basis, the displayed expansion proves spanning after extension. The coordinate maps are balanced over F and are L-linear by their formula on pure tensors; evaluation gives the individual coefficients of any relation. This proves the exact basis assertion, not only equality of dimensions. The empty-basis expansion gives W=0. I kept this explicit proof of the item's own clause instead of introducing a node restating it. No general flatness or faithful-flatness theorem is used. The calculations work for inseparable and infinite extensions as well as F=L.

Step 5 uses both numbered clauses in the statement of lem-weil-pbc-tensor-over-quotient-ring, which I opened: quotient tensor is M/JM and further tensoring with an R/J-module may be taken over the quotient. I read its source places, 00DF (`lemma-tensor-product-exact`) and 00D2 (`lemma-tensor-with-bimodule`), and checked J=m and that L is an A/m-module via the given map. The existing statement is phrased with the scalar factor on the left; the proof writes the tensor swap, formulas and inverses explicitly using the tensor universal property, and checks lift independence and scalar linearity. Thus it gives the F- and L-linear identifications actually needed, not just an unspecified A-linear isomorphism. The displayed images of each lifted generator verify the basis correspondence.

I reviewed delivery-errors B through E against the node and these source/node statements. B: no new nodes, no missing standalone objects, no hollow data or source-dependent meaning; TeX is serialized once. C: every used non-elementary result has a cited node, and citations.json copies its statement verbatim; no node proof is used as an interface. D: the five steps contain the basis extraction, Nakayama application, exact generator count, extended-basis calculation, and fibre maps; nothing is relabelled as a fresh lemma. E: finiteness is checked where Nakayama is applied, the quotient is M/mM rather than an ideal quotient, and all scalar maps factor through the specified residue field.

Small cases checked: M=0 and r=0; nonzero M with r=0 (Nakayama excludes V=0); A itself a field; a finite torsion module over a nonfield local ring; identity field extension; arbitrary infinite and inseparable residue extensions; padding from d to r>d. These tests require no change to the statement. There are no proof steps exceeding 2000 characters (the longest is under 900). I corrected the initially absent definition dependencies and made all inverse maps and zero padding explicit. No other worker or second reader was used, as required by the direct-delivery brief.
