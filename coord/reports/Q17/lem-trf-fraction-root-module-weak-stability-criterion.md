## Worker report

Files written:

- `dag/nodes/sec-trace-formula/lem-trf-fraction-root-module-weak-stability-criterion.json`: item split into five steps; statement unchanged.
- `dag/nodes/sec-trace-formula/lem-trf-frobenius-root-coordinate-test.json`: one new statement-only node, unsplit; no Mathlib match.
- `citations.json`: the one proof-step citation, with a verbatim quotation of the new node's conclusion.

Attachments: none. Searches in `lean/WeilConjectures/` for the item tag, fraction roots, weak stability, weak cartesianness, bounded separation, and Frobenius/spectral combinations found no declaration stating this criterion. The finite-fraction-root-substitution declaration concerns algebraic substitution, not bounded linear forms or norm topology.

WANTED: Bosch–Güntzer–Remmert, *Non-Archimedean Analysis*, local archival PDF `literature/bosch-guentzer-remmert-nonarchimedean-analysis.pdf`, sections 2.3.3 and 3.5.2–3.5.3, for both the item and `lem-trf-frobenius-root-coordinate-test`.

The local PDF is absent. I did not download it. The primary PDF's indexed online text was accessible through web search at https://math.arizona.edu/~cais/scans/BGR-Non_Archimedean_Analysis.pdf; I read the extracted text of printed pp.154–155 (Theorem 3.5.3/1, the denominator calculation immediately after its proof, and Lemma 3.5.3/2). Opening the complete PDF in the web reader failed because it exceeded that reader's size limit. Thus I do not claim to have inspected the full local book or section 2.3.3. The item's explicit localization and matrix argument is recorded as agent-written. The new node's exact source is Theorem 3.5.3/1, printed p.154, not the whole ring criterion of Lemma 3.5.3/2.

The imported source locator attributed bounded separation to 3.5.2/1, which defines weak stability. I corrected the locator to distinguish that definition from the module argument preceding Lemma 3.5.3/2. No hypothesis or conclusion of the item changed. No statement dispute was found. No Lean was written and no compiler, Lake, or build tool was run.

The new node is a proper input, not the item restated: it has no ring A, root ring, finitely generated modules, or bounded module functionals. The argument converting those hypotheses into its finite-subspace hypothesis is carried by item steps 1–4. Its later split can address the root-field tower and perfect-closure argument in BGR Theorem 3.5.3/1. No proof sketch was put in the new node's statement or proof fields.

## Searches and route

Before creating the new node I searched all DAG files for weak cartesianness, weak stability, bounded separation, Frobenius roots and the source place 3.5.3/1, and inspected the statement/source fields of candidates rather than treating incidental matches in search records as duplicates. Whole-blueprint searches used `tools/blueprint_refs.py search` with `weak stability`, `bounded linear`, `root`, `3.5.2`, `weakly cartesian`, `Frobenius root`, and `3.5.3/1`. The broad root search produced 69 unrelated root-of-unity, Kummer, and polynomial nodes; the numerical 3.5.2 search gave unrelated nodes. No node states the Frobenius-root coordinate test. `ancestor` identifies `lem-trf-local-term-locality`.

The current latest blueprint's `lem-trf-local-term-locality.md`, its proof, and the unit `_section.md` concern contracting correspondences and zero stalks. They no longer contain an analytic proof at this place. I retained the item's inherited historical analytic chain, including its exact `from.place` and `via`, and extended that chain for the new node. This split changes neither a chapter nor a unit and does not substitute an analytic proof for the current contracting-correspondence argument.

The item retains every inherited search record. All additional searches were run through the required `msearch.py Q17 <item> ...` command and are retained verbatim in `searches.jsonl`. The new node has two LeanFinder phrasings (root-coordinate topology and separable completion), LeanSearch, Loogle and source grep; the item has its own bounded-module phrasing in LeanFinder and LeanSearch, Loogle and source grep. Every service returned an answer; none was represented as unavailable or falsely represented as a search I did not run.

I read the hits. `spectralAlgNorm` gives algebra-norm axioms, not the lower coordinate estimate. `spectralNorm.completeSpace` and the normed-field topology constructions are under a complete-base assumption; I read the relevant source around `spectralAlgNorm` and `completeSpace`. Completeness is explicitly unavailable here. The other hits were invariant norm constructions, tilts, valuation wrappers, and generic bounded linear-map declarations. The grep hits for separable completion referred to topological separability and measures, not separability of a field extension. No hit states the new node or the item, nor specializes to either in one line.

## Not duplicates

- `lem-trf-frobenius-root-coordinate-test` vs `lem-trf-fraction-root-module-weak-stability-criterion`: the former assumes finite-subspace norm equivalence inside the first root field; the latter derives it from bounded A-module separation. Steps 1–4 supply that derivation.
- `lem-trf-frobenius-root-coordinate-test` vs `lem-trf-char-zero-spectral-coordinate-topology`: the latter assumes characteristic zero and gives no positive-characteristic root test.
- `lem-trf-frobenius-root-coordinate-test` vs `lem-trf-tate-fraction-weak-stability`: the latter concerns a specific Tate fraction field over a complete coefficient field, not arbitrary valued fields in characteristic p.
- `lem-trf-frobenius-root-coordinate-test` vs `lem-trf-tate-root-finite-rank-bseparation`: the latter proves module separation over a Tate algebra and does not give the general field-theoretic root test.
- `lem-trf-frobenius-root-coordinate-test` vs `lem-trf-incomplete-spectral-algebra-norm`: the latter provides spectral norm axioms for algebraic extensions, not equivalence with coordinate norms.
- `lem-trf-frobenius-root-coordinate-test` vs `lem-trf-dense-weak-stability-transfer`: the latter assumes weak stability of a dense overfield and deduces exact orthogonal stability; it does not prove weak stability from first-root subspaces.

## Review by Q17

I read the primary source's extracted pp.154–155 as described above, and compared the item with BGR Lemma 3.5.3/2 and the new node with Theorem 3.5.3/1. The former uses finitely generated submodules only; it does not require A Noetherian, complete, or a valuation ring. The root-field theorem does not require K_1/K finite. The chosen coordinate formulation allows arbitrary finite subspaces and arbitrary finite extensions. These are exactly the hypotheses needed; no perfectness or separability assumption was added. The local archival limitation is explicit rather than presented as a full-book reading.

Step 1 uses only the given characteristic-p identities, fraction representation, and norm definitions. I checked the denominator exponent: from v_i^p=b_i/a_i it is (a_i v_i)^p=a_i^(p-1)b_i, not b_i^p. Nonzero denominator products stay nonzero because A is a domain. The rescaled generators m_i still span the original V over K. The zero-dimensional case is handled before positive maxima are taken.

Step 2 uses no black-box localization theorem: the formula for h, the equality after two denominators, addition, scalar multiplication by b/a, and the bound are all written out. Both d y and e y must lie in the same M before A-linearity is used. The bound uses the extension |d|=G(d) and the exact scalar norm identity, so cancellation of G(d) is legitimate and no uniform choice of denominators is needed.

Step 3 applies the hypothesis only to the already constructed finite M, at a nonzero element d y. It is not assumed that the whole root ring is finitely generated. The common-kernel procedure lowers the dimension by one at each choice, so exactly r bounded forms suffice; this is elementary finite linear algebra, not a hidden continuous-dual theorem or Hahn–Banach argument.

Step 4 uses the invertible square evaluation matrix, not an unsupported assertion that a separating dual determines the topology. The entries of its inverse lie in K and form a finite set. Because r>0 and the inverse is invertible, D is positive. Each B_j is positive by hypothesis and each N(v_i)>0 because basis vectors are nonzero. This makes c_V and C_V strictly positive. The upper estimate is directly ultrametric. These are finite matrix calculations, and no finite-dimensional norm-equivalence theorem over an incomplete base is used.

Step 5 is the sole non-elementary step and cites the new node. I reopened its statement: it assumes precisely the finite-subspace root-norm bounds established in steps 1–4 and states precisely the finite-extension spectral bounds being concluded. `citations.json` quotes that conclusion verbatim. The field, characteristic, root norm and spectral norm are the same on both sides. Its definition dependencies are the existing field node and existing spectral-algebra-norm node, whose statements I opened and read. No proof of another node is used as an unstated interface.

I tested the new statement on V=0, a one-dimensional subspace, a perfect field (K_1=K), and a complete field. The empty maximum convention handles V=0; in dimension one the coordinate bound is the scalar norm formula. Perfect and complete fields have the familiar weak-stability behavior, so these do not expose a missing hypothesis. Conversely, an incomplete field with an immediately approximable nontrivial purely inseparable element does not satisfy the root-coordinate hypothesis: subtracting approximants makes the norm tend to zero while one coefficient is 1. Thus the new node does not silently assert weak stability for every imperfect incomplete field. Neither its hypotheses nor the item exclude inseparable finite L/K.

I checked delivery-errors B–E: the new node is self-contained TeX with no proof, all its objects and norms are introduced, its source locator is exact, searches and blueprint fields are recorded, and it duplicates neither an existing node nor a clause of the ring-module hypothesis. No Stacks tag is being used for a different fact; this is a BGR source route. There is no SGA citation. All four elementary steps give their actual algebraic arguments, and the only non-elementary input is cited. Every step is shorter than 2000 characters. The correction made during review was the source locator and the explicit distinction between the root-field theorem and the module criterion; the mathematical statement was retained.

Nothing remains unfinished in this one-level split. The new node is intentionally unsplit, with its proof obligation and source intact. The required server dry run and push follow this report.
