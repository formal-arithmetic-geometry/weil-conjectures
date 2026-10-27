# Stage-1 delivery: lem-pur-quotient-expression-strict-kflat-towers

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-quotient-expression-strict-kflat-towers.json`: item, statement unchanged, split into ten proof steps. Mathlib verdict: no complete match.
- `citations.json`: 37 step/node entries, each quotation checked verbatim against the live node statement.
- `report.md`: this report. `searches.jsonl` is the prescribed search command's own log. `write_split.py` is sandbox-only working material.

There are **0 new nodes and 0 Mathlib leaves**. Every non-elementary ingredient was already in the DAG. No Lean file was written and no compiler, Lake or build tool was run.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint tag and for quotient-expression, semilinear-system, sequence-site and K-flat terminology. The existing generic K-flat library and finite-coefficient pullback/tensor declarations do not state this complete strict-expression tower assertion. No exact attachment was found.

## WANTED

None. The proof is explicitly agent-written assembly, not attributed verbatim to Stacks or to the blueprint.

## Findings and corrections

The item had no proof. Its statement and all statement dependencies are retained. Its source's 0G7E and 07A2 supply the generic preservation inputs, not the entire strict-tower conclusion. I supplied the syntactic induction, balanced transition maps, their chain and cocycle equations, and the componentwise system test. The current blueprint's `def-weil-frobenius-coefficient-twists.md` is the historical ancestor, not itself a theorem about these representatives; the precise extracted place in the existing blueprint provenance remains recorded. Whole-blueprint searches for K-flat, quotient expression, semilinear and constant coefficient found no alternate blueprint statement of this full result. There is no released repair note for this item and no pre-existing sandbox split.

The crucial distinction is preserved: system flatness is over the sequence ring. No flatness after restriction to the completed ring is claimed. No inverse-image/limit interchange, coefficient-map flatness, normalization of adjoints, boundedness or constructibility was used.

## Not duplicates

No new node was created. The existing `lem-pur-quotient-system-flat-models` covers reduction generators and simple operations; the present item's induction handles every prescribed finite syntactic tree and verifies its actual maps. Existing `lem-pur-system-evaluation-kflat` and `lem-pur-system-evaluation-flat` only give the forward evaluation direction and were deliberately not cited for the converse system test. That converse here is a few-line argument from componentwise ordinary tensor and exactness, so it is a proof step, not a new lemma node.

## Review by Q28

I read the item and its parent `lem-pur-quotient-expression-kflat-normalization`, the strict-expression definition, the chapter and unit records, and the current blueprint ancestor. For the preservation inputs I read Stacks `sites-cohomology.tex`, Tag 0G7E (`lemma-pullback-K-flat`) and Tag 07A2 (`lemma-tensor-product-K-flat`), and checked the actual flat-term hypotheses; the former applies even when the structural ring map is a nonflat quotient. I also read the abelian and colimit descriptions in `sites-modules.tex`, Tags 03DA and 03DB, and Zheng Construction 4.1 in the available PDF (the paragraph defining the topos of projective systems, its ring, and vertical evaluation). For every cited node I opened and read its statement rather than using facts hidden in its proof. There are no new nodes whose source requires separate review.

Step 1 uses `lem-pur-proetale-constant-coefficient-comparison` for invertibility of precisely the specified canonical ring map and `prop-weil-pbc-proetale-constant-exact` for exactness of fixed finite-coefficient module inverse image. The definition of pro-etale inverse image supplies its adjunct constant-section characterization. The quotient square is proved by taking adjuncts and testing their constant-presheaf maps; it is not assumed as part of the comparison theorem. Every coefficient ring O_E/varpi^n is finite commutative, so the finite exactness theorem applies on all permitted arrows. Empty schemes are allowed by the comparison theorem.

Steps 2-5 use only the actual definitions and equations: completed coefficients give q pi_m = pi_n; sheaf tensor is sheafification of the presheaf tensor; total tensor gives the signed differential and summand maps; scalar restriction leaves section groups unchanged; inverse image gives its colimit/sheafification generators. I checked balancing separately at the tensor and pullback constructors. The pullback balancing uses the coefficient square proved in Step 1. The chain calculation retains the sign (-1)^p. The cocycle proof names both induction hypotheses at a tensor and the single induction hypothesis plus quotient composition at a pullback, and checks all identity indices. Thus these elementary steps contain their arguments instead of concealing a preservation theorem.

Step 6 applies `lem-weil-pbc-ringed-pullback-preserves-kflat` to the identity topos with R_Y -> B_Y,n for a generator, and to the actual pro-etale morphism and c_n for a pullback. The small-site and flat-term K-flat hypotheses are exactly those of the item or the induction hypotheses. `lem-pur-derived-change-of-rings` states that the actual K-flat complex computes derived reduction. `lem-pur-kflat-total-tensor-model` explicitly covers doubly unbounded direct-sum total tensors and flat terms. `lem-weil-pbc-ringed-topoi-derived-tensor-pullback` explicitly computes derived pullback on these representatives. Unit flatness and K-flatness are the tensor-unit identities, written out without a bounded-flat theorem. No hypothesis on cohomology or on the quotient homomorphism is inserted.

Step 7 uses the statement of `lem-pur-system-ringed-sequence-site` for the actual equivalence with module sheaves and `def-coef-ringed-sequence-site` for the vertical topology. It writes the ordinary tensor presheaf at (n,U) and explains why vertical sheafification gives exactly level tensor. The same argument applies to direct sums. The componentwise exactness assertion is copied from the statement of `lem-coef-semilinear-derived-sections`; a definition interface alone was not cited for that theorem. Step 8 then applies the definitions of flatness and K-flatness to arbitrary exact test sequences and arbitrary acyclic test complexes of systems. Each evaluated test is legitimate by componentwise exactness, and Step 6 supplies the corresponding level property. This proves the assertion about the particular constructed system, rather than replacing it by a resolution with merely good evaluations.

Step 9 uses the explicit derived evaluation, system tensor and exact levelwise geometric inverse-image clauses in `lem-coef-semilinear-derived-sections`. It also applies the total-tensor-model theorem on the sequence site itself, now that Step 8 proves the hypotheses. `lem-weil-pbc-exact-functor-derived-functor` says every complex computes the derived functor of an exact functor; this justifies keeping the actual pullback constructor. The step does not use the internal-Hom clause, which has a cartesian-input restriction, and does not assume normalization. Step 10 checks R_W-linearity directly with q pi_m = pi_n, then uses exact scalar restriction/evaluation and `lem-sf-exact-functor-derived-triangulated` to localize the already constructed strict tower. The normalized-tower definition is used only for its coherent derived-tower datum, explicitly stopping before adjoint invertibility.

I tested the zero complex, empty generator list (unit expressions still exist), n=m, k=m=n, empty schemes, negative cochain degrees and complexes unbounded in both directions. Tensor signs remain correct at negative degrees since the maps have degree zero. All tensor terms use direct sums; no product totalization enters. With E=Q_l, the quotient Z/l^2 -> Z/l is nonflat, but the preservation theorem still applies and the construction is unchanged. I checked the dependency closure of the non-elementary inputs for a path back to the item and found none. Every proof step is below 2000 characters; none hides an inline comparison lemma behind a long paragraph. Off-unit citations are declared as generic tool uses in split_report, not as changes of the chapter or unit route.

The Mathlib queries were run with the required command and read as returned. LeanSearch found Module.Flat tensor-exactness declarations for ordinary modules; Loogle returned no hits for CochainComplex plus Flat; grep found no relevant K-flat or semilinear-system implementation in Mathlib. LeanFinder's two formulations returned module flatness, local cohomology diagrams, completion maps, and HomologicalComplex.HasGoodTensor associator hypotheses. I read the relevant Module.Flat signatures in RingTheory/Flat/Basic.lean and CategoryTheory.lean, and HasGoodTensor in Algebra/Homology/Monoidal.lean: none states a prescribed sheaf-complex tower construction. Historical searches already in the item are retained verbatim; the five Q28 searches are appended from this sandbox's log.

The checklist in delivery-errors B-E was checked against the written JSON: no new statement-only node or duplicate is needed; statement and definitions are unchanged; every non-elementary ingredient is a cited existing statement; every citation quotation is an actual substring; every map uses the intended ring and site; the induction includes bases and constructors; there is no SGA citation or alternate purity route. The server review_split check passed. The first deliver.py dry run rejected the 28-character change-of-rings quote as too short; I replaced it with the full cited statement. Final delivery validation is performed with the required deliver.py dry run.

## Unfinished work

None within stage 1 for this item. The independent maintainer review and the proofs of existing unsplit dependencies remain the project's later work.
