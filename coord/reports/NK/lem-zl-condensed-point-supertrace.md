# Stage-1 report: lem-zl-condensed-point-supertrace

## Files written

- `dag/nodes/sec-zeta-weil/lem-zl-condensed-point-supertrace.json`: statement node, now split into eleven proof steps; no exact Mathlib match. Its statement, statement dependencies, ancestry, provenance and earlier searches are retained.
- `citations.json`: one verbatim statement quotation for every dependency citation in every proof step.
- `report.md`: this report. `searches.jsonl` contains the real search command records; `prepare.py` is sandbox-only preparation material, not a DAG delivery file.

## New nodes

None. Zero Mathlib leaves added. Existing generic tools suffice; creating nodes for the matrix realization, transported duality or trace equality would merely restate clauses of the item.

## Attachments

None. Read-only searches of `WeilConjectures/` in slopmaster2 by the exact blueprint tag, supertrace, condensed realization and cohomology-trace terms found no project declaration covering this item. I also read `WeilConjectures/CategoryTheory/DerivedCategory/PerfectTrace.lean`: its alternating-sum theorem is `sorry`, concerns ordinary ring modules and assumes the duality witness. It is not an attachment for the present condensed construction. The master reference checkout was searched read-only and was not treated as evidence of finished proofs.

## WANTED

None. The required source texts and the existing DAG tools are available locally. The proof is explicitly agent-written: the rationality blueprint motivates this coefficient comparison but does not contain its proof as a verbatim theorem.

## What changed and what was wrong

The item had an empty proof. The substantive obligations were: realizing the full cohomologically defined category rather than only a category of chain models; computing derived relative tensor in the internal module category; checking constructibility of the resulting cohomology; proving scalar injectivity; and distinguishing the ordinary-field supertrace from the desired internal categorical trace.

I supplied these arguments and did not change the statement. Its displayed cohomology isomorphism is understood with the cohomology module placed in degree zero, as made explicit in step 5. This resolves the customary module/derived-object notation without changing its mathematical assertion.

The geometric-point conclusion uses exact terminal evaluation after passage to the algebraically closed field, not conservativity of classical geometric points on the pro-etale topos. The source Bhatt--Scholze Example 4.2.11 expressly gives a counterexample to such conservativity, so the proof tests only scalar maps or evaluates an already identified finite free module.

Source metadata note for maintenance, outside my permitted edits: the existing node `lem-pc-bounded-above-flat-kflat-site` calls its bounded-flat criterion Tag 06YS. In the supplied Stacks tag index the criterion is Tag 06YQ (`sites-cohomology-lemma-bounded-flat-K-flat`), while 06YS is the K-flat resolution lemma. The cited node's **statement** is the criterion actually needed and is correct. Step 7 cites the corrected source place 06YQ. No existing dependency file was edited.

The stored unit record has the older smooth-proper rationality formulation, while the current `main-20261015` unit text states rationality for finite-type schemes. This item is the parent's generic coefficient-point comparison obligation in the first finite-determinant sentence, independently of either geometric rationality formulation; I made no unit or chapter edit and replaced no route step.

## Unfinished work

No missing step remains in this one-level split. Its cited existing unsplit obligations remain the responsibility of their own DAG items; no Lean proof or compilation is claimed.

## Searches and reuse

I searched the whole DAG by supertrace, finite free complexes, cohomology traces, condensed evaluation and realization, then opened the candidate statements. Blueprint searches with `tools/blueprint_refs.py search` for `supertrace`, `trace`, `finite-dimensional` and `geometric-field-proetale-evaluation` found the already cited trace tools and no other node stating this combined construction. The ancestor command identifies `sk-thm-rationality`, which is retained.

The new real searches logged by `msearch.py NK lem-zl-condensed-point-supertrace` are both semantic phrasings in LeanFinder, LeanSearch for condensed realization and trace, grep for condensed dual/trace or complex duals, and Loogle queries for categorical trace and `HasRightDual`. The first Loogle name was unknown; the successful second query gives duality classes, the unit dual and tensor dual, not this construction. LeanFinder returned ordinary finite-module rigidity and additive `Mat_` infrastructure. LeanSearch returned ordinary trace/duality and monoidal equivalence infrastructure. The direct grep returned no hits. I read the returned types and retained the negative conclusion for the complete item. No new node is declared absent from Mathlib. Earlier searches already stored by NN in the item are retained as historical searches, not represented as my own tool calls.

## Not duplicates

No new node, so there is no new/existing same-tag pair. I reused the existing vector-space projectivity, bounded-free splitting, derived morphism, internal/section tensor, geometric-field evaluation and trace nodes instead of duplicating them.

## Review by NK

I read the item, its chapter and unit records, and the current `main-20261015` rationality statement and proof. The item's source calls it an agent-formulated obligation for the first finite-determinant sentence, not a quotation from that proof. I also read the current trace blueprint proofs `lem-trf-chain-supertrace.proof.md` and `prop-trf-trace-formal-laws.proof.md`, the Stacks ordinary perfect-trace calculation in `trace.tex` Tags 03TG/03TI, the projective-complex full-faithfulness statement in `derived.tex` Tag 064B, the bounded-flat criterion in `sites-cohomology.tex` Tag 06YQ, and Bhatt--Scholze Examples 4.1.10 and 4.2.11 from the local PDF. I read the Mathlib `CochainComplex.IsKProjective.Qh_map_bijective` source as a check on the existing derived-morphism interface. There are no new node source claims to check.

For step 1 I opened `lem-weil-pbc-geometric-field-proetale-evaluation`: it explicitly identifies inverse image with the identity on the profinite site and terminal evaluation with singleton evaluation, over any algebraically closed field. Thus its hypotheses hold for the item's arbitrary algebraically closed positive-characteristic k; it does not require k to be the algebraic closure of a finite field. `sk-def-sfb-qlbar-condensed` really defines finite-subextension-valued functions, so singleton evaluation gives Omega. The coefficient-map statement supplies the actual E inclusion. The derived-category definition supplies H^0, which makes the scalar-injectivity argument valid even without any general conservativity theorem.

Step 2 uses the actual biproduct identities written in `def-sfb-finitely-presented-module`. Matrix conjugation, composition and the preservation of a homotopy equation are written out. No equivalence between the whole internal module category and ordinary vector spaces is assumed.

For step 3, `lem-weil-pbc-vector-space-projective` applies to all vector spaces, including the possibly infinite terms, cycles and boundaries of the original representative. The lifting clause of `def-weil-pbc-projective-module` supplies each section. Only the cohomology complements are asserted finite dimensional and bounded. Inclusion of their zero-differential complex is explicitly checked on cohomology. The bounded-projective full-faithfulness statement `lem-pc-ring-derived-map-representative` applies to the resulting finite model; this establishes the correct full-subcategory domain and covers every morphism.

Step 4 uses both directions of that bijection: fullness represents the inverse of a quasi-isomorphism, and faithfulness makes the inverse equations into homotopies. Realizing the equations then gives an actual inverse in the target derived category. No projectivity of the internal coefficient unit in its sheaf category is claimed or needed.

For step 5 I opened `lem-wf-bounded-free-complex-projective-cohomology-splitting`. Its statement includes the chain-level decomposition and contractible identity summands, not just a derived isomorphism. Over E its projectivity hypothesis is supplied by vector-space projectivity. This is exactly what realization can carry degreewise. The three definition statements for finite presentation, local finite presentation and constructibility yield the finite-free cohomology objects on the identity cover and one stratum. `sk-def-sfb-bounded-constructible` uses those cohomology objects and imposes no completion condition. The quotient-block description explains naturality and avoids claiming a natural choice of splitting.

Step 6 uses the finite-free module evaluation assertion from the geometric-field node. The tensor-coordinate map and its inverse are written explicitly; no scalar extension comparison from the older completed-integral coefficient framework is used.

In step 7 the finite-free tensor-exactness node applies to a commutative internal ring on any scheme and to the identity cover. The internal/section tensor comparison explicitly preserves and reflects flatness, K-flatness and total tensor, so it authorizes using the ringed-site bounded-flat criterion rather than silently switching coefficient categories. The derived-tensor definition says that K-flat total relative tensor computes the operation being restricted. I checked the basis-pair tensor maps against differentials, associators, units and Koszul symmetry. The comparisons therefore have the specified strong symmetric monoidal meaning.

Step 8 uses the cone and shift formulas actually contained in the derived-category definition and the full-faithfulness node for chain representatives. The exactness argument is the displayed cone matrix calculation. Every cone stays bounded finite dimensional before realization and has the constructible cohomology proved in step 5, so the proof does not assume that arbitrary constructible kernels form a Serre category.

For step 9 I checked the complete `lem-trf-chain-supertrace` statement, including its general commutative-ring scope, signed dual complex, evaluation, coevaluation, triangle identities and derived perfect-complex interpretation. It is applied only over the ordinary field E. Applying our constructed strong monoidal functor to those equations gives internal module maps and the required identities. The dual complex is again bounded finite dimensional, so its realization is in the same subcategory.

Step 10 uses the chain-map representative theorem and the trace composite from `sk-d-trace`. I expanded that composite as scalar matrices, obtaining the sign (-1)^{i(-i)}=(-1)^i. Only after this internal calculation do I apply the ordinary E clauses of `lem-trf-chain-supertrace` and clause (4) of `prop-trf-trace-formal-laws`. I verified that the latter node really says the cohomological supertrace over E, and did not use its filtered-additivity assertion on an arbitrary Verdier triangle. The ordinary trace definition agrees with the diagonal sums used here.

Step 11 uses exactly the duality-transport statement `lem-trf-exact-pairing-iso-transport`, with the inverse of the item's w and identity on the chosen dual. Its equations require only a monoidal category, so they apply to our full tensor subcategory. I wrote the transported maps and the braiding-naturality calculation that cancels w against its inverse, proving the trace equality rather than merely saying it transports.

I tested the zero complex (empty sums and zero dual), E[0] (unit trace one), E[-1] (trace of its identity minus one), and [E --1--> E] in consecutive degrees (contractible realization and trace zero). A rank-two endomorphism is the diagonal matrix sum; its conjugation by a basis-change matrix matches step 2. Characteristic two is a possible characteristic of k but not of E, and does not remove the Koszul sign in coefficient characteristic zero. None of the arguments adds geometric hypotheses on k or substitutes a completed-integral coefficient ring. I checked transitive dependency reach for all substantive tools and found no path back to this item. All eleven steps are below 2000 characters, with the routine matrix comparisons explicit. I corrected the potential coefficient-category mismatch by inserting the existing internal/section tensor comparison and corrected the source tag for K-flatness locally in the proof citation, leaving the dependency's maintainer-owned metadata untouched.

The authorized remote `review_split` check has passed with zero new nodes and the generic tool uses declared. The required full delivery dry run follows this signed review.
