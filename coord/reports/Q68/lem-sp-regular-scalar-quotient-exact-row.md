# Q68: lem-sp-regular-scalar-quotient-exact-row

## Files written

- `dag/nodes/sec-smooth-purity/lem-sp-regular-scalar-quotient-exact-row.json`: statement item, now split into six proof steps; statement unchanged; no Mathlib match.
- `citations.json`: twelve step/node entries, each quoting a verbatim substring of the cited node's statement.
- `report.md`: this report.

New nodes: 0. New Mathlib leaves: 0. There was no earlier item copy, proof or report in this sandbox. Existing item search records from its creation by NX were retained; five searches actually run as Q68 were appended from `searches.jsonl`.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint id, regular-scalar/quotient terminology and Koszul/KFlat concepts. No project declaration states all the clauses. The general K-flat infrastructure in `WeilConjectures/FromJoel/CategoryTheory/Abelian/Flat/KFlat.lean` is an ingredient, not this item. Existing DAG definitions and general results were reused rather than restated.

## WANTED

None. The needed blueprint and Stacks sources are present. No SGA source was used.

## What was wrong and what changed

The imported item was a statement-only child of `lem-sp-ell-coefficient-fiber`, not a completed split. Its statement is correct under the strong explicit hypothesis that multiplication by t is injective on every section ring. No statement dispute or weakening was necessary. The proof is explicitly agent-written: the blueprint motivates the coefficient calculation but does not provide this general ringed-site row as a named theorem.

One source-label issue was caught while checking citations: the existing node `lem-pc-bounded-above-flat-kflat-site` has a stale source place saying 06YS, whereas the actual Stacks label `sites-cohomology-lemma-bounded-flat-K-flat` is Tag 06YQ. The node's statement is exactly the general theorem needed; the item cites 06YQ correctly. Similarly, exact module sheafification itself is Tag 03EI (`sites-modules-lemma-sheafification-exact`), not just the broad sheafification section mentioned in the existing exactness node's source. No other worker's node was edited.

## Unfinished work

None for this one-level split. The two non-elementary tools already have DAG nodes. Delivery validation is recorded below.

## Blueprint and route

Read `dag/chapters/sec-smooth-purity.json`, `dag/units/sk-lem-sp-tower.json` and the current main-20261015 proof of sk-lem-sp-tower. This item supplies the first paragraph's explicit calculation of the two cohomology sheaves of the displayed coefficient tensor. It does not change the normalized-tower reconstruction route. `blueprint_refs.py ancestor` returns sk-lem-sp-tower, via the existing item parent lem-sp-ell-coefficient-fiber. Whole-blueprint searches for "regular scalar" and "quotient powers" found no equivalent blueprint statement; `same_as` remains empty. The unit's key node is not this item, so no unit realization record was changed.

The two off-unit statement citations are generic tools: `lem-weil-pbc-ringed-site-module-sheafification-exact` transports a sectionwise exact row to sheaves, and `lem-pc-bounded-above-flat-kflat-site` proves that the displayed finite free complex is K-flat. Their uses and reasons are declared in `split_report.tool_uses`. The definitions used for sheaf modules, tensor and cochains specify the existing library notions.

## Mathlib searches and candidates read

Ran leanfinder, loogle, grep and leansearch through the required msearch.py command, then a second, differently phrased leanfinder query. All five services returned successfully. Their exact queries and returned declaration lists are preserved in searches.jsonl and appended to the item's mathlib_searches, alongside the original NX records.

Read the actual candidates: `IsSMulRegular.smulShortComplex_shortExact` at Mathlib/RingTheory/Regular/Category.lean:51; `QuotSMulTop.map_first_exact_on_four_term_exact_of_isSMulRegular_last` at Regular/IsSMulRegular.lean:173; `Ideal.exact_mulQuot_quotOfMul` at OrderOfVanishing/Basic.lean:91; and the free-cokernel presentation constructors at Algebra/Category/ModuleCat/Sheaf/Quasicoherent.lean:74–114. These are ordinary-module exactness theorems or constructors that assume a sheaf cokernel presentation, not the requested quotient-sheaf row with augmented K-flat complexes. The grep found no Mathlib KFlat/kFlat theorem. The second phrasing returned cotangent/power-ideal quotient and ramification declarations; those concern different quotients (and sometimes require a domain), not this item on arbitrary ringed sites.

## Not duplicates

No new nodes were created. The generic ringed-site exactness and bounded-above K-flat nodes are cited directly. The scalar map, its kernel computation, and the identity case are elementary proof steps rather than new nodes or re-labelled clauses of the item.

## Review by Q68

I read the current blueprint's sk-lem-sp-tower proof, in particular the first paragraph asserting the coefficient tensor's H^{-1} and H^0, and checked the chapter and unit route. For the actual tools I read Stacks `sites-modules.tex`, lemma-sheafification-exact (03EI), its preceding module-sheafification adjunction discussion (03CY), the tensor definition in the DAG against section 03EK, the flatness definition (03ER), and `sites-cohomology.tex`, lemma-bounded-flat-K-flat (06YQ), including its reduction through good truncations. Every source used is present locally. There are no new-node sources to review.

For step 1, I opened the exact module-sheafification node and checked that it applies to a ringed site with a sheaf of rings, not merely a constant coefficient ring. It explicitly says sheafification is exact. The category-of-module-sheaves statement supplies sectionwise kernels and sheafified cokernels. The abstract-derived-category statement supplies the cohomology definition and the criterion for a quasi-isomorphism. The only algebra needed is repeated cancellation of the given injective multiplication by t, which proves injectivity of every positive power without a domain or stalk hypothesis. The augmentation is the stated quotient, not an arbitrary cohomology isomorphism.

For step 2, the tensor definition actually specifies sheafification of sectionwise balanced tensor. I wrote both unit maps and checked their inverse equation by balancing and restriction, so the use of the flatness definition is justified by an exact functor explicitly isomorphic to the identity. Zero terms are flat by their zero tensor functor. The bounded-above K-flat statement is for any ringed site and has exactly the hypotheses now checked: terms flat and zero above degree 0. The K-flat-complex definition says that a quasi-isomorphism with K-flat source is a K-flat resolution. These citations therefore give all of step 2, without pretending that a definition itself asserts K-flatness of free complexes.

For step 3, I opened the total-tensor definition and read its signed differential. Putting the first factor in degree 0 makes the sign +1, and the explicit tensor unit sends the differential to multiplication by t^m. I also checked the degree-zero augmentation on b tensor r and used n >= m precisely to obtain the reduction B_n -> B_m. No assertion that B_n is flat over R is used or needed.

Steps 4 and 5 are direct ring calculations, written out rather than hidden behind a quotient-isomorphism lemma. In step 4 changing a lift by t^m y changes its image by t^n y, which proves well-definedness. Cancellation of t^{n-m} proves injectivity, and cancellation of t^m in step 5 identifies the middle kernel. The last kernel is computed by x = t^m y and reduction is visibly onto. Commutativity of the section rings gives linearity, and t being a global section makes these formulas commute with every restriction. The image ideal is explicitly the complementary power, with no extra finiteness or nonzero-ring assumption.

For step 6, I reread the exact sheafification statement and the actual universal property in the module-sheafification definition; they provide precisely the exactness and extension/uniqueness used. The row was proved sectionwise for quotient PRESHEAVES before sheafification; the argument does not assume that every section of a quotient sheaf has a global lift. The quotient-module actions and linearity can be checked on those local formulas; kernels and cokernels of B_n-modules have the same underlying abelian-sheaf descriptions, as the category-of-module-sheaves statement says for every coefficient ring sheaf. Exactness preserves the calculated image ideal on sheafifying. I then explicitly substituted n = m to obtain identity, zero, identity; this also checks the exponent-zero cancellation used in step 4.

I tested m = 1 and n = m, t a unit (all quotient sheaves are zero and the two-term complex is acyclic), and the zero ring (every module appearing is zero). A ring with other zero divisors, such as (Z/6Z)[s] with t = s, satisfies the proof because only the powers of t are cancelled. As a negative check, t = 2 in Z/4Z would invalidate cancellation and is excluded by the stated injectivity hypothesis. No enough-points assumption, flatness of the quotient, terminal-object assumption, Noetherianity or domain hypothesis entered the proof.

I checked B1–B10, C1–C8, D1–D5 and E1–E7 of delivery-errors against the final files: no new nodes with sketches, no unchecked search record, no clause-restatement nodes, no source-route substitution, and no uncited non-elementary inference. All twelve citations were checked as verbatim substrings of node statements. No proof step exceeds 2000 characters; the longest is below 900. The statement and imported metadata were preserved; only the worker-owned split fields and recorded searches changed. No Lean was written, no compiler/build ran, and no repository or launcher file was edited.

## Validation

The required `deliver.py Q68 lem-sp-regular-scalar-quotient-exact-row --no-push` completed with exit 0 and printed `OK (not pushed)` at c2fa941a0ad: server preflight passed, including the DAG and split checks. The report now records that result; the final dry run and direct push use the same reviewed proof and citations.
