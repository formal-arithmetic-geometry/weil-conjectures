# Worker report: lem-coef-marked-sharp-enrichment

## Files written

- dag/nodes/sec-six-functors/lem-coef-marked-sharp-enrichment.json — statement, now split in eight coordinate calculations; Mathlib verdict: no full match.
- citations.json — a verbatim statement excerpt for the internal-Hom citation in each of the eight steps.
- report.md — this report.

No new nodes; no Mathlib leaves. The helper write_split.py is sandbox-only and is not a delivery file.

## Attachments

None. Searches of /home/ubuntu/weil-src-slopmaster2/WeilConjectures for the blueprint id and the patterns marked.?simplicial, MarkedSSet, MapSharp, mapSharp and markedSharp found no candidate. Searches for enrichment/sharp terminology in CategoryTheory returned unrelated ordinary or sheaf-theoretic enrichment. No upstream master sorry declaration is being treated as a proof.

## WANTED

WANTED: Jacob Lurie, Higher Topos Theory, Section 3.1.3 opening paragraph, printed p.154, and Corollary 3.1.4.4, printed p.162, for lem-coef-marked-sharp-enrichment. The author-hosted PDF https://www.math.ias.edu/~lurie/papers/HTT.pdf was read online on 2026-10-17, including the page-154 mapping formulas and the page-162 corollary and proof. No HTT copy is archived under literature/. No document was downloaded. The proof is therefore marked agent-written; it expands the source's mapping-property formula into coordinate checks.

## Problems found and repairs

The statement is correct as written and is unchanged. It had no proof. Its only external mathematical input is the already existing marked internal Hom and its exponential adjunction in lem-coef-marked-internal-hom. The proof does not invoke the marked-point model theorem, whose proof uses the present item, or any fibrancy/weak-equivalence assertion. No source error, target change, unit-route departure, or coefficient-category identification is involved.

The item initially was absent from the shared snapshot. The first dry-run invocation completed its fetch and exited because the sandbox had no node files. The item then appeared in the refreshed shared DAG; work continued from that actual JSON. That transient acquisition failure is resolved.

## Mathlib and duplicate searches

The inherited searches are retained. Five searches were actually run for this item with msearch.py, and searches.jsonl contains their outputs: LeanFinder with two different semantic formulations, LeanSearch, Loogle, and a source grep. All services answered. Loogle and grep returned zero hits. The semantic hits include SSet.instMonoidalClosed, CategoryTheory.SimplicialObject.instEnrichedCategorySSet and CategoryTheory.SimplicialCategory.sHom. I read Mathlib/AlgebraicTopology/SimplicialCategory/Basic.lean:15-27 and 45-72, SimplicialCategory/SimplicialObject.lean:30-43, and SimplicialSet/Monoidal.lean:1-100. The first two either assume an enrichment or give it for ordinary simplicial objects; the third treats unmarked simplicial sets. None states the marked sharp-parameter construction or its marking check, and these cannot be obtained from one of those declarations by a one-line specialization.

Whole-DAG searches for sharp enrichment, marked internal Hom, and tensor/cotensor terminology were checked against the nearby marked-point-model, marked-anodyne, internal-Hom and abstract tensor/cotensor nodes. blueprint_refs.py search 'sharp enrichment' and search 'marked internal' found no imported blueprint duplicate; ancestor returned prop-coef-integral-exceptional-adjoint. def-coef-simplicial-tensor-cotensor defines the abstract universal elements, whereas the present item proves the specific sharp enrichment and its specific tensor and cotensor. lem-coef-marked-internal-hom constructs the marked closed structure, which is exactly the retained input. No extra node is needed for the defining currying/evaluation computation.

## Not duplicates

No new nodes were created. All eight elementary calculations are steps of this item. In particular, the sharp-parameter transposition is written out, rather than turned into a node restating a clause.

## Unfinished work

None in the stage-1 split. The cited internal-Hom node has its own independent queue state; this delivery does not claim to prove it or split it. No Lean was written or compiled.

## Review by Q140

I read the stage-1 brief, stages/1-dag.md, SETUP.md's three blueprint levels, GOAL.md, coord/dag-sync.md and delivery-errors.md B through E. I read the whole item, its chapter/unit records, the current main-20261015 ancestor proof, the full statement of lem-coef-marked-internal-hom, the enhanced-diagram definition and the abstract tensor/cotensor definition. HTT p.154 identifies sharp mapping sets by the sharp-parameter mapping property. Corollary 3.1.4.4 p.162 uses that enrichment and explicitly tensors with the fully marked simplicial parameter. The historical ancestor is the derived coefficient-adjunction display in paragraph 2; this is an auxiliary construction beneath it, not a replacement of the unit's route.

For Step 1 the cited internal-Hom statement explicitly supplies marked objects, the two markings and coordinatewise product markings. I checked that every restriction of a fully marked parameter is marked, the simplicial identities hold by precomposition, and degree zero recovers precisely marked morphisms. Step 2 uses the same product-marking sentence: the pair (f, parameter) sends a marked pair to a marked pair, and restriction, associativity and both units are the displayed equalities on coordinates.

Steps 3 and 4 use these same definitions to prove, not assume, the sharp-parameter currying calculation. I checked the inverse at an arbitrary simplex, its naturality identity for every ordinal map, and its marking check on (e,id_[1]); this tests every marked edge, not only degenerate edges of the parameter. The second inverse is verified at every pair (x,tau), so a hidden presheaf-density or colimit lemma is not being invoked. The internal-Hom citation in Step 4 also states explicitly that its bijection is ordinary transposition restricted to marking-preserving maps; the sharp variant here is verified directly.

Step 5 applies that calculation to K times Delta^n. The fully marked product identity follows edge by edge, and the operator 1_K times Delta(alpha) proves that the resulting bijections are a simplicial isomorphism, not just a vertex bijection. Step 6 cites exactly the internal-Hom statement's natural exponential bijection, with exponent K^sharp and test object X times fully marked Delta^n. I checked the order of all three factors, the product markings under interchange and naturality under parameter restriction. Thus the citation genuinely states every non-elementary input to this step (C4).

Step 7 identifies the two transposes through the actual three-variable map. It checks pre/postcomposition, restriction and composition of families at the same parameter, and gives the universal elements by inclusion and evaluation. Step 8 uses the internal-Hom statement's explicit input-universe assertion together with the elementary closure of a Grothendieck universe under the displayed products and map sets. All constructions stay in the universe; there is no colimit over a large indexing category.

I tested K empty (empty tensor, terminal cotensor, terminal adjunction targets), K=Delta^0 (identity mapping objects), X empty, Y empty, and minimally versus fully marked X and Y. The inverse marking check still applies without extra hypotheses, and no quasicategory or Kan assumption occurs. The all-elementary labels refer to explicit defining coordinate computations, not to an unproved model-category theorem: the only existing theorem used is the marked exponential adjunction, specialized explicitly in Step 6. Every step is under 1000 characters, so none conceals a long standard-argument lemma. The statement and its sole statement dependency are unchanged. There are no new nodes, no SGA citations and no cycle through the parent model theorem; the proof-dependency union is exactly the existing internal-Hom node. Every cited step has a verbatim excerpt in citations.json.
