## Files written

- dag/nodes/sec-proper-base-change/lem-weil-pbc-local-derived-restriction-comparisons.json: statement, split into seven steps; not a Mathlib leaf as a whole.
- citations.json: one verified verbatim statement quotation for each of the 19 step/node pairs.
- searches.jsonl: the search command's unmodified results, retained.
- report.md: this report.

No new DAG nodes or Mathlib leaves. The sandbox had no prior item, split, report or searches when this session started. The repository item was copied without changing its statement, statement dependencies, source, provenance or blueprint fields.

## Attachments

None. Searches by the exact blueprint id and by derived/local restriction concepts in lean/WeilConjectures found no declaration stating all clauses. Existing exact-functor homology comparisons are general ingredients, not the actual inverse-image-ring/slice/representative comparison. The recorded local object definition is in lean/Sheaf/CategoryTheory/RingedSiteDerivedRestrictionUniverses.lean, not an attachment for this theorem.

## WANTED

None. The sources needed for this split are present locally.

## What was wrong or incomplete

The item had no proof. Stacks 015F states that exact functors are computed on every complex, but omits its details and does not discuss the project's chosen objectwise representative. I supplied the representative comparison, conjugated morphism formula, and explicit cohomology/shift comparisons. The proof is marked agent-written rather than attributed as a verbatim Stacks proof.

The inherited blueprint reference names the earlier ancestor proof sentence “Choose an integral lattice for K”. The main-20261015 thm-weil-pbc-finite-extension.md file contains its theorem statement but no proof paragraph. I retain the inherited provenance and explicitly describe which local comparison of the descendant integral-lattice characterization this item serves; I do not claim that the absent paragraph is present in the current snapshot.

The source of the existing slice exactness node points at 03DJ. That tag states exactness of extension by zero; the localization morphism and identity coefficient structure are described in Section 03DH and Definition 04IX, and restriction exactness is also used explicitly in the paragraph following 03DJ. I cite the existing node's actual restriction-exactness assertion and use the more precise localization source place in step 2. No repair of that other node is part of this delivery.

## Unfinished work

None for this one-level split. All non-elementary ingredients already have nodes.

## Not duplicates

No new nodes were created. Whole-DAG searches by exact-functor, inverse-image-module, localization and slice-restriction terminology and by Tag 015F found the existing ingredients. Whole-blueprint searches with blueprint_refs.py for “exact functor”, “derived restriction”, “local restriction”, “cohomology exact” and “restriction cohomology” found no duplicate of the complete item. No same_as entry was added.

## Mathlib searches

I ran the required msearch.py services: LeanFinder with both the exact-functor/representative and slice-restriction phrasings, Loogle for "mapDerivedCategory", LeanSearch for the induced exact functor and homology/shift comparison, and grep for mapDerivedCategoryHomologyFunctorIso|objObjPreimageIso|mapDerivedCategorySingleFunctor|overFunctor in CategoryTheory. All returned successfully. I read the hits: mapDerivedCategory, mapDerivedCategoryFactors, its shift compatibility, and mapDerivedCategorySingleFunctor in Mathlib/Algebra/Homology/DerivedCategory/ExactFunctor.lean. These supply the already-existing factorization node. Scheme.Modules.restrictFunctor and restrictFunctorIsoPullback concern structure sheaves/open immersions, so do not state this arbitrary-ring pro-etale comparison. The grep hits for objObjPreimageIso supply representative isomorphisms, not this composite local functor. Existing inherited searches remain in the item; all newly appended records are literal logged queries and their actual summaries.

## Review by Q09

I read the item, its unit sk-thm-properbasechange and chapter sec-proper-base-change, the current blueprint ancestor theorem, and the definition of local derived restriction in both its DAG statement and its existing Lean source. The coefficient ring is the actual inverse image of the arbitrary sheaf R; it is never replaced by a completed coefficient ring. Compatible small site models are already part of the pro-etale conventions. Only stage 1 was performed: no repository edits, git commands in the shared repository, Lean writing, compilers or Lake.

For the mathematical source I read derived.tex Tag 015F (lemma-right-derived-exact-functor), sites-modules.tex Tags 03D2 (lemma-pullback-module), 03D3 (lemma-adjoint-push-pull-modules), 03DA (lemma-abelian), 03DB (lemma-limits-colimits), Section 03DH and Definition 04IX (definition-localize-ringed-site), and homology.tex Tag 010N (lemma-exact-functor). There are no new-node sources to audit and no SGA reference. Stacks' missing representative calculations are written out and marked as my argument.

Step 1 uses the full statement of the pro-etale module inverse-image comparison, which explicitly allows an arbitrary ring sheaf and supplies a natural comparison with abelian inverse image. I read the left-exact-site inverse-image/tensor statement: it actually supplies exactness on abelian sheaves. The definition of pro-etale inverse image records the finite-limit-preserving base-change construction to which it applies. The forgetful-colimit node explicitly says faithful and exact, and the exact-functor homology node supplies preservation of the homology quotient. Thus reflection of zero homology is proved using faithfulness; it is not silently inferred from a definition of flatness or from constant coefficients.

Step 2 cites the full ringed-site module restriction/adjunction node. Its statement explicitly says j_U^* is exact for any object U and any commutative ring sheaf, including R'. The localized-site definition actually gives both the coefficient ring and the sectionwise morphism formula. No assumption that U is an open subscheme or immersion is introduced. I declared this generic off-unit tool in split_report.tool_uses, as required; it does not replace a geometric step of the unit.

Step 3 cites the exact-functor derived factorization statement. I verified that it includes quasi-isomorphism preservation, a natural factorization for every unbounded complex, and integer-shift compatibility. Both module categories are abelian by the existing module-sheaf conventions on the chosen small sites, and steps 1–2 establish the exactness hypotheses.

Step 4 uses the local-restriction definition only for its actual object construction, the abstract-derived-category definition for localization and its representative interpretation, and the factorization node for the isomorphism phi. I checked the directions: epsilon is QC to X, so DG(epsilon inverse) goes from DG(X) to DG(QC), then phi goes to QG(C). The conjugation formula proves identities, compositions and preservation of inverses directly. It never treats the object-preimage choice as a functor on complexes.

Step 5 uses precisely naturality and quasi-isomorphism preservation in the factorization statement, together with localization. The equation t b = b' Q(h) gives Q(h)b inverse = b' inverse t, which proves the displayed naturality square. Cancellations prove the cocycle for representative changes; inverses of quasi-isomorphisms give the same formula for localized arrows.

Step 6 uses the complex-cohomology node's natural kernel/image comparison, not a theorem about some different derived cohomology. The abstract-derived-category statement explicitly factors cohomology through Q. The factorization node supplies the other comparison. I checked both inverse directions in h, and wrote the three arrows from GFH(K) to H(LK). Naturality descends on chain maps and their inverted quasi-isomorphisms. Thus the comparison square with alpha commutes by its displayed definition.

Step 7 uses the same factorization and complex-cohomology statements. I computed the single complex termwise, then used the cited signed shift/factorization compatibility. The nonzero cohomology of M[r] occurs in degree -r. Its comparison is the identity under the canonical cycle/image identifications, so the cohomology and shifted-single maps have the required compatibility after representative transport.

For the B–E checks: no unsplit new nodes contain hidden proof material; no new definitions or duplicate clauses were introduced; every cited statement was opened and its used portion copied verbatim into citations.json; the proof-dependency list is exactly the union of uses; the chosen existing dependencies do not reach this item, so they create no cycle. The elementary steps consist of the displayed factorization, conjugation and localization calculations from cited facts; all seven step texts are below 2000 characters. No statement was weakened or corrected. I checked the zero ring, zero module, empty scheme/site, arbitrary nonconstant R, unbounded K and positive/negative shifts. Faithful forgetting and exact localization work in the zero categories as well; no nonemptiness, nonzero coefficient, torsion, flatness or boundedness is used.

## Dry-run repairs

The first dry run required a longer quotation for the slice-restriction node. I replaced the short exactness clause with its whole statement, which records the site, ring and object hypotheses as well as exactness. The proof did not change.
