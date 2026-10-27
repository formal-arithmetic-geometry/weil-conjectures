# Stage-1 delivery: lem-pur-product-tensor-test-bounds

1. Files written: dag/nodes/sec-smooth-purity/lem-pur-product-tensor-test-bounds.json (statement, split, no Mathlib match); citations.json (six verbatim statement quotes); report.md. No new nodes and no Mathlib leaves.
2. Attachments: none. The exact blueprint tag is absent from lean/WeilConjectures/. Searches for Tor amplitude and product/equivalence notions found the project's generic TorAmplitude definitions and geometric clopen/projector results, which do not state this abstract equivalence theorem under its hypotheses. No proof attachment applies.
3. WANTED: none.
4. The item statement is unchanged. Its source is an agent-extracted exact-product lemma, not a theorem stated verbatim by the blueprint. The current blueprint section-invariant file says “invertible by [def-pur-co-smoothness]”; the finer finite-clopen bounds argument belongs to the ancestor DAG split. This proof is accordingly marked agent-written. All previously recorded searches and provenance are retained, with Q52's actual searches appended. There was no earlier sandbox split or report to resume.
5. Unfinished work: none for this one-level split. The assumed cohomology/tensor comparisons are hypotheses, not results silently established here.

## Searches and reuse

Read the item, its chapter and unit, its section-invariant blueprint source, and both ancestor statements lem-pur-clopen-finite-constructibility-bounds and lem-pur-finite-clopen-derived-decomposition. Searched the whole DAG by zero detection, faithful equivalence, products, and Tor amplitude concepts; inspected candidate statements rather than their proofs. Geometric clopen lemmas impose scheme/restriction hypotheses absent here and the ancestor bounds statements depend on this item, so neither can be used as an abstract proof dependency. Ran blueprint_refs.py ancestor and searches for “Tor amplitude”, “zero object”, and “product decomposition”. None gives this exact abstract statement. No new nodes were needed: identity-map detection of zero and degree-zero transport are direct arguments, not lemmas to add to the queue.

Q52 ran msearch.py leansearch, loogle, grep and two different leanfinder phrasings, as logged in searches.jsonl and appended to mathlib_searches. The grep for Tor-amplitude names returned no hits in Mathlib; the search hits concern ordinary module tensor products, flatness, internal projectivity, and the standard derived t-structure. In particular isGE_Q_obj_iff/isLE_Q_obj_iff compare localization with a complex's bounds, not arbitrary product-equivalence detection or Tor tests. None is an exact or one-line match for the item. Services answered successfully.

## Review by Q52

I read coord/delivery-errors.md B–E in full and checked each proof step against the item's actual hypotheses. For the source I read the current main-20261015 def-pur-section-invariant.md and the extracted ancestor statements, and read Stacks sites-cohomology.tex, Tag 08FZ, label definition-tor-amplitude (lines 12377 onward). That definition tests every module sheaf in degree zero; no boundedness, finite presentation or constructibility can be imposed on the tests. The item's definition agrees with it. I also read the statements of every cited definition/tool and checked each quote in citations.json as a literal substring.

Step 1 is an explicit identity-map proof: additivity sends the identity of the zero module to a zero identity, product maps are tuples, and faithfulness gives 1_A=0. This proves zero detection without claiming that the equivalence is sectionwise faithful or preserves a chosen literal zero sheaf. The empty tuple has a unique morphism, so the same proof covers the empty index set.

Step 2 uses def-weil-derived-cohomology-sheaves only for its stated cohomology functor and functoriality. The cohomology comparison is supplied by the item itself. Applying step 1 to H^m(K) proves vanishing separately in each degree and then in the requested fixed interval. It uses no acyclicity criterion or hidden t-exactness theorem.

Step 3 uses def-weil-abstract-derived-category for localization from complexes and lem-weil-pbc-site-derived-tensor-descent for its stated derived tensor bifunctor. The degreewise definition of D_i and additivity identify the single-term complex directly: degree zero is r_iM and all other terms have zero identity. The counit r_ie_iN is an item hypothesis. Applying the tensor bifunctor to its single-term isomorphism after the assumed tensor comparison supplies the full derived-object comparison, rather than just a per-degree conclusion. No compatibility with a separately chosen inverse equivalence on derived categories is needed.

Step 4 tests the global Tor hypothesis on the actual module e_iN for every component module N, then uses the item comparisons and step 3. This verifies the often-missed arbitrary-test-module quantifier. Step 5 tests each component on r_iM for an arbitrary global M and applies the already proved cohomology assertion to K tensor M[0]. Neither direction invokes a resolution of K with bounded terms or a hypothesis absent from the item.

Step 6 uses def-pc-kflat-complex and def-pc-tensor-complex-sheaves exactly for K-flatness and the total-tensor formula. The zero complex tensor any complex has zero terms, so it is K-flat; the zero module is flat since tensor with it is the zero exact functor. With a K-flat flat-term resolution of M[0], the K-flat formula in lem-weil-pbc-site-derived-tensor-descent computes zero derived tensor as zero. The quoted descent statement supplies both the resolving equivalence and the tensor formula. It is a generic off-unit tool already used to specify the item's tensor; this tool use is declared with its reason in split_report.tool_uses.

I checked singleton products (both assertions become the usual transport under an equivalence), a nonzero module in a single shifted degree (bounds are preserved, not enlarged), a component with only zero modules, K=0, a=b, and I empty. With I empty, the equivalence forces every module to have zero identity, so all cohomology sheaves vanish and no component Tor test remains; no nonzero empty-base object is being discarded. No statement dispute, missing hypothesis or source correction was found. Every new proof step is under 2000 characters; the elementary label refers to the written argument from the supplied hypotheses and cited definitions, not to a general theorem being used without citation.

## Not duplicates

No new nodes were created.
