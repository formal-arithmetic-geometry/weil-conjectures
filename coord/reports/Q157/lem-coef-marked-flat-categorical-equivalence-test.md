# Q157: lem-coef-marked-flat-categorical-equivalence-test

## Files written

- dag/nodes/sec-six-functors/lem-coef-marked-flat-categorical-equivalence-test.json — statement, split; no exact Mathlib match. Seven proof steps, using existing nodes only.
- citations.json — a verbatim statement quote for every step/node pair.
- report.md — this report. New nodes: 0. Mathlib leaves: 0.

## Attachments

None. Searches of /home/ubuntu/weil-src-slopmaster2/WeilConjectures for the exact blueprint tag, marked simplicial categories and categorical equivalences found no declaration giving this statement. Mathlib CategoryTheory.Equivalence.core is about ordinary categories, not quasicategories and marked weak equivalences; it cannot attach this item.

## Wanted literature

WANTED: Jacob Lurie, Higher Topos Theory, Remark 3.1.3.1, Lemma 3.1.3.2, Proposition 3.1.3.3 and Definition 3.1.3.4, for lem-coef-marked-flat-categorical-equivalence-test. The PDF is not archived under literature/. I read these portions online at the source URL already in the item. No source was downloaded or written into the shared repository. proof_origin remains explicitly agent-written.

## Corrections and route

The statement is unchanged and is true. Its inherited source lists HTT Proposition 3.2.2.14, but that proposition concerns mapping simplices over a simplex. It is not needed for the absolute test. The relevant direct argument is the currying and inverse construction in Lemma 3.1.3.2 and Proposition 3.1.3.3. The maintainer-owned source field was preserved; the steps and proof_origin give the corrected proof references.

I read the current main-20261015 proof of prop-coef-integral-exceptional-adjoint, especially its second paragraph and displayed finite-stage mapping-complex adjunction, as well as the assigned unit and chapter. This is the ancestor retained in the imported item's blueprint.from. The absolute marked/Joyal test is the prerequisite already extracted along that ancestor's cartesian cone-fiber comparison branch; this delivery makes no new unit-level assertion or route replacement.

No existing sandbox node or report was present at resumption; only searches.jsonl existed. I retained and read those search records, including the two distinct semantic phrasings, the empty Loogle result, and the JoyalTrick grep hits. The additional semantic query returned ordinary cores, SSet.QCat and nerves; reading Core.lean:253 and Quasicategory/Basic.lean distinguishes these from the desired theorem. Reading JoyalTrick.lean:40 confirms that it is a generic lifting argument, not this simplicial comparison. Prior searches recorded in the repository item were preserved as inherited records, not claimed as new Q157 searches.

## Not duplicates

No new node is created. Whole-DAG statement searches for cores, categorical equivalences and marked tests found the existing functor-equivalence, marked-anodyne and homotopy interfaces used here. blueprint_refs.py searches for categorical equivalence found no imported blueprint node stating this test; blueprint ancestry is prop-coef-integral-exceptional-adjoint and same_as remains empty.

## Review by Q157

I read HTT Remark 3.1.3.1 and the proof of Lemma 3.1.3.2 and Proposition 3.1.3.3 online, and compared them with every cited DAG statement. There are no new-node sources to certify. The original two markings and all three assertions are retained; in particular arbitrary A and B are not assumed quasicategories in the core test. I checked the contract's B--E requirements against the actual node: no unsplit placeholder, no restated child, no hollow construction and no unrecorded Mathlib query is introduced.

Step 1 uses the marked-anodyne statement's precise assertion that Map-sharp is the core of Map-flat, and the point-model statement's separate natural-natural identity. Minimal markings make Map-flat(K-flat,Q-natural) literally Fun(K,Q); preservation is automatic only because both product markings here are minimal. I did not apply the natural-natural identity to an arbitrary simplicial domain. Both identities preserve the specified restriction maps.

Step 2 uses condition (ii) of lem-coef-joyal-functor-equivalence-test for the given t-star, not an unspecified equivalent functor category. The functor-cone statement supplies the Kan cores and pointwise equivalence criterion. The triangle-calculus statement says exactly that triangle composites represent composition; together with the two inverse witnesses this checks that the evaluated natural equivalences restrict to homotopies of cores. The cited simplicial-homotopy-equivalence statement then supplies the weak homotopy equivalence, including empty cases. These are generic tools, and the two off-unit tools are declared in split_report.tool_uses.

Step 3 applies the hypothesis to Fun(K,Q), which is a quasicategory by the existing functor-equivalence theorem. The degreewise currying identity commutes with t-star, so the resulting maps are postcomposition by p, not an unrelated map of spaces. Weak homotopy equivalence gives a component bijection. Its interpretation is spelled out by edge paths in a realization and horn concatenation in a Kan core; no equivalence of homotopy categories is inferred merely from a single equivalence of cores. The target tests Fun(K,Q) for all K are essential.

Step 4 takes K=E for surjectivity and K=D for injectivity. The actual equation p(sp)=(ps)p puts the images of sp and 1_D in the same component. The resulting quasi-inverse is for p itself. This is the short Yoneda argument written out from the already obtained component bijections; it is a proof step rather than a new node restating the desired converse. Applying the existing test's condition (ii) closes the arbitrary-domain case.

Steps 5 and 6 use the point-model statement's literal definition of weak equivalence by all Map-sharp tests. The minimal-natural and natural-natural identities from step 1 make these exactly the core tests proved in steps 2--4. In step 6 a simplicial map preserves inverse edges and witness triangles, which verifies preservation of natural markings using def-cbc-enhanced-diagrams-cones. No additional hypothesis, fibrant replacement comparison, or Cartesian-fibration statement is silently used.

Step 7 checks sizes and empty cases. Each exponent and each of D and E is small in the chosen containing universe. The existing functor test permits all sufficiently large universes, and the point-model theorem explicitly asserts invariance under enlargement. The only selected objects are identity functors, which exist for empty categories. For an empty-to-nonempty simplicial map, the empty target test fails as required; for empty-to-empty the tests are identities of points. Non-groupoidal examples, such as the identity on the nerve of [1], also agree: the markings on source and target differ but the tested core maps are identities by step 1. Thus the result is not confusing categorical equivalence with weak homotopy equivalence of underlying spaces.

Every step/node citation has a verbatim statement quote in citations.json. A read-only transitive dependency check of the cited nodes found no path back to this item. Each proof step is below 2000 characters; the only comparison proved inline is the short degreewise identity in step 1 and the routine currying identity in step 3. No long step hides a new theorem. No statement dispute was needed and no hypothesis was added or removed.

## Unfinished work

No mathematical part remains at this split level. The existing dependency nodes retain their own states. No Lean files were written and no compiler, Lake command or build was run. Delivery validation is performed by the required server-side tools.
