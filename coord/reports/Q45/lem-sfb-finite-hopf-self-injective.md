# Worker report: lem-sfb-finite-hopf-self-injective

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-finite-hopf-self-injective.json: existing statement, now split; no Mathlib match. The statement and its statement dependencies are unchanged.
- dag/nodes/sec-six-functors-basics/lem-sfb-finite-hopf-frobenius-form.json: new statement-only structural lemma, unsplit; no Mathlib match.
- citations.json: the two proof-node citations, with literal statement excerpts.
- searches.jsonl: genuine search results recorded by the required msearch command; the original item's earlier search records were retained.
- report.md: this report and author's review.

There is one new node and no new Mathlib leaf.

## Attachments

None. Searches of lean/WeilConjectures for the exact blueprint tag, HopfAlgebra, Hopf algebra, and self-injectivity found no declaration proving the item. Module.exists_bijective_comp_mulLeft in WeilConjectures/RingTheory/FrobeniusForm.lean assumes a finite free extension of domains with the larger ring a PID, so it does not prove this statement for finite Hopf algebras with nilpotents.

## Wanted literature

WANTED: Julien Bichon, Faithful flatness of Hopf algebras over coideal subalgebras with a bimodule conditional expectation, arXiv:2301.05480v2, section 3 first paragraph, for lem-sfb-finite-hopf-self-injective. The node already names literature/bichon-faithful-flatness_arXiv-2301.05480.pdf, absent locally. I read https://arxiv.org/html/2301.05480v2 and verified the self-injectivity assertion. The assembly proof is marked agent, since this remark does not give it.

WANTED: Siqi Clover Zheng, Frobenius Algebra Structure in Hopf Algebras and Cohomology Ring with Poincare Duality (17 October 2020), Theorem 4.15, printed p.10, and proof of Theorem 4.8, pp.9-10, for lem-sfb-finite-hopf-frobenius-form. Proposed local path: literature/zheng-frobenius-algebra-hopf-2020.pdf. I read these results online at https://math.uchicago.edu/~may/REU2020/REUPapers/Zheng,Siqi.pdf without downloading a document. Theorem 4.15 gives a product pairing from a nonzero dual integral, and the proof of 4.8 constructs the injective map to the dual; finite dimension makes it bijective. There is no Stacks tag for this Hopf-algebra theorem, and no unrelated tag is substituted.

For the next worker, the structural input can be proved by equipping the finite dual with its Hopf-module structure, applying the fundamental theorem of Hopf modules (4.13), obtaining the one-dimensional integral space and invertible antipode (4.14), and using the nondegeneracy argument of 4.8. This route is source guidance for the unsplit node, not an additional assertion in its statement.

## Problems found and corrections

No statement dispute: the imported extension condition is true and remains unchanged. In particular arbitrary, possibly infinitely generated, modules are still quantified over. The item had no proof, and the source remark alone was not a split. I supplied the extension argument rather than creating a node that merely restates self-injectivity.

The inherited blueprint chain has from.node = null. The required ancestor command also prints None; the chain passes through earlier created nodes and never reaches an imported blueprint record. I retain that result and the inherited via list, adding the item at the front for the new node. The source location remains the supporting-input chain under det-thm-sf-ctf-stability-direct-images proof (3). I read the latest blueprint unit, chapter and direct-image proof, as well as their DAG records. Those generic-algebra prerequisites are below the unit's route. The unit record still names the older chapter sec-six-functors, while the item's fixed chapter is sec-six-functors-basics; no chapter, unit record, source field, or maintainer field was changed.

## Mathlib searches and reuse

Every new search was made with the required msearch command and appears in searches.jsonl. The new structural lemma has LeanSearch, Loogle, LeanFinder with two distinct wordings, and source-grep searches. All services responded successfully. The item retains its old searches and records the fresh ones. Searches found Hopf constructors and antipode identities, not a Frobenius-functional existence theorem. The potentially relevant LinearMap.BilinForm.toDual (Properties.lean:351) assumes an already nondegenerate form; traceForm_nondegenerate (Trace/Basic.lean:504) assumes a separable field extension. Neither produces the required form on a general finite Hopf algebra. A search for linear-functional extension did find LinearMap.exists_extend and Subspace.dualRestrict_surjective; no new node was made for this fact, since the existing basis-extension leaf supplies the elementary basis construction directly.

## Not duplicates

lem-sfb-finite-hopf-frobenius-form vs lem-sfb-finite-hopf-self-injective: the new node asserts a bijective product-pairing map to the field-linear dual; it asserts no extension property for modules. The item proves that property by constructing the extension from the pairing and an independently extended field-linear functional.

lem-sfb-finite-hopf-frobenius-form vs lem-weil-coefficient-frobenius: the existing blueprint node concerns the specific arithmetic coefficient rings A_(E,n), E and Qbar_l and their module/derived duality, not product pairings on arbitrary finite commutative Hopf algebras over any field.

lem-sfb-finite-hopf-frobenius-form vs lem-sfb-hopf-relative-kernel-shear: the existing node gives tensor-product trivializations of Hopf quotients, not a functional identifying an algebra with its linear dual.

Whole-DAG searches for Larson, Sweedler, Frobenius algebra, Frobenius pairing, the proposed id and the source name, plus blueprint_refs searches for Hopf, Frobenius algebra, Frobenius pairing and self-injective, found no existing node supplying the new statement. There are no same-Stacks-tag pairs for the new node. Reused lem-weil-pbc-vector-space-basis-through-vector rather than creating any basis, retraction or linear-functional-extension node.

## Review by Q45

I read Bichon's section 3 remark for the item and Zheng's Theorem 4.15 and proof of 4.8 for the new structural input. Both statements allow any base field; neither requires characteristic zero, algebraic closedness, separability, reducedness, or semisimplicity. The Hopf convention in the new node is copied in full from the item, so the new node introduces its own objects and does not depend on its parent. The full finite-basis hypothesis is preserved. Hom_k(H,k) and the functional's bijection are explicitly defined, with no unnamed Frobenius-algebra notion or integral left in the statement.

Step 1 takes exactly the bijective product-pairing map from lem-sfb-finite-hopf-frobenius-form. Its hypotheses are precisely the Hopf structure and finite basis already assumed. The additional assertion of linearity follows by evaluating lambda on h(a+b) and h(ca); it is not a claim taken from a definition-only citation.

Step 2 uses the actual statement of lem-weil-pbc-vector-space-basis-through-vector, which includes every independent subset, and includes existence of a basis by taking the empty set. I read that node in full and checked Module.Basis.extend, coe_extend and subset_extend at VectorSpace.lean:52,62,90 and exists_basis at line 176. These have arbitrary vector-space dimension. The image of the basis is independent because any finite relation in the image pulls back through injective j. The assigned values are well-defined because j is injective. Unique finite expansions then give t and t composed with j = lambda composed with f. No finite-coordinate retraction lemma is misused for infinite U or V.

Step 3 is a direct formula, with no extra black box. The expression h maps to t(hv) is k-linear by the restricted k-module structure and the module scalar laws. Bijectivity of Phi defines g(v); evaluating on every h proves its additivity and its H-scalar law. Associativity gives (ha)v = h(av) and h(ag(v)) = (ha)g(v). This verifies H-linearity without claiming an unexplained transport between module structures on a dual.

Step 4 checks the extension at every h, using exactly H-linearity of j and f and the identity for t proved in step 2. Injectivity of Phi gives g(j(u)) = f(u). The formulas include the zero module, the zero map and the identity inclusion. Arbitrary-dimensional U and V are handled by unrestricted bases and finite sums.

For small cases of the new input, H=k has lambda equal to the identity and Phi the usual k-to-dual identification. For the finite constant group algebra of functions k^G, summing coordinates gives the nondegenerate diagonal product pairing in every characteristic. For H=k[t]/(t^p) over characteristic p with primitive t, coefficient of t^(p-1) gives the anti-diagonal nonsingular pairing; this checks that nilpotents and modular characteristic are allowed. An algebra such as k[x,y]/(x,y)^2 need not have such a pairing; we have not removed the essential Hopf hypothesis. A zero algebra cannot satisfy the stated unital counit to a field.

I checked delivery-errors B through E against the files: the sole new node is statement-only, all objects and tensor/basis conventions are introduced, its sources have actual theorem numbers, and its searches were executed and recorded with their real queries. No new node is an elementary consequence or a clause of the item. The two cited statements are exactly what the corresponding steps use; citations.json contains literal excerpts. The remaining steps are explicit elementary calculations from preceding choices. The graph points from the item to the structural theorem and existing basis leaf, never back to the item. No step exceeds 2000 characters, no SGA source is used, and no Lean or compiler command was written or run.

## Unfinished work

The new Frobenius-functional theorem is intentionally unsplit, as required for a one-level split; it is queued for a later worker. No part of the item's assembly proof is omitted.

## Validation

The required deliver.py --no-push finished with exit code 0 and printed OK (not pushed): server preflight passed, including the DAG and split checks. The two citation excerpts were also verified as literal substrings of their cited node statements. No local checker, compiler, Lake, build, or repository git command was run. The push command performs the same preflight before publishing the delivery branch.
