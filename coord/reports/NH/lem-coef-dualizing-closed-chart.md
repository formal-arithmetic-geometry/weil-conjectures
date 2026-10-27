# lem-coef-dualizing-closed-chart — NH stage 1

## Files written

- `dag/nodes/sec-six-functors/lem-coef-dualizing-closed-chart.json`: eight-step split; no new nodes, no new Mathlib leaves. The mathematical statement and statement dependencies are unchanged.
- `citations.json`: one literal statement quotation for every node used in every numbered proof step.

## Attachments

None. I searched `lean/WeilConjectures/` for the item id and the closed/dualizing/coefficient terminology. The library contains constituent closed-immersion and exceptional-pullback APIs, including the bounded-below upper-shriek instance in `SixFunctors/Etale/Derived/UpperShriek.lean`, but no project declaration gives every clause of this item. Constituent APIs are not an attachment of the item.

## WANTED

None. The blueprint and the Stacks sources needed by this argument are available locally. The proof is labelled agent-written because the blueprint gives the factorization and counit outline and I supplied its detailed module and boundedness argument.

## Audit findings and corrections

The imported item had no proof. Its statement is correct, with the conventional equality of derived objects and functors understood through the canonical identifications it specifies. I made the omitted comparison map explicit: for theta: omega_Y -> I omega_P the untransported equation has a final factor F_Y(theta); after identifying by theta this is exactly the displayed equation of the item. No mathematical clause was changed.

I did not use the proof of `lem-exc-closed-ambient` as evidence for exactness or boundedness: that node's statement asserts existence of the right adjoint only. Instead, exactness comes from the stated abelian support adjunction, is transferred to modules by their explicit kernel/cokernel construction, and the lower bound comes from the general exact-derived-adjunction bound node. Likewise, I did not confuse ordinary O-module pushforward nodes with constant-coefficient small-etale pushforward. The pro-etale exactness nodes are not used. No coefficient comparison is used to prove that either representing object lies in D+.

## Searches and reuse

The entire DAG was searched by ids, titles and statements for affine polynomial charts, closed exactness, finite/proper immersions, adjoint bounds and unique adjoints. `tools/blueprint_refs.py search` was run with `dualizing affine`, `dualizing closed`, `affine closed`, `affine finite type`, `04C4`, `closed exact`, and `adjoint t-exact`. The nearest blueprint ancestor is `lem-coef-finite-dualizing`, and the existing `from.place` identifies its second proof paragraph. There is no blueprint node stating this whole package in another form; `same_as` remains []. The source ancestor's paragraph 2 and paragraph 3's counit sentence are exactly the route followed.

The required Mathlib search command was run with LeanFinder twice (different phrasings), LeanSearch, Loogle, and grep. The exact queries and summaries of actual hits are appended to the item and recorded by the command in `searches.jsonl`; all services answered. The hits concerned affine space, Spec, structure-module pushforward and abstract module-sheaf adjunctions. They do not state the complete small-etale dualizing-chart result. Earlier searches imported with the item were retained. No new node needs a separate search. In particular no elementary specialization or clause of the item was repackaged as a new node.

## Not duplicates

No new nodes. Existing finite-type coordinate-algebra, affine closed-immersion criterion, finite/proper closed immersion, exact abelian support, derived exact functor, and unique-adjoint nodes are reused directly.

## Review by NH

I read the standing brief, the stage-1 contract, the three blueprint levels in SETUP, GOAL, and delivery-errors B–E (including their retained copy), as well as the item's chapter and unit records. This is not a unit-key node, so no unit realization file is changed. I read the current ancestor proof in main-20261015, particularly the choice of the closed affine-space chart, the composition of ambient right adjoints, and the explanation of the structure-morphism counit. The split keeps that route, with no SGA source.

Step 1 uses `lem-pc-affine-finite-type-algebra` for precisely the finitely generated coordinate algebra; its hypotheses are an affine scheme and a finite-type map to Spec k, both given. I read its source Stacks 01T2, lemma-locally-finite-type-characterize. The finite-type algebra definition actually states existence of a surjection from a polynomial ring, so this does not assume an unrecorded embedding theorem. `def-sbc-affine-space` identifies the affine-space chart with that polynomial spectrum; `def-weil-affine-spectrum` supplies the contravariant morphism over k. `lem-weil-pbc-closed-immersion-affine-cover-criterion` actually permits the one-element affine cover and assumes the section map is surjective, which is exactly the chosen map. I read 01QO, lemma-closed-immersion, and the quotient example 01IG in schemes.tex.

Step 2 uses the existing finite-closed-immersion node and clause (a) of the proper-closed-immersion node, which include respectively finiteness and properness/finite type. I checked morphisms.tex labels lemma-closed-immersion-finite (035C) and lemma-finite-proper (01WN), and the proper-closed node cites 01W5. The remaining polynomial geometry is written out: the finite generators give finite type, and the diagonal quotient gives separatedness. The affine-cover criterion used here really gives closedness for a surjective polynomial quotient. This is a direct coordinate calculation, rather than a new geometric lemma hidden in the step.

Step 3 uses the finite-stage ring clause of `def-weil-l-adic-coefficient-extension`, not the unrelated finite-field definition as proof of finite coefficients. I read its entire statement. The reviewed `lem-weil-boundary-etale-adjunction-restriction` states exactly Noetherianity, compactifiability, and preservation of D+ by both sides of the ordinary adjunction for separated finite-type k-morphisms and finite coefficient stages. I read its statement and reviewed proof, including the prerequisites for the cohomological bound. Applying it to a_Y and p is legitimate after steps 1–2; R_s is degree zero. This yields lower boundedness of both structural dualizing objects independently of reduction A -> B. Its source is the local blueprint discharge node, not a prohibited trace reference.

Step 4 uses the *statement* of `lem-pur-etale-supported-kernel-adjunction`: it explicitly asserts exactness on abelian sheaves. I read Stacks 09XQ, lemma-sections-with-support-acyclic, and the closed-pushforward section, especially 04FX; I also checked that 04C4 is a big-site statement and did not cite it for the small-site assertion. `def-weil-pbc-direct-image` explicitly says the module direct image commutes with forgetting scalars. `def-weil-sheaf-of-modules-category` explicitly constructs kernels and cokernels; I checked Modules on Sites 03DA, lemma-abelian. These statements justify the few-line transfer of exactness to modules, with no assumptions about constructibility or flatness.

Step 5 uses exactly the termwise realization and quasi-isomorphism preservation stated in `lem-weil-pbc-exact-functor-derived-factorization`, and the cohomology comparison stated in `lem-weil-pbc-exact-functor-complex-cohomology`. I read derived.tex 015F, lemma-right-derived-exact-functor (which covers *unbounded* complexes), and homology.tex 010N, lemma-exact-functor. The supplied compact-support definition really is Rr_* Dj_! on a chosen compactification. For (id,i), extension by zero is the identity, so the argument computes the actual unbounded candidate rather than merely its D+ restriction.

Step 6 uses `lem-exc-closed-ambient` only for existence of i_* ⊣ I. Clause (1) of `lem-pur-exact-derived-adjunction-bounds` says that the right adjoint of a termwise exact derived functor preserves every lower bound. Its hypotheses are supplied by steps 4–5, not assumed. I read its full statement and proof; the orthogonality argument is independent of coefficient change. In particular this is stronger than the mere preservation of D+ required here, and it applies to arbitrary module complexes.

Step 7 uses `lem-amb-etale-compact-comparisons` for exactly the D+ composition comparison: its statement names composable compactifiable separated finite-type morphisms between Noetherian schemes. Steps 1–3 verify all those hypotheses, including for P; step 5 supplies Ri_!=i_*. I read more-etale.tex 0F7H–0F7J (the compactification definition, well-definedness, and lemma-shriek-composition) and the cited node's statement. Full inclusions into the ambient category mean the restricted adjunction Hom bijections have the original counits; no new comparison of counits is assumed here.

Step 8 uses the exact composite Hom bijection and counit formula stated in `def-weil-pbc-composite-adjunction` and the *counit-compatible* unique isomorphism stated in `det-sp-unique-right-adjoint`. I read the latter's blueprint statement in main-20261015. Both candidates are functors on D+ by steps 3 and 6, so the abstract uniqueness result applies on that category; there is no attempt to infer equality of ordinary unbounded adjoints from only bounded tests. The equation with theta is written with its correct source, and then expressed under that identification as in the item. This also explains why the structural counit is the closed counit followed by the affine-space counit.

I checked small cases: r=0 gives P=s and identity affine-space projection; an empty affine Y is Spec of the zero algebra and the same surjection/adjunction argument applies; no nonempty hypothesis enters exactness or uniqueness; m=n leaves everything unchanged and is not used as a reduction argument; singular and nonreduced Y are allowed because only a polynomial quotient, not a regular immersion, is used. The proof never assumes i^! is exact, only that it preserves lower bounds. All steps are shorter than 2000 characters. Every node in a step's uses list has a verbatim statement quote in citations.json. I checked that the reused nodes do not depend back on this item. Generic off-unit prerequisites are declared in split_report.tool_uses; they realize the given closed-chart route and do not replace a unit step.

## Unfinished work

None for this stage-1 split. No Lean was written or compiled, and no repository or launcher file was changed.
