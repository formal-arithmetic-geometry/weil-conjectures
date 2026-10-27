## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-ringed-counit-from-cohomology.json`: statement, split; unchanged mathematical statement, four proof steps using eight existing nodes; no Mathlib match for the whole item.
- `citations.json`: one verbatim statement excerpt for every step/node citation.
- `searches.jsonl`: genuine msearch.py searches, including both semantic phrasings, Loogle and two source-grep queries. The item retains its inherited searches and appends this run's results.
- `report.md`: this report. No new nodes and no new Mathlib leaves.

## Attachments

None. I searched the actual read-clone `lean/WeilConjectures/` for the item id, blueprint tag, counit/cohomology and boundedness variants. No declaration there states the whole arbitrary-ringed-topos item. Affine-algebra, open-immersion and condensed adjunction counits impose extra hypotheses and do not give an attachment. Sorry declarations are not evidence of completion.

## Wanted sources

None. The proof source is available locally.

## Findings and corrections

The mathematical statement is correct as written: exact module pullback is the flatness hypothesis in Stacks Tag 0D7S, all cohomology degrees are quantified, and bounded below does not mean bounded above. No statement correction or weakening was made. The original item had no proof. I filled it using the pre-existing generic heart test after establishing its actual hypotheses, rather than duplicating that lemma or creating nodes for elementary specializations.

The inherited `blueprint.from.node` is null although its place and via chain identify the supporting input below `det-thm-sf-ctf-stability-direct-images`. `tools/blueprint_refs.py ancestor` also returns None. I retain this maintainer-owned field and the entire creation/source metadata. This is the same inherited issue noted by the accepted parent's review. I read the current blueprint through `literature/blueprint/latest/`, including `sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md` and the direct-images proof (3), plus the stored chapter/unit records. The current proof describes the direct-image route more briefly; this abstract ringed-topos tool does not change that route.

## Not duplicates

No new nodes. Whole-DAG and whole-blueprint searches for counit, truncation, the Stacks tag and lower cohomology bounds found the existing `lem-weil-pbc-heart-test-bounded-below` as the relevant generalization; I cite it. The item is not a new restatement of that generalization: verifying its exact-pullback, total-derived, bound and canonical-shift hypotheses is the content of steps 1–3. The neighboring unit-detection node concerns the unit on the other coefficient category, not this counit.

## Review by NQ

I read the full statement and proof of Stacks `sites-cohomology.tex`, Tag 0D7S, label `lemma-bounded-in-image-upstairs`, together with `lemma-upstairs` (0D7R), the neighboring unit case and the derived adjunction. I also read `derived.tex` Tag 05TC (`lemma-negative-vanishing`) and Tag 0A8D (`lemma-adjoint-is-exact`). The source's reduction to a bounded truncation and its finite cohomology devissage are exactly the argument packaged by the existing heart-test node. No SGA route is used.

For step 1 I opened all three cited statements. `prop-pur-kinjective-resolutions-exist` says precisely that modules on a small ringed site form a Grothendieck abelian category and have K-injective resolutions. The size hypothesis of this item applies separately to both ringed sites. `lem-weil-pbc-exact-functor-derived-factorization` supplies the triangulated termwise functor and its fixed shift comparison, not just an unnamed localization. `lem-weil-pbc-exact-functor-complex-cohomology` gives the natural cohomology comparison for this exact functor. Its right side vanishes for every degree below the given lower bound. These statements justify the assertions for all integers, with no positivity restriction.

For step 2 I read `lem-pc-right-derived-functor-triangulated`, which explicitly concerns the unbounded K-injective right derived functor of an additive functor and asserts triangle preservation and shift commutation. Its hypotheses follow from step 1 and additive module direct image. I also read `lem-pur-exact-derived-adjunction-bounds`: only its clause (1), preserving every lower bound, is used. I do not use its faithfulness, reflection or essential-image counit clauses. The given canonical adjunction and the termwise factorization of step 1 meet clause (1) exactly. Both composite and identity therefore restrict to the bounded-below category and satisfy the heart test's universal lower-bound assumption, not merely a bound on this K.

For step 3 I opened the ringed-topoi module-adjunction node and the entire statement of `lem-sp-canonical-right-derived-adjunction-shift`. The first applies to arbitrary ringed topoi presented by the small sites in this item and gives the actual tensor pullback/direct-image adjunction. Direct image is additive sectionwise. The second assumes an exact additive left adjoint and K-injective resolutions in its target; these have just been checked. Its conclusion retains the fixed K-injective shifts, so it proves compatibility for the specified counit, not for a replacement natural transformation with arbitrary components. I chose this generic exact-left-adjoint shift theorem rather than introducing unnecessary K-flat hypotheses.

For step 4 I opened the full heart-test statement. Its categories may coincide, its functors need preserve only lower bounds, and its transformation must commute with shifts; steps 1–3 verify each requirement. Its hypothesis on the individual degree-zero cohomology objects is verbatim the item's assumption. Its conclusion includes both the finite-truncation counit and the naturality formula written in the proof. With Psi the identity that formula has exactly H^m(c_m) as its first factor. It applies at every integer m. Thus the step uses the statement of the cited node, not an unpublished argument hidden in its proof, and establishes the actual counit at K.

I tested K=0, K a sheaf shifted to a negative or positive degree, f the identity, and a bounded-below K with infinitely many nonzero positive cohomology sheaves. For m below the lower bound the heart test includes the empty Postnikov interval; there is no induction starting at degree zero and no infinite-product argument. For f=id the construction gives the identity counit, as required. No constructibility, weak-Serre, cohomological dimension, conservativity or bounded-above hypothesis is introduced.

I checked B–E of `coord/delivery-errors.md` against the resulting files. There are no statement-only new nodes to audit, no duplicated or merely relabeled lemmas, and no step exceeding 2000 characters (lengths 579, 537, 522, 899). Every non-elementary invocation is an existing cited statement, with a literal excerpt in citations.json. The statement dependencies are unchanged and introduce the correct module coefficient categories. I followed each proposed proof citation's dependency closure and found no path back to this item. Generic off-unit uses are declared in split_report.tool_uses and preserve the geometric unit route. I made no repository or launcher edits and ran no Lean/compiler/Lake tool.

Mathlib searches were run through the required command and read. The first semantic phrasing returned localization, exact-derived shift and strict representative declarations; the second returned other topos/condensed counits. LeanSearch returned `CategoryTheory.Adjunction.derivedε`, which I read at Mathlib/CategoryTheory/Functor/Derived/Adjunction.lean:118–128: it constructs the counit and states its factorization, without a bounded-below cohomology detection result. Loogle returned no hits. The broad source grep returned elementary homology/quasi-isomorphism facts; the focused derived-category grep returned only the injective-subcategory equivalence's identity counit. None states the whole item or a one-line specialization of it. No unavailable service was represented as a negative result.

## Unfinished work

No mathematical work remains in the requested one-level split. Dry-run and push results are reported by the required delivery command.

The first dry run requested longer citation excerpts for step 1's module-category fact and step 4's heart test. I replaced both short fragments with their complete verbatim statements; the mathematical proof is unchanged.
