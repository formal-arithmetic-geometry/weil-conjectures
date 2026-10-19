# Stage-1 worker report

Item: lem-per-ind-etale-closed-support-base-change. Group N6. Date 2026-10-18.

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-ind-etale-closed-support-base-change.json`: statement, split; retained the statement verbatim; eleven proof steps using existing nodes. Mathlib searches give no match.
- `citations.json`: one verbatim statement excerpt for every step/dependency pair.
- `searches.jsonl`: the five actual search-command records. The existing imported searches were replaced by this item's logged searches rather than being attributed to N6.
- `report.md`: this report. `build_split.py` is a sandbox-only preparation script.

No new nodes and no new Mathlib leaves. No unit or chapter record changed.

## Attachments

None. Searched the read-only slopmaster2 `WeilConjectures/` tree for the item id and the `(blueprint: lem-per-ind-etale-closed-support-base-change)` tag, and for ind-etale, costalk, extraordinary, supported/closed base change, and upper-shriek/base-change names. The localization and compact-support formalism declarations are not this bounded-below, arbitrary-complex, ind-etale closed-support interface. They do not provide an attachment.

## WANTED

None. The sources used are present locally.

## What needed correction

The item arrived unsplit, with no proof or proof dependencies. Its statement is retained exactly. Its source does not state the whole interface as one named theorem: it is an agent-formulated assembly of Stacks 03Q9, 0A45 and 09XQ. The proof is therefore honestly marked `proof_origin.by = agent`.

Two tempting shortcuts were avoided in the proof after reading the existing statements. `lem-pur-support-localization-triangle` and `det-lem-formal-closed-support-adjunction` concern the pro-etale site, so neither can be substituted for the specified small-etale functor. `lem-exc-closed-support-triangle` concerns an unbounded abstract right adjoint, whereas the item specifies the right derived supported-kernel functor on D+. Steps 2–3 verify that specified functor and its counit directly from existing general inputs. Also, `lem-weil-pbc-strict-local-base-change-closed-stalk` is only about sheaves in degree zero. Step 7 instead cites `lem-weil-pbc-strict-local-base-change-global-homology`, whose statement quantifies over every bounded-below abelian complex and every integer degree.

The local source citation for inverse-image stalks was corrected while preparing the split: the verified Stacks tag of `lemma-stalk-pullback` is 03Q1. No source statement was changed. There is no statement dispute.

## Mathlib and duplicate searches

The search command was used for LeanFinder twice (different phrasings), Loogle, grep and LeanSearch, and every result was read. The first phrasing returned scheme-limit and differential statements, Loogle returned ordinary topological stalks, and LeanSearch returned structure-sheaf restrictions and stability of scheme immersions. The second LeanFinder phrasing returned `localCohomology`, its ideal-power variants, and structure-sheaf adjunctions. Algebraic ideal-power local cohomology on modules over a ring does not state small-etale supported cohomology or its ind-etale base-change mate. The grep returned only manifold bordism documentation using the word “extraordinary”. None is an exact match or a one-line specialization. Exact queries and actual hit names are recorded in the item's `mathlib_searches` and in the command log.

Searched the whole DAG by ind-etale, strict-local, closed support, the cited Stacks tags, and relevant statement titles; ran `tools/blueprint_refs.py ancestor` and whole-blueprint searches for ind-etale, strict-local invariance, closed support base change, closed etale support, and closed-support right adjoint. The ancestor is `lem-per-artin-gabber-affine-curve`. Read the chapter and unit records and the current main-20261015 ancestor text. The existing `blueprint.from` locality provenance is retained, and `same_as` is empty. The split supplies a generic locality input below the perverse unit, not a replacement of either Fourier/perverse unit step. Off-unit statement inputs are declared in `split_report.tool_uses` with their step numbers.

## Not duplicates

No new nodes. In particular the strict-local invariance assertion reuses `lem-trf-ind-etale-strict-local-invariance`; exchange coherence reuses `lem-kun-derived-exchange-cube`; module/abelian exchange comparison reuses `lem-weil-pbc-exchange-forget-coefficients`. The bounded-below supported triangle is a short exact sequence construction from existing statements, not a newly named copy of the unbounded closed-support triangle.

## Unfinished work

None at stage 1. This delivery proves no Lean declaration and runs no compiler. All lower lemmas remain in their existing DAG states.

## Review by N6

I read Stacks `etale-cohomology.tex`, Tag 03Q9 (`theorem-higher-direct-images`), including its derived assertions and the construction on a bounded-below injective complex; Tag 09XQ (`lemma-sections-with-support-acyclic`) and its support-adjunction proof; and Tag 0A45 (`lemma-cohomology-with-support-triangle`) and its short-exact-complex proof. These have no constructibility hypothesis. For strict-local geometry I read `algebra.tex`, Tags 05WR (`lemma-quasi-finite-strict-henselization`) and 0GIP (`lemma-base-change-strict-henselization-quasi-finite`), including the filtered-colimit case. I also read Tag 04CA (`proposition-closed-immersion-pushforward`), the Noetherian topology statements in `properties.tex`, and the composition-of-exchange discussion in `cohomology.tex`. The proof follows the source's supported-kernel and strict-local route, and its extra canonical-map argument is explicitly agent-written. There are no new node statements to audit against a separate source.

I opened every cited node and checked its statement, not its proof. Step 1 uses the open/closed base-change statements for the two immersions and the Noetherian open-subscheme theorem for quasi-compactness. The diagonal of an open immersion is explicitly identified with an identity, which checks quasi-separatedness directly from the cited definition. Thus the qcqs hypothesis needed later is available even when T is not separated.

Step 2 uses the supported-kernel adjunction exactly for its abelian Hom bijection and exactness assertion; it writes out why the bijection restricts to A-linear maps by testing the action of each scalar. The module forgetful functor's exactness, enough injectives for constant-ring module sheaves, and the general bounded-below derived-adjunction theorem supply precisely the specified derived right adjoint and its counit normalization. This does not assume an injective module sheaf has injective underlying abelian sheaf. Step 3 uses the module restriction-kernel lemma for surjectivity on every etale object, etale restriction preserving injective modules to compute the open derived image, the bounded-below injective representative and right-derived comparison statements, and the short-exact-complex triangle theorem. These give the displayed triangle for the item's actual functor, including the kernel-inclusion counit.

Step 4 uses the closed supported-sheaf equivalence, the closed-pushforward stalk formula and inverse-image germ formula, and the underived exchange's representative-section formula. At points on the closed subscheme this is the identity on the original stalk; outside it both stalks vanish. Thus stalk conservativity proves invertibility of the canonical closed comparison, not merely existence of some isomorphism. Closed direct image exactness was established in Step 2, and inverse image exactness is cited here. The exact-adjunction localization interface gives the ordinary closed inverse-image/direct-image adjunction on D+ with its termwise counit. That counit is an isomorphism, so the adjunction Hom bijection proves full faithfulness on D+, and the left inverse proves reflection of derived isomorphisms. Step 5 is the explicit transpose formula of the cited mate definition; it fixes the counit identity before any invertibility argument.

Step 6 takes exactly the strict-local isomorphism, over the base, asserted by the existing ind-etale invariance node. The hypothesis holds because g is locally ind-etale, with both geometric points defined using the same field. Base-changing this isomorphism gives the open-source isomorphism, and the local exchange becomes the identity under those equivalences. Step 7 invokes the existing strict-local global-homology theorem only for the qcqs open maps proved in Step 1, and uses its all-complex/all-integer statement. The natural global-sections/closed-stalk isomorphism converts those maps to closed-stalk isomorphisms. I did not promote the sheaf-only closed-stalk node to a theorem about complexes.

Step 8 writes the exact exchange-cube equation and explains each of its three already invertible factors at the closed point. The inverse-image germ, exact-stalk and composition statements identify the fourth factor with the original exchange stalk. Derived stalk conservativity is used only for abelian complexes; the separate constant-coefficient exchange comparison then transfers the result to modules. Its statement both compares the specific mate maps and reflects their invertibility, so this step makes no unsupported assertion about preserving injectives under coefficient forgetting.

Step 9 uses exact pullback preserving distinguished triangles and the TR3 axiom after rotation. The right square commutes by the exchange's transposed-counit formula and the adjunction triangle identity. Full faithfulness from Step 4 lets any first component be written as a pushed-forward map; the adjunction bijection then identifies it with the beta fixed in Step 5. Step 10 cites both the long exact cohomology theorem and its naturality ladder, applies the five lemma to the five displayed consecutive terms, and uses cohomology detection of derived isomorphisms and the closed left inverse. Step 11 spells out the composition transpose, which is g2* g1* of the original counit. Its shift check uses the same supported-kernel inclusion on shifted injective complexes, so all integer shifts, not just positive ones, are covered. The remaining equality of transposes is elementary use of the mate bijection.

I checked B–E of the delivery-errors checklist against these files: no new statement-only or duplicate-node issue arises, every non-elementary input is in `uses`, quotes in `citations.json` are literal statement excerpts, and no step invokes a result from inside another node's proof. All steps are below 2000 characters; the comparison and canonical-map inputs have their own existing nodes. The small cases are Z empty (zero supported functors), Z=T (both supported functors are identity), the zero coefficient ring (zero categories), g an identity or an open localization, and K a shift in any integer degree. The constructed mate gives the expected identity or zero map in each case. Arbitrary bounded-below complexes, nonconstructible sheaves, nonreduced bases, and coefficient torsion at residue characteristic were never excluded. Affineness of g is retained as stated even though strict-local invariance needs only local ind-etaleness.

During self-review I added the explicit long-exact-cohomology and cohomology-detection citations to Step 10 and made Step 9's use of full faithfulness explicit, including the exact-adjunction localization that establishes it in Step 4; these are needed to justify the five-lemma and transpose arguments rather than citing a definition for them.
