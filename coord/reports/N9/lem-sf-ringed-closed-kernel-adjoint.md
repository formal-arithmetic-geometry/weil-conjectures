# Stage-1 report: lem-sf-ringed-closed-kernel-adjoint

## Files written

- `dag/nodes/sec-smooth-purity/lem-sf-ringed-closed-kernel-adjoint.json`: statement, split into nine proof steps; not a Mathlib leaf. The support-kernel construction and all four unbounded adjunctions are proved from existing nodes. The statement and its hypotheses are unchanged.
- `citations.json`: one entry for every step/node citation, quoting that existing node's statement verbatim (including its hypotheses).
- `searches.jsonl`: the actual msearch log. Five searches were run and their hits read; the inherited questions have been retained and the grep result corrected to the three actual hits.
- `report.md`: this report. `write_split.py` is a sandbox-only reproducible authoring script, not a delivered project file.

There are **0 new nodes and 0 new Mathlib leaves**. The item already existed in the current repository and was unsplit; there was no earlier sandbox node, report, or search log to recover.

## Attachments

None. Searched the project source `WeilConjectures/` for the exact blueprint id, closed-kernel/support-kernel spellings, kernel/adjoint combinations, and the exceptional-operation vocabulary. No declaration there states the entire arbitrary-ring-sheaf construction with its unbounded adjunctions. Existing abstract geometric exceptional functors do not give this construction. The read-only upstream master is not used as proof evidence. The item's imported metadata has no Lean audit entry to expand.

## Wanted sources

None. All sources used are present in `literature/stacks-project/`.

## What was wrong or missing

The item had a statement and Mathlib searches but no proof. It is correct as stated: the quasi-compact complementary open is needed for the cited localization/exactness theorem, and small sites are needed for the K-injective existence theorem. No statement dispute was found. There is no new definition or imported statement change.

The blueprint unit's ambient closed/open Hom rewritings need actual adjunctions before the supported localization triangle. The current accepted ancestor `prop-sf-localization-all-stages`, Step 2, names this item for exactly that purpose. I read the main-20261015 ancestor proof as historical context and its current DAG replacement, and realize the latter's ambient-adjoint step. The proof does not invoke the supported triangle, or use finite-constant-coefficient statements for arbitrary ring sheaves. No forbidden SGA route is used.

The ringed open-closed theorem alone does not explicitly state that the ordinary open direct-image counit is invertible. Step 2 supplies the short sectionwise proof using the existing open-comparison equivalence and the direct-image formula; it is not asserted from the wrong node. The finite-ring `lem-exc-proetale-derived-adjunction-triangle` has narrower hypotheses and is not used to establish the arbitrary-ring item.

## Unfinished work

None at stage 1. No Lean was written or compiled. The remote dry run and delivery results are recorded below after they finish.

## Not duplicates

No new node was created, hence there are no new/existing same-tag pairs. Whole-DAG concept and tag searches, and blueprint searches for support-kernel, closed-kernel and support kernel, found no blueprint statement of this full arbitrary-ring item. The existing finite-ring derived-adjunction node does not cover arbitrary ring sheaves or all of this item's open counits and adjunctions. The general ringed-topoi adjunction and existing K-injective nodes are cited rather than restated as new nodes.

## Review by N9

I read the worker contract, the three fixed/followed/free levels, the localization chapter and unit, the current ancestor's ambient-adjoint step, and delivery-errors B--E. For the item I read Stacks `proetale.tex`, Tag 09AA (`lemma-closed-immersion`), 09BM (`lemma-closed-immersion-complement-retrocompact-exact`), 09BN (`lemma-open-immersion`), and 09AH (`lemma-ses-associated-to-open`). I also read `sites-modules.tex` Tag 03D7 (`lemma-adjoint-pullback-pushforward-modules`) and `lemma-restrict-back`; `derived.tex` Tags 070I, 070K, 08BJ, 014X and 015F; `sites-cohomology.tex` Tag 07A5; and `injectives.tex` Tag 079P. There are no new-node sources to audit.

Step 1 uses `lem-weil-pbc-ringed-topoi-module-adjunction` for the adjunction over an arbitrary ring sheaf (the structural ring map here is the identity), `lem-weil-pbc-proetale-ringed-open-closed` for the exact closed pushforward, exact open extension, closed counit and actual short exact sequence, and `lem-weil-pbc-proetale-immersion-limit-preservation` for exact module inverse images. I checked their statements allow arbitrary schemes and arbitrary commutative ring sheaves, with a quasi-compact complementary open exactly as assumed. The tensor identification is the two explicit inverse maps, not a replacement of coefficient categories.

Step 2 uses `lem-weil-pbc-proetale-ringed-open-comparison` for the actual inverse-image/slice-restriction comparison and `def-weil-proetale-inverse-image` for direct-image base-change evaluation. I checked that the latter actually states the section formula, and did not cite a definition for a hidden theorem. For an object already over U, its fibre product with U is itself; the counit is evaluation under that identification. This proves rather than merely assumes the open counit isomorphism. The open triangle identity then proves that the restricted unit is invertible.

Step 3 uses the immersion theorem's exactness to restrict the kernel, and the ringed localization theorem's actual short exact sequence at that kernel. Thus its supported closed unit is invertible. This is a short deduction from the cited statements, not a new support lemma. Naturality and additivity are obtained from the universal property of kernels.

Step 4 uses the closed counit and disjointness in the ringed localization statement, and the ordinary ringed adjunction of Step 1. I checked the directions of both maps in the Hom bijection: the forward map is i*(g) after the inverse counit, and the inverse is i_*(alpha) followed by the inverse supported unit and then the kernel inclusion. Naturality and the triangle identities explicitly verify the inverse maps. In particular the inclusion becomes the counit of i_* left adjoint to i^!_0, rather than being confused with the counit of i^* left adjoint to i_*.

Step 5 uses `prop-pur-kinjective-resolutions-exist` for arbitrary commutative ring sheaves on sites small in the fixed sheaf universe, and `lem-weil-pbc-exact-functor-derived-factorization` for the unbounded termwise exact functors. The latter states preservation of quasi-isomorphisms and the triangulated factorization, not merely a bounded-below version. The exactness hypotheses were established in Step 1.

Step 6 uses `lem-weil-pbc-kinjective-total-derived` for existence and evaluation on K-injectives and `lem-weil-pbc-right-adjoint-preserves-kinjective` with exact LEFT adjoint i_* for preservation of K-injectives. I checked the direction carefully; left exactness of i^!_0 alone would not establish that claim. The termwise functor respects homotopies, shifts and the cone matrices from `def-weil-abstract-derived-category`; this is the elementary additive cone argument, not a claim that i^!_0 is exact on the abelian categories.

Step 7 uses `lem-weil-pbc-kinjective-hom-derived` on both sides and `lem-weil-pbc-termwise-adjunction-homotopy` for the middle bijection. Their full statements apply to unbounded complexes and arbitrary additive adjunctions respectively. The right target i^!_0(I) is K-injective by Step 6. Tracking the identity across these precise bijections proves the derived counit formula.

Step 8 uses those same two Hom interfaces, `lem-weil-pbc-right-adjoint-preserves-kinjective`, `lem-weil-pbc-kinjective-total-derived`, and `lem-weil-pbc-exact-functor-derived-functor`. I checked all three exact-left-adjoint pairs separately: j! with right adjoint j*, i* with right adjoint i_*, and j* with right adjoint j_*. Exactness of j* and i_* then identifies their right derived functors with the termwise functors, whereas j_* need not be exact and its right derived functor is Rj_*. All derived Hom equalities compute maps into K-injective targets and have no boundedness requirement.

Step 9 uses the ringed localization theorem for its ordinary closed counit and disjointness, and the termwise exact factorization theorem. For the open derived counit I use the explicit counit calculation of Step 2 on a K-injective complex on U. It is a degreewise isomorphism, not a higher-direct-image vanishing assertion that would need an extra hypothesis on j_*.

I tested the construction at Z empty (kernel and exceptional inverse image zero), U empty / i the identity (kernel N and the identity adjunction), at B the zero ring (all module categories zero), and for a nonconstant B (every argument uses the pulled-back ring and no constants). A nonreduced closed immersion also causes no issue: the cited pro-etale statements concern closed immersions generally. None of these tests requires Noetherianity, finite type, boundedness or constructibility. Every cited statement was opened and its hypothesis checked; `citations.json` copies the complete statements verbatim so that C4 can also be checked mechanically. Proof-dependency union is exact. No proof step reaches 2000 characters, and no step conceals an independent comparison lemma. The only comparisons proved inline are the two explicit inverse tensor maps, open evaluation on a slice, and the kernel/adjunction identities.

All off-unit non-Mathlib interfaces are declared as generic tools in `split_report.tool_uses`, preserving the unit's closed/open Hom route. I reviewed the B1/D1/D2 traps: no statement-only helper was given a proof, no clause was moved to a restatement node, and no elementary two-line lemma was manufactured as a node. The source statement is unchanged and every new mathematical fact is either an existing cited node or an explicit short universal-property calculation. The dry run will check dependency cycles, route declarations and citation integrity on the server.

## Validation

The required server dry run exited successfully: `OK (not pushed) deliver/N9/lem-sf-ringed-closed-kernel-adjoint at f8e6fdeec3: preflight passed`. This ran the delivery preflight, DAG and split review on the server, and checked every verbatim citation. No local validator, compiler, Lake command, or git command was run.
