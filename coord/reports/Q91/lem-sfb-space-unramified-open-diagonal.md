# Stage-1 report: lem-sfb-space-unramified-open-diagonal

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-space-unramified-open-diagonal.json: existing statement node, now split; not a Mathlib leaf.
- citations.json: every step citation, with a verbatim quotation of its statement.
- searches.jsonl: actual searches made through msearch.py, including two semantic phrasings.
- report.md and write_split.py: report and sandbox-only preparation script.

No new nodes and no Mathlib leaves.

## Attachments

None. Searched lean/WeilConjectures for the blueprint id, unramified/diagonal phrases and AlgebraicSpace. Existing project proofs concern schemes, not the item for arbitrary algebraic spaces. Mathlib's FormallyUnramified instance at FormallyUnramified.lean:79 and isOpenImmersion_diagonal at :126 were read: neither supplies algebraic-space chart reduction.

## WANTED

None. All sources used are present in literature/stacks-project/.

## Issues found and corrected

The item statement is unchanged. Its local finite type and unramified definitions are scheme notions extended to algebraic spaces by the chart convention already in the statement. Step 1 spells out that convention, using the all-diagrams form of Stacks 03MJ and Definitions 03XF and 03ZH. This is not an extra assumption or a scheme-only interpretation of the conclusion. It avoids treating def-weil-finite-type-morphism as if that node alone defined morphisms of algebraic spaces.

The Stacks 05W1 proof invokes a scheme-diagonal immersion statement and then concludes an etale immersion is open. We use the direct flat, locally finitely presented monomorphism criterion (025G) instead. Monicity is proved by a projection. This supplies precisely the needed argument without any separatedness or global immersion hypothesis.

There was no earlier item, report or search log in the sandbox, and no running delivery was found at resumption. An interrupted search session had completed: its actual searches.jsonl records were read instead of repeating those searches.

## Unfinished work

None for this one-level split. The two generic algebraic-space inputs are existing DAG tasks and remain their owners' work. No compiler, Lake or Lean-writing operation was used.

## Blueprint and route

Read dag/chapters/sec-six-functors-basics.json and dag/units/sk-thm-sf-ctf-stability.json. This supporting lemma remains on the inherited stable-curve/Deligne--Mumford-atlas branch. blueprint_refs.py ancestor reports None; the inherited null ancestor and detailed from.place are preserved. Searches across the imported blueprint for 05W1, open diagonal, unramified diagonal and unramified found no duplicate of this converse. Existing lem-sfb-unramified-space-open-diagonal proves the reverse implication, with scheme target, and is not used to prove its converse.

The two off-unit tool uses are declared in split_report.tool_uses: lem-trf-space-fibre-products-etale-covers only supplies fibre-product existence, and lem-trf-space-representable-etale-scheme-tests supplies scheme-source representability and etale calculus. Both are foundational tools, not an alternative proof of a unit step. The latter's statement was read in full; it explicitly includes comparison of scheme maps etale over an algebraic space.

## Not duplicates

No new nodes were created. Existing nodes supply all non-elementary inputs.

## Review by Q91

I read the entire proof and statement of Stacks Tag 05W1, lemma-diagonal-unramified-morphism in spaces-morphisms.tex, especially part (2), together with the chart definitions 03XF and 03ZH and the all-diagrams condition of 03MJ. I read spaces-properties.tex lemma-etale-over-space (03EC), which gives the exact comparison between two etale scheme maps to an algebraic space, and etale.tex theorem-etale-radicial-open (025G), whose third condition is the final open-immersion test. There are no new nodes needing separate source review.

For Step 1 I opened def-weil-finite-type-morphism and def-weil-unramified-morphism. They state the scheme local finite type notion and the local finite type plus open diagonal criterion, respectively. The algebraic-space meanings are explicitly the item's chart convention; this step only fixes an arbitrary chart diagram and specializes that convention. In particular, I did not cite a scheme definition for an unproved algebraic-space descent theorem or require charts to be surjective when using the all-diagrams form.

For Step 2 I opened lem-trf-space-fibre-products-etale-covers and checked that it states existence of the sheaf fibre product as an algebraic space, so Q really is an allowed algebraic-space base for Step 4. I opened lem-trf-space-representable-etale-scheme-tests and checked its scheme fibre-product, base-change and composition clauses. The first of the two product arrows is the pullback of a by the first X projection, and the second by the second X projection; neither arrow is being assumed etale without that base-change argument.

For Step 3 the same scheme-test node gives both E and D as schemes, E etale over Y, and etaleness of V -> E by its final comparison clause. I verified the cartesian square on each test scheme: P times_E V consists of u1,u2 with h(u1)=h(u2), exactly D. No assumption that Y or X is a scheme occurs. This proves D -> P etale and hence D -> Q etale. The comparison input is explicitly in the cited statement, not merely in that node's proof.

For Step 4 I opened lem-weil-pbc-etale-composition-cancellation and used only clause (1), open immersions of schemes are etale, on each scheme pullback of the assumed open immersion Delta_f. Thus this scheme-only node is applied to schemes. The representable composition and final comparison clauses of the scheme-test node then apply to U and D over Q. Their triangle commutes because both maps send u to (a(u),a(u)); no cartesianness of the left square or surjectivity of D -> Q is claimed.

For Step 5 I opened def-weil-etale-morphism: its statement supplies flatness and local finite presentation of the scheme map Delta_h. I opened lem-pe-flat-lfp-monomorphism-open: its three hypotheses are exactly these two plus monicity, which I checked directly by a projection of U times_V U. It follows that Delta_h is open. The scheme unramified definition therefore applies with the finite type hypothesis established in Step 1. Since that diagram was arbitrary, this proves the exact algebraic-space assertion of the item.

I checked delivery-errors B through E: all existing cited statements were opened; every non-elementary input appears in uses and citations.json; no new clause of the item was disguised as a node; no definition is used to supply an unstated comparison theorem; proof_deps is the exact union of uses. Each step is under 2000 characters, so there are no mechanically flagged long steps; the product identifications are explicit elementary inverse maps. Empty spaces/charts, identity maps, and nonseparated targets cause no difficulty: the argument uses functor points and products, not reducedness, separatedness, noetherianity, quasi-compactness or a surjectivity assumption on the chart diagonal. A positive-dimensional affine line has non-open diagonal and does not satisfy the hypothesis; omitting local finite type would invalidate the intended unramified criterion, and that hypothesis has been retained and used for h.


## Repair of the returned delivery (2026-10-22)

The return entry identifies head `b54c1c03b75`: the reader approved it, but landing refused the side completion because the live DAG used by the queue had not received it. I retained the delivered sandbox proof, report, citations and search log. The first required dry run completed successfully (`1345e62fd58`, not pushed), confirming that the delivery tool can now build the retained split on the current DAG. I then reapplied the worker stage-1 fields to the current live item record, whose status is still `unsplit` and whose proof is empty; its statement, source, statement dependencies, creation metadata, chapter, unit and blueprint fields agree with the retained version. No maintainer review or completion field is invented.

I re-read the current statements of all four statement dependencies and all seven proof dependencies, including the full final comparison clause of `lem-trf-space-representable-etale-scheme-tests`. Every quotation in the ten citation records is still a verbatim part of the current cited statement. Thus no citation had to be replaced and no hypothesis changed. In particular the comparison lemma still applies to arbitrary scheme sources etale over an algebraic space, not just schemes over a scheme. The scheme-only open-immersion and flat-monomorphism criteria are still applied only to scheme maps. The search questions have not changed, so I read and reused the recorded Mathlib hits instead of rerunning their queries.

To make this repair reviewable beyond a rebase, I expanded Step 2 with the actual pullback isomorphisms and their inverse maps. Step 3 now gives both directions of the natural bijection between points of $P\times_E V$ and $U\times_V U$: forget the uniquely determined $v$, or insert $v=h(u_1)=h(u_2)$. These are elementary identities, not new lemmas or a change of route. I re-read Stacks 05W1(2), the chart definitions 03XF/03ZH with 03MJ(1), 03EC(2), and 025G(3). The expansions require no surjectivity of the product charts and work equally for empty schemes and nonseparated spaces. This repairs the requested current-DAG delivery while preserving the argument the reader approved. There are still zero new nodes and zero Mathlib leaves in the delivery.


## Follow-up repair against current DAG (2026-10-23)

The current return in coord/returns/Q91.md names head `80e89542896` (2026-10-22 15:07 UTC), again approved mathematically but refused because the side completion was not promoted to the live DAG. This is the return addressed by this follow-up; the preceding section describes the earlier retained repair and remains as history. The required initial dry run exited successfully at `5d68c4a68ae` without pushing. I compared the retained node with the current live node: only proof, proof_deps, proof_origin, mathlib_searches, status and split_report differed. The live item remains unsplit with empty proof. I started again from that current record and reapplied the retained worker fields, preserving the current statement, statement dependencies, source, blueprint and creation metadata.

For this repair I reopened every current statement dependency and proof dependency, rather than relying on the earlier review. Steps 2--4 still receive the scheme-source fibre-product, base-change, composition and comparison clauses from lem-trf-space-representable-etale-scheme-tests; its comparison clause expressly allows an algebraic-space base. The fibre-product node still makes Q an algebraic space. The other cited statements still give exactly the scheme local finite type/unramified definitions, open-immersion-to-etale implication, etale flatness and local finite presentation, and the flat locally finitely presented monomorphism criterion used in Steps 1, 4 and 5. All ten citations.json quotations are verbatim in those current statements, and all five uses lists are covered. No dependency replacement or new node is needed.

I reread Stacks 05W1(2), 03XF, 03ZH, 03MJ(1), 03EC(2) and 025G(3) in the local TeX sources. The actual proof adjustment is in Step 3: the inverse from D to P times_E V now explicitly obtains the P coordinate from fa=bh and h(u_1)=h(u_2), before inserting their common V coordinate. This checks both inverse maps, not just the direction forgetting v. It retains the approved chart-comparison route and does not require a cartesian chart square, separatedness, nonempty charts or surjectivity of D to Q. I checked empty charts, identity maps and arbitrary nonseparated targets again. All steps remain shorter than 2000 characters.

The project Lean search by blueprint id, unramified/diagonal and AlgebraicSpace still finds no declaration of this algebraic-space assertion. I read the recorded search results and the scheme-only candidates at Mathlib/AlgebraicGeometry/Morphisms/FormallyUnramified.lean:79 and :126; the question and statement have not changed, so no search was rerun or invented. Blueprint search for open diagonal again returned no equivalent node, and the ancestor command still reports None. No source, unit route or target statement changed. There remain zero new nodes and zero Mathlib leaves. This follow-up is an actual current-record repair with an explicit proof adjustment, not an unchanged re-push.
