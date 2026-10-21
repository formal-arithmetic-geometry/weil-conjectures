# Stage-1 delivery: lem-sp-etale-ctf-chart-domain

## Files written

- `dag/nodes/sec-smooth-purity/lem-sp-etale-ctf-chart-domain.json`: existing statement, split into ten proof steps; no Mathlib match. The statement, its seven statement dependencies, imported metadata, and blueprint ancestry are retained.
- `citations.json`: 35 step/node entries, each containing a substantive literal passage from the cited node's statement.
- `report.md`: this report. `searches.jsonl` contains the five actual searches made for this item. `write_split.py` is the sandbox-only reproducible writer, not a library or launcher edit.

New nodes: 0. New Mathlib leaves: 0. No unit record is changed: this item supplies a domain check, not the unit's key statement.

## Attachments

None. Searched the project Lean library for the exact blueprint id and the finite-Tor/chart notions. The source has flat-model and stability declarations covering ingredients, but no declaration giving all clauses of this item. In particular the project flat-model theorem in `WeilConjectures/SixFunctors/Etale/Derived/Finiteness/FlatModel.lean` does not by itself state compact support, comparison, and Tate compatibility. It is already represented by `lem-sf-etale-flat-constructible` and is reused through that node.

## Literature wanted

None.

## Corrections and scope

There was no proof in the item. Its statement is unchanged and no statement dispute arose. The source's Charts paragraph uses a canonical isomorphism involving pullback, coefficient extension, a finite Tate twist and a shift. The split supplies the domains of those operations on ordinary etale categories, then transfers them through the existing finite-Tor comparison. It makes no use of smooth purity, an exceptional inverse image, or SGA.

I corrected the primary-source references in my new proof steps after reading the tag index: the bounded-above-flat K-flat lemma is 06YQ (`lemma-bounded-flat-K-flat`), whereas the existing node's source says 06YS (the resolution lemma). The scalar-extension constructibility lemma is 0GKB (`lemma-tensor-constructible`), not 095J (a section tag). The existing cited node statements are correct for these uses; I did not edit those nodes.

I did not use the broad all-coefficient stability theorem or the older flat-model/tensor nodes restricted to `A_{E,n}` over the algebraic closure of a finite field. Here the field is arbitrary of positive characteristic and the finite ring need not be a DVR quotient. The ordinary-etale flat constructible model node is explicitly for every finite commutative ring on every Noetherian scheme, so it has the hypotheses actually available.

## Searches and duplication review

The inherited Mathlib search entries are retained. I ran the search wrapper for leanfinder (two mathematical phrasings), loogle (`"TorAmplitude"`), grep (`proetale|finiteTor|constructible.*compactSupport`), and leansearch (comparison, coefficient change and twists). All services answered; no unavailable service is called a negative result. I read the hits. They concern etale ring maps, structural module pushforward, generic flat functors, generic derived support conditions, and definitions of the pro-etale topology and ell-adic cohomology. I read the Mathlib `Sites/Proetale.lean` and `Sites/ElladicCohomology.lean` files; neither supplies the item. No hit states it or specializes to it in one line.

I searched the whole DAG by ids/titles and by the finite-Tor, compact-support, tensor-comparison and root-comparison statements, and ran `tools/blueprint_refs.py search` for `finite Tor`, `comparison tensor`, `chart domain`, and `Tor amplitude under comparison`. Existing nodes supplied all needed facts. The blueprint ancestor command gave `det-sp-reduction-exceptional`, agreeing with the retained ancestry. No other blueprint node states this complete chart-domain package, so `same_as` remains empty.

## Not duplicates

No new nodes. Existing lemmas are cited directly; neither a clause of this item nor an elementary consequence is turned into a fresh node.

## Review by ND

I read the worker brief, the three blueprint levels in SETUP, the unit and chapter records, GOAL, and both copies of delivery-errors B--E. For the item I read the current `main-20261015` proof of `det-sp-reduction-exceptional`, especially Charts, and the current proof of `det-pe-finite-tor-comparison-noetherian`. For the compact-support argument I read the existing proper finite-Tor proof and its geometric-fibre-bound node. The primary sources I opened were Stacks `etale-cohomology.tex` (03TT and its following flat/projective remark, the pullback-ctf lemma, 03S5, 095I, 0GKB), `sites-modules.tex` (0E8I), `sites-cohomology.tex` (06YQ, 0G7E, 07A4), and `proetale.tex` (09AL, 0GLZ). I also checked 03TT and 07A4 on the Stacks website. There are no new-node sources to audit.

I opened and read the statement of every cited node; the citation manifest records the exact part used, with whole statements where a short fragment could conceal a hypothesis. Step by step:

1. Finite-type Noetherian permanence gives the Noetherian scheme hypothesis of `lem-sf-etale-flat-constructible`; a field and a finite ring are Noetherian for the elementary reasons written out. The flat-model statement gives terms zero in the same Tor interval, not merely some unknown bounded resolution. The bounded-above-flat K-flat statement then applies to this model.
2. `lem-weil-pbc-extension-by-zero-exact` gives exactness and preservation of quasi-isomorphisms, and `lem-fin-extension-by-zero` gives constructibility of the terms for the ordinary etale finite-ring coefficients in force. The ringed-slice tensor identity is explicitly for arbitrary modules; with exact restriction (the module inverse-image node), flatness of the input term, and exact extension by zero, it proves flatness of the extended term. The K-flat criterion and the kernels/cokernels clauses of `thm-constructible-serre` finish the Tor and constructibility checks. No unsupported assertion that extension by zero preserves Tor amplitude is smuggled in.
3. `lem-sfb-finite-proper-geometric-cd-bound` controls all torsion sheaves, not just constructible ones; hence it covers the exact fibre hypothesis of `det-ctf-finite-proper-tor`. I use its uniform bound `2e`, and do not assume a uniform bound on the arithmetic cohomology of the ground field. The middle compactification scheme is in the standing setting by the item's explicit hypothesis. The proper finite-Tor statement gives both bounded constructibility and the output Tor interval; the ordinary compact-support definition identifies that functor with the named one. I checked the dependencies of these nodes do not reach this item.
4. The change-of-rings theorem computes derived extension on the chosen K-flat model. The general ringed-topos pullback statement says that pullback of a K-flat flat-term complex again has flat terms; its identity-topos specialization permits arbitrary `A -> B`. Constructibility of each extended term is checked directly from the finite-module local trivializations in the definition, and the Serre statement supplies constructible cohomology. This does not use flatness or finite projective dimension of `B` over `A`.
5. The etale module inverse-image statement supplies exactness and the constant-ring identification. The ringed-topos theorem supplies flat terms. The constructible-pullback statement supplies constructibility; its module interpretation is made explicit using the local trivializations with their scalar actions. The finite support of the model and the Serre statement give exactly the bounded constructible finite-Tor output.
6. The finite-etale-twist-line statement is for every finite coefficient ring killed by an invertible positive integer, and explicitly includes every nonnegative tensor power and flatness. Its local constant finite line satisfies the definition of constructibility. `lem-fd-flat-constructible-tensor` says precisely that tensoring a bounded constructible complex with such a flat constructible sheaf preserves bounded constructibility. For Tor amplitude the proof writes out the composite-exact-tensor argument on the model, then uses the K-flat criterion. The shift formula is written with the cochain convention: shift by `b` takes `[alpha,beta]` to `[alpha-b,beta-b]`.
7. The finite-Tor comparison node already states the equivalence and both directions for each Tor interval, under qcqs and discrete Noetherian coefficients. Step 1 verifies these hypotheses. This node is used directly, not the adjunction-transfer statement whose equivalence is an assumption.
8. The comparison exactness statement identifies the inverse images of both constant rings. The ringed tensor theorem gives the canonical natural tensor isomorphism, as well as its computation on flat K-flat models. I verify `B`-linearity through the second factor, so this is a comparison in the `B`-module derived category and not just after forgetting coefficients.
9. The comparison-pullback statement explicitly gives the natural scheme inverse-image comparison, including identities and composites. The cited etale, pro-etale, and comparison exactness statements justify using the same maps termwise in the derived categories. Steps 5 and 7 verify the subcategory membership of the compared functors.
10. `lem-amb-finite-root-site-comparison` is the needed theorem, not merely a definition of a comparison predicate. It states the root-preserving isomorphism for arbitrary positive invertible `m` and finite `R` killed by `m`, and its compatibility with scheme pullback. Taking `m=N`, the tensor theorem gives all nonnegative powers and tensoring with the input; exact termwise comparison gives shifts. This checks the actual canonical Tate comparisons rather than choosing arbitrary line trivializations.

I checked small and degenerate cases: the empty scheme and empty fibres, the zero coefficient ring, `N=1` (both rings are then zero), the identity coefficient map, identity/open/proper compactification factors, a singleton Tor interval, twist power zero, and either sign of the shift. The nonflat example `A=Z/ell^2 -> B=F_ell` still works by tensoring the bounded flat input model; it never asks for a bounded flat resolution of `B` over `A`. None of these tests requires changing a hypothesis. Every proof step is under 1200 characters, below the long-step audit threshold; the arguments are applications of cited statements or explicit calculations from them, with no new hidden lemma. All cross-unit statement tools are explained in `split_report.tool_uses`; no maintainer-owned `tool_uses` field is set.

The server `review_split` check passed before packaging. I will run the required full dry run and direct delivery; their final results are recorded below after they exit. No Lean was written, and no compiler, Lake, build, local DAG checker, or repository git command was run.

## Unfinished work

None in this one-level split. Existing dependency nodes retain their own proof obligations; this delivery does not assert that those obligations have been proved in Lean.

## Validation

The required `deliver.py ND lem-sp-etale-ctf-chart-domain --no-push` exited successfully: `OK (not pushed) ... at 185548bb0b4: preflight passed`. This includes the server preflight, DAG and split checks. The full split has zero new nodes and zero Mathlib leaves.
