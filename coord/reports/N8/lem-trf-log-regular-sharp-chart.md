# Stage-1 delivery: lem-trf-log-regular-sharp-chart

## Files written

- dag/nodes/sec-trace-formula/lem-trf-log-regular-sharp-chart.json: statement, split in five steps; no Mathlib match.
- dag/nodes/sec-trace-formula/lem-trf-fs-face-sharpening.json: new statement-only lemma; no Mathlib match.
- dag/nodes/sec-trace-formula/lem-trf-fine-log-stalk-chart-spreading.json: new statement-only lemma; no Mathlib match.
- citations.json: verbatim statement excerpts for all nine step/node pairs.
- report.md: this report. search-results.json retains the actual search outputs; searches.jsonl is the search command's own log.

## Attachments

None. Read-only searches of WeilConjectures in slopmaster2 for the blueprint id, LogStructure, LogScheme, logRegular, characteristicMonoid and sharp charts returned no declaration. The upstream master check for this id/characteristic chart also found none; it was not treated as proof evidence.

## WANTED

None: the proof's source is the available Illusie--Laszlo--Orgogozo volume. Its references to Kato are not substituted for the proof below.

## Findings and corrections

The item had an empty proof and already-recorded searches from its creation by Q109. I retained its complete statement, source, original searches, blueprint ancestry and all import/ownership fields. No statement dispute was found. The fs hypothesis alone suffices for the chart construction; log regularity remains a hypothesis of the item as imported.

I read Expose VI 1.1--1.6, especially printed p. 70, and the explicit splitting argument (3.a) in VI 3.7(a), printed p. 75. I use its nonequivariant construction only; no group action, root of unity, tameness, Cohen ring or completed-local-ring theorem enters this item. Expose VIII 3.1.1--3.1.5, printed pp. 98--99, gives the localization/sharpening conventions. The two new lemmas expose the algebraic and chart-spreading inputs which those pages use without supplying full proofs. They remain unsplit, with statements only. In particular the last sentence of VI 3.7(a) uses the usual fine-log chart-spreading fact: its abstraction with a *specified* stalk homomorphism is recorded explicitly as an input, not passed off as an elementary calculation.

The item proof is marked agent-written because it supplies the face-localization and pushout calculations and a direct basis construction around that source route. I also read Stacks Tag 01T6, label morphisms-lemma-finite-type-noetherian in literature/stacks-project/morphisms.tex, and cite the existing node rather than creating another Noetherian-ascent lemma.

## Mathlib and duplicate searches

All new searches ran through msearch.py N8 lem-trf-log-regular-sharp-chart; each new node has its own five queries (LeanFinder twice with different phrasings, Loogle, source grep, LeanSearch). Every service succeeded. I read the returned types and the relevant Mathlib sources. Localization.fg and Algebra.GrothendieckGroup.instFG in GroupTheory/MonoidLocalization/Finite.lean establish finite generation only. IsAffineMonoid in Algebra/AffineMonoid/Basic.lean assumes cancellation, finite generation and torsion freeness and does not establish the sharp quotient assertions. Submonoid.PowSaturated in GroupTheory/Subgroup/Saturated.lean defines the relevant root-closure property; Submonoid.MulSaturated in Algebra/Group/Submonoid/Saturation.lean means closure under factors instead. Neither states our algebra lemma. The logarithmic searches returned ordinary etale morphisms, schemes, spreading of ring morphisms or manifold charts, which do not specialize to a log-structure chart theorem.

Before creating nodes I searched every DAG statement for characteristic monoids, groupification, sharpening, face-localization and log charts; I ran blueprint_refs.py ancestor and blueprint_refs.py search for sharp, monoid, log structure, chart, localization monoid, sharp characteristic, logarithmic and fine monoid. Broad matches were ordinary geometric charts or categorical monoid objects. No imported blueprint node supplies either new lemma. The new ids were searched in the DAG and Lean source before writing.

## Not duplicates

lem-trf-fs-face-sharpening vs def-trf-fs-log-blowup: the existing node defines fs monoids and charts, but states no theorem preserving saturation under face localization/sharpening and no freeness of the sharp group completion.

lem-trf-fs-face-sharpening vs lem-trf-log-regular-sharp-chart: the new lemma concerns an arbitrary algebraic monoid and face, with localization units and a quotient-group identification; it constructs no log-scheme chart. The item's proof uses these stronger algebraic interfaces to construct a section explicitly, rather than citing a copy of its characteristic-monoid clause.

lem-trf-fine-log-stalk-chart-spreading vs lem-trf-log-regular-sharp-chart: the new lemma requires a given stalk homomorphism and a given associated-log-stalk isomorphism. It neither constructs such a homomorphism nor proves that a characteristic monoid is fine. Steps 1--4 of the item supply those inputs explicitly.

lem-trf-fine-log-stalk-chart-spreading vs lem-trf-snc-divisorial-log-chart: the existing SNC result starts with a smooth scheme and a transverse Cartier boundary and gives parameter charts. Our input is any fine log structure with a specified stalk chart, without smoothness or a boundary divisor, and its conclusion preserves that germ.

## Unfinished work

No unfinished part of the assigned one-level split. The two new statement-only lemmas are the next DAG items, not claimed proved here. There is no Lean edit and no compiler, Lake or build invocation.

## Review by N8

I checked delivery-errors B--E against the actual node statements and sources. For the item I read VI 1.6 and VI 3.7(a). For the new face-sharpening node I read VIII 3.1.1--3.1.5 together with VI 1.6/3.7(a); its statement separates localization from quotienting by units and does not assume the original group completion is torsion free. For the new spreading node I read VI 1.1 and the final sentence of VI 3.7(a); it includes the exact hypothesis that the germ's logification is an isomorphism. Fine means finitely generated integral charts here, and does not silently require saturation. I introduced every object and defined face, localization, quotient relation and finite free basis inline where not already defined by a cited node. The new files contain no proof sketches or proof dependencies.

Step 1 uses precisely the fs chart existence and stalk pushout in def-trf-fs-log-blowup. I checked its statement includes both. The inverse image F of the ring units really is a face, and the step proves that in one line using inverses to a product. Replacing the pushout by one over F^gp is the elementary universal property of inverting elements already mapping to units; quotienting out the same A-units gives P. No injectivity of F^gp into A-units is assumed or needed.

Step 2 uses lem-trf-fs-face-sharpening for the fs/sharp quotient, its group identification, freeness and localization units. I checked every one of those clauses is in that new node's statement. The hypotheses hold because Q is an fs chart and F was shown to be a face. This is a genuine algebra lemma, not an assertion that a log scheme admits the desired chart.

Step 3 uses the same algebra statement for a finite basis and kernel F^gp. Choosing lifts of the basis and extending by integer linear combinations explicitly splits the quotient group. The written membership argument uses that F^gp consists of units of Q_F, and the two inverse formulas verify the monoid product decomposition. No abstract splitting theorem or hidden comparison is invoked. The argument works also for the empty basis.

Step 4 uses that monoid decomposition and the associated-log pushout from def-trf-fs-log-blowup. The formula identifies the stalk as P plus its actual ring units. The preimage of units is {0}, since the characteristic map is the identity and P is sharp. Thus the new spreading lemma receives the full stalk isomorphism it requires, not just surjectivity or an unchosen characteristic isomorphism. The specification of the germ is essential for the chosen-identification clause.

Step 5 uses lem-trf-fine-log-stalk-chart-spreading only after those hypotheses are checked; its statement supplies an affine pointed etale neighbourhood and preservation of the germ. The statements of def-weil-etale-morphism and def-sbc-locally-finite-presentation give locally finite presentation and finite polynomial algebra presentations; discarding relations shows finite type directly. I opened pqf-lem-locnoeth-lft and checked it states ascent for any locally finite type map to a locally Noetherian target. This last citation is a generic off-unit tool and is declared in split_report.tool_uses; it does not replace the trace-formula route. I did not alter maintainer-owned tool_uses or unit metadata.

For edge cases, Q=N^r with the minimal face leaves N^r, with F=Q it gives P=0, and mixed coordinate faces remove just those coordinates. Q=Z/n as a group is allowed as an fs monoid: its sharpification is zero, so no false torsion-freeness of Q^gp is asserted. For Q=N plus Z/n, the torsion is in the units and is killed in the sharp quotient. The stalk-spreading hypothesis excludes an arbitrary map to a stalk which merely generates part of the log structure; the zero monoid case requires and yields a trivial log structure near the point. The final Noetherian assertion is local and uses no quasi-compactness or excellence.

Finally I checked each citation against its statement, each new node against all three exclusions (elementary, duplicate, renamed item clause), the new-source Mathlib candidates against their types, and the proof graph's intended directions. Each elementary step is an explicit algebraic construction, while the two non-elementary ingredients have nodes. Every proof step is shorter than 2000 characters. No prohibited source is used. The source and blueprint route remain the monoidal-resolution ancestry already attached to this item.
