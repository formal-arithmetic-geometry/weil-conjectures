# Q127 — lem-sfb-space-fibre-assassin-etale-atlas

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-space-fibre-assassin-etale-atlas.json`: statement, split into five steps; statement and statement dependencies preserved. No Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-scheme-etale-assassin-invariance.json`: new statement-only scheme comparison lemma, unsplit; no Mathlib match. One new node, zero Mathlib leaves.
- `citations.json`: one verbatim statement quotation for each node cited by each numbered proof step.

## Attachments

None. Searches in the live read clone's `lean/WeilConjectures/` for the blueprint tag, the item id, assassin, associated points and associated-prime terminology found no project declaration proving this assertion. Existing sorry declarations are not attachments. Mathlib associated-prime localization declarations do not state invariance of associated points under arbitrary etale scheme pullback.

## WANTED

None: all sources used are available under `literature/`.

## Problems and changes

The item had no proof. Its statement is correct with its present finite-type hypotheses, including over a non-Noetherian scheme base. I did not change it or introduce extra hypotheses. In particular I do not assume that a finite-type fibre chart is globally Noetherian or quasi-compact. The argument proves local Noetherianity on every etale fibre chart before using ordinary associated points instead of weakly associated points.

The inherited blueprint ancestry has `from.node: null`. `tools/blueprint_refs.py ancestor` reports this same null ancestry; it is retained, with the inherited chain and an explicit place. I read the latest blueprint (main-20261024), especially the constructibility step of `det-thm-sf-ctf-stability-direct-images` in unit `sk-thm-sf-ctf-stability`. This comparison is an input to that constructibility argument, not a substitute route through the trace formula. Blueprint searches for assassin, associated points, fibre assassin etale atlas, 05FP and 0CUZ found no blueprint node stating the comparison. Both nodes have `same_as: []`.

The new node is the scheme-local geometric comparison, not a clause about this item's algebraic space or chosen atlas. Applying a ring weak-assassin theorem is not by itself a comparison for quasi-coherent sheaves on non-affine schemes: the affine/stalk localization bridge, pullback module identification and Noetherian weak/ordinary comparison are its content. I have kept this as one meaningful statement-only lemma, rather than duplicating the existing ring lemmas or making nodes for tensor reassociation, finite presentation implying finite type, or the final set-image argument.

## Unfinished work

None in the assigned split. The new scheme lemma is deliberately statement-only and joins the stage-1 queue, as required for a one-level split. No Lean was written or compiled.

## Searches and candidate checks

The exact Mathlib queries and their returned results are recorded in `mathlib_searches`, with the command's underlying log in `searches.jsonl`. I searched the item and the new scheme lemma with semantic queries, a second phrasing, Loogle names and source grep, and read the returned hits. Associated-prime localization in `Mathlib/RingTheory/Ideal/AssociatedPrime/Localization.lean` compares localization and comaps under localization hypotheses, not arbitrary etale pullback of quasi-coherent sheaves. Other hits concerned etale loci, morphism properties and scheme fibres. None is an exact or one-line generalization. Loogle unrecognized-name errors are recorded as errors, not claims of an empty search; the subsequent quoted-name patterns supplied usable results. An initial grep directory with an extra Mathlib prefix was invalid; the correct relative directories and whole-Mathlib searches were then run and read. Only the successful corrected grep calls are evidence for the absence conclusion. Existing inherited search records were preserved.

I searched the whole DAG by associated/weakly-associated terminology, etale invariance, and the Stacks tags before creating the new node. The following list includes even nodes whose tag occurs only in an existing proof or review, to make the same-tag check explicit.

## Not duplicates

lem-sfb-scheme-etale-assassin-invariance vs lem-trf-etale-weakass-invariance: the existing statement concerns prime ideals of rings and tensor products, with WeakAss, on an affine etale ring map; the new statement concerns ordinary associated points of arbitrary quasi-coherent sheaves on possibly non-affine locally Noetherian schemes. The geometric localization and ordinary/weak comparison remain to be supplied in its future split; the existing algebra lemma can be reused there.

lem-sfb-scheme-etale-assassin-invariance vs lem-trf-finite-ring-map-weakass-contraction: the existing statement contracts weakly associated primes through finite ring maps; it gives neither etale pullback equivalence nor a scheme/sheaf statement.

lem-sfb-scheme-etale-assassin-invariance vs lem-trf-flat-tensor-weakass-fibre: the existing statement is the ring-theoretic flat tensor formula with an extra associated-prime condition on the fibre ring, not etale invariance of scheme module associated points.

lem-sfb-scheme-etale-assassin-invariance vs lem-sc-ass-weakass-fg-prime: the existing statement compares Ass and WeakAss for a finitely generated prime in a single ring/module; it does not compare schemes or pullback.

lem-sfb-scheme-etale-assassin-invariance vs lem-sc-ass-weakass-fg-stalk: the existing statement compares two predicates at a single scheme stalk with finitely generated maximal ideal, not association under an etale map.

lem-sfb-scheme-etale-assassin-invariance vs lem-sc-ass-weakass-locally-noetherian: the existing statement treats only the structure sheaf of one locally Noetherian scheme; the new one treats every quasi-coherent module and compares two schemes under pullback.

lem-sfb-scheme-etale-assassin-invariance vs lem-sc-locnoeth-stalk-maxideal-fg: the existing statement gives finite generation of the maximal ideal at a locally Noetherian scheme stalk; it states no associated-point comparison.

lem-sfb-scheme-etale-assassin-invariance vs lem-sc-meromorphic-sheaf-generic-product: the existing statement describes meromorphic sections by generic-point products under a no-embedded-points hypothesis; it states no etale pullback theorem.

lem-sfb-scheme-etale-assassin-invariance vs lem-sbc-depth-two-hartogs-restriction: the existing statement is depth-two Hartogs extension across a closed complement, not associated-point invariance.

lem-sfb-scheme-etale-assassin-invariance vs lem-sbc-affine-section-associated-stalk: the existing statement detects unequal finite-module sections at an associated stalk; it supplies neither etale pullback nor its converse.

lem-sfb-scheme-etale-assassin-invariance vs lem-sbc-depth-one-restriction-injective: the existing statement proves restriction injectivity from depth one on a complement; it has no etale associated-point equivalence.

lem-sfb-scheme-etale-assassin-invariance vs lem-sbc-depth-two-finite-hom-equality: the existing statement is uniqueness of morphisms from a finite scheme from equality on an open subset under depth-two assumptions, not a theorem about etale pullback of modules.

Additional candidates checked: `lem-trf-flat-pullback-associated-points` has a general flat formula involving association in the fibre, whose etale fibre identification is additional content; `lem-trf-relative-assassin-base-change` is scheme base change of relative assassins, not independence of algebraic-space charts. Neither states the new node or the assigned item. The existing definition of universal relative purity supplies the chartwise union, not its detection on each individual chart.

## Review by Q127

I read the item against Stacks `spaces-divisors.tex`: 0CUY gives locally Noetherian fibres for locally finite type morphisms, 0CUZ identifies the chart conditions (3), (4), (6) and expressly permits associated points when fibres are locally Noetherian, and the proof of 0CVV uses precisely the image equality from a surjective etale presentation. For the new node I read `flat.tex`, 05FP (the scheme etale weak-assassin up/down theorem, for arbitrary quasi-coherent modules), and `divisors.tex`, 05AR (ordinary and weak association agree at finitely generated maximal ideals). On locally Noetherian schemes every maximal ideal of a local ring is finitely generated, so these sources give exactly the stated ordinary-associated-point version. No finite generation of the module, surjectivity of this auxiliary etale map, or global Noetherian assumption is necessary. The source's proof reduces locally to standard etale and an open subset of a finite free algebra; this is not being silently replaced by a mere flatness assertion.

For step 1 I opened each cited node. `def-trf-algebraic-space` provides a scheme atlas. `def-sfb-space-morphism-properties` tests local finite type on every compatible pair of etale charts, so the identity chart of the scheme base is allowed. `lem-weil-pbc-lft-base-change` supplies exactly scheme base change, and `pqf-lem-locnoeth-lft` applies because the new base is the spectrum of a field. `lem-trf-space-representable-etale-scheme-tests` explicitly represents the common refinement by a scheme and preserves etale and surjective etale under base change. `def-weil-etale-morphism` and `def-sbc-locally-finite-presentation` supply the finite polynomial presentation; forgetting its relations is the written elementary finite-type argument. `lem-trf-etale-local-noetherian-descent` is descent for a jointly surjective etale cover, so it applies to the single surjective map D -> U. This establishes local Noetherianity for arbitrary charts, not just the originally chosen atlas. There is no hidden application over a Noetherian Y.

For step 2, `lem-sfb-space-module-pullback-quasicoherent` explicitly allows arbitrary algebraic-space maps, so it applies also to fibre pullbacks. `lem-trf-scheme-zariski-etale-quasi-coherent-equivalence` gives both the inverse restriction to Zariski opens and the pullback comparison for every scheme morphism. `def-trf-space-etale-module-functors` gives the tensor pullback and its local tensors. I wrote the two inverse tensor reassociation maps rather than assuming a separate base-change theorem: their balancing and compatibility with restriction directly give the sheaf comparison on the common refinement. These comparisons identify the actual modules whose associated points are tested.

Step 3 uses only the union-of-chart-images clause of `def-sfb-space-universal-relative-purity`, specialized to the fibre, and the representable-etale base-change statement. Hence the chosen chart itself witnesses membership; it is marked elementary. This does not yet assume the reverse implication being proved.

For step 4 I checked the exact statements of all four cited nodes. The purity definition supplies a chart and an associated point u witnessing membership, with the same image as the particular t under consideration. The scheme-test lemma supplies a scheme W and etale projections, not merely a sheaf product. `lem-a1-space-point-open-calculus` explicitly states surjectivity onto compatible point pairs, so it provides a point over this specified pair (u,t); surjectivity of one projection alone would not suffice. The new scheme comparison applies first to q with module a*M_y and then to r with N_y; step 1 provides local Noetherianity, step 2 supplies quasi-coherence and the module identification. It proves association of every lift t. No appeal to Yoneda, support, or flatness is being used as a surrogate for this theorem.

For step 5 the scheme-test lemma preserves surjective etale under base change and the point-calculus lemma explicitly converts representable scheme-test surjectivity into surjectivity of point classes. Thus every associated point downstairs has a lift; step 4 associates it, and step 3 gives the other inclusion. All non-elementary facts in this assembly are cited; the final membership and set-image manipulations are written out.

I tested empty fibres, the zero module (the maximal ideal cannot annihilate the zero element exactly, since its annihilator is the unit ideal), the identity atlas, and the two-copy disjoint-union atlas. The equivalence is also consistent at embedded associated points, e.g. the origin of Spec k[x,y]/(x^2,xy): the argument uses association rather than just generic points of support. Non-Noetherian Y is harmless because only residue-field fibres and etale charts over those fibres enter the comparison. The auxiliary scheme lemma allows arbitrary quasi-coherent G; 05FP and 05AR do not require G finite. For a nonsurjective etale map the pointwise assertion remains meaningful and does not assert equality of its full image with all associated points downstairs.

I checked delivery-errors B–E against the actual statements, not just their titles: no axiom/tautological replacement or circular child was introduced; no non-small colimit or category-size assumption is used; definitions are used only to unpack their clauses; each non-elementary comparison has a theorem node; each quoted citation is verbatim from the cited statement; the item statement and every clause are proved. The four generic off-unit tools (scheme tests, Noetherian descent, scheme QC equivalence, and point calculus) are declared in `split_report.tool_uses`. All five steps are below 2000 characters; none hides an unmentioned long comparison. Sources follow the latest blueprint/Stacks route and use no SGA source. I corrected the initial temptation to infer the full equivalence just from the definition: its reverse direction needs the common refinement and the scheme associated-point theorem, which are now explicit.
