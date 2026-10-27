# Q115: lem-sfb-chevalley-birational-integral-envelope

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-chevalley-birational-integral-envelope.json`: item, statement unchanged; split into four assembly steps.
- `dag/nodes/sec-six-functors-basics/lem-sfb-chevalley-integral-birational-law.json`: new statement-only node; no Mathlib match. This is a strict partial multiplication on the explicit root-coordinate scheme, before any containing group is constructed.
- `dag/nodes/sec-six-functors-basics/lem-sfb-dedekind-strict-law-realization.json`: new statement-only node; no Mathlib match. This realizes an arbitrary strict birational law over a Noetherian domain with DVR localizations, including the integer base.
- `citations.json`: verbatim statement excerpts for every dependency of every assembly step.
- `searches.jsonl`: actual Mathlib service and grep searches. Both new nodes have LeanFinder in two phrasings, Loogle, grep, and LeanSearch. All services answered. The original item's inherited searches are preserved; fresh item-level searches are appended.

Two new nodes, zero Mathlib leaves. No Lean was written and no compiler or build was run. The repository and launcher were read only.

## Attachments

None. The exact blueprint-tag search and searches for birational laws, Chevalley cells, integral prolongations and root subgroups in `lean/WeilConjectures/` found no declaration giving the item. The Chevalley hits concern constructible images; root-pairing and Lie-algebra constructions do not construct algebraic group schemes.

## Literature wanted

WANTED: Brian Conrad, *Reductive Group Schemes*, local copy of https://math.stanford.edu/~conrad/papers/luminysga3smf.pdf, Section 6.3, printed pp.214--227; rational rank-one normalization also Theorem 4.2.6(1), equation (4.2.1), and Corollary 5.1.9(3). Used for the item and both new nodes. I read the author's online PDF. No download or modification of literature was made. The assembly is marked agent-written because the local document is absent. No Stacks tag states either group-theoretic construction. No SGA source was used.

## What needed correction or clarification

The unsplit item had no proof. Its source already distinguishes this envelope from the later affine/reductive integral model; the split keeps that distinction. In particular we cannot use the parent integral prolongation theorem or the special-fibre semisimplicity criterion, which depend on this item.

The existing `lem-sfb-strict-birational-law-realization` quantifies over a field or DVR, so applying it with R = Z would be a hypothesis error. The new Dedekind-base statement records the spreading and gluing theorem described immediately before Conrad Proposition 6.3.13 instead of silently treating Z as a trait. Its future split can reuse the existing field/DVR theorem.

The first draft justified geometric density informally. I replaced that argument with the existing smooth fibrewise-dense-open base-change theorem, whose statement explicitly permits arbitrary base change. The equality step spells out the parameter schemes, including the principal open D(1+uv), so it proves the formulas on all algebra points, not only geometric points or points where the partial multiplication was initially defined.

The item's `blueprint.from.node` is null in the live created-node chain. `tools/blueprint_refs.py ancestor` also returns None. I retained the inherited chain and recorded the precise root-cell prerequisite in each new `from.place`; no chapter or unit was rewritten. I read the latest blueprint's direct-image node and proof in `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/`, the current chapter, and the unit record. This item is a lower prerequisite of the already recorded alteration/moduli/invariant-theory route; it is not the unit's key node and does not fill unit realization fields.

## Not duplicates

lem-sfb-chevalley-integral-birational-law vs lem-sfb-chevalley-birational-integral-envelope: the new node constructs only a partial law on an explicit polynomial/Laurent-polynomial scheme, with strict universal-translation charts; it constructs no containing group. The item constructs a global smooth group and proves that its multiplication has the prescribed coordinate chart and integral identities.

lem-sfb-chevalley-integral-birational-law vs lem-sfb-rational-split-integral-prolongation: the latter constructs an affine reductive integral realization and depends on the item; the new node is the earlier rational-coordinate integrality/strictness input and asserts neither affine group completion nor reductive special fibres.

lem-sfb-dedekind-strict-law-realization vs lem-sfb-strict-birational-law-realization: the existing node's base is a field or DVR; the new node allows a general Noetherian domain with DVR localizations, notably Z. Its extra content is spreading the generic solution and gluing the finitely many remaining local solutions, not another local realization theorem.

lem-sfb-dedekind-strict-law-realization vs lem-sfb-trait-birational-group-envelope: the existing node assumes a DVR and a whole generic-fibre group, and permits a merely birational law on the model; the new node assumes a strict law and embeds its entire chart over a Dedekind base. Neither specializes to the other in the application over Z.

DAG searches covered the whole graph for Chevalley systems, 6.3.11, 6.3.13, strict birational laws, Dedekind birational envelopes, and generic-fibre equality. Blueprint searches for birational, Chevalley, root cell, strict law and Dedekind found no node stating either new input (the Chevalley blueprint hit is the unrelated constructible-image theorem). No Stacks-tag duplicate is introduced.

## Review by Q115

I read Conrad's online Section 6.3 through the construction of the root-cell partial law, the strictness proposition, the preceding Dedekind-base realization discussion, and the paragraph and equation (6.3.5) after it. For the first new node, the opposite-root normalization following Remark 6.3.5, the integral unipotent-coordinate construction of Lemma 6.3.7, the Weyl-coordinate transitions of Lemmas 6.3.8--6.3.9, Proposition 6.3.11 and Proposition 6.3.13 are the source. Its statement includes the needed definitions of rational and strict maps and the rational rank-one normalizations. It does not claim that an arbitrary unit-bearing birational law is strict: multiplication on A1 with identity 1 and absorbing point 0 is a useful counterexample to such an overgeneralization. Strictness is part of the specialized Chevalley-coordinate theorem.

For the second new node I read the paragraph immediately before Proposition 6.3.13, printed p.225. It explicitly passes from the field/DVR case to the generic point, spreads the solution over a dense open, and reduces the finite complement to the local DVR solutions. This is the source for the base extension of the existing realization result. The new statement introduces its own R, S, X, rational law and density conventions and includes the finite-presentation and separatedness hypotheses. It is statement-only; the gluing argument has not been hidden in its statement as a purported proof. No SGA citation in Conrad was followed.

Step 1 takes the explicit cell, the base and the normalized parameters and strict law from `lem-sfb-chevalley-integral-birational-law`, exactly as that node states. Both semisimple spanning and integral coroot spanning are supplied by the item. No arbitrary pinning must be preserved. Empty roots with these spanning hypotheses force the zero lattice; the new statement includes that case.

Step 2 uses the Dedekind-base realization statement, not the field/DVR statement. Z is Noetherian by its principal ideals; its nonzero prime localizations have ideals generated by powers of p and are nonfield local principal ideal domains. The previous cell node supplies every geometric input. I opened `lem-sfb-smooth-fibrewise-dense-open-base-change`: it applies to the smooth H and its fibrewise dense open chart, and asserts exactly the geometric-density consequence. Coordinate axes and the torus are closed coordinate subschemes of C (set the other coordinates to zero and the torus variables to 1 as appropriate); an open chart therefore identifies them with locally closed subschemes of H. This elementary coordinate argument needs no subgroup-closedness theorem.

Step 3 uses the statement of `lem-sfb-rational-group-hom-extension`, which I opened and read: a multiplication-compatible birational map between smooth separated finite-type groups over any base extends uniquely to a group isomorphism. Both groups here are over Q and have finite presentation; the first node supplies the rational cell open immersion, and the second supplies the chart in H with the same rational law. Thus the common chart provides the required birational map and its multiplication compatibility. Its torus and root restrictions follow from the specified restrictions of c, not from a uniqueness theorem for pinned integral models.

Step 4 uses all three rational formulas explicitly stated in the new cell node and the equality assertion in `lemma-nagata-ext-scheme-theoretically-dominant-separated`, whose entire statement I read. I checked scheme-theoretic dominance instead of appealing to density of rational points: the domains are explicit Z-polynomial/Laurent-polynomial rings, or Z[u,v,(1+uv)^{-1}], and each injects into its Q-localization. The separated target is the H obtained in step 2. Applying that equality theorem also verifies that the coordinate maps are group homomorphisms and that their ordered product is the original chart i. This avoids assuming that repeated products remain in the initially defined partial-law domain.

For B1--B10 I checked self-contained new statements, definition dependencies, TeX escaping, unchanged item statement, statement-only new nodes, actual logged searches and inspected hits, the absence of a Mathlib match and the inherited blueprint chain. For C1--C8 I opened every cited existing statement and checked that every use has a verbatim citation entry; the only off-unit equalizer theorem is a declared generic tool use, and no cyclic appeal to the parent model theorem occurs. For D1--D4 these are partial-law construction and a general realization theorem, not two renamed clauses of the item: the assembly still proves integral identities and identifies the product chart. For E1--E6 I checked the base hypothesis, the specified generic torus, the scheme-theoretic parameter domains, and all-algebra functoriality.

Small cases: the zero datum has C = Spec Z and yields the trivial group via the generic isomorphism. In rank one, upper/lower unitriangular SL2 matrices give the displayed denominator 1+uv, coroot diag(1+uv,(1+uv)^{-1}), and Weyl conjugation with the minus sign. At u=0 or v=0 the opposite-root formula reduces to an identity; u=v=0 gives the identity section. At 1+uv=0 no formula is asserted. These calculations survive characteristics 2 and 3 because every denominator is restricted to the stated unit locus; no nonzero characteristic constant is inverted. Reducible root systems are permitted by the source's root-datum construction. Nilpotent coefficient algebras are covered by equality of scheme morphisms.

All four proof steps are below 2000 characters individually; no long step conceals another lemma. The existing density, equality and rational-homomorphism tools have been cited rather than re-created as new nodes. I corrected the geometric-density citation during this review. There is no statement dispute and no unfinished part of this one-level split; the two new inputs are deliberately left for later stage-1 workers.

## Checks

The preliminary server `review_split` passed. The full required delivery dry run and push are run after this report is written; their final results are recorded below when available.
