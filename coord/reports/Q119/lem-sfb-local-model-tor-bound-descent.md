# Q119 — lem-sfb-local-model-tor-bound-descent

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-local-model-tor-bound-descent.json`: statement, now split into six proof steps. Its mathematical statement, hypotheses, interval, conclusion and inherited provenance are unchanged. New Mathlib searches were appended to the inherited record; no match.
- No new nodes and no new Mathlib leaves.
- `citations.json`: 15 exact statement quotations, one for each step/node citation.
- `searches.jsonl`: five actual search results recorded by msearch.py; previous inherited searches in the item remain intact. `write_split.py` is a sandbox-only preparation script.

## Attachments

None. Searches of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` by the full blueprint tag, item id, Tor-amplitude/local-model vocabulary and the relevant derived-category files found no declaration giving this entire statement. `SixFunctors/ProEtale/Derived/TorAmplitude.lean` defines Tor amplitude for coefficient-category sheaves; `CategoryTheory/DerivedCategory/TorAmplitude.lean` gives its elementary permanence properties. The flat-model and pullback-stability declarations give only other parts or specializations, not the condensed-ring local tensor comparison plus descent required here. No upstream master sorry declaration was counted as a proof.

## WANTED

None: the needed source material is available locally.

## Corrections and observations

The imported item was statement-only, not a proof. Its statement is valid, including arbitrary commutative condensed coefficients; no restriction to finite or admissible coefficients was added. The proof retains its blueprint ancestry `det-prop-scalar-six-ctf`, paragraph (2), and the unit route `sk-prop-scalar-six`. This is not the unit's key node, so its realization record is not changed.

The existing `lem-pc-bounded-above-flat-kflat-site` has the right statement but its source field mistakenly labels bounded-above-flat K-flatness 06YS. Reading the actual TeX and tag table identifies it as **06YQ**, `sites-cohomology-lemma-bounded-flat-K-flat`; 06YS is existence of K-flat resolutions. This delivery cites the correct tag in its proof. The existing node itself was not edited. Derived pullback is Lemma **06YY**, `lemma-derived-base-change`, in Section 06YV; the proof distinguishes the lemma from its section.

The localization node has additional constant-ring clauses. Only its clause (1), the equivalence of the small site and the slice and equality of coverings, is used. A condensed coefficient sheaf is not identified with a constant discrete coefficient sheaf. Its ring comparison instead comes from `lem-sfb-alpha-iso`, whose statement applies to every condensed ring.

## Unfinished work

None for this one-level stage-1 split. The existing cited nodes retain their own proof frontiers. No Lean was written, no build or compiler was run, and no shared repository or launcher file was written.

## Not duplicates

No new nodes were created. Whole-DAG searches for bounded flat/K-flat complexes, derived tensor pullback and local detection, and whole-blueprint searches for K-flat and Tor amplitude found the existing nodes reused below. The sites/Tor-amplitude blueprint hits do not give the exact statement of this item: most concern finite coefficient stages, particular coefficient comparisons or unrelated operations. Consequently `blueprint.same_as` remains empty.

## Review by Q119

I read the current `main-20261015` chapter and unit and the exact source paragraph `det-prop-scalar-six-ctf.proof.md` (2). Its claim is that the bounded flat local model supplies the same Tor interval globally. I expanded this claim rather than moving it to a new lemma. I read `sites-cohomology.tex` at Lemmas 06YQ, 06YS, 06YY, 07A4 and the construction preceding Definition 06YU, `proetale.tex` at Definition 098K, `sites.tex` at the localization construction 00XZ/00Y0 and the sheaf condition 00VM/00VR, and `homology.tex` at Lemma 010N. I also read the blueprint source of `lem-sfb-alpha-iso` and the coefficient-transport paragraph (Step 2) of `lem-trf-ordinary-kunneth.proof.md`. The latter source contains other material, but this proof uses only the existing ringed-site lemma's explicit K-flat representative clause, whose computation is justified by Stacks 06YU. It does not invoke any SGA result, including the additional references in that source's provenance paragraph.

For step 1 I opened `lem-weil-proetale-weakly-etale-localization`, `def-pur-localized-ringed-site` and `lem-sfb-alpha-iso`. The first applies because every member of the given cover is a weakly etale object; its first clause identifies the sites, not merely their underlying schemes. The localized-site definition gives the section formula for restriction for arbitrary ring sheaves. Alpha-isomorphism gives the coefficient-ring transport for arbitrary condensed Gamma. This checks the otherwise potentially wrong constant-ring identification.

For step 2 I opened the exact-functor/cohomology node, the K-flat resolution node and the ringed-topos derived pullback node. They respectively give cohomology comparison, a resolution with both K-flatness and flat terms, and computation of pullback on exactly those representatives. Exactness of the module inverse image is explicitly stipulated in the item. It makes the pulled-back resolution a quasi-isomorphism, so the identification of derived and exact inverse image uses no preservation claim beyond what is stated and cited. Work takes place on small site representatives relative to the larger module universe, as required by these generic statements.

For step 3 I opened the entire statement of `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`. It gives the displayed canonical bifunctorial tensor comparison for arbitrary complexes and arbitrary ringed-topos morphisms. The coefficient rings here are Gamma_S and Gamma_Vi with the alpha map from step 1. Step 2 supplies its exact-pullback interpretation, and functoriality transports the given local-model isomorphism. No flatness of N, perfectness of Q or Noetherian condition is used.

For step 4 I checked `lem-pc-bounded-above-flat-kflat-site` against Stacks 06YQ: bounded above by s and termwise flat are precisely the hypotheses we have. I read all of `lem-trf-site-derived-tensor-restriction`, not its proof, and verified that it explicitly says its K-flat flat-term representatives compute both derived objects by the displayed ordinary tensors. With the identity ring map, H represented by L_i and the identity resolution of L_i, that computational clause gives L_i tensor g_i^*N. This avoids making a duplicate general computation node and avoids citing a definition as a theorem. The identity-ring specialization needs no flatness of the test module.

For step 5 I opened the total tensor definition, abstract derived-category/cohomology definition and exact-cohomology comparison node. Because the second complex is concentrated in degree zero, the degree formula has only the summand L_i^q tensor g_i^*N; outside the interval it is zero. The kernel/image definition gives zero cohomology at that degree even next to either endpoint. The comparison then identifies the pullback of the global cohomology sheaf with that zero sheaf. These are elementary deductions from the cited formulas, not an uncited assertion that tensor preserves exactness.

For step 6 I read the full site/sheaf definition and the restriction formula, and the exact clause (3) of the Tor-amplitude definition. The site axiom supplies a covering after base change to every test object W. Each restriction section group is zero because its projection factors through V_i. Uniqueness in the sheaf equalizer forces every section on W to be zero. This proves joint detection directly, without a new descent node or a geometric-point argument (which would be inappropriate without enough points). As N was arbitrary, the final quantifier agrees with the definition of Tor amplitude.

I checked the one-object identity cover, the case r=s (a single flat term), N=0, zero local models, empty source/empty cover, and degrees immediately adjacent to r and s. None requires an extra hypothesis. Finiteness of the cover is retained but is not needed once a common interval is given. I checked the existing dependencies for a path back to this item; there was none. Every non-elementary fact is a cited existing statement, and each elementary step contains its kernel/image or sheaf-uniqueness argument. All six steps are under 800 characters, so none exceeds the 2000-character review threshold.

The generic statements from other units are declared in `split_report.tool_uses`: site localization, Cartesian coefficient identification, K-flat resolution and calculation of pullback, derived tensor pullback, bounded-flat K-flatness and the identity-ring specialization of the representative-computation clause. They are tools for the prescribed local-model route, not replacements of any unit step. The exact-cohomology lemma is already a Mathlib leaf and the remaining off-unit citations are definitions.

The initial server `review_split` passed with zero new nodes and declared tool uses; it observed that the parent unit has no realization recorded yet. This item does not own that unit record. The required final dry run and push are performed after this report is written.

The first full dry run required longer quotations for the localized-site definition in steps 1 and 6. I replaced the short section formula by its full ring/module restriction clause, without changing the proof.
