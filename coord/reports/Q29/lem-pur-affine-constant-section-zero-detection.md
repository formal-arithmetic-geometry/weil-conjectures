# Q29 stage-1 delivery: lem-pur-affine-constant-section-zero-detection

## Files written

- dag/nodes/sec-smooth-purity/lem-pur-affine-constant-section-zero-detection.json: statement, split into five steps; not a Mathlib match.
- dag/nodes/sec-smooth-purity/lem-pur-affine-projection-connected-fibres.json: statement, Mathlib leaf, one-line specialization of AlgebraicGeometry.Scheme.Hom.isIrreducible_preimage followed by IsIrreducible.isConnected, with the affine-space instances inferred.
- citations.json: exact statement quotations for each step citation.
- searches.jsonl: actual search-command log; report.md: this report.

## Attachments

No attachment for the item. I searched lean/WeilConjectures for its blueprint tag, constant-section terminology, affine-space connectedness and zero-section terminology. The project helper AlgebraicGeometry.AffineSpace.isConnected_preimage_singleton_over in WeilConjectures/AlgebraicGeometry/AffineSpace/Components.lean:54 proves the new leaf's fact, not the full item's ordinary etale isomorphisms and naturality. Its Mathlib-only expression is recorded in mathlib_match; the new node needs no proof split. Existing section-comparison declarations are already attached to their own nodes and are reused.

## WANTED

None. The blueprint proof, Stacks source, and Mathlib source used here are available locally.

## What was wrong or incomplete

No statement dispute or change. The item was statement-only. Its geometric-fibre intuition needed an actual cited topological-fibre theorem, and the canonical locally constant section description alone did not explicitly state compatibility with arbitrary scheme pullback. I supplied the former as a Mathlib leaf and cited the existing constant-pullback-unit-continuous-map node for the latter. The imported lem-pur-a1-components cannot be used under the present hypotheses: its statement assumes a nonempty separated finite-type scheme over the fixed purity field and concerns the affine line. The present base is arbitrary and the rank can be zero. The project Components.lean source has stronger general helpers, but that does not strengthen the narrower DAG statement.

## Unfinished work

None at stage 1. No Lean was written and no compiler or build tool was run.

## Not duplicates

lem-pur-affine-projection-connected-fibres vs lem-pur-a1-components: the new leaf states connectedness of each topological fibre in all finite ranks over every scheme; the existing node states connected-component comparisons for the affine line and its puncture over a nonempty separated finite-type base in the fixed purity setting. It neither states the arbitrary-base fact nor the rank-zero case.
lem-pur-affine-projection-connected-fibres vs def-sbc-affine-space: the definition gives the affine-space object and coordinate charts, not connectedness of its fibres.
lem-pur-affine-projection-connected-fibres vs lem-sbc-subset-geometric-irreducibility: the latter transports irreducibility of a supplied subset between field extensions; it assumes irreducibility and does not establish affine-space fibre connectedness.

## Review by Q29

I read the chapter and unit records, the model-agreement paragraph of lem-pur-projection-purity-agreement, and the current main-20261015 vector-bundle orientation proof, especially Step 1. The route is exactly its clopen-locus argument. I also read Stacks Tag 03P5, label remark-constant-locally-constant-maps in etale-cohomology.tex:2438-2455, which identifies ordinary etale constant sheaf sections with Zariski-locally constant functions. The cited section-description node states that isomorphism and its normalization on constant values. It does not alone state the arbitrary-morphism pullback formula, which is why Step 1 also cites lem-weil-pbc-constant-pullback-unit-continuous-map. I opened that node's entire statement and its source declaration in WeilConjectures/AlgebraicGeometry/EtaleConstantSheafPullbackUnitContinuousMap.lean. Its formula applies to every scheme morphism, every abelian group and the identity etale object, so precisely gives precomposition on the functions in the item. Neither of these tools invokes a purity theorem or changes the unit route.

For the new leaf I read Mathlib/AlgebraicGeometry/AffineSpace.lean:393-415, Geometrically/Irreducible.lean:74-84, Topology/Irreducible.lean:70, and Topology/Connected/Basic.lean:67. The generic inverse-image theorem requires a geometrically irreducible morphism and an open underlying map. Both hypotheses are provided for affine-space projection by the actual instance at line 407 and isOpenMap_over at line 393, for every base and coordinate type. Applying to a singleton yields irreducibility; IsIrreducible.isConnected includes nonemptiness. This is the one-line specialization recorded in the leaf, not an unproved identification of scheme and topological fibres. Its statement deliberately names the topological inverse image directly.

In Step 2 I checked that the leaf supplies exactly connectedness of the subspace F_s and that the zero section lies in F_s. The latter follows on every affine chart by composing coefficient inclusion with evaluation at zero; def-sbc-affine-space states the coordinate chart and inclusion of constants used here. Step 3 uses the definition of connectedness: the fibre of a value of a locally constant function is clopen, and here nonempty because it contains e(s). Its complement is the union of all other open value fibres, with no finite-image assumption. This forces equality of b at x and e(p(x)). No extra topological descent theorem or connected-component openness is used.

Step 4 spells out both inverse identities. The additive structure comes from pointwise addition and the isomorphism of Step 1. The unit clause uses the additive group of A and the constant-value normalization; the proof actually detects all A-valued sections, so needs no extra theorem about a units sheaf. Step 5 uses the base-change construction and affine chart description stated in def-sbc-affine-space. I checked both coordinate identities, including h e-prime = e g because coordinates map to zero. I wrote both resulting function equations separately, so naturality of the inverse isomorphism is verified as well. The actual section equations follow from the precise formula established in Step 1.

I searched the entire DAG and the blueprint index with affine-space, connected-fibre, irreducible-preimage, locally-constant-function and zero-section phrases, and searched the project Lean source before creating the leaf. No existing statement has its arbitrary-base topological-fibre conclusion. The near match lem-pur-a1-components was read and rejected for its stronger base assumptions, rather than silently applying its more general Lean proof to its narrower node statement. All Mathlib queries recorded for the new node were run with msearch.py, and both semantic phrasings and the exact Loogle hit were read. The grep matches and their source lines were read. The item searches return coordinate universal properties and presheaf stalk comparisons, not the full theorem.

I tested the empty scheme, disconnected bases, d=0, the trivial coefficient group, and infinite coefficient groups. Empty bases require no fibre point and have the unique empty function; rank zero has singleton fibres and identity projection; disconnected bases are treated fibrewise. No Noetherian, finite-type or finiteness hypotheses were introduced. No new unsplit lemma restates a clause of the item: the only new node is a reusable geometric Mathlib leaf. All non-elementary steps are below 2000 characters. I checked B through E of delivery-errors.md, including the duplicate search, exact applicability of every citation, absence of inline hidden lemmas, source fidelity, and the lack of a circular dependency. citations.json copies the relevant full statements verbatim.
