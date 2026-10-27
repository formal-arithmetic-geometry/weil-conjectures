## Worker report

Files written: dag/nodes/sec-six-functors-basics/lem-sfb-henselian-parameter-root-domain-tower.json (statement, split, no Mathlib match), citations.json, and this report. No Lean, repository, launcher, unit, or chapter files changed.

## New nodes

None. All algebraic input statements already have nodes. There are zero new Mathlib leaves.

## Attachments

None for the item. The source searches for the exact blueprint tag and for henselian parameter/root/domain/tower terminology found single-divisor results, not the full statement here. The closed declaration AlgebraicGeometry.IsRegular.isIntegral in lean/WeilConjectures/AlgebraicGeometry/Regular.lean:249 covers the already-existing lem-sc-regular-connected-integral and is used through that node. It is not an attachment for this item.

## WANTED

None. I read the ILO PDF and the Stacks TeX locally.

## Findings and corrections

The statement is retained verbatim. It is true even when a root degree is divisible by the residue characteristic: the radical hypothesis forces every root into every maximal ideal, so the argument uses the regular-quotient criterion, not an etale derivative criterion. Existing SNC root-regularity nodes require invertible degrees or an SNC global presentation and therefore are not substituted for the present hypotheses.

The inherited proof was empty. It is now twelve steps. In particular, the partial-parameter clause must not be justified by treating the parameter ideal as the maximal ideal, or by assuming henselianity along an arbitrary smaller ideal. Step 12 uses the genuine maximal-ideal henselian pair and its truncated-polynomial special fibre instead.

The filtered coefficient maps need not be injective: a unital map of domains may kill a nonzero element. Steps 8--10 use eventual equality and the fact that the particular labelled product f stays nonzero at every later stage, not a supposed injection of all stages. The canonical coefficient/root-colimit identification is proved by its universal property rather than by an uncited assertion that presentations commute with colimits.

No statement dispute, source error, or unfinished mathematical clause remains.

## Searches and reuse

I searched the complete DAG by the source tags 00NU, 00J9, 09XI, 0AFS and by root/free/regular, filtered/domain, connected/idempotent, regular-parameter/quotient and localization/exact terminology. I opened the statements of every cited node (the full statements are also the verbatim quotes in citations.json), checked unmerged ids, and checked that the nontrivial regularity/connectedness inputs have no dependency path back to the item.

Whole-blueprint searches with tools/blueprint_refs.py were run for `henselian parameter`, `regular sequence`, `connected integral`, `root regular`, `monic`, `filtered domain`, and `regular local generators`. No blueprint node states this full item. The ancestor command reports node null; its inherited ancestry chain and exact paragraph (3) open-direct-image place are retained. The current chapter and unit records were read together with the inherited split place. This work fills in the existing algebraic root-chart route, without changing the unit or chapter.

Mathlib searches were made only with the required msearch.py. I read its hits: HenselianRing and HenselianLocalRing give terminology, Jacobson containment, and Hensel lifting; AdjoinRoot.isDomain_of_prime (Mathlib/RingTheory/AdjoinRoot.lean:368, source read at 355--375) requires a prime polynomial, which is precisely not yet established here; the integral-Spec instance presupposes a domain. Neither gives the regular connected simultaneous-root theorem or its filtered extensions in one specialization. A second semantic phrasing was run. All queries are logged in searches.jsonl and recorded literally in the item, while its previous search records were preserved. The last search session disappeared after a provider interruption, but its completed log records its successful eight hits; I read those recorded hits and did not rerun it.

## Tool uses

lem-exc-regular-local-lift-regular-sequence-quotient is the general Noetherian-local criterion 00NU used in Step 5; lem-weil-pbc-regular-local-localization is the general localization theorem 0AFS used there; lem-weil-pbc-regular-local-generators-regular-sequence is the general parameter/quotient theorem 00NQ used in Step 12. These are algebraic black boxes rather than replacement routes for another geometric unit. They are declared in split_report.tool_uses for independent approval; no maintainer-owned top-level tool_uses was written. Other cited tools are Mathlib leaves, definitions or Lean-closed nodes.

## Not duplicates

No nodes were created. In particular I reused the monic quotient basis, nilpotent idempotent lifting, regular-local lifting criterion, regular-local localization, connected regular integrality, parameter-sequence theorem, filtered-ring element calculus and affine qcqs theorem rather than creating special cases of them.

## Review by Q40

I read ILO IX Proposition 2.1 on printed p.133 (PDF p.139), specifically its simultaneous parameter-root presentation before taking invariants. The present item is an agent extension of that local calculation; I did not claim that ILO states the filtered-coefficient or arbitrary-degree result. No SGA result is used, including the later SGA reference on the next PDF page. I read Stacks algebra.tex labels lemma-regular-mod-x (00NU), lemma-regular-ring-CM (00NQ), lemma-localization-of-regular-local-is-regular (0AFS), lemma-Noetherian-permanence (00FN), proposition-localization-exact (00CS), proposition-localize-quotient (00CT), lemma-disjoint-decomposition (00EE), and lemma-lift-idempotents (00J9), and more-algebra.tex lemma-characterize-henselian-pair (09XI). For integrality I checked properties.tex lemma-regular-normal (0569) and lemma-normal-locally-Noetherian (033N). There are no new nodes whose sources need a separate review.

Step 1 uses exactly uniqueness of lifting idempotents for finite algebras in def-weil-pbc-henselian-terminology. The two residue maps and the explicit Chinese remainder calculation show the radical containment; no separate unproved equivalence of definitions is used. Nonemptiness rules out C/J=0.

Step 2 uses the full monic-basis assertion of lem-weil-pbc-monic-quotient-free repeatedly, and the finite-type hypothesis of lem-weil-pbc-finite-type-algebra-noetherian is supplied by the displayed finite-variable presentation. Its basis includes a coefficient coordinate and therefore proves injectivity of C into K_n without a flatness theorem.

Step 3 uses the statement of lem-weil-pbc-finite-algebra-is-integral and then lem-weil-pbc-integral-algebra-ideal-in-radical: the latter explicitly supplies maximal contraction, not merely the going-up lemma. Every x_i is in the maximal ideal because its positive power is there. The quotient is literally C/J by elimination, and lem-weil-pbc-localization-at-prime-of-quotient gives exactly the local quotient claimed, with the contracted maximal ideal, not the unlocalized fibre ring.

Step 4 is the elementary coordinate calculation underlying the regular sequence; it does not hide a general preservation theorem. After quotienting the previous roots the coefficient ring is D_j, so the assumed injectivity of t_j is exactly the hypothesis used in the cyclic-shift matrix. The cited monic-basis node gives unique coefficients, the regular-sequence definition gives the injection, and the localization exactness and quotient nodes give the same assertion in the required maximal localization. The final quotient is nonzero by the hypothesis of Step 3. This verifies both conditions of the cited definition.

Step 5 applies lem-exc-regular-local-lift-regular-sequence-quotient with a Noetherian local ring (localization-noetherian supplies this), roots inside its maximal ideal, the sequence just proved, and the regular local quotient just identified. The criterion's statement says precisely that this ring is regular. lem-weil-pbc-regular-local-localization then gives all other prime localizations by localizing at a prime below a maximal ideal. The definition of regular ring is consequently met.

Step 6 uses henselian idempotent lifting for the finite algebra, followed by lem-weil-pbc-lift-idempotents-locally-nilpotent. The ideal is demonstrably nilpotent, with bound r(n-1)+1, so the second theorem applies. The connectedness-idempotent criterion is used twice only for nonempty schemes, as its statement requires. This is why the nonzero conclusion in Step 2 is recorded before connectedness.

Step 7 uses lem-weil-pbc-affine-open-stalk-localization for regularity of affine stalks and lem-sc-regular-connected-integral for the integral scheme. def-pc-integral-scheme supplies exactly the domain conclusion on its nonempty affine open, namely the whole spectrum. The nonzero-factor argument uses the actual definition of a regular sequence on the nonzero intermediate local quotient. Injectivity into K_n has already been established in Step 2, so no domain map is incorrectly presumed injective.

Steps 8--10 use only the representative and common-later-stage equality clauses of lem-pc-filtered-colimit-commrings-elementwise. I opened that statement: unlike the underlying-module or algebra representative-only nodes, it explicitly gives both clauses needed here. A zero product is moved to a stage and factored there; a zero labelled f would contradict its value at a later stage. Step 9 also cites the polynomial universal property and the colimit definition, which supply the maps and their uniqueness. Step 10 writes the power substitutions and the composition calculation and verifies nonempty directedness for both allowed root index sets.

Step 11 uses the exact fraction equality in def-weil-ring-localization-away to prove the localized domain property and retains f nonzero. The generic-point argument is written directly from prime ideals and basic opens of the spectrum in def-weil-affine-spectrum. The sole nontrivial geometric input is lem-weil-pbc-affine-scheme-qcqs, whose statement explicitly covers arbitrary affine schemes, so it applies also to the non-Noetherian colimits.

Step 12 uses exactly the regular sequence and every initial regular quotient in lem-weil-pbc-regular-local-generators-regular-sequence, after extending and reordering the partial parameter system. The radical lemma is applied to the maximal ideal of R, which is always available, and henselian idempotents are lifted from the finite algebra modulo that same ideal. The residual field plus nilpotent root ideal gives connectedness, so no hypothesis that the chosen partial parameter ideal equals the maximal ideal enters. Earlier finite and colimit arguments then give every listed conclusion.

I checked r=0 (empty basis product is 1, constant root diagram), n=1 (the cyclic-coordinate calculation reduces to multiplication by t_j and K_1=C), characteristic dividing n (no derivative/invertibility input), a nonzero field with empty parameter list, a henselian DVR with one parameter, and k[[u,v]] with the partial list (u). In the last case the parameter ideal is not maximal, yet reduction modulo (u,v) is the required truncated polynomial ring. The zero ring is excluded by residual nonemptiness; disconnected residual products are excluded explicitly. Noninjective coefficient transition maps cause no failure because all nonvanishing checks use the distinguished labels at later stages. No non-elementary step exceeds 2000 characters (the longest is Step 12 at 1143); the coordinate and common-stage steps are explicit routine arguments, not new lemmas disguised as long steps. I corrected the tempting smaller-ideal henselian inference and the tempting injectivity assumption before writing the final split. The statement itself required no correction.
