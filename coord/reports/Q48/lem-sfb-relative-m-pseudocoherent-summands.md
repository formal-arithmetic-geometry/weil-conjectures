## Worker report

Files written:
- dag/nodes/sec-six-functors-basics/lem-sfb-relative-m-pseudocoherent-summands.json: existing statement, now split in four steps; statement unchanged; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-scheme-m-pseudocoherent-summands.json: new statement-only absolute fixed-integer summand lemma; unsplit, no Mathlib match.
- citations.json: eight verbatim statement excerpts for the eight step/node citations.
- searches.jsonl: actual search-command log, retained with the delivery.

Attachments: none. Searches by item tag and by relative pseudo-coherence in lean/WeilConjectures found no declaration of the item. Read the scheme theorem AlgebraicGeometry.Scheme.pseudoCoherent_of_isIso_biproduct and the ring theorem DerivedCategory.mPseudoCoherent_summand: the former assumes all-degree pseudo-coherence, and the latter concerns modules over one ring, not arbitrary sheaf complexes. Neither attaches to this item or the new node. No Lean was written or compiled.

WANTED: none.

The imported statement is correct. The original item had no proof. Its Stacks source really is Tag 09UN, more-morphisms lemma-summands-relative-pseudo-coherent, lines 17069–17079 in this checkout. I expanded the source's appeal to definitions into chart selection, a binary K-injective comparison, the absolute summand lemma, and the same-chart conclusion. In particular, I did not replace fixed-m pseudo-coherence by the stronger all-m notion. The existing relative definition had already been independently reviewed and supplies exactly the existential charts required here.

Nothing remains unfinished in this one-level split. Its new statement-only input intentionally remains an open DAG item. One new node; zero new Mathlib leaves.

## New nodes

lem-sfb-scheme-m-pseudocoherent-summands — statement, unsplit; the fixed-m clause of Cohomology Tag 08CE on a scheme. Its statement introduces Y, m, A and B, and cites the existing scheme, derived-category and m-pseudo-coherence definitions. It contains no proof or proof dependencies.

## Searches and blueprint

Read SETUP.md's chapter/unit/node levels, the recorded chapter and unit, and the latest blueprint's sec-six-functors-basics chapter, sk-thm-sf-ctf-stability unit and direct-images proof. The inherited long chain supports the direct-image clause (3); this generic algebraic-geometry tool does not change that route. The ancestor script returns None, as for the already-reviewed relative definition; I preserved the inherited null ancestor and via chain, adding this item at the front only for the child. The inherited exact place was retained and the child's role in the 09UN proof specified.

Before creating the child I searched the whole DAG for 08CE, 09UN, the source labels, pseudo-coherence with summand/retract, and the existing declarations. Whole-blueprint searches used summand, pseudo-coherent summand, m-pseudo-coherent, m-pseudo-coherent summands, strictly perfect approximation, 08CE and 09UN. No blueprint node states the fixed-m scheme assertion. All chapters were included; same_as remains empty.

All new Mathlib records come from actual msearch.py invocations with this group and item. I read the returned signatures: finite-presentation and quasicoherent single-sheaf declarations do not assert a derived approximation property, and the derived-fraction and t-structure hits assert bounds or representatives without finite perfect approximations. Loogle returned zero hits for the quoted PseudoCoherent substring. Full-source grep returned zero for pseudo.?coher|IsMPseudoCoherent; an additional homology-directory search for strictly perfect / pseudo-coherent / MPseudo returned zero. A second and a third semantic phrasing still found only derived bounds and fraction representatives. There is no exact or one-line-specialization Mathlib match.

## Not duplicates

lem-sfb-scheme-m-pseudocoherent-summands vs lem-pc-pseudo-coherent-summand: the existing scheme statement assumes pseudo-coherence (all m), whereas the new statement assumes only one specified m. For example, on Spec k an infinite-dimensional vector space in degree zero is 1-pseudo-coherent (zero approximation) but not 0-pseudo-coherent; the stronger assumption is unavailable.

lem-sfb-scheme-m-pseudocoherent-summands vs lem-pc-ring-pseudo-coherent-summand: the existing fixed-m assertion concerns complexes of modules over one ring, not arbitrary complexes of sheaves on a scheme; passing from arbitrary sheaves to modules is not a one-line specialization and is not legitimate from fixed-m pseudo-coherence alone.

lem-sfb-scheme-m-pseudocoherent-summands vs lem-pc-affine-derived-summand-models: that statement lifts a decomposition of a sheafification of an actual module complex through the affine derived adjunction. It has no fixed-m approximation conclusion and assumes the total object already has a global affine module model. A local finite-degree approximation is weaker than that assumption.

lem-sfb-scheme-m-pseudocoherent-summands vs lem-pc-perfect-summand: the latter assumes and concludes perfectness, not fixed-m pseudo-coherence; its record mentions 08CE only as a tool in its proof.

lem-sfb-scheme-m-pseudocoherent-summands vs lem-sfb-relative-m-pseudocoherent-summands: the child concerns absolute pseudo-coherence on any scheme, with no structure morphism, affine embeddings or derived images. The item proves a relative assertion by applying the child to the two derived images on each ambient affine space. The child is the non-elementary lemma explicitly used by Stacks 09UN, not a restatement of either relative conclusion.

lem-sfb-scheme-m-pseudocoherent-summands vs lem-pc-affine-pseudo-coherent-localization-cover: the existing theorem starts from a sheafified module complex on Spec A that is pseudo-coherent for all m and produces a finite principal cover with all-m module models; it neither has the arbitrary-sheaf fixed-m hypothesis nor concludes pseudo-coherence of summands.

lem-sfb-scheme-m-pseudocoherent-summands vs def-sfb-m-pseudo-coherent-complex: this is the definition of the approximation condition, which the new node cites; its statement contains no summand-closure theorem.

lem-sfb-scheme-m-pseudocoherent-summands vs def-sfb-relative-pseudo-coherent-complex: this defines a condition via affine covers and derived images relative to a morphism, not closure of absolute fixed-m pseudo-coherence under summands. The shared 08CB tag refers to the underlying definition, not to the 08CE summand theorem.

## Review by Q48

I read more-morphisms.tex Tag 09UN (lemma-summands-relative-pseudo-coherent) with its entire two-line proof, and Tag 09UI (definition-relative-pseudo-coherence) with the preceding affine-embedding criterion. I compared every hypothesis: the morphism is locally finite type, m is any integer, K and L lie in the full unbounded module derived category, and neither quasi-coherence nor a Noetherian or uniform boundedness condition is present. The delivery leaves the statement unchanged.

For the child I read cohomology.tex Tag 08CE (lemma-summands-pseudo-coherent), including its local bounded-above reduction and cone/shift induction, together with Tag 08CB and the immediately following independence-of-representative lemma 08CC. The child is precisely 08CE's fixed-m assertion for the ringed space underlying a scheme, using the already-reviewed derived-map definition of m-pseudo-coherence. The proof of 08CE is not smuggled into the child's statement; it remains a statement-only node. The point of the child is that closure under summands at one m requires the cone induction and cannot be inferred just by projecting a perfect approximation.

Step 1 uses the actual statement of def-sfb-relative-pseudo-coherent-complex: it gives the chosen affine covers and closed immersions, and says their derived images are m-pseudo-coherent. It is not being cited for a locality theorem about all possible charts. Restriction and binary sum commute term by term and on stalks, so the original approximation really is one for the displayed restricted binary sum. Only those same charts are used later.

Step 2 uses def-pc-derived-direct-image to pass to the ringed-space construction; I opened def-pc-ringed-spaces-derived-direct-image and checked that its last sentence allows computation on EVERY K-injective resolution, not merely a preferred functorial choice. That matters here. I opened def-pur-kinjective-complex and checked the acyclic-to-null-homotopy condition: pairing the two component homotopies proves finite sums stay K-injective. The resolution is a quasi-isomorphism since kernels and images of the binary direct sum split. Direct image of modules is sectionwise and additive according to the ringed-space definition itself, so it commutes with this binary sum. Finally, lem-sfb-derived-localization-additive explicitly says Q is additive; applying Q to the two inclusions and projections preserves p_r i_s = delta_rs and i_1 p_1 + i_2 p_2 = 1. Those identities prove the derived binary-sum identification. This is the two-component calculation written in the step, not a hidden infinite-coproduct or derived-functor additivity lemma. It uses no boundedness or special closed-immersion exactness theorem.

Step 3 uses def-sfb-m-pseudo-coherent-complex for invariance under the displayed derived isomorphism: compose its approximation maps, keeping the same cohomology thresholds. The child's statement then gives exactly both summand conclusions at the same m on Y = A^n_V, with no unverified quasi-coherence hypothesis. This is the sole non-elementary step and it cites the child, not a definition in place of a theorem.

Step 4 invokes the relative definition a second time: the original affine covers and embeddings now witness each summand separately. There is no need to strengthen an existential chart condition to all embeddings or to choose a uniform bound. The union of the four uses lists is exactly proof_deps. Every cited node was read and has an exact statement excerpt in citations.json. No step is over 2000 characters.

Small cases checked: the empty source is vacuous; a zero summand gives the other summand unchanged; n=0 (a closed immersion into V itself) causes no change in the argument; m is arbitrary including negative values. The infinite-dimensional k-vector space in degree zero at m=1 versus m=0 checks why an all-m theorem is insufficient. A complex with arbitrary lower tail but zero cohomology in degrees at least m has a zero m-approximation, so the proof must not assume lower boundedness; it does not. A non-quasi-compact disjoint union may have different upper bounds on its charts, and the proof keeps all constructions local. Non-Noetherian bases cause no difficulty because neither finite-sum calculation nor Tag 08CE assumes coherence of the ring.

I checked delivery-errors B–E against the actual files and sources. The main correction to the tempting initial route was rejecting the all-m scheme theorem as an inadequate citation for fixed m and isolating its precise missing absolute lemma. No definition was added, no elementary calculation made into a new node, and no clause of the relative item was relabelled. No SGA source, off-unit proof tool, new target, unit edit or repository write is involved. Search logs and citations were checked against the records actually written.

Dry-run repair: the first full dry run listed three additional records sharing the subsidiary definition tag 08CB. I opened all three statements and added the explicit comparisons above. The localization-cover theorem has the stronger all-m and sheafified-module hypotheses; the other two are definitions, not closure theorems. No node change was warranted.
