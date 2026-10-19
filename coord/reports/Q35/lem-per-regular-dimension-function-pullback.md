## Worker report

Item: lem-per-regular-dimension-function-pullback. Group: Q35. Stage 1 only.

### Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-regular-dimension-function-pullback.json: statement, retained verbatim; eight proof steps, split, no Mathlib match.
- dag/nodes/sec-deligne-laumon-a1/lem-per-dimension-functions-strict-localization.json: new statement-only lemma, unsplit, no Mathlib match. It states restriction and testing of dimension functions at strict localizations, not the regular pullback formula.
- citations.json: one verbatim statement quotation for each node cited in each proof step.
- report.md: this report and direct-delivery self-review.

### Attachments

None. A search of /home/ubuntu/weil-src-slopmaster2/WeilConjectures for the item tag, dimensionFunction, dimension_function, dimension function and codimensionFunction returned no declaration. The upstream master source is not used as evidence of a completed proof. The existing Mathlib leaf lem-weil-pbc-flat-height-formula carries Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (Mathlib/RingTheory/Ideal/KrullsHeightTheorem.lean:462); this is already a DAG node, not a new attachment or new leaf.

### Literature

No WANTED document. I read ILO, Travaux de Gabber, Expose XIV Definition 2.1.8 and following paragraph (pp.211–212), Proposition 2.1.4, Theorem 2.2.1, Corollary 2.2.4 and the proof of Lemma 2.2.5 (pp.210–213), Proposition 2.5.4 and its proof (pp.217–218); also Expose XVII Lemma 4.3.2.3 (pp.284–285). The PDF is literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf; gabber.txt in this sandbox is the existing extraction. I read Stacks algebra.tex, Tag 00ON, lemma-dimension-base-fibre-equals-total, and schemes.tex, Tag 0HA1, lemma-local-ring-fibre. The steps cite those documents or the ILO result, and use no SGA source.

### Findings and changes

The imported item has the correct sign and hypotheses: delta_P(u) = delta_X(r(u)) minus the dimension of the local ring of the fibre. It is the assertion of ILO XIV Proposition 2.5.4. I kept its statement and statement dependencies unchanged. The original empty proof was not a split. The existing split in this interrupted sandbox is retained, together with its searches and citation records. There was no report or running delivery when this continuation began; the required server review_split check was run first and passed before writing this report.

The source compares a dimension function on a strictly local source with the proposed formula, first on fibres and then on their generic points. The split follows that comparison. To make the last codimension assertion explicit, it uses the existing flat height formula on A/p -> B/pB instead of abbreviating the calculation as Hauptidealsatz. The proof is therefore marked agent-written. The local domain descent and the quotient-localization computations are written in the steps, rather than made into elementary new nodes. In particular it never cites lem-per-regular-specialization-geometry, which already depends on this item.

The chapter and unit records were read. This is a local-geometric input below the unit, through the ancestor lem-per-artin-gabber-affine-curve and its dimension-normalized duality argument. The current main-20261015 ancestor statement was read; there is no blueprint_update on this item. Its recorded ancestry and blueprint place are retained, and the new lemma records that same ancestor, via the item. No unit realization or fixed route is changed.

### Searches and reuse

I read all ten records in searches.jsonl. The first five are the item's first and second formulations, using grep, Loogle, LeanFinder and LeanSearch. Smooth relative dimension, flat base change and the prime height equality are the returned candidates; only the latter is used, through its existing DAG node. Smoothness with a fixed relative dimension does not state regular pullback without finite presentation. The remaining five searches concern the new strict-local locality lemma, with a second etale-local phrasing. The hits concern localization bounds, ring equivalences, Krull dimension and the etale locus, and do not state restriction/testing of integer-valued dimension functions. No service in these ten records was unavailable. The stored query texts, tools, results and no-match verdicts have been preserved, rather than claiming any new search execution.

The whole DAG was searched for dimension functions and strict localization, and the whole imported blueprint was searched with tools/blueprint_refs.py for dimension function and strict localization. The dimension-function query has no blueprint match. The existing local existence/calculus, finite-type dimension-function, immediate-specialization, strict-local fibre and perversity-localization nodes were opened to distinguish their statements. There is no existing node giving the new equivalence. The new node is statement-only, has all its definition dependencies and provenance, and its searches include all required services and a second phrasing.

### Unfinished work

No unfinished split work. The new strict-local locality lemma remains unsplit intentionally, as required for a one-level split. Validation and delivery are performed by the prescribed server tools.

## Not duplicates

lem-per-dimension-functions-strict-localization vs lem-per-local-dimension-function-calculus: the existing node gives local existence and differences equal to codimension on one universally catenary scheme; it does not give pullback or the converse test along strict localizations.

lem-per-dimension-functions-strict-localization vs lem-per-finite-type-dimension-function: that node treats locally finite-type maps with a residue-field transcendence-degree correction; strict localization is not generally locally finite type, and it does not give the converse locality criterion.

lem-per-dimension-functions-strict-localization vs lem-per-strict-localization-discrete-fibres: that node states nonempty discrete fibres of a strict localization, not preservation or testing of dimension functions.

lem-per-dimension-functions-strict-localization vs lem-per-immediate-specialization-criterion: the existing node compares geometric and Zariski immediate specializations on one scheme; it does not compare dimension functions on a scheme with its strict localizations.

lem-per-dimension-functions-strict-localization vs lem-per-perversity-localization-calculus: that node concerns derived t-structures and t-exact restriction for a prescribed perversity; it does not assert that a pulled-back dimension function has the codimension-one decrement or the converse.

lem-per-dimension-functions-strict-localization vs lem-per-regular-dimension-function-pullback: the new node is a locality criterion for an arbitrary integer-valued function. It neither assumes a regular morphism P -> X nor gives the fibre-dimension correction. The item's mathematical argument remains in steps 2–8.

## Review by Q35

I checked the split against delivery-errors B–E with the source and the cited node statements open. For the item I matched regularity, excellence, the local-ring fibre dimension and the minus sign against ILO XIV Proposition 2.5.4. In particular I did not replace regularity by smoothness. For the sole new node I matched the definition and etale restriction/locality paragraph of XIV 2.1.8 and the explicit strict-local reduction at the start of XIV 2.5.4. The new assertion records that locality input separately, with Noetherian excellence stated and the meaning of dimension function expanded; its statement contains no proof sketch or implicit reference to an unnamed setting.

Step 1 uses the new lemma in both directions, and lem-per-regular-strict-local-model for exactly the asserted regular local morphism, Noetherian excellence and equality of all local fibre dimensions. The full statement of that existing node includes these equalities; no argument hidden in its proof is being used. def-weil-flat-morphism defines flatness by stalk maps, so at the closed point of the two affine local schemes it gives flatness of A -> B. Neither the new lemma nor the local-model node assumes finite type.

Step 2 uses lem-per-local-dimension-function-calculus for existence on the local universally catenary Y, def-exc-excellent-ring for the bounded saturated-chain condition, and lem-per-immediate-specialization-criterion for Zariski immediate implying geometric immediate. Those statements do supply exactly those claims. I checked that the codimension calculation needed later is the ordinary local closure dimension: a saturated chain in the interval is finite and has maximal length by the bounded catenary condition, and every adjacent decrement is one. Its sum is the required dimension. No stronger identification of arbitrary strict-local components is taken from a definition node.

Step 3 uses lem-per-strict-local-regular-integral-fibres. Its statement explicitly requires a local morphism of Noetherian strictly local schemes, available from step 1, and gives nonempty integral geometric fibres. The displayed linear retraction along the residue-field extension proves the domain assertion for the ordinary affine fibre; it is not an uncited descent theorem. def-weil-pbc-localization-at-prime supplies the fibre-ring description. The source XVII 4.3.2.3 has precisely this strict-local hypothesis. I do not assert integral fibres for an arbitrary regular morphism.

Step 4 uses lem-weil-pbc-flat-module-base-change to get flatness of B/pB over A/p, and lem-trf-flat-module-torsionfree-domain to get injectivity of nonzero scalar multiplication. These are actual statements about modules, not just a definition of flatness. A/p is a domain because p is prime. The remaining kernel argument is written explicitly: zero in the localization means annihilation by a nonzero scalar, and torsion-freeness forces zero. Nonzero fibre in step 3 excludes the zero quotient. Thus pB is prime, contracts to p, and gives the unique fibre-generic point. I checked the distinction between the quotient B/pB and its localization, which is the fibre ring.

Step 5 applies the local dimension equality in lem-weil-pbc-flat-height-formula, not merely a claim about finite-type algebras. I read Stacks Tag 00ON: Noetherian rings and going down suffice, and flatness supplies going down. The rings here are the Noetherian quotients A/p and B/pB. The target prime is mB/pB, its contraction is m/p, and its local closed fibre is the fraction field of the domain B/mB, of dimension zero. def-weil-pbc-localization-at-prime states the localization and fibre-ring conventions. All hypotheses needed for the equality are established by step 4, with no finite-type assumption added.

Step 6 cites no further theorem: it subtracts the two explicit chain equalities of step 2, using the dimension equality of step 5. This is elementary arithmetic, not a renamed copy of the item. It establishes constancy of d_S(p)-d(pB) at the fibre-generic points. This avoids the dependency cycle through regular-specialization-geometry.

Step 7 uses lem-sbc-scheme-fibre-stalk-quotient, whose statement gives the isomorphism O_Y,q / m_p O_Y,q with the local ring of the scheme-theoretic fibre, not a tensor product before localization. I checked it against Stacks 0HA1. In the affine notation the ideal is pB_q. The closure of the already proved prime pB therefore has local ring B_q/pB_q. Its dimension is precisely b_f(q), so step 2 gives d(q)=d(pB)-b_f(q). The elementary successive-localization identity is also written in the step. This existing off-unit node is a generic scheme tool; split_report.tool_uses declares that usage, since this unit has no separate fibre-stalk formula. No maintainer-owned tool_uses field is edited.

Step 8 substitutes steps 6 and 7 and obtains the proposed function as d plus one integer independent of q. Adding a constant preserves each decrement by one by subtraction. The new locality lemma then supplies descent back to P. Thus the elementary flag is justified by an arithmetic identity and a direct use of a cited statement, rather than an unproved global claim. No non-elementary step exceeds 2000 characters.

For the new lemma I tested the empty scheme (both conditions vacuous), a field (all specializations have length zero), and a strictly henselian local scheme (the closed-point localization is the original local scheme). For a smooth curve the formula gives zero correction for an etale map and, over a field, minus one at a closed point of a one-dimensional fibre, with the required decrement from its generic point. For a general local flat regular map the proof retains quotient and fibre separately, so it does not assume the base is a domain: it passes to A/p separately for every p. Identity specializations give zero length and no erroneous decrement. Nonreduced bases are permitted; reduced closures and the primeness of pB, obtained from integral fibres and flatness, are what the calculations use.

The review found no statement dispute or source error in this item. I retained the earlier sandbox proof and exact logged queries after checking their results, and supplied the missing substantive review/report. I checked that every cited node's actual statement contains the quotation stored for it in citations.json. The only new node is a genuinely separate locality lemma, not an elementary algebraic computation, a duplicate, or a clause merely relabelled from the item. No Lean, compiler, live-project file or launcher file was written or run.
