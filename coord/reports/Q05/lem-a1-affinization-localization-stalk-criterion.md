# Worker report — Q05

## Files written

- `dag/nodes/sec-purity-real-sheaves/lem-a1-affinization-localization-stalk-criterion.json`: statement node, now split into six steps; no exact Mathlib match. The statement and its statement dependencies are unchanged.
- `citations.json`: 15 literal statement quotations, one for every step/node citation.
- `report.md`: this report. New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searched the live project's `lean/WeilConjectures/` for the exact blueprint id, affinization, and stalk-criterion descriptions. No declaration states all clauses. The derived-global-sections affinization comparison concerns derived objects on schemes, not this arbitrary locally ringed space or its filtered-stage localizations.

## Wanted sources

None. All sources used are present locally.

## Findings and corrections

The imported item was statement-only. No mathematical error or missing hypothesis was found, so its statement is preserved verbatim. The source's sentence “For any e” in Stacks Tag 0API compresses the passage from stage local rings to the colimit-ring stalk and the resulting identification of structure sheaves. The split supplies those details and retains the requirement that the sheaf isomorphism is induced by the original j, not chosen separately.

The work follows Tag 0API (more-groupoids.tex, lemma-sits-in-functions), in the existing Gabber descent branch below lem-a1-affine-hc0. The chapter and unit records and the three levels of SETUP.md were read; no chapter route or unit statement is changed. The apparently remote Rankin–Selberg unit assignment is inherited from the blueprint ancestor, not a new route selected here.

## Search evidence

Read the item's inherited searches, then ran and recorded fresh LeanFinder, Loogle, LeanSearch and Mathlib grep searches through the required msearch.py command; all services answered. A second LeanFinder phrasing specifically searched for filtered rings all of whose stage prime localizations map isomorphically to a fixed local ring. The hits are spectrum stalks, the affine adjunction, maps induced by a ring homomorphism and iterated localization. They do not assert the item's filtered-stage implication together with the specified structure-sheaf comparison. The commands' exact queries and result digests are in searches.jsonl and are copied into the item without changing the inherited records.

Searched the whole DAG for localization-colimit and sheaf-stalk isomorphism statements, and used blueprint_refs.py searches for stalks, localization, localization colimit, sheaf isomorphism stalk, and affinization. Read the existing generic localization-colimit, affine-spectrum stalk, topological inverse-image stalk, sets-sheaf stalk criterion, filtered commutative-ring elementwise, inverse-image-adjunction and ringed-subspace statements. Thus neither the localized-colimit lemma nor a new ringed-space criterion is duplicated. The categorical inverse calculation and the conversion of bijective ring maps into ring isomorphisms are explicit elementary arguments in the item.

## Not duplicates

No new nodes were created. Existing lem-weil-pbc-filtered-colimit-localization-at-prime is used directly, rather than reproduced as a differently named local-ring lemma. Existing lem-weil-pbc-topological-inverse-image-stalk and lem-weil-pbc-sets-sheaf-iso-on-stalks provide the sheaf inputs.

## Review by Q05

I read Stacks more-groupoids.tex, Tag 0API (lemma-sits-in-functions), including its canonical morphism, colimit and local-ring comparison. For the algebra input I read the full statement of lem-weil-pbc-filtered-colimit-localization-at-prime: it supplies both the localized transition maps and the particular cocone maps to C_q, not just existence of an abstract colimit. For the sheaf part I read sheaves.tex, Tags 008H (lemma-stalk-pullback) and 007T (lemma-points-exactness), and the inverse-image adjunction preceding 008H. For the affine map I read schemes.tex, Tags 01I1 (lemma-morphism-into-affine), its germ square and the construction on basic opens, and used the existing affine-spectrum stalk statement for Tag 01HV. There are no new node sources to audit.

Step 1 uses the spectrum-stalk node's part (1), which has no domain hypothesis on R; the domain hypothesis belongs only to its unused part (2). Its isomorphism is an isomorphism of C-algebras, so the stalk map's restriction is the original germ map. The affine-adjunction node applies to arbitrary locally ringed spaces. The morphism definition supplies the compatibility of germs, and the localization definition supplies fractions and inverses. Consequently beta denotes the actual j stalk map in these coordinates.

Step 2 uses the existing localization-colimit statement with the small directed poset I viewed as a filtered category. Nonemptiness, smallness and compatibility of r_i are all hypotheses of the item. The primes are contractions of q, so all localized transition maps and their denominators are legitimate. I wrote the compatibility with the assumed theta_i on a/s explicitly; no additional compatibility of independently chosen abstract isomorphisms is assumed.

Step 3 uses only the colimit universal property and elementary algebra. The inverse gamma is defined using i_0, whose existence uses nonemptiness. For another stage, a common upper bound proves that its formula agrees with gamma. The two composites are checked separately, and the second is an identity because it agrees on every colimit leg. There is no hidden assertion that the transition maps A_i to A_k are injective or that the colimit is a union.

Step 4 uses the ringed-subspace definition with the exact inverse-image sheaf i^{-1}O_Y, and the inverse-image stalk node with coefficient category commutative rings, which its statement explicitly allows. That gives local rings on F even if F is not open or closed. The topological inverse-image node explicitly states the adjunction on ring-valued sheaves. Its adjoint of j sharp gives alpha and the equation i_*alpha composed with eta equals j sharp; no descent or effectivity assertion is being imported here.

Step 5 uses the germ compatibility clause of that inverse-image-stalk node, not just an abstract isomorphism. The homeomorphism h identifies the neighbourhood systems, so its direct image has the same stalk at the corresponding point. These facts identify alpha's stalk map with the already proved j stalk map. The sets-sheaf criterion is used only after accounting for its coefficient category: the existing filtered commutative-ring elementwise theorem gives the same representatives and equality relation as the set germ construction. This is sufficient to identify set and ring stalks. Inverses of the resulting bijective section ring maps preserve operations and restrictions; that elementary check is written out. This avoids citing a scheme-module criterion for arbitrary ring sheaves.

Step 6 uses the definitions of locally ringed-space morphism and ringed subspace. It explicitly specifies the inverse section maps over the inverse homeomorphism. The stalk maps in both directions are ring isomorphisms, hence local; the subspace inclusion's stalk maps are identities in the canonical coordinates. The original j is recovered by the already established adjunction equation, so the conclusion concerns the required sheaf-map factorization.

I checked B1–B10: no new unsplit statements or duplicate leaves, no new notions without definitions, all expressions use single TeX escapes in their decoded text, sources identify tags and labels, and searches are actual logged calls. I checked C1–C8: every non-elementary input is a cited statement; citations.json contains exact substrings from all 15 uses; no proof of a cited node is used as extra data. Generic off-unit inputs are declared in split_report.tool_uses with their role. I checked D1–D5: no clause has been moved into a replacement node, and both formerly implicit comparisons are argued explicitly. I checked E1–E7 on the actual hypotheses and objects: no affineness of Z, no scheme structure on F, no openness or closedness of F, and no injectivity of ring transition maps is used. No proof step exceeds 2000 characters.

For small cases, I checked a one-object directed system, where the algebra reduces to the assumed theta isomorphism; constant systems; and empty Z, for which the stalk assertions are vacuous and the unique sheaves on the empty subspace give the asserted isomorphism. For nonempty Z, q is a genuine prime and all fraction formulas use denominators outside its contraction. Arbitrary noninjective transition maps cause no difficulty because the inverse argument is expressed through cocone identities. The identity homeomorphism case recovers a stalkwise isomorphism of the original ring sheaves. No statement dispute is needed.

## Unfinished work

None in the stage-1 split. The required server dry run and delivery are performed after this report is written; the maintainer supplies the independent review.
