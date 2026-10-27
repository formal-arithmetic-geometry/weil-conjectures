# Q143: lem-sfb-space-pushout-compatible-etale-charts

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-space-pushout-compatible-etale-charts.json: item, statement, split; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-space-thickening-etale-scheme-equivalence.json: new statement-only input, unsplit; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-space-pushout-etale-base-change.json: new statement-only input, unsplit; no Mathlib match.
- citations.json: verbatim statements for each proof-step citation.

## Attachments

None. The live WeilConjectures source was searched for the blueprint tag, compatible charts, infinitesimal/etale pushouts, and thickening equivalences. Scheme open gluing and finite-etale gluing do not state this algebraic-space result.

## WANTED

None. The necessary sources are present in literature/stacks-project/.

## Corrections and route

The mathematical statement is unchanged. Its imported doubled TeX escapes were normalized. It had an empty proof. I supplied four steps and two reusable prerequisites, rather than moving its atlas clauses into new nodes. The first input states the general equivalence of etale scheme objects over any algebraic-space thickening. The second states the universal mapping property after etale base change of any affine-thickening pushout, with no atlas or compatible-triple construction. Neither gives the item's conclusion on its own.

The construction follows the compatible-chart input at 07W0/07W2, with a different assembly below the unit: first lift X_1 across X -> Z by 05ZS; then identify the restriction over Y by full faithfulness. Finally use the etale specialization of 07W3's flat counit. This keeps the general etale-base-change theorem visible as a separate unsplit task; it must eventually be proved without using this item as a black box. There is no DAG cycle: neither new node cites the item or its flat-lfp parent. No flatness or finite presentation of X/S or Y/T^+ has been inserted. The etale map E -> Z itself supplies the hypothesis of the base-change input.

I read the latest blueprint direct-images proof (3), the chapter, and the recorded unit. The inherited long ancestry describes the infinitesimal-pushout tool supporting the alteration/moduli route. The current blueprint direct-images paragraph is higher-level preservation by compactification; the present local proof changes neither it nor the unit. The blueprint ancestor command returned None, matching the item's inherited null ancestor; new nodes retain it and prepend the item to the existing via list. Whole-blueprint searches: pushout, thickening, topological invariance, etale equivalence, flat base change, etale scheme, etale base change. Whole-DAG searches included 05ZS, 05ZH, 07VX, 07W0, 07W2, 07W3, and the relevant notions. No equivalent blueprint statement was found.

## Not duplicates

lem-sfb-space-thickening-etale-scheme-equivalence vs lem-sfb-space-pushout-compatible-etale-charts: equivalence of categories of all etale scheme objects over an arbitrary thickening; no pushout or compatible-atlas conclusion. The item constructs and compares covers using this equivalence.
lem-sfb-space-thickening-etale-scheme-equivalence vs lem-sfb-space-square-zero-ringed-realization: that node is about square-zero ring-sheaf extensions and their realization/maps, and its site equivalence is restricted to first-order thickenings; the new node allows arbitrary thickenings.
lem-sfb-space-thickening-etale-scheme-equivalence vs lem-sfb-space-first-order-ringed-description: that node has a site-equivalence clause only for first-order thickenings and then ring-sheaf extension classification; it does not lift etale objects for arbitrary thickenings.
lem-sfb-space-thickening-etale-scheme-equivalence vs lem-sfb-space-etale-thickening-detects-iso: the existing statement detects whether one given etale map is an isomorphism; it does not assert essential surjectivity or full faithfulness for scheme objects.
lem-sfb-space-pushout-etale-base-change vs lem-sfb-flat-lfp-space-pushout-gluing: the existing statement glues flat locally finitely presented spaces over a pushout of schemes; it does not state the counit for an etale scheme over a pushout of arbitrary algebraic spaces. In particular X,Y,U in this proof are not assumed schemes or flat over the original bases.

Other conceptually nearby nodes were read: sbc-lem-thickening-etale-site only concerns scheme bases (and has a different sheaf/cohomology clause); lem-sfb-scheme-pushout-flat-patching has scheme pieces, so does not apply over Z with arbitrary space pieces; lem-sfb-space-affine-thickening-pushout gives existence and recovery of glued pieces, not preservation by etale base change; lem-sfb-etale-affine-pinching-descent concerns schemes and finite pinching, not arbitrary affine morphisms of spaces.

## Mathlib search review

All new searches ran through msearch.py and are recorded in searches.jsonl. Each new node has two semantic phrasings, Loogle, grep and LeanSearch. The item was searched twice semantically and with Loogle, grep and LeanSearch, while retaining its earlier searches. The hits concern Scheme.Etale, base-change stability of Etale/Flat, affine-small-site sheaf equivalences, open gluing, and Spec of ring pushouts. I read the relevant local Morphisms/Etale.lean and Sites/AffineEtale.lean declarations: forgetting an etale scheme is fully faithful into Over X, and the affine-site equivalence concerns sheaf categories on the same scheme. Neither is invariance of scheme objects across an algebraic-space thickening. Spec of a ring pushout has the opposite variance (a scheme pullback), so cannot prove the geometric pushout-base-change assertion. The grep searches returned no relevant algebraic-space or thickening-pushout declarations. No unavailable search was called a negative result. There are zero new Mathlib leaves; the existing affine-morphism permanence Mathlib leaf is reused.

## Review by Q143

I read spaces-pushouts.tex, lemma-pushout-along-thickening-schemes (07SY), lemma-pushout-along-thickening (07VX), lemma-equivalence-categories-spaces-over-pushout (07W0), equation-cube-over (07W2), and lemma-equivalence-categories-spaces-pushout-flat (07W3), including the final flat counit. For the first new node I read spaces-more-morphisms.tex, lemma-thickening-equivalence (05ZS), and the surrounding proof using topological invariance and the fact that a thickening of a scheme is a scheme. Its actual statement is an equivalence of categories of etale schemes, precisely what the lift and full-faithfulness steps need. For the second new node I read the final counit of 07W3: the pushout of restrictions of a flat space recovers that space. An etale scheme over Q is a legitimate special case, and the new statement spells out the universal mapping property without asserting a scheme property of its restricted pieces.

Step 1 cites thickening-base-change for U -> Y and U_1 -> Y_1, fibre-products-etale-covers for U_1 -> U, the new equivalence for the lift Y_1 and the comparison isomorphism, and affine-morphism-permanence for scheme base changes of T -> S. I opened each statement. In particular the fibre-products node gives surjectivity of the pulled-back atlas, and the thickening node gives the homeomorphisms that make the elementary surjectivity argument work. This avoids silently assuming the lift is surjective merely from categorical equivalence.

Step 2 uses the geometric-pushout statement exactly for X -> Z being a thickening, then the new equivalence to lift the prescribed X_1 -> X. The base-change thickening statement gives X_1 -> E. Surjectivity of E -> Z follows by lifting a point of Z through the homeomorphism X -> Z, then through the surjective atlas; the commuting square supplies a preimage in E. No assumption on X/S is used.

Step 3 uses the fibre-products node to know E_Y is a scheme etale over Y, since E -> Z is representable etale, and to form its restrictions. Associating those fibre products is just their universal property. I checked that both E_Y and the prescribed Y_1 belong to EtSch(Y) and restrict to the same U_1. The new equivalence states a bijection on morphisms, which supplies both directions of the isomorphism; faithfulness proves the inverse equations. This uses the statement, not the proof, of the equivalence node.

Step 4 invokes precisely the new etale-base-change mapping property for E -> Z. It does not infer that arbitrary base change preserves arbitrary pushouts. The geometric-pushout node explicitly says a pushout of scheme pieces agrees with their scheme pushout; affine permanence applies to U_1 -> X_1, a base change of T -> S. The two pushout universal properties identify E and Z_1 while fixing both pieces. Thus the identified map to Z is the map requested in the item, and the two cartesian squares are exactly the identifications already constructed in steps 2 and 3. Every non-elementary fact has a node citation, and citations.json copies the corresponding statement verbatim.

I checked identity thickenings (the construction reduces to the original atlas), T empty (T^+ and U are empty and Z=X), X empty (U is empty and the thickening U -> Y forces Y empty), square-zero dual-number thickenings, and an arbitrary nil but not uniformly nilpotent ideal (for example (x_n) in k[x_1,x_2,...]/(x_n^(n+1))). The lifting theorem has no finite-order restriction, so that last case is allowed. For the etale-base-change input, the identity and empty E cases give the original and empty pushout. A non-surjective etale E is also allowed there: surjectivity is separately proved for the particular E used by the item. The proof covers every compatible pair, not just the one constructed in step 1. Every non-elementary step is below 2000 characters. The new nodes are statement-only and self-contained, with definitions inline and foundational notion dependencies. I corrected an initially implicit use of affine base-change stability by citing the existing Mathlib leaf. No source or statement dispute was found; no SGA source, Lean writing, compiler or repository modification was used.

## Unfinished work

The two new general statements remain unsplit by the one-level contract. Nothing in the item's natural-language assembly remains unproved relative to the explicitly cited inputs. Server validation and direct delivery follow this report.
