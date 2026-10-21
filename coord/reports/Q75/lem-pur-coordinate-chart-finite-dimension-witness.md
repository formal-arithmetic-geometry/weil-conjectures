# Q75: lem-pur-coordinate-chart-finite-dimension-witness

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-coordinate-chart-finite-dimension-witness.json`: statement node, split in nine steps; the complete witness is not a Mathlib leaf. All subsidiary facts already have DAG nodes. Zero new nodes and zero new Mathlib leaves.
- `citations.json`: one verbatim statement quotation for each of the 19 step citations.
- `report.md`: this report. `searches.jsonl` was produced by the prescribed search command.

## Attachments

None. Searched the live `lean/WeilConjectures/` for the exact blueprint tag and the coordinate-chart, finite-dimension-witness, minimal-prime and etale local-dimension notions. No project declaration states this entire witness. The standard-smooth polynomial-chart results and local etale statements found by search do not give all its conclusions.

## WANTED

None. Every source used is available locally in the Stacks project. Read the current main-20261015 `lem-pur-frame-independence` statement and proof as the blueprint ancestor, as well as the chapter and unit records. This item supplies the commutative-algebra witness extracted by the coordinate-model node; it makes no change to the purity proof route.

## Corrections and observations

The item was statement-only. Its statement is correct and unchanged; no STATEMENT-DISPUTED claim arises. The original source field explicitly says its smooth-openness tag alone does not assert this witness. The proof now supplies the witness rather than treating that tag as its proof.

It is unnecessary to prove openness of the projection to the base. Instead, the open image of the restricted etale map contains a prime P of R[u]. A minimal prime s below P contracted to R gives the prime sR[u] below P, which stays in that open. This produces the required point directly. It avoids a separate smooth-composition or projection lemma.

The nil ideal in a local ring over the minimal base prime need not be nilpotent with a single exponent. The finite-sum calculation in Step 7 establishes precisely nilness, which is sufficient for the prime-poset argument in Step 8. No dimension subtraction, Noetherian dimension formula, finiteness of dimension of the base, or reducedness is used.

The required msearch calls for the complete item returned standard-smooth/etale-locus and generic-point results, not the combined witness. A second phrasing searched for the generic-fibre point through a nonempty open. Additional searches found etale base-change declarations, and the DAG search found the already existing exact Mathlib leaf `lem-weil-pbc-etale-scheme-base-change`, so no new node was created. One grep used a single-file root; msearch's output then had unlabelled line entries. I repeated the relevant grep with a directory root and read the labelled Etale.lean hits, rather than treating those unlabelled entries as file names. All executed queries are preserved in the log and recorded honestly in the item.

## Unfinished work

None in the stage-1 split. There are no new statement-only nodes. Existing dependencies remain assigned to their existing DAG nodes; this delivery does not edit them or claim their Lean proofs are finished.

## Not duplicates

No new nodes. In particular, reused existing nodes for etale base change (02GO), etale openness (03WT), prime containment of a minimal prime (00E0), minimal-prime localization (00EU), etale local dimension (07QP), polynomial-origin dimension (00OP), affine stalk localization (01HV), and the fibre-stalk quotient (0HA1).

## Review by Q75

I checked the statement under its actual arbitrary-base hypotheses before writing the proof. I read Stacks morphisms.tex `lemma-base-change-etale` (02GO) and `lemma-etale-open` (03WT), algebra.tex `lemma-Zariski-topology` (00E0), `lemma-minimal-prime-reduced-ring` (00EU), and `lemma-dim-affine-space` (00OP), more-algebra.tex `lemma-dimension-etale-extension` (07QP), and schemes.tex `lemma-spec-sheaves` (01HV) and `lemma-local-ring-fibre` (0HA1). The proof is marked agent-origin because the assembly into this particular witness is mine; the cited component statements are from these sources. The sources impose no Noetherian hypothesis in the places where the proof uses them. The source for 00OP requires a field, which is verified by passing to K = kappa(s)(u), and requires a maximal ideal, which is the coordinate origin ideal (v).

Step 1 uses the actual second-projection assertion of `lem-weil-pbc-etale-scheme-base-change` for the inverse-image chart, its affine-base restriction, and Z to Y, with the harmless factor exchange in Z = Y times_X T. It uses `lem-weil-pbc-etale-morphism-open-map` only to assert openness of its image. `def-sbc-affine-space` gives exactly the coordinate-ring description over Spec R, and `def-pc-scheme` supplies affine neighborhoods. No claim of openness is being extracted from a definition of smoothness.

Step 2 uses `lem-weil-pbc-prime-contains-minimal-prime` with I = 0 and p = P contracted to R, not with an arbitrary nonexistent minimal prime in a prescribed closed subset. Its statement gives exactly the minimal s below p. The remainder is written out: the polynomial quotient by sR[u] is a polynomial ring over a domain, sR[u] lies below P, and a basic-open test keeps it in the image. Thus this step proves its small prime/open calculation itself and does not hide a separate generic-point existence lemma.

Step 3 uses `def-weil-pbc-localization-at-prime` for the residue field fractions, `def-sbc-affine-space` for the fibre polynomial coordinates, and the explicit localization conclusion (c) of `lem-weil-pbc-affine-open-stalk-localization`. Reducing the chosen polynomial prime yields zero, and the zero prime is generic by the definition of Zariski closure. Step 4 uses that same affine-stalk conclusion for the ambient local ring and writes both directions of its localization identification over the rational function field. No claim that the ambient image is a closed point in the entire affine space is made: (v) is only maximal after passing to K[v].

Step 5 uses exactly the dimension clause of `lem-weil-pbc-polynomial-ring-origin-regular-local`, with the field K and number of variables b. A field's dimension zero is checked directly. Step 6 uses the base-change node for g_s and h_s and the unrestricted ring statement of `lem-sc-etale-local-dimension`, not a Noetherian flat height formula. `def-weil-etale-morphism` explicitly includes the equivalent affine-chart characterization needed for the ring maps, and the affine-stalk node identifies their prime localizations with scheme stalks.

Step 7 uses exactly the first assertion of `lem-weil-pbc-minimal-prime-reduced-localization-field`: every element of the maximal ideal is nilpotent. It does not use the reduced-ring clause. The displayed finite multinomial argument proves the nilness of the extended ideal. Step 8 uses the first quotient isomorphism of `lem-sbc-scheme-fibre-stalk-quotient` separately for Z, T, Y and X; its statement allows arbitrary scheme morphisms. All four selected points lie over s because all maps are over S. The quotient prime bijection and equality of chain suprema are written out, so no non-elementary nil-invariance lemma is silently being assumed.

Step 9 again uses the precise dimension equality in `lem-sc-etale-local-dimension`, on the original etale maps rather than confusing them with the fibre morphisms. The affine-stalk and etale-definition citations justify its ring-local applications. The fibre-product relation gives x = i(y) without a new geometric lemma.

I checked the small cases a = 0, b = 0, a = b = 0, and the exclusion of empty Z. Over a field this is the usual generic point of the coordinate subspace. Over a nonreduced base such as k[epsilon]/(epsilon squared), Step 7 retains the nil ideal instead of falsely identifying the local rings with their reductions. Over a ring k[epsilon_1,epsilon_2,...]/(epsilon_i^(i+1)), the maximal nil ideal has no uniform nilpotence bound, and the same finite-sum proof still works; over an infinite-dimensional domain the choice s = 0 removes the base dimension without subtraction. The zero base ring cannot occur in the selected affine neighborhood, since that neighborhood contains the image of z_0.

I checked B through E of delivery-errors against the final item: no new nodes, no statement changes, all cited statements opened and quoted, no circular subsidiary statement, no unsupported standard comparison, and no step over 2000 characters. The three non-Mathlib generic tools from other units (etale local dimension, polynomial-origin dimension, fibre-stalk quotient) are declared individually in split_report.tool_uses for the maintainer's judgement. The ancestor reference and original metadata are retained.
