# Q42: lem-a1-relative-affinization-compatible-charts

## Files written

- `dag/nodes/sec-purity-real-sheaves/lem-a1-relative-affinization-compatible-charts.json`: statement, split; no Mathlib match for the whole statement. Four proof steps, using existing nodes only.
- `citations.json`: eight literal statement quotations, one for each cited node in each step.
- `searches.jsonl`: five searches run with the prescribed msearch command, including two distinct LeanFinder phrasings. The item retains its earlier recorded searches as well.

New nodes: 0. New Mathlib leaves: 0. No Lean written or compiler invoked.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact item tag and for relative-affinization and compatible-chart terminology. The existing `AlgebraicGeometry.affine_algebra_local_maps` is a useful general dependency, not a declaration stating this item's full conjunction, so this is a split rather than ATTACH.

## WANTED

None.

## Findings and changes

The item was a statement-only node, and its statement agrees with Constructions Tag 01LY, `lemma-canonical-morphism`, read in `literature/stacks-project/constructions.tex`. The local compatibility requested here is furnished by the existing, more general `lem-weil-pbc-affine-algebra-local-maps`, which also specifies the section map. Thus there is no reason to create a new overlap-comparison lemma. Applied to the inverse algebra isomorphism, this existing statement gives the difficult part of the construction; the assembly steps still check quasi-coherence, construct the relative spectrum, factor through each open chart, and compute the chart ring map.

I preserved the statement and all maintainer-owned data. The blueprint ancestor is `lem-a1-affine-hc0`, through `lem-a1-quasi-affine-target-locality`; the recorded ancestor place is already precise. I read the current main-20261015 proof of the ancestor, the chapter and unit records, and the parent's current Tag 01SM proof. The ancestor's original lisse-support proof does not itself discuss relative Spec: this node is the generic scheme tool introduced below its affine-locality dependency. Its split keeps that route. The item is not the unit's key statement and no unit realization fields were changed.

## Not duplicates

No new nodes were created. The whole-DAG searches for Tags 01LY, 01LC and 01SA and for relative spectrum, direct-image quasi-coherence and affine-algebra local maps found the existing dependencies used here. Blueprint searches with `relative affinization`, `relative spectrum`, `affine algebra`, `morphism into affine` and `pushforward` found no blueprint node that states this item. In particular `lem-trf-qcqs-relative-affinization-map` gives a global canonical map and its charts, so it implies this item; I read its statement and dependencies, but used the smaller existing generic ingredients directly instead of making the proof a single application of a parallel relative-affinization theorem.

## Mathlib searches

All five new search records are copied verbatim from this sandbox's msearch log, with the same tool and query text and a separate verdict. LeanSearch and Loogle were available. The first LeanFinder phrasing found normalization maps, ideal-sheaf maps, Spec section formulas and maps into affine spectra. The second found absolute Gamma-Spec and Spec functor maps. The Loogle query found stalk-pushforward formulas, pushforward of modules along Spec, and affine-etale equivalences. The grep found absolute `toSpecΓ` and affine predicates, stalk and residue-field maps, and Proj charts. I read Mathlib `GammaSpecAdjunction.lean` around `Scheme.toSpecΓ` and `AffineScheme.lean` around `IsAffine` and `Scheme.isoSpec`. These are the absolute constructions; none gives the quasi-coherent algebra's relative-Spec realization plus a compatible family over an arbitrary base. Hence no whole-item Mathlib leaf is claimed. The exact Gamma-Spec correspondence is already the existing Mathlib node `lem-weil-pbc-morphism-into-affine-scheme`.

## Review by Q42

I checked the statement against Tag 01LY (`lemma-canonical-morphism`) and its proof: its hypotheses are precisely qcqs on h, and it constructs the map from the identity algebra map, with the absolute affinization map on affine base opens. I also read Section `section-spec`, which explicitly describes an algebra map A to f_*O_T as the equivalent input to the relative-Spec functor, and Tags 01LW/01LX (`definition-relative-spec`, `lemma-spec-properties`) for the affine chart and algebra isomorphism. No new nodes require a separate source check.

For step 1 I opened the full statements of `lem-weil-pbc-spec-tilde-free-module`, `pqf-def-coherent`, `pqf-lem-pushforward-qcoh` and `def-weil-pbc-comm-algebra-sheaf`. The rank-one free-module statement explicitly gives quasi-coherence on Spec R; the definition makes that affine-local conclusion enough for O_Z. The pushforward theorem explicitly assumes a quasi-compact and quasi-separated morphism, both supplied by this item's hypotheses; it does not require S to be qcqs. I read Schemes Tag 01LC (`lemma-push-forward-quasi-coherent`), Tag 01HV (`lemma-spec-sheaves`) and Tag 01I7 (`lemma-compare-constructions`), which support these exact uses. Sectionwise rings and h sharp supply the algebra structure by the definition, without any new theorem about algebras being presumed.

For step 2 the existing statement `lem-weil-pbc-affine-morphism-relative-spec` part (2) supplies both pi and alpha, and explicitly says that the morphism corresponding to alpha_U is an isomorphism for every affine U. I verified that it is exactly this chart, rather than a noncanonical arbitrary affine presentation, that is used later. The only hypothesis needed is the quasi-coherent algebra just established. This is the chart content of Tags 01LW/01LX, read in the source.

For step 3 I read the full statement of `lem-weil-pbc-affine-algebra-local-maps` and the docstring and declaration in `lean/WeilConjectures/AlgebraicGeometry/AffineAlgebraLocalMaps.lean`. It permits arbitrary f and requires only g affine. Substituting f=h, g=pi and beta=alpha inverse satisfies that requirement by step 2. Its statement gives all three used facts: maps over S, pairwise overlap equality, and the component beta_U on sections over Y_U. Its section clause is crucial: merely citing a fully-faithful functor would not give this formula. I opened `lem-weil-pbc-morphism-factors-through-open-subscheme` and read Schemes Tag 01HI (`lemma-restrict-map-to-opens`). Its image-containment hypothesis follows pointwise from pi k_U = h restricted: h(z) lies in U for z in Z_U. Thus k_U factors uniquely through the open Y_U. The same unique factorization through U proves e_U is over U; no claim that mere image containment gives factorization through a general immersion is being used. This step needs neither affineness of Z_U nor of overlaps.

For step 4 I opened `lem-weil-pbc-morphism-into-affine-scheme`. Its bijection has an arbitrary scheme source, so it applies to Z_U even when Z_U is nonaffine. Taking sections of q_U e_U in the contravariant order gives alpha_U followed by alpha_U inverse, the identity. This proves precisely q_U e_U = j_U. Overlap compatibility follows from the same k_U obtained simultaneously in step 3, with no gluing theorem or compatibility hidden here. The citations file quotes the relevant statements literally; all eight entries were checked as substrings of the live dependency statements. None of the four non-elementary steps exceeds 2000 characters.

I checked small and boundary cases. Empty U gives empty open subschemes and the unique empty-source morphism, so the identity and overlap formulas still apply. If Z is empty over nonempty S, the direct-image algebra is the zero algebra and the relative spectrum is empty, again consistent. If S is empty, h has empty source. For h:P^1_k to Spec k the source inverse image is not affine, but the Gamma-Spec map and the local-maps lemma still apply. For a nonseparated base, or a base with an affine-open intersection that is not affine, the existing local-maps statement explicitly allows nonaffine overlaps. No finite-type, separated, globally quasi-compact, or nonempty hypothesis was inserted. I checked delivery-errors B through E against the actual four steps: there are no new nodes, no cited proof-only constructions, no missing section-map assertion, and no source or statement correction to report.

The off-unit ingredients are generic scheme tools, declared in `split_report.tool_uses`; they implement the recorded Tag 01LY construction and do not replace the unit's route.

## Unfinished work

None within this split. Existing dependencies retain their own proof/audit state. The required server dry run and delivery follow this report.
