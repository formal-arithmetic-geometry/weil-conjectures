# Q67 — lem-per-smooth-punctual-purity-ascent

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-smooth-punctual-purity-ascent.json`: statement split into seven steps; no Mathlib match.
- No new nodes; no Mathlib leaves created.
- `citations.json`: one verbatim statement quotation for each node cited by each step.
- `searches.jsonl`: actual msearch records, retained with this delivery.

## Attachments

None. Searches of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` by the exact blueprint tag and by smooth/punctual purity found no declaration stating this item. The occurrences of punctual purity in the affine-line weight modules concern Frobenius weights, not local cohomological purity. The upstream master reference likewise has no exact tagged declaration for this item. Nothing was compiled.

## WANTED

None. The source for the item and the supporting statements used here is available locally.

## Findings and route

The imported statement is retained exactly. I read ILO Exposé XVI Corollary 3.5.6, printed p.249, with Proposition 3.5.5 immediately before it and Definitions 3.2.1–3.2.2 and Proposition 3.2.3 on p.244. The corollary itself has no separate proof. Its immediate preceding argument uses a relative Gysin class over the trait, but the existing trait-relative-class node is restricted to complete strictly henselian mixed-characteristic traits. Those restrictions are absent from our item. Applying that node here would be a hypothesis error.

Instead, I expanded the fibrewise proof using the existing regular supported base-change theorem, smooth regularity and the same two-of-three criterion. I read ILO XVII Corollary 4.2.3 and its localization-triangle explanation, printed p.281, and XVI Proposition 3.2.5 on p.245. These are the supporting existing statements, not newly manufactured versions of the conclusion. No statement is disputed. The argument proves a more general smooth-ascent fact but the item keeps its original trait and finite-type hypotheses.

The blueprint ancestor is `lem-per-artin-gabber-affine-curve`; the inherited ancestry leads through the regular finite-coefficient duality input to `lem-per-monomial-trait-punctual-purity`, whose zero-exponent affine-space reduction uses this item. The unit and chapter records were read and not changed. No unit key node is being realized here. This is a supporting local calculation under the inherited route, not a replacement of the curve/perverse unit's proof.

The coefficients throughout are the same ordinary small-etale constant `F_ell` modules, regarded as `Z/ell` modules when applying the existing prime-power statement at exponent one. In particular the finite-field, pro-etale smooth-purity theorem is not applied over an arbitrary trait. The supported-base-change input is the existing no-excellence ordinary-etale node; no prohibited trace-route source is cited by this split.

## Mathlib and duplicate searches

I searched the source library by tag and concept, the whole DAG by punctual purity, smoothness, regularity, closed support and the relevant ILO places, and ran `tools/blueprint_refs.py search` for `purity`, `smooth punctual purity ascent`, `Corollary 3.5.6`, and `punctual purity`, as well as its ancestor command. The purity search includes all chapters. Its weight-theoretic punctual-purity hits have different statements.

I ran msearch leanfinder, leansearch, loogle and grep for the item and read their actual returned signatures. A second leanfinder phrasing uses “Gysin fundamental class isomorphism at all local rings”. The results concern algebraic smoothness, etale base change, or scheme presentations; the grep's “Gysin” hits are the substring in `finestTopologySingle`. No returned declaration states cohomological purity. All actual queries and results are appended to the item's existing search records, preserving the inherited searches. There are no newly created nodes to search or declare absent from Mathlib.

## Not duplicates

No new nodes. All substantive ingredients already exist and are cited directly. In particular the two-of-three, prime-field purity, regular supported base-change and regular-immersion calculus statements are reused instead of making trait-specific duplicates. The exact smooth-ascent item is not identified with weight purity or with the etale-locality statement.

## Review by Q67

I read the item, the seven steps and the statement of every cited node, checking B–E of `coord/delivery-errors.md`. I checked the ILO pages named above for the item. No new node needs a separate source review.

Step 1 first checks that the finite-type scheme $X$ over the Noetherian trait is Noetherian using `lem-weil-pbc-finite-type-over-noetherian`. It then uses the regular-scheme ascent clause of `lem-per-regular-lci-geometric-calculus`, the precise open-restriction assertion of `lem-weil-pbc-smooth-restrict-open-subschemes`, the local constancy asserted by `sbc-lem-smooth-relative-dimension-locally-constant`, and the all-affine-pairs finite-type criterion in `lem-weil-pbc-lft-affine-pairs`. In particular I verified that shrinking to a constant-dimension affine chart does not require the original smooth map to be separated or to have globally constant dimension. Punctual purity is a property of the displayed local scheme, so the open restriction changes nothing.

Step 2 uses Noetherian localization, finite-type base change and the Noetherian finite-type theorem with their exact hypotheses. The cited permanence theorem is for fixed relative dimension, which is why Step 1 first chooses that dimension on the source chart. The scheme called `F` is the entire scheme-theoretic fibre of `P` over the closed point of `T`, not a selected geometric point. Smooth regularity is then applied over the regular local scheme `T` and over the field `k`. Each is Noetherian, and invertibility pulls back from `X`.

Step 3 proves all hypotheses needed for the next step. The number `c` is the dimension of the regular local ring on the base, not the relative smooth dimension. A minimal generating set of its maximal ideal has `c` terms, and `lem-weil-pbc-regular-local-generators-regular-sequence` says exactly that it is a regular sequence. The class-calculus geometry node explicitly preserves this codimension under flat base change. `lem-pc-smooth-flat` supplies flatness. After every finite extension of a fibre field, the fibre is still smooth by the cited permanence theorem and is regular by the regularity clause. For these field-extended fibres I also checked finite type by `lem-sfb-finite-type-composition-base-change`, and hence Noetherianness by `lem-weil-pbc-finite-type-over-noetherian`, before applying regularity. Hence the map is regular in the precise flat/geometrically-regular sense used by supported base change, without needing excellence. The first dry run passed; on rereading I made these Noetherian checks explicit in Steps 1 and 3 and regenerated the citation manifest before running preflight again.

Step 4 applies `lem-per-regular-supported-base-change` at `n=1` to the actual Cartesian square from Step 2. I checked that its statement allows arbitrary Noetherian bases and bounded-below constant-coefficient complexes and explicitly gives the closed-counit-normalized comparison, including twists and shifts. The statement of `def-per-closed-support-plus-adjunction` identifies the closed functor with the derived supported kernel and its fixed adjunction, so the two appearances of extraordinary pullback use the same comparison. `lem-asd-etale-finite-twist-pullback` gives the roots-of-unity twist identifications. The flat-base-change clause of `lem-per-regular-immersion-class-calculus` is about the canonical class itself; it therefore identifies the pulled-back map, not just the target object. This was the central C4 check.

Step 5 applies `lem-per-prime-field-punctual-purity` to `F` over the prime subfield of `k`. Its statement explicitly imposes neither finite type over that prime field nor excellence. Thus an imperfect or transcendental residue field causes no missing hypothesis. This invokes an existing theorem, rather than calling fibre purity elementary.

Step 6 applies the actual (a)+(b) implies (c) assertion of `lem-per-punctual-purity-two-of-three`. Its statement is for regular Noetherian closed pairs of locally constant codimension with the same normalized Kummer map; those hypotheses and that map were established in Steps 2–4. The conclusion is purity on the image of the closed fibre, which suffices for the chosen point; I did not infer purity at unrelated points from it.

Step 7 is an elementary localization calculation. I wrote both inverse maps for tensoring with a localization and both inverse fraction maps after localizing at the prime of `y`. They identify the ambient local rings, residue fields and closed pairs, so there is no unsupported claim that two different costalks “transport”. The cited flat-base-change clause of class calculus supplies compatibility of the normalized maps under this isomorphism, including its codimension-zero identity clause. The elementary designation is for these explicit fraction maps and use of that stated compatibility; no new purity assertion is hidden here.

I tested empty source, relative dimension zero (etale maps), base local dimension zero (the fibre inclusion is the identity), generic and closed trait points, and nonclosed points of positive-dimensional smooth fibres. The argument never assumes that the chosen point is closed in its fibre, that the residue field is finite/separable/perfect, or that local-ring dimension equals local topological dimension. Applying the fibre theorem at every point and then identifying the local rings handles these cases. I also checked the dependency closures of the base-change and prime-field-purity inputs for paths back to the item; none exists. Every proof step is below 2000 characters. No new clause-sized node or unproved comparison has been introduced.

The off-unit smoothness restriction, local constancy, permanence, regular-system-of-parameters, smooth-flat and Tate-line statements are generic tools; their reasons are declared in `split_report.tool_uses`. They do not replace any unit-level curve argument. Other off-unit statements used here are already Mathlib leaves.

## Unfinished work

No mathematical part remains in this one-level split. The cited existing nodes retain their own stage status. No Lean files or live-project files were written, and no compiler, Lake or build command was run. Delivery is subject to the required server dry run.
