## Files written

- `dag/nodes/sec-smooth-purity/lem-kun-tensor-base-change-exact-transformation.json`: item, statement, now split; Mathlib verdict no exact match. Five proof steps, all shorter than 2000 characters.
- No new nodes and no new Mathlib leaves.
- `citations.json`: one verbatim statement quotation for each of the 19 step/node pairs.
- `searches.jsonl`: actual msearch log. `write_split.py` is sandbox-only preparation code, not a delivered project file.

## Attachments

None. I searched `lean/WeilConjectures/` for the blueprint id and for tensor/base-change terminology. `AlgebraicGeometry.Etale.tensorBaseChangeMap_naturality` in `WeilConjectures/SixFunctors/Etale/Derived/Kunneth/Ordinary.lean:151` covers naturality of the underlying map, but does not state the two shift squares or separate exactness. The isomorphism declarations at lines 416 and 450 have sorry proofs and do not establish this item. They are not attachments.

## WANTED

None. The required blueprint and Stacks source text are available locally.

## Corrections and scope

The imported statement is unchanged. No statement dispute or unit-route departure was found. The imported item had no proof. Its missing argument is coherence of the actual mate, not invertibility of base change. I retained all provenance fields and prior Mathlib searches and appended only searches that I ran through msearch. I inspected the saved result of the interrupted first search before reusing it. The initial LeanFinder result was underived sheaf adjunctions and Kaehler differentials; the second phrasing found generic adjunction shift identities. Loogle and Mathlib grep returned no matches. LeanSearch returned generic CommShift/counit formulas and exact-derived factorization, which assume or supply only individual constituents, not this tensor base-change transformation. I read the relevant Mathlib Shift/Adjunction and DerivedCategory/ExactFunctor source before making that distinction.

The proof reuses existing statements rather than creating nodes for elementary composition, a termwise compositor square, or the algebraic mate calculation. The generic tools outside the Kunneth unit are declared in `split_report.tool_uses`: exact inverse image, exact-derived factorization, unbounded right-derived exactness, exact-functor composition, canonical tensorator shifts, canonical derived-adjunction shifts, and tensor-shift descent. None replaces a step of the unit's telescope route.

## Not duplicates

No new nodes. Whole-DAG title and statement searches found existing `lem-kun-derived-tensor-triangulated`, `lem-weil-pbc-pullback-tensor-canonical-shift-unit`, `lem-sp-canonical-right-derived-adjunction-shift`, and the other generic tools now cited. Blueprint searches for tensor shift, shift, and tensor base did not find another blueprint statement of this item. `blueprint_refs.py ancestor` identifies `lem-kun-0f1n`; the existing precise paragraph-1 origin is retained.

## Review by Q139

I read the chapter and unit records and the current main-20261015 proof of `lem-kun-0f1n`. Its paragraph 1 starts the direct-sum/telescope reduction. Exactness and compatibility of the specified map with shifts are prerequisites for that route; this split supplies them without claiming base-change invertibility. I also read Stacks `sites-cohomology.tex`, `definition-derived-tor`, `lemma-pullback-tensor-product` (07A4), and `lemma-adjoint` (07A6), `derived.tex` `lemma-derived-shift` (05SU) and the argument for `lemma-adjoint-is-exact` (0A8D), and `more-algebra.tex` `item-shift-tensor` (0FNH). Stacks supplies the constructions; the five-step assembly and mate calculation are mine, so proof_origin is agent.

For Step 1 I opened every cited node statement. The exact module inverse-image statement supplies both exactness and the constant-ring identification; exact-derived factorization gives its termwise shifts and triangulated structure. The unbounded-exchange definition supplies K-injective right derived direct images; the unbounded right-derived triangulated lemma gives exactness, rather than incorrectly taking it from the definition. Tensor exactness is exactly what `lem-kun-derived-tensor-triangulated` states. The composite lemma applies four times with one tensor input fixed. No properness, finite type or boundedness is needed.

For Step 2 the canonical-shift-unit node explicitly states both integer-shift squares for the normalized ringed-topos inverse tensorator. This is stronger than the inverse-image-monoidal node, which alone supplies only invertibility and bifunctoriality. I verified that the ringed-topos structural map here is the constant-ring isomorphism from the exact inverse-image node, so its pullback equals the stipulated inverse image. Both normalizations are the same ordinary pullback tensor map on K-flat representatives, and exact-derived factorization uses its termwise shifts. Thus the proof retains the prescribed comparison, not merely some available strong monoidal structure.

For Step 3 the unbounded-exchange statement explicitly defines the square isomorphism by termwise descent. Writing its degree-r component on K[m] as theta at K^{r+m} checks the shift square directly. Exact-derived factorization supplies the identity comparisons, and localization clause (3) is precisely equality detection after localization; clause (2) supplies naturality. I deliberately did not cite the bounded-below integer-coefficient square-shift node, whose statement has the wrong domain for this application. This is an elementary componentwise argument, not an omitted new comparison lemma.

For Step 4 I used the general exact-left-adjoint/K-injective-right-adjoint node, whose statement explicitly retains the fixed canonical shifts and is unbounded. The exact module adjunction and the existence of the K-injective construction are supplied by the other two cited statements. It applies to g and h without a finiteness hypothesis. The tensor-shift-descent statement explicitly includes arbitrary derived morphisms of the other input; this is the fact needed when tensoring the derived counit, which need not be represented by a chain map on arbitrarily chosen models. Combining those equations with Steps 2 and 3 proves the displayed equation for beta. There is no hidden projection-formula invertibility claim.

For Step 5 the mate is R(beta) followed after the adjunction unit, exactly the formula provided by unbounded exchange. I wrote every intermediate equality: naturality of eta moves the A shift comparison, naturality of the R shift moves R(beta[m]), and the unit shift equation cancels the remaining L and R comparisons. This is a short formal calculation from the cited canonical-adjunction statement, so it is elementary. Naturality follows from the same mate formula. The equation is valid for each integer m; no unproved induction from shift one is being used.

I checked the source hypotheses against the actual module categories rather than the bounded-below abelian ones, and checked the direction of every tensorator and the codomains LA, D, RD in the mate formula. Small cases: all maps identities reduce alpha to the identity tensor map; either input zero gives the unique zero map; m=0 gives naturality with identity shifts; for m=1 the first tensor shift is unsigned and the second has the factor (-1)^p on first degree p, exactly as in 0FNH; negative shifts are already covered by the cited integer-shift statements. Empty schemes and the zero coefficient ring impose no extra hypotheses. Separate exactness remains true without any assertion that alpha is an isomorphism.

Against delivery-errors B--E: no new statement-only lemmas are necessary, all non-elementary facts are supplied by cited statements, all 19 quotations are literal substrings checked against the actual node JSON, no citation uses the proof of another node, and a transitive dependency traversal finds no return path to this item. Each step is under 2000 characters. No Lean file, compiler, Lake or global build was used.

## Unfinished work

None in the stage-1 split. The existing cited nodes retain their own states; this delivery does not claim their Lean proofs are finished. Required server preflight and delivery results follow below.

Dry run 1 rejected one citation quotation as shorter than 40 characters. I replaced it with the full exact-functor-composite statement; no proof or statement changed.
