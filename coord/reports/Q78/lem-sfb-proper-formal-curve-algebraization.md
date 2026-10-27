# Stage-1 delivery: lem-sfb-proper-formal-curve-algebraization

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-proper-formal-curve-algebraization.json`: existing statement, split into eight proof steps; existing mathematical statement and inherited metadata retained; definition links for power series and topological dimension made explicit. Fresh Mathlib searches appended to the inherited searches.
- `dag/nodes/sec-six-functors-basics/lem-sfb-polarized-formal-algebraization.json`: new statement-only lemma, unsplit, not a Mathlib leaf. Grothendieck's polarized algebraization theorem for an arbitrary adically complete Noetherian ring, with its finite projective-space embedding made explicit.
- `citations.json`: 24 verbatim statement quotations, one for every dependency of every proof step.

One new node; zero new Mathlib leaves. No Lean files, compiler invocations, repository writes, or manual git commands.

## Attachments

None. Searches under `lean/WeilConjectures/` for the exact blueprint tag, formal curves, curve algebraization, polarized formal schemes and algebraization theorem found no declaration stating this item or the new lemma. Existing coherent-module and finite-over-proper algebraization declarations have different inputs and conclusions, and do not attach this item.

## WANTED

None. All mathematical sources needed are present in `literature/stacks-project/`.

## Issues found and scope

The item's existing correction to Stacks 0E7R is essential and is preserved: the printed statement omits properness although its proof immediately calls X_1 proper. Without properness, X_n = affine one-space over R_n is a counterexample: the alleged projective algebraization would have projective special fibre affine one-space over k. The assigned item already explicitly assumes properness of every X_n, so this delivery makes no further statement correction. The empty curve and dimension-zero schemes remain allowed.

The item previously had no proof. It is not sufficient to cite the bare 0E7R assertion: the split now supplies the compatible polarization by induction, then cites the polarized effectivity theorem whose hypotheses include that additional data. Flatness is proved separately, since neither 0E7R nor 089A states it. Finite presentation is checked separately as well. In particular, flatness of the algebraization on the closed fibre is not inferred from flatness of X_1 alone: all powers are used in 0523.

## Not duplicates

No existing unmerged node has 089A or 0899 in its source. Whole-DAG keyword and source-label searches, and blueprint searches for algebraization, polarized, 089A, 0D4G and infinitesimal neighbourhoods, found no existing polarized formal-scheme effectivity theorem. Coherent-module Grothendieck existence and finite-over-a-fixed-proper-scheme algebraization are different: the new lemma constructs the proper ambient scheme itself from a supplied formal polarization. The new node has no dimension restriction or flatness assertion; conversely it assumes a compatible polarization, which is constructed by steps 2-3 of this item. Thus it does not restate the item or merely move its curve argument below a new name.

A search for flatness modulo powers found `lem-weil-pbc-flat-module-powers`, so the initially contemplated geometric flatness-on-infinitesimal-neighbourhoods node was not created. The existing statement suffices directly on affine charts. The ample-bundle existence and dimension-one Picard lifting results are likewise reused rather than restated.

## Mathlib and blueprint searches

The ten fresh searches are recorded by msearch.py in `searches.jsonl`, and their complete output is saved in the corresponding `item-*.txt` and `polarized-*.txt` files. Each of the item and the new lemma was searched with two semantic phrasings in LeanFinder, Loogle, grep and LeanSearch; all services answered. The JSON contains the exact tool/query pairs and actual returned output. The new node's five searches all have verdict no match. The inherited item searches are retained.

The main apparent candidates are Proj properness and valuative existence, which establish a property of a specified graded-ring construction; they do not construct a graded ring or a scheme realizing a formal system. The affine-transition-limit declarations concern maps between already given schemes and their cofiltered limits, rather than a compatible family of nilpotent thickenings. Formal unramifiedness and the Flat class do not supply effectivity. I inspected Mathlib's ProjectiveSpectrum/Proper.lean and the statements returned for AffineTransitionLimit and Flat. The power-series DVR instance returned by LeanSearch is useful ring structure, not an algebraization theorem. No exact or one-line specialization was found.

The item's blueprint ancestor command reports `blueprint.from.node = None`; this is the inherited ancestry, not a missing invented blueprint id. The new node extends the exact inherited place (the isolated-lci smoothing input on the ctf-stability branch), prepends this item to its inherited `via` chain, and records no same-as blueprint match. Chapter and unit records are read and unchanged: this item is an auxiliary lemma, not the unit's key statement.

## Review by Q78

I read Stacks spaces-more-morphisms.tex, lemma-formal-algebraic-space-proper-reldim-1 (0E7R), including its ample-bundle lifting and final algebraization paragraphs. For the sole new node I read coherent.tex, theorem-algebraization (089A), from the hypotheses through the last line of the proof, and lemma-algebraize-formal-closed-subscheme (0899). The theorem is stated as proper algebraization with an ample module, while its proof actually constructs a closed subscheme of a fixed finite projective space. This is why the new statement's finite-projective-space clause is justified; it does not rely on confusing projective-bundle projectivity with the convention required here. I also read the power-series remark 032C, the Picard lifting lemma 09NY, the definition statements used, and algebra.tex lemma-flat-module-powers (0523), together with the geometric translation 0D4G.

For step 1 I opened `lem-weil-pbc-power-series-field-cohen-regular-complete`, `lem-weil-pbc-finite-type-over-noetherian`, and `def-weil-proper-morphism`. The first gives all the required Noetherian/local/domain/completeness and residue assertions with coefficient field k and d=1. The second applies because proper includes finite type and the quotient base is Noetherian. Quotient Noetherianity is written out by lifting ideal chains; it is not imported from an unrelated regularity statement.

For step 2 I opened `lem-weil-pbc-quotient-base-change-closed-immersion-ideal`, which explicitly gives both the closed immersion and its affine quotient description. Its ideal is t^n on X_(n+1), hence nilpotent, and the proof writes out why quotient prime correspondence gives a homeomorphism. The node `lem-weil-pbc-noetherian-scheme-closed-subsets-minimal` supplies precisely the topological Noetherian condition required by the lifting theorem. Dimension is preserved because these are actual homeomorphisms, not merely bijections of points.

For step 3 I opened `lem-sc-dim-one-ample-invertible` and `lem-sc-pic-lift-closed-immersion-dim-le-one`: the former allows an arbitrary field and dimension at most one, including empty X; the latter takes exactly a closed immersion into a scheme whose underlying space is Noetherian of dimension at most one. Those hypotheses are steps 1-2. The induction is explicitly based at L_1 and lifts each L_n to L_(n+1), choosing the restriction isomorphism too. The statement of `def-pc-module-pullback` supplies its canonical composition isomorphisms. The required comparisons for nonadjacent stages are their composites, so no separate unproved simultaneous-compatibility assertion is hidden.

For step 4 I compared every hypothesis of the new polarized algebraization node with the data just constructed: A=R is complete for I=(t), X_1 is proper, the given scheme squares are cartesian, and the recursively chosen invertible modules and restriction isomorphisms have ample first term. The cited statement gives compatible scheme isomorphisms at all n and the finite-projective-space embedding. The new node remains statement-only; none of its proof is silently assumed inside its statement.

For step 5 I opened `pqf-lem-lft-fp-locnoeth`: its target hypothesis is locally Noetherian, which holds for Spec R. Properness gives finite type and quasi-compactness, while its closed diagonal gives quasi-separatedness. `def-sbc-locally-finite-presentation` explicitly states that local finite presentation plus quasi-compactness and quasi-separatedness is finite presentation. The finite-type-over-Noetherian statement also proves Y Noetherian, needed next. No finite-type-only conclusion is substituted for finite presentation.

For step 6 I opened `pqf-lem-affine-open-locnoeth`, the quotient-base-change statement, `def-weil-flat-morphism`, and `lem-weil-pbc-flat-ring-map-iff-flat-affine`. They say respectively that B is Noetherian, that the base-changed affine chart is Spec(B/t^n B), that flatness is local on the unchanged stalks when restricting the source, and that its affine flat morphism is precisely a flat ring map. Consequently the quotients required in 0523 are flat over R/(t^n), not just over k.

For step 7 I opened `lem-weil-pbc-flat-module-powers` in full. It requires both rings Noetherian and M finite over the second ring; M=B satisfies this with generator 1, without incorrectly supposing B finite over R. Its conclusion says that B_q is flat over R for primes containing t, exactly the closed-fibre points. The affine-open-stalk-localization node identifies this with the actual local ring of Y, and Spec R has local ring R at (t). Thus the cited assertion gives the pointwise flatness claimed here.

For step 8 I opened `lem-weil-power-series-unit-constant-coefficient`, `lem-weil-pbc-affine-open-stalk-localization`, `lem-pc-flat-field`, and the flat-morphism definition. Factoring a nonzero series at its least nonzero coefficient, together with the stated unit criterion, proves that the only base primes are (0) and (t). The local ring at (0) is a field; the field-module assertion in the cited flat-field node makes every local ring above it flat over that field. This checks the generic points directly, instead of assuming closed-fibre flatness automatically covers the whole source.

Every proof dependency has a verbatim full-statement quote in citations.json; none uses the proof of another node in place of its statement. Off-unit statements are recorded as generic tool uses in split_report.tool_uses: they are the ring/scheme and dimension-one lifting tools for this auxiliary algebraization step, not replacements for the unit's global route. I checked no new node is elementary, a duplicate, or one clause of the item: the only new theorem is the general polarized effectivity input. All eight proof steps have fewer than 900 characters, so none triggers the long-step threshold. The routine nilpotent-prime and power-series factorization arguments are written out.

Small cases: when X_1 is empty, all X_n have empty underlying space and the theorem permits the empty algebraization (its empty closed immersion into P^0 is valid); dimension zero still satisfies both line-bundle lemmas. No algebraic closure, smoothness, reducedness, connectedness, or assumption on char k is introduced. For the new general theorem, I=A forces A=0 by completeness and gives the empty case, and I=0 gives a constant scheme system; neither contradicts its conclusion. Polarization is an actual compatible family, not merely ample classes on independent thickenings. The inherited properness omission in 0E7R is explicitly diagnosed above rather than copied into the new node.

## Unfinished work

The new polarized effectivity theorem is deliberately left unsplit, as a stage-1 child for a later worker. There is no unresolved gap in the eight-step split of the assigned item.
