# Stage-1 report: lem-sfb-base-coefficient-condensed-identification

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-base-coefficient-condensed-identification.json`: statement node, split into five elementary construction/check steps; not a Mathlib leaf. The statement and statement dependencies are unchanged. Six actual NU searches were added to the six preserved searches from the node's creation.
- `citations.json`: verbatim statement excerpts for each step-node citation.
- `report.md`: this report. `searches.jsonl` is the search command's own log.

New nodes: 0. New Mathlib leaves: 0. No unit or chapter record changed.

## Attachments

None. Searched the whole `lean/WeilConjectures/` tree for the item tag, base-coefficient terminology, bottom equivalences, unit balls and condensed identifications. Read `CategoryTheory/RingObjects/Condensed/EllAdic.lean` and `Condensed/ContinuousMap.lean`, and inspected the declarations listed in `CategoryTheory/RingObjects/EllAdic.lean`. The project supplies the coefficient objects and inclusions, and generic postcomposition with its identity/composition laws, but no declaration asserts this full item, including the integral identification, natural inverses and inclusion square. Generic project definitions are not an attachment of the item.

## WANTED

None. The blueprint gives the coefficient specialization; the detailed verification is elementary and written here, with `proof_origin.by = agent`. No unavailable external theorem is used.

## What was wrong or incomplete

The imported item had no proof. Its statement is correct: the symbol $E=\mathbf Q_\ell$ in the blueprint must be realized as the structural image inside the fixed algebraic closure. An abstract identification without checking the norm and its unit ball would not justify the asserted condensed identifications. The split now provides those checks and the actual maps, without changing any hypothesis or conclusion. There is no statement dispute, route departure or SGA citation.

The missing `coord/dag-sync.md` mentioned by the inherited standing brief is obsolete for this shared read-only checkout; the explicit current user brief supplies the read and delivery paths. No workaround or repository write was performed.

## Unfinished work

None for this split. No Lean file was written and no compiler, Lake or build command was run.

## Not duplicates

No new node was created. Whole-blueprint searches for `isometric ring`, `bottom intermediate`, `base coefficient` and `isometrically` found no matching imported blueprint node. Whole-DAG searches for the structural-image, bottom-field and isometric-ring terminology identify the item and its parent/citers, rather than another theorem giving these identifications. The existing `sk-def-sfb-condensed-ring` already supplies the generic continuous-map construction and was reused. Its specialized p-adic and integers definition nodes define the same coefficient objects but do not assert the isomorphisms, so no redundant statement node was introduced. The blueprint ancestry command returned `sk-thm-existence`; the existing `from.place` and `via` are retained and `same_as` is the empty list.

## Mathlib search assessment

All new search records are exact queries actually run through msearch.py for NU and this item, recorded in searches.jsonl. Read the printed hits, and read the source of `IntermediateField.botEquiv` (Mathlib/FieldTheory/IntermediateField/Adjoin/Defs.lean:207, with its defining equations at 212 and 216) and `PadicAlgCl.norm_extends` (Mathlib/NumberTheory/Padics/Complex.lean:81). These cover scalar ingredients. LeanSearch also found `TopCat.continuousFunctions.map`, `TopCat.commRingYoneda` and `RingHom.compLeftContinuous`: generic continuous-function constructions, not the whole p-adic, unit-ball and condensed ring-object compatibility statement. The second natural-language phrasing found scalar inclusions and `Padic.withValRingEquiv`, which identifies a valuation completion with p-adic numbers, not the bottom intermediate field. The scoped Padics grep found no condensed coefficient identification. Loogle returned zero hits. No service was reported unavailable. The original six search records are preserved as historical records, not claimed as searches performed by NU.

## Review by NU

I read the chapter and unit records for `sec-six-functors-basics` and `sk-thm-existence`. The unit explicitly identifies the base integral and rational cases with the $\mathcal O_E$ and $E$ cases. I read the opening paragraphs of the current main-20261015 `det-existence-localizing.proof.md` and `det-existence-restriction.proof.md`; these are the source for precisely this specialization, not a proof of Brown representability or a replacement of the unit's geometric route. I also read the current condensed-ring blueprint section and both cited DAG statements in full. There are no new-node sources to review.

Step 1 uses only the hypothesis that $\iota$ is a ring embedding and that $E_0$ is its image. Surjectivity is image membership; injectivity makes the inverse unique. The inverse ring identities follow by applying the injective forward map, as written. This is an elementary argument rather than a new lemma or an appeal to a definition for a theorem.

Step 2 uses the hypothesis that the norm extends the p-adic norm and the specified subspace metric. The displayed norm-of-difference computation proves the distance equality; substitution through the inverse proves the reverse equality. The epsilon/delta check explicitly proves continuity of both maps. No theorem about extending valuations, completeness or finite extensions is needed: extension of the norm is already a hypothesis.

Step 3 cites only the unit-ball formula in `def-weil-l-adic-coefficient-extension`, quoted verbatim in citations.json. It does not take DVR structure, finiteness of the residue field or uniqueness of norm extension from that definition. The norm equality gives membership in both unit balls in both directions, so both restrictions are defined; the inherited ring identities and distances prove the integral clause. This node's use of an absolute value instead of norm notation does not change the datum here: the item's restricted norm is the absolute value defining this unit ball.

Step 4 cites `sk-def-sfb-condensed-ring`, whose statement actually gives continuous-map sections with pointwise operations, the underlying ring-object interpretation, and functorial postcomposition by continuous ring homomorphisms. Its excerpt in citations.json includes those clauses. Continuity was established in steps 2 and 3. The argument explicitly checks preservation of operations and both inverse identities on arbitrary sections. Thus no comparison theorem between unrelated coefficient categories or between constant and continuous-function sheaves is hidden here.

Step 5 cites that same node for restriction by precomposition. Associativity is checked on an arbitrary point for each of the four scalar maps, including the inverses. The scalar inclusion square is checked on an arbitrary integral element, and the resulting equality is then checked on arbitrary sections. This supplies the compatibility clause rather than saying merely that it transports.

I checked B--E of delivery-errors.md against these files. Each cited node says exactly the part used; citations.json contains literal substrings of those statements. Every other step is a short direct argument from the hypotheses or preceding steps; no non-elementary fact is concealed under the elementary marker. No new lemma restates a clause of the item, no unsplit node contains a proof, no source tag or claimed Mathlib match is invented, and no off-unit statement tool is used. Each proof step is under 900 characters, so there is no long step concealing an independent lemma.

The small cases are consistent: $q=0,1$ tests the ring maps; $\lVert q\rVert=1$ checks that the closed unit-ball boundary is included on both sides, while $q=\ell^{-1}$ lies outside both integral rings. A one-point profinite set recovers the scalar square. On the empty profinite set all maps of sections are the unique map of the one-element section ring and all identities still hold; the proof uses no nonemptiness. The argument requires neither completeness of the algebraic closure nor local compactness, a chosen uniformizer, finite quotients, a completion, or any sheafification comparison. No hypotheses were added and no clause was weakened.

The required server dry run and delivery are the remaining mechanical actions at the time of writing this report.

The first dry run rejected the step-3 citation excerpt as shorter than its 40-character minimum. I expanded it to the full unit-ball definition, and expanded the step-4 excerpt to include the condensed-ring and functorial postcomposition clauses. Both are verbatim statement excerpts. No mathematical argument changed.
